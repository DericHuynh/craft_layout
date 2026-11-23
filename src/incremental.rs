use crate::*;
use crate::solve::dependency_rules::{self, Form, Input};
use crate::solve::cycle_rules::{self, Route};
use crate::Axis::{X, Y};
#[path = "placement_work.rs"]
mod placement_work;
pub(crate) use placement_work::{PlacementWork, update_scale_dirty};

#[path = "registration_rules.rs"]
mod registration_rules;
use registration_rules::{AxisEdits, Context as SeedContext, Seeds};
#[path = "region_list.rs"]
mod region_list;
#[path = "queue_storage.rs"]
mod queue_storage;
pub(crate) use queue_storage::WorkQueue;
mod inputs;
mod checked_view;
mod publication;
pub(crate) use checked_view::OutputRecord;
use checked_view::CheckedView;
use publication::{Publication, publication_route};
pub(crate) use inputs::SameInput;

/// What `solve_layout_incremental` did. The `Fallback` variants give the reason for a full solve.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IncrementalRelayoutOutcome {
    /// The relayout was incremental.
    Success {
        /// Slot computations.
        computed: u32,
    },
    /// The checked pass found different sizing values or output rectangles.
    /// The tree keeps the result of the canonical full solve.
    CheckedIncrementalRelayoutMismatch,
    /// The incremental relayout fell back to a full relayout because the full layout was never solved before.
    FallbackNeverSolved,
    /// Legacy outcome retained for API compatibility. Structural edits use incremental measurement.
    FallbackStructuralChange,
    /// The previous solve found a cycle and this pass has no structural edits to rebuild its dependencies.
    FallbackCycle,
    /// A block or wrapping flow must rebuild its line or collapsed-margin data.
    FallbackFlow,
    /// The queued work exceeded its budget, or a dependency rank exceeded the queue's representable ordering.
    FallbackTooMuchWork,
    /// The incremental relayout fell back to a full relayout because `LayoutTree::invalidate()` was called explicitly.
    FallbackInvalidated,
}

pub(crate) use crate::structural_changes::StructuralChange;

impl NodeLayoutData {
    pub(crate) fn mark_moved(&mut self) {
        self.structural_change = self.structural_change.with_move();
    }

    pub(crate) fn mark_subtree_changed(&mut self) {
        self.structural_change = StructuralChange::Subtree;
    }

    pub(crate) fn mark_children_changed(&mut self) {
        self.structural_change = self.structural_change.with_children();
    }

    pub(crate) fn mark_placement_changed(&mut self) {
        self.placement = PlacementWork::Subtree;
    }
}

impl<I> LayoutData<I> {
    pub(crate) fn record_node_change(&mut self, i: I, old: &LayoutParams, new: &LayoutParams, node: &mut NodeLayoutData) -> bool {
        if !self.tracks_structure() { return false; }
        let change = NodeChange::between(old, new, self.tracks_sizes());
        if self.record_change(i, change) {
            node.mark_subtree_changed();
        } else {
            node.mark_placement_changed();
        }
        change.is_none()
    }

    pub(crate) fn tracks_structure(&self) -> bool {
        use IncrementalRelayoutOutcome::*;
        matches!(self.pending_full_solve, None | Some(FallbackFlow | FallbackTooMuchWork))
    }

    fn tracks_sizes(&self) -> bool {
        self.pending_full_solve.is_none()
    }

    // A queued node can be deleted before the next solve. Mark it on the live tree
    // as well, so a later structural pass can discard all queued IDs safely.
    fn record_change(&mut self, i: I, change: Option<NodeChange>) -> bool {
        match change {
            None => true,
            // While a sizing fallback is pending, between() only checks for a change
            // of rule. Retain the live mark if the batch later includes a tree edit.
            Some(_) if self.pending_full_solve.is_some() => true,
            Some(change) if change != NodeChange::default() => {
                if self.accept_sizing_change() && !self.children_changed {
                    self.node_changes.push((i, change));
                }
                true
            }
            Some(_) => false,
        }
    }

    fn record_content(&mut self, i: I) -> bool {
        if !self.tracks_structure() { return false; }
        if self.accept_sizing_change() && !self.children_changed {
            self.content_changes.push(i);
        }
        true
    }

    pub(crate) fn record_content_change(&mut self, i: I, node: &mut NodeLayoutData) {
        if self.record_content(i) { node.mark_subtree_changed(); }
    }

    pub(crate) fn start_children_change(&mut self) -> bool {
        if !self.tracks_structure() { return false; }
        // Regional measurement includes earlier sizing marks, regardless of edit order.
        self.pending_full_solve = None;
        self.children_changed = true;
        true
    }

    pub(crate) fn record_children_change(&mut self, node: &mut NodeLayoutData) {
        if self.start_children_change() {
            node.mark_children_changed();
        }
    }

    /// Check the fallback before growing a change list that the solver would discard.
    fn accept_sizing_change(&mut self) -> bool {
        use registration_rules::Intake;
        let at_limit = self.node_changes.len() + self.content_changes.len() >= (self.n_nodes_solved / 2) as usize;
        match registration_rules::intake(!self.tracks_sizes(), self.has_cycle, self.children_changed, self.has_flow, at_limit) {
            Intake::Region | Intake::Queue => true,
            Intake::Pending | Intake::Cycle => false,
            Intake::Flow => {
                self.pending_full_solve = Some(IncrementalRelayoutOutcome::FallbackFlow);
                false
            }
            Intake::Budget => {
                self.pending_full_solve = Some(IncrementalRelayoutOutcome::FallbackTooMuchWork);
                false
            }
        }
    }

    /// An explicit full solve takes priority over a fallback inferred from sizing edits.
    pub(crate) fn request_full_solve(&mut self, reason: IncrementalRelayoutOutcome) {
        if self.tracks_structure() {
            self.pending_full_solve = Some(reason);
        }
    }

    pub(crate) fn clear(&mut self) {
        self.children_changed = false;
        self.unknown_structure = false;
        self.node_changes.clear();
        self.content_changes.clear();
    }
}

/// The sizing inputs that changed. Placement reads the latest params directly.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub(crate) struct NodeChange {
    declared: u8,
    inner: Xy<bool>,
    margin: Xy<bool>,
    fill_weight: bool,
    content: bool,
}

impl NodeChange {
    /// A structural change requires rebuilding the affected dependencies.
    fn between(old: &LayoutParams, new: &LayoutParams, track_sizes: bool) -> Option<Self> {
        if is_structural(old, new) {
            return None;
        }

        let mut change = Self::default();
        if !track_sizes {
            return Some(change);
        }
        for axis in [X, Y] {
            for (kind, changed) in [
                (Kind::Regular, !old.size[axis].same_input(&new.size[axis])),
                (Kind::Min, !old.min_size[axis].same_input(&new.min_size[axis])),
                (Kind::Max, !old.max_size[axis].same_input(&new.max_size[axis])),
            ] {
                change.declared = registration_rules::register_declaration(change.declared, slot_index(axis, kind), changed);
            }
            change.inner[axis] = !old.padding[axis].same_input(&new.padding[axis]);
            change.margin[axis] = !new.free_placement && old.margin[axis] != new.margin[axis];
        }
        change.fill_weight = !new.free_placement && !old.fill_weight.same_input(&new.fill_weight);
        let max_changed = [X, Y].into_iter().any(|axis|
            registration_rules::declaration_changed(change.declared, slot_index(axis, Kind::Max))
        );
        change.content = registration_rules::content_input_changed(
            !old.image.same_input(&new.image), new.content_measure != ContentMeasure::None,
            change.inner.x || change.inner.y, max_changed,
        );
        match (old.children_layout, new.children_layout) {
            (ChildrenLayout::Stack { spacing: a, .. }, ChildrenLayout::Stack { axis, spacing: b, .. }) if !a.same_input(&b) => {
                change.inner[axis] = true;
            }
            (ChildrenLayout::Wrap { spacing: a, line_spacing: line_a, .. }, ChildrenLayout::Wrap { axis, spacing: b, line_spacing: line_b, .. }) => {
                change.inner[axis] |= !a.same_input(&b);
                change.inner[axis.other()] |= !line_a.same_input(&line_b);
            }
            (a @ ChildrenLayout::Grid { .. }, b @ ChildrenLayout::Grid { .. }) if !a.same_input(&b) => {
                change.inner = Xy::new_symm(true);
            }
            _ => {}
        }
        Some(change)
    }
}

/// True if the change can change the dependencies between the slots.
fn is_structural(old: &LayoutParams, new: &LayoutParams) -> bool {
    use std::mem::discriminant;
    let same_kind = |a: Option<Size>, b: Option<Size>| a.map(|a| discriminant(&a)) == b.map(|b| discriminant(&b));
    let same_layout = match (old.children_layout, new.children_layout) {
        (ChildrenLayout::Free, ChildrenLayout::Free) => true,
        (ChildrenLayout::Block, ChildrenLayout::Block) => true,
        (ChildrenLayout::Stack { axis: a, .. }, ChildrenLayout::Stack { axis: b, .. }) => a == b,
        (ChildrenLayout::Wrap { axis: a, .. }, ChildrenLayout::Wrap { axis: b, .. }) => a == b,
        // The `Count` grid cells are assigned in `prepare`.
        (ChildrenLayout::Grid { columns: MainAxisCellSize::Count(a), main_axis: main_a, backfill: backfill_a, .. }, ChildrenLayout::Grid { columns: MainAxisCellSize::Count(b), main_axis: main_b, backfill: backfill_b, .. }) => a == b && main_a == main_b && backfill_a == backfill_b,
        (ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis: main_a, backfill: backfill_a, .. }, ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis: main_b, backfill: backfill_b, .. }) => main_a == main_b && backfill_a == backfill_b,
        _ => false,
    };
    old.disabled != new.disabled
        || old.free_placement != new.free_placement
        || old.grid_span != new.grid_span
        || old.text != new.text
        || old.content_measure != new.content_measure
        || old.image.is_some() != new.image.is_some()
        || ! same_layout
        || [X, Y].into_iter().any(|axis| {
            ! same_kind(Some(old.size[axis]), Some(new.size[axis]))
                || ! same_kind(old.min_size[axis], new.min_size[axis])
                || ! same_kind(old.max_size[axis], new.max_size[axis])
        })
}

/// Disjoint subtrees to measure in document order, plus live counts for the next solve.
pub(crate) struct StructuralPlan<I> {
    regions: Vec<I>,
    retained: SubtreeCounts,
}

#[derive(Clone, Copy)]
pub(crate) struct PlanFrame<I> {
    node: I,
    next: Option<I>,
    start: usize,
    retained: SubtreeCounts,
    independent: Option<bool>,
    changed_children: bool,
    coupled: bool,
    placement: PlacementWork,
}

pub(crate) enum PlanStep<I> {
    Done(bool),
    Children(PlanFrame<I>),
}

#[derive(Default, Clone, Copy)]
pub(crate) struct SubtreeCounts {
    pub(crate) nodes: u32,
    pub(crate) blocks: usize,
    pub(crate) has_flow: bool,
    has_cycle: bool,
}

impl SubtreeCounts {
    pub(crate) fn include(&mut self, flags: NodeFlags) {
        // A disabled node has no solved slots. An enabled node has both final sizes.
        if flags != NodeFlags::EMPTY {
            self.nodes = cycle_rules::add_count(self.nodes, 1);
            self.blocks = self.blocks.saturating_add(usize::from(flags.is_block_container()));
            self.has_flow |= flags.has_flow();
            self.has_cycle |= flags.has_cycle();
        }
    }
}

pub(crate) trait Incremental: Solve {
    fn measure_structure(&mut self, window_size: Xy<f32>) -> IncrementalRelayoutOutcome {
        // Reconciliation can use the cleared region buffer for its style edits.
        let mut regions = std::mem::take(&mut self.layout_data().regions);
        if self.layout_data().unknown_structure && self.reconcile_topology(&mut regions)
            && let Some(snapshot) = self.layout_data().topology.take()
        {
            let mut tickets_valid = true;
            let outcome = self.measure_structure_regions(window_size, regions, |tree, region| {
                let ticket = tree.node_layout_data(region).topology_index;
                let sizes = tree.measure_subtree(region);
                // Sizing can reset records only inside this retained region.
                tickets_valid = tickets_valid && snapshot.restore_region_tickets(tree, region, ticket);
                sizes
            });
            if tickets_valid {
                self.layout_data().topology = Some(snapshot);
            } else {
                self.layout_data().topology = Some(TopologySnapshot::new());
                self.remember_topology();
            }
            outcome
        } else {
            let outcome = self.measure_structure_regions(window_size, regions, Self::measure_subtree);
            self.remember_topology();
            outcome
        }
    }

    fn measure_structure_regions(
        &mut self, window_size: Xy<f32>, regions: Vec<Self::NodeId>,
        mut measure_region: impl FnMut(&mut Self, Self::NodeId) -> (u32, u32, usize),
    ) -> IncrementalRelayoutOutcome {
        let root = self.root();
        let old_window = std::mem::replace(&mut self.layout_data().window_size, window_size);
        if [X, Y].into_iter().any(|axis| !old_window[axis].same_input(&window_size[axis])
            && DECLARED_SIZES.into_iter().any(|kind| self.read_size(root, axis, kind).is_some_and(|size| size.is_flex())))
        {
            self.node_layout_data_mut(root).mark_subtree_changed();
        }
        let mut plan = StructuralPlan {
            regions,
            retained: SubtreeCounts::default(),
        };
        self.plan_subtree(root, &mut plan);
        let data = self.layout_data();
        // Pending queues can reference removed IDs. The live nodes carried the same edits.
        data.clear();
        data.has_flow = plan.retained.has_flow;
        data.has_cycle = plan.retained.has_cycle;
        let mut computed: u32 = 0;
        for &region in &plan.regions {
            let (nodes, slots, blocks) = measure_region(self, region);
            self.node_layout_data_mut(region).placement = PlacementWork::Subtree;
            plan.retained.nodes = cycle_rules::add_count(plan.retained.nodes, nodes);
            plan.retained.blocks = plan.retained.blocks.saturating_add(blocks);
            computed = computed.saturating_add(slots);
        }
        self.layout_data().n_nodes_solved = plan.retained.nodes;
        self.compact_block_margins(plan.retained.blocks);
        plan.regions.clear();
        self.layout_data().regions = plan.regions;
        IncrementalRelayoutOutcome::Success { computed }
    }

    /// Discover sizing regions in sibling order. A completed child can force
    /// the parent to replace its tentative child regions with one enclosing cut.
    fn plan_subtree(&mut self, node: Self::NodeId, plan: &mut StructuralPlan<Self::NodeId>) {
        let mut step = self.begin_plan(node, plan);
        let mut parents = work_stack::work_stack::<_, 8>(Vec::new());
        loop {
            let mut frame = match step {
                PlanStep::Children(frame) => frame,
                PlanStep::Done(size_changed) => {
                    let Some((mut frame, child)) = parents.pop() else { return; };
                    self.include_planned_child(&mut frame, child, size_changed);
                    frame
                }
            };
            while let Some(child) = frame.next {
                frame.next = self.next_sibling(child);
                // Clean leaves need no planner frame or cache writes.
                let cached = self.node_layout_data(child);
                if cached.structural_change == StructuralChange::Clean && cached.placement == PlacementWork::Clean
                    && self.first_child(child).is_none()
                {
                    plan.retained.include(cached.flags);
                    continue;
                }
                match self.begin_plan(child, plan) {
                    PlanStep::Done(changed) => self.include_planned_child(&mut frame, child, changed),
                    PlanStep::Children(child_frame) => {
                        parents.push((frame, child));
                        frame = child_frame;
                    }
                }
            }
            step = PlanStep::Done(self.finish_plan(frame, plan));
        }
    }

    fn begin_plan(&mut self, node: Self::NodeId, plan: &mut StructuralPlan<Self::NodeId>) -> PlanStep<Self::NodeId> {
        let mark = self.node_layout_data(node).structural_change;
        if region_policy::starts_region(mark) {
            self.node_layout_data_mut(node).placement = PlacementWork::Subtree;
            plan.regions.push(node);
            return PlanStep::Done(true);
        }
        if self.node_layout_params(node).disabled {
            self.node_layout_data_mut(node).placement = PlacementWork::Clean;
            return PlanStep::Done(false);
        }
        let independent = (mark == StructuralChange::Children).then(|| self.try_refresh_independent_parent(node));
        // A changed, coupled child list already requires measuring the whole region.
        // prepare() will visit and count those descendants, including any pending edits.
        let start = plan.regions.len();
        if independent == Some(false) {
            return PlanStep::Done(self.rebuild_region(node, plan, start));
        }
        let retained = plan.retained;
        plan.retained.include(self.node_layout_data(node).flags);
        let changed_children = mark == StructuralChange::Children;
        let coupled = self.node_layout_params(node).children_layout != ChildrenLayout::Free;
        let placement = self.node_layout_data(node).placement.for_parent(changed_children, coupled);
        PlanStep::Children(PlanFrame {
            node, next: self.first_child(node), start, retained, independent, changed_children, coupled, placement,
        })
    }

    #[inline]
    fn include_planned_child(&self, frame: &mut PlanFrame<Self::NodeId>, child: Self::NodeId, size_changed: bool) {
        frame.changed_children |= size_changed;
        if frame.placement != PlacementWork::Subtree {
            let free = size_changed && frame.coupled && self.node_layout_params(child).free_placement;
            let coupled_size_change = placement_work::coupled_child_changed(frame.coupled, size_changed, free);
            frame.placement = frame.placement.with_child(self.node_layout_data(child).placement, coupled_size_change);
        }
    }

    fn finish_plan(&mut self, frame: PlanFrame<Self::NodeId>, plan: &mut StructuralPlan<Self::NodeId>) -> bool {
        let node = frame.node;
        let flags = self.node_layout_data(node).flags;
        if self.node_layout_data(node).placement != frame.placement {
            self.node_layout_data_mut(node).placement = frame.placement;
        }
        // Replay the enclosing cycle if a descendant may have read a provisional value.
        match region_policy::after_children(frame.changed_children, flags.has_cycle(), plan.regions.len() > frame.start) {
            region_policy::AfterChildren::Keep => return false,
            region_policy::AfterChildren::Refresh => {
                if frame.independent.unwrap_or_else(|| self.try_refresh_independent_parent(node)) {
                    self.node_layout_data_mut(node).structural_change = StructuralChange::Clean;
                    return false;
                }
            }
            region_policy::AfterChildren::Rebuild => {}
        }
        plan.retained = frame.retained;
        self.rebuild_region(node, plan, frame.start)
    }

    /// Return true if a rebuilt subtree can change the parent's sizing inputs.
    fn rebuild_region(&mut self, node: Self::NodeId, plan: &mut StructuralPlan<Self::NodeId>, start: usize) -> bool {
        self.node_layout_data_mut(node).placement = PlacementWork::Subtree;
        region_list::replace_descendants(&mut plan.regions, start, node);
        // A parent's collapsed margins or line metrics are shared by its whole
        // in-flow list. Use the live attachment when selecting a region.
        let in_flow = !self.node_layout_params(node).free_placement;
        let flow_parent = in_flow && self.parent(node).is_some_and(|parent| {
            matches!(self.node_layout_params(parent).children_layout, ChildrenLayout::Wrap { .. } | ChildrenLayout::Block)
        });
        let in_parent_flow = region_policy::attached_flow_child(in_flow, flow_parent);
        // A parent can enter a cyclic region through a different slot than the
        // region's own traversal would. Include it when those sizes are coupled.
        let flags = self.node_layout_data(node).flags;
        region_policy::affects_parent(flags.has_cycle(), self.size_depends_on_children(node), flags.is_block_item(), in_parent_flow)
    }

    // Rebuilding a block can replace a saved collapsed margin; deleting one drops
    // its owner. Bound the arena by the live block count across repeated edits.
    fn compact_block_margins(&mut self, blocks: usize) {
        let data = self.layout_data();
        if blocks == 0 {
            data.block_margins.clear();
            return;
        }
        if data.block_margins.len() <= blocks.saturating_mul(2) { return; }
        let old = std::mem::take(&mut data.block_margins);
        let mut live = std::mem::take(&mut data.margin_scratch);
        let mut next = Some(self.root());
        while let Some(node) = next {
            next = self.tree_traversal_next(node);
            if !self.node_layout_params(node).disabled
                && let Some(index) = self.node_layout_data(node).block_margin_index()
            {
                let next_index = margin_storage::copy_margin(&old, &mut live, index);
                self.node_layout_data_mut(node).set_block_margin_index(next_index);
            }
        }
        let data = self.layout_data();
        data.block_margins = live;
        data.margin_scratch = old;
        data.margin_scratch.clear();
    }

    fn measure_sizes_incremental(&mut self, window_size: Xy<f32>) -> IncrementalRelayoutOutcome {
        let root = self.root();
        let data = self.layout_data();
        let last_window_size = std::mem::replace(&mut data.window_size, window_size);
        if last_window_size.same_input(&window_size) && data.node_changes.is_empty() && data.content_changes.is_empty() {
            return IncrementalRelayoutOutcome::Success { computed: 0 };
        }
        let max_computed = data.n_nodes_solved / 2;

        // Borrow the change lists independently while queuing slots through the adapter.
        let mut changes = std::mem::take(&mut data.node_changes);
        let mut content_changes = std::mem::take(&mut data.content_changes);
        for axis in [X, Y] {
            if !last_window_size[axis].same_input(&window_size[axis]) {
                self.queue_declared(root, axis, |size| size.is_flex());
            }
        }
        for (i, change) in changes.drain(..) {
            self.node_layout_data_mut(i).structural_change = StructuralChange::Clean;
            self.queue_node_change(i, change);
        }
        for i in content_changes.drain(..) {
            self.node_layout_data_mut(i).structural_change = StructuralChange::Clean;
            self.queue_content_change(i);
        }
        let data = self.layout_data();
        data.node_changes = changes;
        data.content_changes = content_changes;
        self.run_queue(max_computed)
    }

    /// Records a change in the params of a node.
    fn incr_register_node_change(&mut self, i: Self::NodeId, old: &LayoutParams) {
        let data = self.layout_data();
        if data.tracks_structure() {
            let track_sizes = data.tracks_sizes();
            let change = NodeChange::between(old, self.node_layout_params(i), track_sizes);
            if self.layout_data().record_change(i, change) {
                self.node_layout_data_mut(i).mark_subtree_changed();
                if change.is_none() {
                    let parent = self.parent(i).unwrap_or(i);
                    self.incr_register_children_change(parent, Some(i));
                }
            } else if !self.node_layout_params(i).same_input(old) {
                self.node_layout_data_mut(i).mark_placement_changed();
            }
        }
    }

    /// Records that the text or the image of a node changed.
    fn incr_register_content_change(&mut self, i: Self::NodeId) {
        if self.layout_data().record_content(i) {
            self.node_layout_data_mut(i).mark_subtree_changed();
        }
    }

    fn incr_register_children_change(&mut self, parent: Self::NodeId, attached: Option<Self::NodeId>) {
        if self.layout_data().start_children_change() {
            self.node_layout_data_mut(parent).mark_children_changed();
            if let Some(child) = attached {
                self.mark_attached(child);
            }
        }
    }

    /// Runs the selected pass. Checked passes also compare the ordered view
    /// and sizing slots against a canonical full solve.
    fn solve_incremental(&mut self, window_size: Xy<f32>, verify: bool) -> IncrementalRelayoutOutcome {
        let data = self.layout_data();
        let needs_topology = data.topology.is_some() && !data.track_topology;
        data.track_topology = true;
        let structural = data.children_changed;
        let same_window = data.window_size.same_input(&window_size);
        let partial_placement = placement_work::partial_placement(
            structural, needs_topology, same_window, data.placement_scale_changed,
        );
        let outcome = if let Some(reason) = data.pending_full_solve {
            reason
        } else {
            match cycle_rules::route(structural, data.has_cycle, data.has_flow, !same_window) {
                Route::Structural => self.measure_structure(window_size),
                Route::Cycle => IncrementalRelayoutOutcome::FallbackCycle,
                Route::Flow => IncrementalRelayoutOutcome::FallbackFlow,
                Route::Queue => self.measure_sizes_incremental(window_size),
            }
        };
        let succeeded = matches!(outcome, IncrementalRelayoutOutcome::Success { .. });
        match publication_route(succeeded, verify, partial_placement, || self.retains_output_rects()) {
            Publication::Rebuild => self.solve_layout(window_size),
            Publication::Checked => {
                if !self.run_full_solve_and_compare(window_size) {
                    return IncrementalRelayoutOutcome::CheckedIncrementalRelayoutMismatch;
                }
            }
            Publication::Retained => self.place_nodes::<true>(),
            Publication::All => self.place_nodes::<false>(),
        }
        if needs_topology && !structural && !verify && succeeded {
            self.remember_topology();
        }
        outcome
    }

    fn run_full_solve_and_compare(&mut self, window_size: Xy<f32>) -> bool {
        // Compare values that belong to the solver. Empty special-purpose slots may
        // hold an arena index or a leaf's temporary retained measurement constraint.
        let bits = |tree: &Self, i| {
            let mut bits = tree.node_layout_data(i).values.map(f32::to_bits);
            match tree.node_layout_params(i).children_layout {
                ChildrenLayout::Block => bits[slot_index(X, Kind::EvenShare)] = 0,
                ChildrenLayout::Free | ChildrenLayout::Stack { .. } => bits[slot_index(Y, Kind::Flow)] = 0,
                _ => {}
            }
            bits
        };
        let data = self.layout_data();
        let mut incremental = std::mem::take(&mut data.checked_values);
        let mut expected = std::mem::take(&mut data.checked_view);
        incremental.reserve(data.n_nodes_solved as usize);
        let mut next = Some(self.root());
        while let Some(i) = next {
            incremental.push((i, bits(self, i)));
            next = self.tree_traversal_next(i);
        }
        expected.reserve(incremental.len());
        CheckedView::capture(self, &mut expected).place_nodes::<false>();
        let mut reference = CheckedView::compare(self, &mut expected);
        reference.solve_full::<false>(window_size);
        let matches = reference.agrees() && incremental.iter().all(|(i, values)| bits(self, *i) == *values);
        incremental.clear();
        expected.clear();
        let data = self.layout_data();
        data.checked_values = incremental;
        data.checked_view = expected;
        matches
    }

    /// Queues the slots affected by the sizing inputs that changed.
    fn queue_node_change(&mut self, i: Self::NodeId, change: NodeChange) {
        if self.node_layout_params(i).disabled {
            return;
        }
        let mut fraction_changed = Xy::new_symm(false);
        for axis in [X, Y] {
            for kind in DECLARED_SIZES {
                if registration_rules::declaration_changed(change.declared, slot_index(axis, kind)) {
                    self.queue(Slot { node: i, axis, kind });
                    if kind == Kind::Regular {
                        fraction_changed[axis] = matches!(self.node_layout_params(i).size[axis], Size::Frac(_));
                    }
                }
            }
        }
        if !change.inner.x && !change.inner.y && !change.margin.x && !change.margin.y
            && !change.content && !change.fill_weight && !fraction_changed.x && !fraction_changed.y
        {
            return;
        }
        let parent = self.parent(i);
        let parent_layout = parent.map(|p| self.node_layout_params(p).children_layout);
        let parent_stack = parent.and_then(|p| self.stack_axis(p));
        let stack = self.stack_axis(i);
        let grid = self.width_grid_main_axis(i);
        let mut seeds = Xy::new_symm(Seeds::default());
        for axis in [X, Y] {
            let params = self.node_layout_params(i);
            let edits = AxisEdits {
                inner: change.inner[axis], other_inner: change.inner[axis.other()], content: change.content,
                margin: change.margin[axis], weight: change.fill_weight,
                regular_fraction: fraction_changed[axis],
            };
            let work = edits.seeds(SeedContext {
                in_flow: !params.free_placement,
                placed_parent: parent_layout.is_some_and(|layout| layout != ChildrenLayout::Free),
                parent_stack_axis: parent_stack == Some(axis),
                stack_axis: stack == Some(axis),
                width_grid: grid.is_some(), grid_main: grid == Some(axis), wraps_text: self.text_wraps(i, axis),
            });
            seeds[axis] = work;
            if work.own_intrinsic || work.own_fill {
                self.queue_declared(i, axis, |s| work.own_intrinsic && s == Size::FitContent || work.own_fill && s.is_fill());
            }
            if work.own_final { self.queue(Slot { node: i, axis, kind: Kind::Final }); }
            if work.own_share { self.queue(Slot { node: i, axis, kind: Kind::EvenShare }); }
            if let Some(parent) = parent {
                if work.parent_intrinsic { self.queue_declared(parent, axis, |s| s == Size::FitContent); }
                if work.parent_share { self.queue(Slot { node: parent, axis, kind: Kind::EvenShare }); }
            }
        }
        if seeds.x.child_available || seeds.y.child_available {
            for_each_layout_child!(self, i, child, {
                let free = self.node_layout_params(child).free_placement;
                for axis in [X, Y] {
                    if seeds[axis].child_available {
                        let in_stack = stack == Some(axis) && !free;
                        self.queue_declared(child, axis, |s| matches!(s.dependency_form().input(in_stack), Input::ParentFinal));
                    }
                }
            });
        }
    }

    fn queue_content_change(&mut self, i: Self::NodeId) {
        if self.node_layout_params(i).disabled {
            return;
        }
        for axis in [X, Y] {
            self.queue_declared(i, axis, |size| size == Size::FitContent);
        }
    }

    fn queue(&mut self, slot: Slot<Self::NodeId>) {
        let Slot { node, axis, kind } = slot;
        let data = self.node_layout_data_mut(node);
        if data.flags.check_state(axis, kind) != SOLVED {
            return;
        }
        data.flags.set_state(axis, kind, UNSOLVED);
        let level = data.levels[slot_index(axis, kind)];
        self.layout_data().queue.push(level, slot);
    }

    /// Computes slots in increasing rank and queues the readers of changed results.
    /// A saturated rank or exhausted computation budget switches to a full solve.
    fn run_queue(&mut self, max_computed: u32) -> IncrementalRelayoutOutcome {
        let mut computed = 0;
        loop {
            let data = self.layout_data();
            let Some(slot) = data.queue.pop() else { break };
            let Some(next) = dependency_rules::charge_queue_slot(computed, max_computed) else {
                data.queue.clear();
                return IncrementalRelayoutOutcome::FallbackTooMuchWork;
            };
            computed = next;
            let k = slot_index(slot.axis, slot.kind);
            let old = self.node_layout_data(slot.node);
            if !dependency_rules::queueable(old.levels[k]) {
                self.layout_data().queue.clear();
                return IncrementalRelayoutOutcome::FallbackTooMuchWork;
            }
            let old_value = old.values[k];
            let old_grid = (slot.kind == Kind::Final
                && grid_state::writes_width_grid(true, self.width_grid_main_axis(slot.node) == Some(slot.axis)))
                .then(|| old.grid_line_bits());
            // The level of the slot stays the same.
            self.finish_slot(slot);
            let new = self.node_layout_data(slot.node);
            // A width grid can move its children even if its own size stays the same.
            if new.values[k].to_bits() != old_value.to_bits() || old_grid.is_some_and(|counts| grid_state::count_changed(counts, new.grid_line_bits())) {
                self.queue_dependents(slot);
            }
        }
        IncrementalRelayoutOutcome::Success { computed }
    }

    /// Queues every slot that reads `slot`. It is the reverse of `solve_all_dependencies`, and it has to stay in sync with it.
    fn queue_dependents(&mut self, slot: Slot<Self::NodeId>) {
        let Slot { node: i, axis, kind } = slot;
        match kind {
            Kind::EvenShare => {
                for_each_layout_child!(self, i, child, {
                    if self.is_in_stack(child, axis) {
                        self.queue_declared(child, axis, |size| matches!(size.dependency_form().input(true), Input::ParentShare));
                    }
                });
            }
            Kind::Final => {
                let other = axis.other();
                let grid_main = self.width_grid_main_axis(i) == Some(axis);
                let constrained = dependency_rules::reads_intrinsic_constraint(
                    self.node_layout_params(i).intrinsic_reads_other_axis(other), grid_main,
                );
                self.queue_declared(i, other, |size| size.dependency_form().reads_opposite_final(constrained));
                if self.stack_axis(i) == Some(axis) {
                    self.queue(Slot { node: i, axis, kind: Kind::EvenShare });
                }
                for_each_layout_child!(self, i, child, {
                    for child_axis in [X, Y] {
                        // A placed child of a width grid also reads the main axis for its other axis.
                        if dependency_rules::reads_parent_axis(child_axis == axis, !self.node_layout_params(child).free_placement, grid_main) {
                            let in_stack = self.is_in_stack(child, child_axis);
                            self.queue_declared(child, child_axis, |size| matches!(size.dependency_form().input(in_stack), Input::ParentFinal));
                        }
                    }
                });
                if let Some(parent) = self.stack_parent(i, axis) && ! self.any_size_is_fill(i, axis) {
                    self.queue(Slot { node: parent, axis, kind: Kind::EvenShare });
                }
            }
            Kind::Flow => unreachable!("flow currently uses full measurement"),
            declared => {
                self.queue(Slot { node: i, axis, kind: Kind::Final });
                if ! self.node_layout_params(i).free_placement && let Some(parent) = self.parent(i) {
                    let size = self.read_size(i, axis, declared).unwrap();
                    if self.stack_axis(parent) == Some(axis) && self.any_size_is_fill(i, axis) && size.dependency_form().contributes_to_share() {
                        self.queue(Slot { node: parent, axis, kind: Kind::EvenShare });
                    }
                    if size.dependency_form().contributes_to_intrinsic() {
                        self.queue_declared(parent, axis, |size| matches!(size.dependency_form(), Form::Intrinsic));
                    }
                }
            }
        }
    }

    /// Queues the declared slots of a node on `axis` whose size matches `filter`.
    #[inline(always)]
    fn queue_declared(&mut self, i: Self::NodeId, axis: Axis, filter: impl Fn(Size) -> bool) {
        for kind in DECLARED_SIZES {
            if let Some(size) = self.read_size(i, axis, kind) && filter(size) {
                self.queue(Slot { node: i, axis, kind });
            }
        }
    }
}

impl<T: TreeAdapter + ?Sized> Incremental for T {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rebuilding_blocks_compacts_live_margins_after_reordering() {
        let mut tree: LayoutTree = LayoutTree::new();
        let root = tree.root();
        let block = LayoutParams {
            size: Xy::new(Size::Fill, Size::Auto),
            children_layout: ChildrenLayout::Block,
            ..LayoutParams::DEFAULT
        };
        let groups = [tree.add_node(&root, block).unwrap(), tree.add_node(&root, block).unwrap()];
        let nested = groups.each_ref().map(|parent| tree.add_node(parent, block).unwrap());
        let mut children = nested.each_ref().map(|parent| tree.add_node(parent, LayoutParams::DEFAULT).unwrap());
        let window = Xy::new_symm(100.0);
        tree.solve_layout(window);
        for i in 0..24 {
            let hot = i % 2;
            tree.remove(&children[hot]).unwrap();
            children[hot] = tree.add_node(&nested[hot], LayoutParams {
                size: Xy::new(Size::Auto, Size::Pixels(10.0)),
                margin: Xy::new([Margin::ZERO; 2], [Margin::px(i as f32 + 2.0).unwrap(), Margin::px(3.0).unwrap()]),
                ..LayoutParams::DEFAULT
            }).unwrap();
            tree.move_node(&groups[hot], Destination::LastChildOf(&root)).unwrap();
            let mut full = tree.clone();
            full.invalidate();
            full.solve_layout(window);
            assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
            for id in groups.iter().chain(&nested).chain(&children) {
                assert_eq!(tree.layout(id).unwrap(), full.layout(&full.node_id(id.key())).unwrap());
            }
            assert!(tree.layout_data.block_margins.len() <= 2 * (groups.len() + nested.len()));
        }
        assert!(tree.layout_data.margin_scratch.capacity() > 0);
    }

    #[test]
    fn queue_preserves_priority_and_lifo_order_when_reusing_entries() {
        let mut queue = WorkQueue::new();
        let slot = |node| Slot { node, axis: X, kind: Kind::Regular };
        for (level, id) in [(4000, 1), (3999, 2), (3990, 3), (3999, 4)] {
            queue.push(level, slot(id));
        }
        assert_eq!(queue.pop().unwrap().node, 3);
        queue.push(4001, slot(5));
        assert_eq!(queue.pop().unwrap().node, 4);
        queue.push(4000, slot(6));
        for expected in [2, 6, 1, 5] {
            assert_eq!(queue.pop().unwrap().node, expected);
        }
        assert!(queue.pop().is_none());

        queue.push(65535, slot(7));
        queue.clear();
        queue.push(0, slot(8));
        assert_eq!(queue.pop().unwrap().node, 8);
        assert!(queue.pop().is_none());
    }

    #[test]
    fn saturated_dependency_level_recovers_with_a_full_solve() {
        let mut tree: LayoutTree = LayoutTree::new();
        let root = tree.root();
        let mut params = LayoutParams { size: Xy::new(Size::Frac(0.5), Size::Pixels(1.0)), ..LayoutParams::DEFAULT };
        let child = tree.add_node(&root, params).unwrap();
        for _ in 0..16 { tree.add_node(&root, LayoutParams::DEFAULT).unwrap(); }
        let window = Xy::new_symm(120.0);
        tree.solve_layout(window);
        // Inject the terminal rank directly to avoid a 65,535-frame test stack.
        tree.nodes[child.key()].layout.levels[slot_index(X, Kind::Regular)] = u16::MAX;
        params.size.x = Size::Frac(0.25);
        tree.update_node_params(&child, params).unwrap();
        let mut full = tree.clone();
        full.invalidate();
        full.solve_layout(window);
        assert_eq!(tree.solve_layout(window), IncrementalRelayoutOutcome::FallbackTooMuchWork);
        assert_eq!(tree.layout(&child).unwrap(), full.layout(&full.node_id(child.key())).unwrap());
        assert_ne!(tree.nodes[child.key()].layout.levels[slot_index(X, Kind::Regular)], u16::MAX);
    }

    #[test]
    fn explicit_invalidations_take_priority_over_inferred_fallbacks() {
        use IncrementalRelayoutOutcome::*;
        let window = Xy::new_symm(100.0);
        for fallback in [FallbackFlow, FallbackCycle, FallbackTooMuchWork] {
            let mut tree: LayoutTree = LayoutTree::new();
            let root = tree.root();
            if fallback == FallbackFlow {
                tree.update_node_params(&root, LayoutParams { children_layout: ChildrenLayout::Block, ..LayoutParams::DEFAULT }).unwrap();
            } else if fallback == FallbackCycle {
                tree.add_node(&root, LayoutParams { size: Xy::new_symm(Size::AspectRatio(1.0)), ..LayoutParams::DEFAULT }).unwrap();
            }
            let item = tree.add_node(&root, LayoutParams { size: Xy::new_symm(Size::Pixels(10.0)), ..LayoutParams::DEFAULT }).unwrap();
            tree.solve_layout(window);

            let mut params = *tree.params(&item).unwrap();
            params.size.x = Size::Pixels(11.0);
            tree.update_node_params(&item, params).unwrap();
            for _ in 0..4 {
                tree.mark_content_changed(&item).unwrap();
            }

            let mut invalidated = tree.clone();
            invalidated.invalidate();
            params.size.x = Size::Fill;
            invalidated.update_node_params(&invalidated.node_id(item.key()), params).unwrap();
            assert_eq!(invalidated.solve_layout(window), FallbackInvalidated);

            let mut structural = tree.clone();
            structural.update_node_params(&structural.node_id(item.key()), params).unwrap();
            structural.invalidate();
            assert_eq!(structural.solve_layout(window), FallbackInvalidated);
            assert_eq!(tree.solve_layout(window), fallback);
        }
    }
}
