use crate::*;
use crate::Axis::{X, Y};
use crate::vec_memory::{RustVec, VecMemory};
pub(crate) use crate::placement_work::PlacementWork;

#[path = "registration_rules.rs"]
mod registration_rules;
#[path = "region_list.rs"]
mod region_list;
#[path = "queue_storage.rs"]
mod queue_storage;
pub(crate) use queue_storage::WorkQueue;
mod inputs;
mod checked_view;
mod publication;
mod numeric;
pub(crate) mod tape;
pub(crate) mod tape_plan;
mod intake;
pub(crate) mod readers;
mod register;
use readers::Filter;
pub(crate) use readers::NodeChange;
use numeric::{QueueActions, QueueModel, QueuePoll};
mod regional;
#[cfg(feature = "batch-pilot")]
pub(crate) use regional::block::{accepts_declarations as accepts_block_declarations, width as resolve_block_width};
mod plan;
pub(crate) use plan::{SubtreeCounts, Suspended};
pub(crate) use checked_view::OutputRecord;
use checked_view::CheckedView;
pub use publication::IncrementalRelayoutOutcome;
use publication::{FrameActions, FrameInputs, same_viewport};
pub(crate) use publication::{FrameResult, enter_frame};
pub(crate) use inputs::SameInput;

pub(crate) use crate::structural_changes::StructuralChange;

impl<I> LayoutData<I> {
    pub(crate) fn record_node_change(&mut self, i: I, old: &LayoutParams, new: &LayoutParams, node: &mut NodeLayoutData) -> bool where I: Copy {
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
        register::tracks_structure(self.pending_full_solve)
    }

    fn tracks_sizes(&self) -> bool {
        self.pending_full_solve.is_none()
    }

    // A queued node can be deleted before the next solve. Mark it on the live tree
    // as well, so a later structural pass can discard all queued IDs safely.
    fn record_change(&mut self, i: I, change: Option<NodeChange>) -> bool where I: Copy {
        match change {
            None => true,
            // While a sizing fallback is pending, between() only checks for a change
            // of rule. Retain the live mark if the batch later includes a tree edit.
            Some(_) if self.pending_full_solve.is_some() => true,
            Some(change) if change != NodeChange::default() => {
                self.submit_edit(register::Edit::Declaration(i, change));
                true
            }
            Some(_) => false,
        }
    }

    fn record_content(&mut self, i: I) -> bool where I: Copy {
        if !self.tracks_structure() { return false; }
        self.submit_edit(register::Edit::Content(i));
        true
    }

    pub(crate) fn record_content_change(&mut self, i: I, node: &mut NodeLayoutData) where I: Copy {
        if self.record_content(i) { node.mark_subtree_changed(); }
    }

    pub(crate) fn start_children_change(&mut self) -> bool where I: Copy {
        self.numeric_tape.invalidate::<RustVec>();
        self.numeric_wrap = None;
        register::start_children_change(&mut self.pending_full_solve, &mut self.children_changed, &mut self.replay_pending)
    }

    pub(crate) fn record_children_change(&mut self, node: &mut NodeLayoutData) where I: Copy {
        if self.start_children_change() {
            node.mark_children_changed();
        }
    }

    fn submit_edit(&mut self, edit: register::Edit<I, NodeChange>) where I: Copy {
        let limits = register::Limits {
            structural: self.children_changed, cycle: self.has_cycle, flow: self.has_flow && self.numeric_wrap != Some(true), population: self.n_nodes_solved,
        };
        register::submit::<_, _, RustVec>(
            &mut self.pending_full_solve, &mut self.replay_pending, &mut self.node_changes, &mut self.content_changes,
            limits, edit,
        );
    }

    /// An explicit full solve takes priority over a fallback inferred from sizing edits.
    pub(crate) fn request_full_solve(&mut self, reason: IncrementalRelayoutOutcome) where I: Copy {
        self.numeric_tape.invalidate::<RustVec>();
        self.numeric_wrap = None;
        register::request_full_solve(&mut self.pending_full_solve, &mut self.replay_pending, reason);
    }

    pub(crate) fn clear(&mut self) where I: Copy {
        self.numeric_tape.invalidate::<RustVec>();
        self.replay_pending = false;
        self.children_changed = false;
        self.unknown_structure = false;
        RustVec::clear(&mut self.node_changes);
        RustVec::clear(&mut self.content_changes);
    }
}

impl NodeChange {
    /// A structural change requires rebuilding the affected dependencies.
    pub(crate) fn between(old: &LayoutParams, new: &LayoutParams, track_sizes: bool) -> Option<Self> {
        if registration_rules::sizing_structure_changed(old, new) {
            return None;
        }

        let mut change = Self::default();
        if !track_sizes {
            return Some(change);
        }
        change.declared = registration_rules::size_declaration_mask::<crate::placement_geometry::RustFloat>(old, new);
        for axis in [X, Y] {
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

pub(crate) trait Incremental: Solve {
    // Rebuilding a block can replace a saved collapsed margin; deleting one drops
    // its owner. Bound the arena by the live block count across repeated edits.
    fn compact_block_margins(&mut self, blocks: usize) {
        crate::sizing_pass::compact_margins::<_, RustVec>(self, blocks);
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
        enter_frame(self, window_size, verify).outcome
    }

    fn queue(&mut self, slot: Slot<Self::NodeId>) {
        let Slot { node, axis, kind } = slot;
        let data = self.node_layout_data_mut(node);
        let Some(level) = numeric::invalidate_solved(&data.levels, &mut data.flags.0, axis.index(), kind) else {
            return;
        };
        let data = self.layout_data();
        if !data.queue.try_push(level, slot) {
            data.request_full_solve(IncrementalRelayoutOutcome::FallbackTooMuchWork);
        }
    }

    /// Queue the reverse dependency requests for one computed slot.
    fn queue_dependents(&mut self, slot: Slot<Self::NodeId>) {
        readers::notify(self, slot.node, slot.axis, slot.kind);
    }

}

impl<T: TreeAdapter + ?Sized> Incremental for T {}

impl<T: Incremental + ?Sized> readers::Model for T {
    type Id = T::NodeId;
}

impl<T: Incremental + ?Sized> readers::Access for T {
    #[inline]
    fn parameters(&self, node: T::NodeId) -> &LayoutParams { self.node_layout_params(node) }

    #[inline]
    fn read_declaration(&self, node: T::NodeId, axis: Axis, kind: Kind) -> Option<Size> {
        self.read_size(node, axis, kind)
    }

    #[inline]
    fn parent_id(&self, node: T::NodeId) -> Option<T::NodeId> { self.parent(node) }

    #[inline]
    fn first_id(&self, node: T::NodeId) -> Option<T::NodeId> { self.first_child(node) }

    #[inline]
    fn following_id(&self, node: T::NodeId) -> Option<T::NodeId> { self.next_sibling(node) }

    #[inline]
    fn enqueue(&mut self, node: T::NodeId, axis: Axis, kind: Kind) {
        self.queue(Slot { node, axis, kind });
    }
}

impl<T: Incremental + ?Sized> checked_view::SizingModel<N_SLOTS> for T {}

impl<T: Incremental + ?Sized> checked_view::SizingSource<N_SLOTS> for T {
    #[inline]
    fn first_size(&self) -> Option<T::NodeId> { Some(self.root()) }

    #[inline]
    fn next_size(&self, node: T::NodeId) -> Option<T::NodeId> { self.tree_traversal_next(node) }

    #[inline]
    fn sizing_words(&self, node: T::NodeId) -> [u32; N_SLOTS] {
        checked_view::sizing_projection(self.node_layout_params(node).children_layout, &self.node_layout_data(node).values)
    }
}

impl<T: Incremental + ?Sized> checked_view::ReferenceModel<N_SLOTS> for T {}

impl<T: Incremental + ?Sized> checked_view::Reference<Xy<f32>, N_SLOTS> for T {
    #[inline]
    fn take_scratch(&mut self) -> checked_view::Scratch<T::NodeId, N_SLOTS> {
        let data = self.layout_data();
        checked_view::Scratch {
            values: RustVec::take(&mut data.checked_values),
            rectangles: RustVec::take(&mut data.checked_view),
            hint: data.n_nodes_solved as usize,
        }
    }

    #[inline]
    fn recycle_scratch(&mut self, buffers: checked_view::Scratch<T::NodeId, N_SLOTS>) {
        let data = self.layout_data();
        data.checked_values = buffers.values;
        data.checked_view = buffers.rectangles;
    }

    #[inline]
    fn capture_rectangles(&mut self, expected: &mut Vec<OutputRecord<T::NodeId>>) -> bool {
        let mut capture = CheckedView::capture(self, expected);
        capture.place_nodes::<false>();
        capture.captured()
    }

    #[inline]
    fn compare_reference(&mut self, window: Xy<f32>, expected: &mut Vec<OutputRecord<T::NodeId>>) -> bool {
        let mut reference = CheckedView::compare(self, expected);
        reference.solve_full::<false>(window);
        reference.agrees()
    }

    #[inline]
    fn publish_reference(&mut self, window: Xy<f32>) {
        self.solve_full::<false>(window);
    }
}

impl<T: TreeAdapter + ?Sized> region_policy::RefreshModel for T {
    type Id = T::NodeId;
}

impl<T: TreeAdapter + ?Sized> region_policy::RefreshSource for T {
    #[inline]
    fn old_flags(&self, parent: T::NodeId) -> NodeFlags {
        self.node_layout_data(parent).flags
    }

    #[inline]
    fn params(&self, node: T::NodeId) -> &LayoutParams {
        self.node_layout_params(node)
    }

    #[inline]
    fn first(&self, parent: T::NodeId) -> Option<T::NodeId> {
        self.first_child(parent)
    }

    #[inline]
    fn following(&self, child: T::NodeId) -> Option<T::NodeId> {
        self.next_sibling(child)
    }
}

impl<T: Incremental + ?Sized> intake::Model for T {
    type Change = NodeChange;
}

impl<T: Incremental + ?Sized> intake::Access for T {
    #[inline]
    fn window_seed(&mut self, root: Self::Id, axis: usize) {
        let axis = if axis == X as usize { X } else { Y };
        readers::declarations(self, root, axis, Filter::Flexible);
    }

    #[inline]
    fn clear_mark(&mut self, node: Self::Id) {
        self.node_layout_data_mut(node).structural_change = StructuralChange::Clean;
    }

    #[inline]
    fn declaration_seed(&mut self, node: Self::Id, change: NodeChange) {
        readers::edited(self, node, change);
        if self.layout_data().numeric_wrap == Some(true) {
            readers::wrap_edit(self, node, change);
        }
    }

    #[inline]
    fn content_seed(&mut self, node: Self::Id) {
        readers::content_edited(self, node);
    }
}

impl<T: Incremental + ?Sized> intake::WindowInputs<Xy<f32>> for T {}

impl<T: Incremental + ?Sized> intake::ChangeBuffers<Xy<f32>> for T {
    #[inline]
    fn numeric_root(&self) -> Self::Id { self.root() }

    #[inline]
    fn set_window(&mut self, window: Xy<f32>) -> intake::WindowChange {
        let data = self.layout_data();
        intake::replace_viewport(
            &mut data.window_size.x, &mut data.window_size.y, window.x, window.y,
            !data.node_changes.is_empty() || !data.content_changes.is_empty(), data.n_nodes_solved,
        )
    }

    #[inline]
    fn take_changes(&mut self) -> intake::Changes<Self::Id, NodeChange> {
        let data = self.layout_data();
        intake::Changes {
            declarations: RustVec::take(&mut data.node_changes),
            content: RustVec::take(&mut data.content_changes),
        }
    }

    #[inline]
    fn recycle_changes(&mut self, edits: intake::Changes<Self::Id, NodeChange>) {
        let data = self.layout_data();
        data.node_changes = edits.declarations;
        data.content_changes = edits.content;
    }
}

impl<T: Incremental + ?Sized> plan::SourceModel for T {
    type Refresh = T;
}

impl<T: Incremental + ?Sized> plan::Source for T {
    type Memory = RustVec;

    #[inline]
    fn parent_id(&self, node: T::NodeId) -> Option<T::NodeId> { self.parent(node) }

    #[inline]
    fn refresh_source(&self, _node: T::NodeId) -> &T { self }
}

impl<T: Incremental + ?Sized> regional::block::Storage for T { type Block = f32; }

impl<T: Incremental + ?Sized> regional::block::Access for T {
    type BlockMemory = RustVec;

    #[inline(always)]
    fn scalar(value: f32) -> f32 { value }

    #[inline(always)]
    fn word(value: f32) -> f32 { value }

    #[inline]
    fn text_height(&mut self, node: T::NodeId, width: Option<f32>) -> f32 {
        self.measure_text_height(node, width)
    }

    #[inline]
    fn warn_height(&mut self, node: T::NodeId) {
        self.warn(LayoutWarning::NotFinite { node, axis: Y });
    }

    #[inline(always)]
    fn block_margins(&mut self) -> &mut Vec<BlockMargins> { &mut self.layout_data().block_margins }

    #[inline(always)]
    fn update_block_record(&mut self, node: T::NodeId) -> &mut NodeLayoutData { self.node_layout_data_mut(node) }
}

impl<T: Incremental + ?Sized> regional::Scene for T {
    type Window = Xy<f32>;
    type Snapshot = TopologySnapshot<T::NodeId>;

    #[inline]
    fn scene_root(&self) -> T::NodeId { self.root() }

    #[inline]
    fn pending_full(&mut self) -> &mut Option<IncrementalRelayoutOutcome> {
        &mut self.layout_data().pending_full_solve
    }

    #[inline]
    fn viewport(&mut self) -> &mut Xy<f32> {
        &mut self.layout_data().window_size
    }

    #[inline]
    fn viewport_changes(&mut self, window: Xy<f32>) -> (bool, bool) {
        let data = self.layout_data();
        let change = intake::replace_viewport(
            &mut data.window_size.x, &mut data.window_size.y, window.x, window.y, false, 0,
        );
        (change.horizontal, change.vertical)
    }

    #[inline]
    fn declared_size(&self, node: T::NodeId, axis: Axis, kind: Kind) -> Option<Size> {
        self.read_size(node, axis, kind)
    }

    #[inline]
    fn take_regions(&mut self) -> Vec<T::NodeId> { RustVec::take(&mut self.layout_data().regions) }

    #[inline]
    fn recycle_regions(&mut self, regions: Vec<T::NodeId>) { self.layout_data().regions = regions; }

    #[inline]
    fn take_plan_spill(&mut self) -> Vec<plan::Suspended<T::NodeId>> {
        RustVec::take(&mut self.layout_data().plan_spill)
    }

    #[inline]
    fn keep_plan_spill(&mut self, spill: Vec<plan::Suspended<T::NodeId>>) {
        self.layout_data().plan_spill = spill;
    }

    #[inline]
    fn reset_edits(&mut self, retained: SubtreeCounts) {
        let data = self.layout_data();
        // Pending queues can reference removed IDs. Live nodes carry the edits.
        data.clear();
        data.has_flow = retained.has_flow;
        data.has_cycle = retained.has_cycle;
    }

    #[inline]
    fn restore_tickets(&mut self, snapshot: &Self::Snapshot, root: T::NodeId, ticket: u64) -> bool {
        snapshot.restore_region_tickets(self, root, ticket)
    }

    #[inline]
    fn update_population(&mut self, totals: regional::Totals) {
        self.layout_data().n_nodes_solved = totals.nodes;
        self.compact_block_margins(totals.blocks);
    }

    #[inline]
    fn unknown_topology(&mut self) -> bool { self.layout_data().unknown_structure }

    #[inline]
    fn reconcile(&mut self, styles: &mut Vec<T::NodeId>) -> bool { self.reconcile_topology(styles) }

    #[inline]
    fn take_topology(&mut self) -> Option<Self::Snapshot> { self.layout_data().topology.take() }

    #[inline]
    fn keep_topology(&mut self, snapshot: Self::Snapshot) { self.layout_data().topology = Some(snapshot); }

    #[inline]
    fn refresh_topology(&mut self, obsolete: Option<Self::Snapshot>) {
        if obsolete.is_some() {
            self.layout_data().topology = Some(TopologySnapshot::new());
        }
        self.remember_topology();
    }
}

impl<T: Incremental + ?Sized> QueueModel for T {
    type Slot = (u16, Slot<T::NodeId>);
}

struct OutputAncestors<'a, T: ?Sized>(&'a mut T);

impl<T: TreeAdapter + ?Sized> layout_tree::solve_frame::MarkModel for OutputAncestors<'_, T> {
    type Id = T::NodeId;
}

impl<T: TreeAdapter + ?Sized> layout_tree::solve_frame::MarkAncestors for OutputAncestors<'_, T> {
    #[inline]
    fn mark_ancestor(&mut self, node: Self::Id) -> Option<Self::Id> {
        let data = self.0.node_layout_data_mut(node);
        data.placement = data.placement.with_child(PlacementWork::Subtree, false);
        self.0.parent(node)
    }
}

impl<T: Incremental + ?Sized> numeric::produce::Access for T {
    #[inline(always)]
    fn finish_retaining_grid(&mut self, slot: crate::solve::sizing_requests::Request<Self::Id>)
        -> crate::solve::sizing_finish::StoredSize<Self::Id>
    {
        self.finish_numeric_slot(slot)
    }
}

impl<T: Incremental + ?Sized> QueueActions for T {
    type BudgetMemory = RustVec;

    #[inline(always)]
    fn take_budget_nodes(&mut self) -> Vec<Self::Id> {
        RustVec::take(&mut self.layout_data().numeric_touched)
    }

    #[inline(always)]
    fn recycle_budget_nodes(&mut self, nodes: Vec<Self::Id>) {
        self.layout_data().numeric_touched = nodes;
    }

    #[inline(always)]
    fn budget_mark(&self, node: Self::Id) -> bool {
        numeric::marked(self.node_layout_data(node).prepared_placement)
    }

    #[inline(always)]
    fn mark_budget_node(&mut self, node: Self::Id, marked: bool) {
        numeric::mark_record(self.node_layout_data_mut(node), marked);
    }

    #[inline]
    fn poll(&mut self) -> QueuePoll<Self::Slot> {
        let data = self.layout_data();
        numeric::poll_queue::<_, RustVec>(&mut data.queue, data.pending_full_solve)
    }

    #[inline]
    fn position(&self, (rank, slot): Self::Slot) -> (Self::Id, usize, Kind, u16) {
        (slot.node, slot.axis.index(), slot.kind, rank)
    }

    #[inline]
    fn slot_record(&self, (_, slot): Self::Slot) -> &NodeLayoutData {
        self.node_layout_data(slot.node)
    }

    #[inline]
    fn writes_width_grid(&self, (_, slot): Self::Slot) -> bool {
        self.width_grid_main_axis(slot.node) == Some(slot.axis)
    }

    #[cfg(test)]
    #[inline]
    fn simple_wrap_queue(&mut self) -> bool {
        self.layout_data().numeric_wrap == Some(true)
    }

    #[inline]
    fn writes_wrap_lines(&self, (_, slot): Self::Slot) -> bool {
        matches!(self.node_layout_params(slot.node).children_layout, ChildrenLayout::Wrap { axis, .. } if axis == slot.axis)
    }

    #[inline(always)]
    fn ranked_slot(&self, step: tape_plan::Ranked<Self::Id>) -> Self::Slot {
        let request = step.request;
        (step.rank, Slot { node: request.node, axis: request.axis(), kind: request.kind })
    }

    #[inline]
    fn compute(&mut self, (_, slot): Self::Slot) {
        numeric::produce::compute(
            self, crate::solve::sizing_requests::target(slot.node, slot.axis == Y, slot.kind),
        );
    }

    #[inline]
    fn send_to_readers(&mut self, (_, slot): Self::Slot) {
        self.queue_dependents(slot);
        if self.layout_data().numeric_wrap == Some(true) {
            readers::wrap_notify(self, slot.node, slot.axis, slot.kind);
        }
    }

    #[inline]
    fn mark_output(&mut self, node: Self::Id, sibling_extent_changed: bool) {
        // An in-flow size can change its siblings' cursor, even when the
        // parent keeps the same outer size.
        let affected = match self.parent(node) {
            Some(parent) if sibling_extent_changed && !self.node_layout_params(node).free_placement
                && !matches!(self.node_layout_params(parent).children_layout, ChildrenLayout::Free) => parent,
            _ => node,
        };
        self.node_layout_data_mut(affected).mark_placement_changed();
        let above = self.parent(affected);
        layout_tree::solve_frame::mark_parents(&mut OutputAncestors(self), above);
    }

    #[inline]
    fn discard_queue(&mut self) {
        self.layout_data().queue.clear();
    }
}


pub(crate) struct TapeEquality<T: ?Sized>(core::marker::PhantomData<T>);

impl<T: Incremental + ?Sized> tape::EditEquality<T::NodeId, NodeChange> for TapeEquality<T> {
    #[inline(always)]
    fn same_id(left: T::NodeId, right: T::NodeId) -> bool { left == right }

    #[inline(always)]
    fn same_change(left: NodeChange, right: NodeChange) -> bool { left == right }
}

impl<T: Incremental + ?Sized> tape_plan::Equal<T::NodeId> for TapeEquality<T> {
    #[inline(always)]
    fn same_node(left: T::NodeId, right: T::NodeId) -> bool { left == right }
}

struct TapeReader<'a, T: Incremental + ?Sized> {
    tree: &'a T,
    work: &'a mut tape_plan::Work<T::NodeId>,
}

impl<T: Incremental + ?Sized> readers::Model for TapeReader<'_, T> {
    type Id = T::NodeId;
}

impl<T: Incremental + ?Sized> readers::Access for TapeReader<'_, T> {
    #[inline(always)]
    fn parameters(&self, node: T::NodeId) -> &LayoutParams { self.tree.node_layout_params(node) }

    #[inline(always)]
    fn read_declaration(&self, node: T::NodeId, axis: Axis, kind: Kind) -> Option<Size> {
        self.tree.read_size(node, axis, kind)
    }

    #[inline(always)]
    fn parent_id(&self, node: T::NodeId) -> Option<T::NodeId> { self.tree.parent(node) }

    #[inline(always)]
    fn first_id(&self, node: T::NodeId) -> Option<T::NodeId> { self.tree.first_child(node) }

    #[inline(always)]
    fn following_id(&self, node: T::NodeId) -> Option<T::NodeId> { self.tree.next_sibling(node) }

    #[inline]
    fn enqueue(&mut self, node: T::NodeId, axis: Axis, kind: Kind) {
        tape_plan::discover_from_record::<_, TapeEquality<T>, RustVec>(
            self.work, node, axis, kind, self.tree.node_layout_data(node),
        );
    }
}

impl<T: Incremental + ?Sized> tape_plan::EventModel for T {}

impl<T: Incremental + ?Sized> tape_plan::Events for T {
    #[inline]
    fn viewport(&self, work: &mut tape_plan::Work<T::NodeId>, root: T::NodeId, axis: Axis) {
        readers::declarations(&mut TapeReader { tree: self, work }, root, axis, Filter::Flexible);
    }

    #[inline]
    fn declaration(&self, work: &mut tape_plan::Work<T::NodeId>, node: T::NodeId, change: NodeChange) {
        let wrap = work.wrap;
        let mut inbox = TapeReader { tree: self, work };
        tape_plan::dispatch_declaration(&mut inbox, node, change, wrap);
    }

    #[inline]
    fn content(&self, work: &mut tape_plan::Work<T::NodeId>, node: T::NodeId) {
        readers::content_edited(&mut TapeReader { tree: self, work }, node);
    }

    #[inline]
    fn readers(&self, work: &mut tape_plan::Work<T::NodeId>, step: tape_plan::Ranked<T::NodeId>) {
        let wrap = work.wrap;
        let request = step.request;
        let mut inbox = TapeReader { tree: self, work };
        tape_plan::dispatch_readers(&mut inbox, request, wrap);
    }
}

impl<T: Incremental + ?Sized> numeric::CachedQueue<Xy<f32>> for T {
    type Equality = TapeEquality<T>;

    #[inline]
    fn take_tape(&mut self) -> tape::Tape<T::NodeId, NodeChange, tape_plan::Ranked<T::NodeId>> {
        core::mem::replace(&mut self.layout_data().numeric_tape, tape::Tape::new())
    }

    #[inline]
    fn keep_tape(&mut self, tape: tape::Tape<T::NodeId, NodeChange, tape_plan::Ranked<T::NodeId>>) {
        self.layout_data().numeric_tape = tape;
    }

    #[inline]
    fn numeric_context(&mut self) -> numeric::NumericContext {
        let data = self.layout_data();
        numeric::NumericContext { wrap: data.numeric_wrap == Some(true), clean: !data.sizing_warned }
    }
}

impl<T: Incremental + ?Sized> FrameActions<Xy<f32>> for T {
    #[inline]
    fn frame_inputs(&mut self, window: Xy<f32>) -> (FrameInputs, &mut bool) {
        let data = self.layout_data();
        let flow_request = matches!(data.pending_full_solve, Some(IncrementalRelayoutOutcome::FallbackFlow));
        let inspect = data.has_flow && data.numeric_wrap.is_none() && !data.children_changed && !data.has_cycle
            && (data.pending_full_solve.is_none() || flow_request && data.replay_pending);
        if inspect {
            let supported = crate::sizing_pass::numeric_wrap_shape(self);
            self.layout_data().numeric_wrap = Some(supported);
        }
        let data = self.layout_data();
        let inputs = FrameInputs {
            pending: data.pending_full_solve,
            has_topology: data.topology.is_some(),
            structural: data.children_changed,
            unknown_structure: data.unknown_structure,
            replay_pending: data.replay_pending,
            same_window: same_viewport(data.window_size.x, data.window_size.y, window.x, window.y),
            scale_changed: data.placement_scale_changed,
            has_cycle: data.has_cycle,
            has_flow: data.has_flow && (data.numeric_wrap != Some(true) || flow_request),
        };
        (inputs, &mut data.track_topology)
    }

    #[inline]
    fn retains_rectangles(&self) -> bool {
        self.retains_output_rects()
    }

    #[inline]
    fn publish_full_solve(&mut self, window: Xy<f32>) {
        self.solve_layout(window);
    }

    #[inline]
    fn publish_placement(&mut self, partial: bool) -> crate::place::placement_entry::RootPlacement<T::NodeId> {
        if partial { self.place_nodes::<true>() } else { self.place_nodes::<false>() }
    }

    #[inline]
    fn remember(&mut self) {
        self.remember_topology();
    }
}


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
            assert!(queue.try_push(level, slot(id)));
        }
        assert_eq!(queue.pop().map(|(rank, slot)| (rank, slot.node)), Some((3990, 3)));
        assert!(!queue.try_push(3989, slot(9)));
        assert!(queue.try_push(4001, slot(5)));
        assert_eq!(queue.pop().map(|(rank, slot)| (rank, slot.node)), Some((3999, 4)));
        assert!(!queue.try_push(3998, slot(10)));
        assert!(queue.try_push(4000, slot(6)));
        for expected in [2, 6, 1, 5] {
            assert_eq!(queue.pop().unwrap().1.node, expected);
        }
        assert!(queue.pop().is_none());

        assert!(queue.try_push(65535, slot(7)));
        queue.clear();
        assert!(queue.try_push(0, slot(8)));
        assert_eq!(queue.pop().map(|(rank, slot)| (rank, slot.node)), Some((0, 8)));
        assert!(queue.pop().is_none());
    }

    #[derive(Clone)]
    struct ViewportFixture {
        params: Vec<LayoutParams>,
        records: Vec<NodeLayoutData>,
        rectangles: Vec<(XyRect, XyRect)>,
        layout: LayoutData<usize>,
    }

    impl ViewportFixture {
        fn new(fractions: usize) -> Self {
            let pixels = LayoutParams { size: Xy::new_symm(Size::Pixels(8.0)), ..LayoutParams::DEFAULT };
            let mut params = vec![pixels; 30];
            params[0] = LayoutParams::DEFAULT;
            for params in &mut params[1..=fractions] {
                params.size.x = Size::Frac(0.5);
            }
            Self {
                params,
                records: vec![NodeLayoutData::new(); 30],
                rectangles: vec![(Xy::new_symm([0.0; 2]), Xy::new_symm([0.0; 2])); 30],
                layout: LayoutData::new(),
            }
        }

        fn assert_budget_cleared(&self) {
            assert!(self.layout.numeric_touched.is_empty());
            assert!(self.records.iter().all(|record| !numeric::marked(record.prepared_placement)));
        }

        fn assert_same_rectangles(&self, full: &Self) {
            let words = |(absolute, local): &(XyRect, XyRect)| {
                [absolute.x, absolute.y, local.x, local.y].map(|edges| edges.map(f32::to_bits))
            };
            for (left, right) in self.rectangles.iter().zip(&full.rectangles) {
                assert_eq!(words(left), words(right));
            }
        }
    }

    impl TreeAdapter for ViewportFixture {
        type NodeId = usize;

        fn retains_output_rects(&self) -> bool { self.layout.topology.is_none() }

        fn root(&self) -> usize { 0 }
        fn parent(&self, node: usize) -> Option<usize> { (node != 0).then_some(0) }
        fn first_child(&self, node: usize) -> Option<usize> { (node == 0).then_some(1) }
        fn next_sibling(&self, node: usize) -> Option<usize> {
            if node > 0 && node + 1 < self.params.len() { Some(node + 1) } else { None }
        }
        fn node_layout_params(&self, node: usize) -> &LayoutParams { &self.params[node] }
        fn node_layout_data(&self, node: usize) -> &NodeLayoutData { &self.records[node] }
        fn node_layout_data_mut(&mut self, node: usize) -> &mut NodeLayoutData { &mut self.records[node] }
        fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }
        fn write_output_rect(&mut self, node: usize, rect: XyRect, local: XyRect) {
            self.rectangles[node] = (rect, local);
        }
    }

    #[test]
    fn viewport_queue_budgets_distinct_nodes_and_matches_full_bits() {
        let mut tree = ViewportFixture::new(10);
        let initial = Xy::new(100.0, 90.0);
        tree.solve_layout(initial);
        let mut full = tree.clone();
        for width in [160.25, 100.0, 201.5] {
            let window = Xy::new(width, initial.y);
            // Root and ten fraction leaves use two slots each. Twenty-two
            // slots exceed the old limit of fifteen, with eleven owners.
            assert_eq!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { computed: 22 });
            full.solve_layout(window);
            tree.assert_same_rectangles(&full);
            for (left, right) in tree.records.iter().zip(&full.records) {
                assert_eq!(left.values.map(f32::to_bits), right.values.map(f32::to_bits));
            }
            tree.assert_budget_cleared();
        }
    }

    #[test]
    fn excess_intake_edits_replay_before_the_queue_changes_any_slots() {
        let mut tree = ViewportFixture::new(10);
        let window = Xy::new(100.0, 90.0);
        tree.solve_layout(window);
        let before = tree.records.clone();
        for i in 1..=18 {
            let old = tree.params[i];
            tree.params[i].size.x = if i <= 10 { Size::Frac(0.25) } else { Size::Pixels(23.0) };
            tree.register_node_change(i, &old);
        }
        assert_eq!(tree.layout.pending_full_solve, Some(IncrementalRelayoutOutcome::FallbackTooMuchWork));
        assert!(tree.layout.replay_pending);
        assert_eq!(tree.layout.node_changes.len(), 15);
        for (old, current) in before.iter().zip(&tree.records) {
            assert_eq!(old.values.map(f32::to_bits), current.values.map(f32::to_bits));
        }
        let mut full = tree.clone();
        let resized = Xy::new(124.25, window.y);
        full.solve_layout(resized);
        assert!(matches!(tree.solve_layout_incremental(resized), IncrementalRelayoutOutcome::Success { .. }));
        tree.assert_same_rectangles(&full);
        tree.assert_budget_cleared();
        assert!(!tree.layout.replay_pending);
        assert!(tree.layout.node_changes.is_empty());
        let old = tree.params[1];
        tree.params[1].size.x = Size::Frac(0.75);
        tree.register_node_change(1, &old);
        full.params[1] = tree.params[1];
        full.solve_layout(resized);
        assert!(matches!(tree.solve_layout_incremental(resized), IncrementalRelayoutOutcome::Success { .. }));
        tree.assert_same_rectangles(&full);
    }

    #[test]
    fn numeric_declarations_budget_distinct_nodes_and_match_full_bits() {
        let window = Xy::new(720.0, 128.0);
        for grid in [false, true] {
            let mut tree = ViewportFixture::new(0);
            tree.params[0].children_layout = if grid {
                ChildrenLayout::Grid {
                    main_axis: X, columns: MainAxisCellSize::Count(4),
                    spacing_x: 2.0, spacing_y: 3.0, backfill: false,
                }
            } else {
                ChildrenLayout::Stack { axis: X, arrange: Arrange::Start, spacing: 1.0 }
            };
            for params in &mut tree.params[1..=10] {
                params.size.x = Size::Fill;
            }
            for params in &mut tree.params[11..] {
                params.free_placement = true;
            }
            if !grid {
                tree.params[1].min_size.x = Some(Size::Pixels(40.0));
            }
            tree.solve_layout(window);
            let mut full = tree.clone();
            for wide in [true, false, true, false] {
                let edited = if grid { 0 } else { 1 };
                let old = tree.params[edited];
                if grid {
                    tree.params[edited].children_layout = ChildrenLayout::Grid {
                        main_axis: X, columns: MainAxisCellSize::Count(4),
                        spacing_x: if wide { 14.5 } else { 2.0 }, spacing_y: 3.0, backfill: false,
                    };
                } else {
                    tree.params[edited].min_size.x = Some(Size::Pixels(if wide { 120.0 } else { 40.0 }));
                }
                tree.register_node_change(edited, &old);
                assert!(!tree.layout.children_changed);
                let before = tree.rectangles[2];
                let outcome = tree.solve_layout_incremental(window);
                // More than half the population in slot computations is
                // compatible with fewer than half the nodes being affected.
                assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { computed: 16.. }), "{outcome:?}");
                assert_ne!(tree.rectangles[2], before);
                full.params[edited] = tree.params[edited];
                full.solve_layout(window);
                tree.assert_same_rectangles(&full);
                for (left, right) in tree.records.iter().zip(&full.records) {
                    assert_eq!(left.values.map(f32::to_bits), right.values.map(f32::to_bits));
                }
                tree.assert_budget_cleared();
            }
        }
    }

    #[test]
    fn viewport_fallback_releases_budget_marks_before_full_solve() {
        let window = Xy::new(160.25, 90.0);
        for (fractions, bad_rank) in [(20, None), (10, Some(u16::MAX)), (10, Some(0))] {
            let mut tree = ViewportFixture::new(fractions);
            tree.solve_layout(Xy::new(100.0, 90.0));
            if let Some(rank) = bad_rank {
                tree.records[1].levels[slot_index(X, Kind::Regular)] = rank;
            }
            // Inspect the attempt itself. A later full preparation could
            // otherwise clear a leaked mark and hide a cleanup regression.
            assert_eq!(
                numeric::measure::<_, _, RustVec>(&mut tree, window, false),
                IncrementalRelayoutOutcome::FallbackTooMuchWork,
            );
            assert!(tree.layout.numeric_touched.capacity() > 0);
            tree.assert_budget_cleared();
        }
    }

    #[test]
    fn broad_viewport_sizing_reuses_only_the_matching_live_tape() {
        let mut tree = ViewportFixture::new(0);
        tree.params.resize(100, tree.params[1]);
        tree.records.resize(100, NodeLayoutData::new());
        tree.rectangles.resize(100, (Xy::new_symm([0.0; 2]), Xy::new_symm([0.0; 2])));
        for params in &mut tree.params[1..=40] {
            params.size.x = Size::Frac(0.25);
        }
        tree.solve_layout(Xy::new(100.0, 90.0));
        let mut full = tree.clone();
        for width in [160.25, 215.5, 121.0] {
            let window = Xy::new(width, 90.0);
            assert_eq!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { computed: 82 });
            assert!(tree.layout.numeric_tape.axes.horizontal);
            assert_eq!(tree.layout.numeric_tape.steps.len(), 82);
            full.solve_layout(window);
            tree.assert_same_rectangles(&full);
            for (left, right) in tree.records.iter().zip(&full.records) {
                assert_eq!(left.values.map(f32::to_bits), right.values.map(f32::to_bits));
            }
            tree.assert_budget_cleared();
        }
        tree.register_structural_change();
        assert!(tree.layout.numeric_tape.steps.is_empty());
        let window = Xy::new(206.75, 90.0);
        full.solve_layout(window);
        tree.solve_layout_incremental(window);
        tree.assert_same_rectangles(&full);
    }

    #[test]
    fn rejected_tape_never_invalidates_the_ordinary_ranked_inputs() {
        let mut tree: LayoutTree = LayoutTree::new();
        let root = tree.root();
        let clamped = LayoutParams {
            size: Xy::new(Size::Fill, Size::Pixels(12.0)),
            max_size: Xy::new(Some(Size::Pixels(12.0)), None),
            ..LayoutParams::DEFAULT
        };
        let child = LayoutParams {
            size: Xy::new(Size::Frac(0.5), Size::Pixels(3.0)),
            ..LayoutParams::DEFAULT
        };
        for _ in 0..36 {
            let group = tree.add_node(&root, clamped).unwrap();
            for _ in 0..3 { tree.add_node(&group, child).unwrap(); }
        }
        tree.solve_layout(Xy::new(100.0, 120.0));
        let mut full = tree.clone();
        for width in [140.0, 110.0, 160.0, 190.0, 205.0] {
            let viewport = Xy::new(width, 120.0);
            // The clamped parent Finals stop numeric propagation. A
            // conservative schedule also sees their fraction grandchildren
            // and must decline without consuming the live queue's budget.
            assert_eq!(tree.solve_layout(viewport), IncrementalRelayoutOutcome::Success { computed: 74 });
            assert!(tree.layout_data.numeric_tape.steps.is_empty());
            assert!(tree.layout_data.numeric_tape.axes.horizontal);
            full.invalidate();
            full.solve_layout(viewport);
            for id in tree.nodes.keys() {
                let actual = tree.layout(&tree.node_id(id)).unwrap();
                let expected = full.layout(&full.node_id(id)).unwrap();
                assert_eq!([actual.x, actual.y].map(|axis| axis.map(f32::to_bits)),
                    [expected.x, expected.y].map(|axis| axis.map(f32::to_bits)));
            }
        }
    }

    #[test]
    fn simple_wrap_numeric_rebuilds_line_boundaries_and_cross_metrics() {
        let mut tree = ViewportFixture::new(0);
        tree.params[0] = LayoutParams {
            size: Xy::new(Size::Fill, Size::FitContent),
            children_layout: ChildrenLayout::Wrap { axis: X, arrange: Arrange::Start, spacing: 2.5, line_spacing: 4.75 },
            ..LayoutParams::DEFAULT
        };
        for (i, p) in tree.params[1..].iter_mut().enumerate() {
            p.size = Xy::new(Size::Pixels(17.0 + (i % 3) as f32), Size::Pixels(9.0 + (i % 5) as f32));
        }
        tree.solve_layout(Xy::new(100.0, 90.0));
        let mut full = tree.clone();
        for (iteration, width) in [72.25, 215.5, 85.0, 115.625].into_iter().enumerate() {
            let window = Xy::new(width, 90.0);
            let old_root = tree.params[0];
            tree.params[0].children_layout = ChildrenLayout::Wrap {
                axis: X, arrange: Arrange::Start, spacing: 2.5, line_spacing: 4.75 + iteration as f32,
            };
            tree.register_node_change(0, &old_root);
            let old_child = tree.params[3];
            tree.params[3].margin.y[0] = Margin::px(6.25 - iteration as f32).unwrap();
            tree.register_node_change(3, &old_child);
            assert!(matches!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { .. }));
            assert_eq!(tree.layout.numeric_wrap, Some(true));
            full.params.clone_from(&tree.params);
            full.solve_layout(window);
            tree.assert_same_rectangles(&full);
            for (left, right) in tree.records.iter().zip(&full.records) {
                assert_eq!(left.flags.starts_wrap_line(), right.flags.starts_wrap_line());
                assert_eq!(left.parent_flow, right.parent_flow);
                assert_eq!(left.values.map(f32::to_bits), right.values.map(f32::to_bits));
            }
        }
        let old_child = tree.params[3];
        tree.params[3].size.y = Size::Fill;
        tree.register_node_change(3, &old_child);
        assert_eq!(tree.layout.numeric_wrap, None);
    }

    #[test]
    fn rebuilt_wrap_partition_marks_retained_output_with_unchanged_final_words() {
        let mut tree = ViewportFixture::new(0);
        tree.layout.topology = None;
        tree.layout.set_pixel_scale(Some(PixelScale::try_from(1.25).unwrap()));
        tree.params[0].children_layout = ChildrenLayout::Wrap {
            axis: X, arrange: Arrange::Start, spacing: 0.0, line_spacing: 2.75,
        };
        for params in &mut tree.params[1..] {
            params.size = Xy::new(Size::Pixels(17.0), Size::Pixels(9.25));
        }
        let window = Xy::new(80.25, 175.5);
        tree.solve_layout(window);
        assert_eq!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { computed: 0 });
        assert_eq!(tree.layout.numeric_wrap, Some(true));
        assert!(tree.records.iter().all(|record| record.placement == PlacementWork::Clean));

        let old = tree.params[0];
        let previous_child = tree.rectangles[4];
        let final_words = |data: &NodeLayoutData| [data.size().x.to_bits(), data.size().y.to_bits()];
        let previous_sizes: Vec<_> = tree.records.iter().map(final_words).collect();
        tree.params[0].children_layout = ChildrenLayout::Wrap {
            axis: X, arrange: Arrange::Start, spacing: 8.0, line_spacing: 2.75,
        };
        tree.register_node_change(0, &old);
        let mut full = tree.clone();

        let outcome = tree.solve_layout_incremental(window);
        assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { computed } if computed > 0));
        assert_eq!(tree.records.iter().map(final_words).collect::<Vec<_>>(), previous_sizes);
        full.solve_layout(window);
        tree.assert_same_rectangles(&full);
        assert_ne!(tree.rectangles[4], previous_child);
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
    fn a_dependency_behind_the_queue_cursor_recovers_with_a_full_solve() {
        let mut tree: LayoutTree = LayoutTree::new();
        let root = tree.root();
        let mut params = LayoutParams { size: Xy::new_symm(Size::Pixels(10.0)), ..LayoutParams::DEFAULT };
        let early = tree.add_node(&root, params).unwrap();
        let late = tree.add_node(&root, params).unwrap();
        for _ in 0..16 { tree.add_node(&root, LayoutParams::DEFAULT).unwrap(); }
        let window = Xy::new_symm(120.0);
        tree.solve_layout(window);

        // The first edit advances the queue from rank zero. Inject a second
        // edit whose Final would be enqueued behind the cursor.
        tree.nodes[early.key()].layout.levels[slot_index(X, Kind::Regular)] = 0;
        tree.nodes[late.key()].layout.levels[slot_index(X, Kind::Regular)] = 10;
        tree.nodes[late.key()].layout.levels[slot_index(X, Kind::Final)] = 1;
        params.size.x = Size::Pixels(20.0);
        tree.update_node_params(&early, params).unwrap();
        tree.update_node_params(&late, params).unwrap();
        assert_eq!(tree.solve_layout(window), IncrementalRelayoutOutcome::FallbackTooMuchWork);
        for child in [&early, &late] {
            assert_eq!(tree.layout(child).unwrap().x, [50.0, 70.0]);
        }
        assert_eq!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { computed: 0 });
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
            if fallback == FallbackCycle {
                assert_eq!(tree.solve_layout(window), FallbackCycle);
            } else {
                assert!(tree.layout_data.replay_pending);
                assert!(matches!(tree.solve_layout(window), Success { .. }));
            }
        }
    }
}
