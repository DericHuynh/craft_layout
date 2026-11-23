use super::*;
use crate::structural_changes::{TailDelta, empty_delta, tail_can_reuse, tail_replaces_prefix};

/// Consecutive pushes and pops leave the siblings before `first_added` in the same order.
#[derive(Debug, Clone, Copy, Default)]
pub(super) enum TailEdits {
    #[default]
    None,
    Stack { parent: NodeKey, delta: TailDelta<NodeKey> },
    Other,
}

/// Cached sizing inputs for the recently edited stack. Pushing or popping
/// zero-margin Fill leaves preserves its fixed costs and the existing bounds.
#[derive(Debug, Clone, Copy)]
pub(super) struct StackTail {
    parent: NodeKey,
    fills: u32,
    space_without_gaps: f32,
    independent_fills: bool,
    bounded_fills: bool,
}

// Changing a leaf's main size cannot change these cross-axis slots.
fn independent_fill(node: &LayoutNode, main: Axis) -> bool {
    let p = &node.params;
    let cross = main.other();
    node.first_child.is_none() && matches!(p.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        && [Some(p.size[cross]), p.min_size[cross], p.max_size[cross]].into_iter().flatten().all(|size| match size {
            Size::AspectRatio(_) => false,
            Size::FitContent | Size::Auto => !p.intrinsic_reads_other_axis(cross),
            _ => true,
        })
}

impl<T> LayoutTree<T> {
    pub(super) fn record_tail_edit(&mut self, id: NodeKey, parent: NodeKey, inserting: bool) {
        if matches!(self.tail_edits, TailEdits::Other) { return; }
        let node = &self.nodes[id];
        let prior = std::mem::replace(&mut self.tail_edits, TailEdits::Other);
        let delta = match prior {
            TailEdits::None => empty_delta(),
            TailEdits::Stack { parent: previous, delta } if parent == previous => delta,
            _ => return,
        };
        let ChildrenLayout::Stack { axis, .. } = self.nodes[parent].params.children_layout else { return };
        let p = &node.params;
        if node.next_sibling.is_some() || node.first_child.is_some() || p.disabled || p.free_placement
            || p.size[axis] != Size::Fill || p.min_size[axis].is_some() || p.max_size[axis].is_some()
            || !p.fill_weight.is_finite() || p.fill_weight <= 0.0 || margins(p, axis) != [0.0; 2]
            || !matches!(p.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
            || p.grid_span.x > 1 || p.grid_span.y > 1
        {
            return;
        }
        if p.size[axis.other()].is_flex() {
            // The first sibling keeps the parent's cross-axis flex flag set, even
            // across a sequence of pops. Otherwise let preparation refresh the flag.
            let Some(first) = self.nodes[parent].first_child else { return };
            let head = &self.nodes[first].params;
            if first == id || head.disabled || head.free_placement || !head.size[axis.other()].is_flex() {
                return;
            }
        }
        if let Some(delta) = delta.record(id, inserting) {
            self.tail_edits = TailEdits::Stack { parent, delta };
        }
    }

    fn stack_tail(&self, parent: NodeKey, axis: Axis, inner: f32) -> Option<StackTail> {
        let mut stack = StackTail { parent, fills: 0, space_without_gaps: inner, independent_fills: true, bounded_fills: false };
        for id in self.children_keys(parent) {
            let node = &self.nodes[id];
            let p = &node.params;
            if p.disabled || p.free_placement { continue; }
            let [start, end] = margins(p, axis);
            let margin = start + end;
            if margin < 0.0 || !margin.is_finite() { return None; }
            stack.space_without_gaps = fill_budget::charge(stack.space_without_gaps, margin);
            match p.size[axis] {
                Size::Fill if p.fill_weight > 0.0 && p.fill_weight.is_finite() => {
                    for bound in [p.min_size[axis], p.max_size[axis]].into_iter().flatten() {
                        if !matches!(bound, Size::Pixels(px) if px.is_finite()) { return None; }
                        stack.bounded_fills = true;
                    }
                    stack.fills += 1;
                    stack.independent_fills &= independent_fill(node, axis);
                }
                Size::Pixels(size) if size.is_finite() && size >= 0.0 && p.min_size[axis].is_none() && p.max_size[axis].is_none() => {
                    stack.space_without_gaps = fill_budget::charge(stack.space_without_gaps, size);
                }
                _ => return None,
            }
        }
        Some(stack)
    }
}

impl<T, M, C> Adapter<'_, T, M, C>
where
    M: FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>,
    C: FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
{
    /// All affected leaves already have solved bounds and dependency levels. Their
    /// two main-axis slots are the only measurements in the prefix that can change.
    fn resize_fill_leaves(&mut self, stack: StackTail, axis: Axis, share: f32, first_added: Option<NodeKey>) -> u32 {
        let mut updated: u32 = 0;
        let mut next = self.first_child(stack.parent);
        while let Some(id) = next {
            if Some(id) == first_added { break; }
            let child = &mut self.tree.nodes[id];
            next = child.next_sibling;
            if child.params.disabled || child.params.free_placement || child.params.size[axis] != Size::Fill { continue; }
            let value = share * child.params.fill_weight;
            child.layout.values[slot_index(axis, Kind::Regular)] = value;
            if stack.bounded_fills && (child.params.min_size[axis].is_some() || child.params.max_size[axis].is_some()) {
                self.finish_slot(Slot { node: id, axis, kind: Kind::Final });
            } else {
                child.layout.values[slot_index(axis, Kind::Final)] = value;
                if !value.is_finite() { self.warn(LayoutWarning::NotFinite { node: id, axis }); }
            }
            updated = updated.saturating_add(2);
        }
        updated
    }

    pub(super) fn solve_stack_tail(
        &mut self, parent: NodeKey, delta: TailDelta<NodeKey>, window: Xy<f32>,
    ) -> Option<u32> {
        let global = &self.tree.layout_data;
        if global.pending_full_solve.is_some() || global.has_cycle || !global.window_size.same_input(&window) { return None; }
        let refresh_output = global.placement_scale_changed;
        let node = &self.tree.nodes[parent];
        let ChildrenLayout::Stack { axis, spacing, arrange } = node.params.children_layout else { return None };
        let layout = &node.layout;
        if !spacing.is_finite() || spacing < 0.0 || layout.flags.is_block_item() || self.size_depends_on_children(parent)
            || layout.flags.check_state(axis, Kind::EvenShare) != SOLVED
        {
            return None;
        }
        let old_share = layout.values[slot_index(axis, Kind::EvenShare)];
        let parent_rect = node.rect;
        let first_added = delta.first_added;
        let count = delta.update_count(layout.n_placed_children)?;
        let solved_nodes = delta.update_count(global.n_nodes_solved)?;
        let inner = (layout.size()[axis] - self.total_padding(parent, axis)).max(0.0);
        let stack = if let Some(mut stack) = self.tree.tail_stack.filter(|stack| stack.parent == parent) {
            stack.fills = delta.update_count(stack.fills)?;
            let mut next = first_added;
            while let Some(id) = next {
                let child = &self.tree.nodes[id];
                stack.independent_fills &= independent_fill(child, axis);
                next = child.next_sibling;
            }
            stack
        } else {
            self.tree.stack_tail(parent, axis, inner)?
        };
        // Either gaps alone or fixed costs alone can exhaust the budget. The
        // fixed-cost bound uses the solver's subtraction order to preserve rounding.
        let gaps = spacing * (count as f32 - 1.0).max(0.0);
        let exhausted = !stack.bounded_fills && fill_budget::exhausted(inner, gaps, stack.space_without_gaps);
        if stack.fills == 0 || !tail_can_reuse(exhausted, old_share.to_bits(), stack.independent_fills) { return None; }

        let layout = &mut self.tree.nodes[parent].layout;
        layout.n_placed_children = count;
        layout.structural_change = StructuralChange::Clean;
        // Each edited leaf reads EvenShare without adding a dependency to it.
        // The levels of the share and the surviving leaves therefore remain valid.
        let share = if exhausted { 0.0 } else { self.solve_even_share(parent, axis) };
        self.tree.nodes[parent].layout.values[slot_index(axis, Kind::EvenShare)] = share;
        self.tree.layout_data.n_nodes_solved = solved_nodes;
        self.tree.layout_data.clear();
        self.tree.tail_stack = Some(stack);

        let changed = share.to_bits() != old_share.to_bits();
        let mut place_all = tail_replaces_prefix(old_share.to_bits(), share.to_bits(), refresh_output, arrange == Arrange::Start);
        let mut computed = if changed {
            self.resize_fill_leaves(stack, axis, share, first_added).saturating_add(1)
        } else {
            u32::from(!exhausted)
        };
        let mut next = first_added;
        while let Some(child) = next {
            next = self.next_sibling(child);
            let (_, slots, _) = self.measure_subtree(child);
            computed = computed.saturating_add(slots);
            if !place_all {
                let previous = self.tree.nodes[child].prev_sibling.map(|id| (id, self.tree.nodes[id].rect));
                place_all = !self.place_appended_stack_leaf(parent, child, parent_rect, previous);
            }
        }
        if place_all {
            if refresh_output || self.tree.layout_data.pixel_scale.is_some() {
                self.place_nodes::<false>();
            } else if let Some(first) = self.first_child(parent) {
                let origin = Xy::new(parent_rect.x[0], parent_rect.y[0]);
                self.place_children::<false>(parent, first, parent_rect, origin, None);
            }
        }
        Some(computed)
    }
}
