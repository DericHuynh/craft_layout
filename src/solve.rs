#[path = "grid_search.rs"]
mod grid_search;
#[cfg(test)]
use grid_search::find_grid_cell;
#[path = "grid_words.rs"]
mod grid_words;
#[path = "grid_sparse.rs"]
mod grid_sparse;
#[path = "grid_state.rs"]
pub(crate) mod grid_state;
#[path = "fill_collection.rs"]
mod fill_collection;
#[path = "fill_compaction.rs"]
mod fill_compaction;
#[path = "root_requests.rs"]
mod root_requests;
use root_requests::visit_sizing_roots;
#[path = "sizing_stack.rs"]
mod sizing_stack;
use crate::*;
use crate::flow::wrap_metrics;
#[path = "wrap_schedule.rs"]
mod wrap_schedule;
use crate::Axis::{X, Y};

#[path = "dependency_rules.rs"]
pub(crate) mod dependency_rules;
#[path = "block_schedule.rs"]
mod block_schedule;
use block_schedule::{BlockSchedule, Request as BlockRequest, ScheduleModel};
use dependency_rules::{Form, Input};
#[cfg(feature = "incremental")]
#[path = "leaf_retention.rs"]
mod leaf_retention;
#[path = "cycle_rules.rs"]
pub(crate) mod cycle_rules;
pub(crate) use cycle_rules::{Kind, N_SLOTS, SOLVED, UNSOLVED};
use cycle_rules::{Entry, IN_PROGRESS};
#[cfg(feature = "incremental")]
use cycle_rules::CHECK_INTRINSIC;
#[cfg(feature = "incremental")]
use crate::fixed_leaf_cache::{self, Summary as FixedLeafSummary};

pub(crate) const DECLARED_SIZES: [Kind; 3] = cycle_rules::declaration_order(Kind::Regular, Kind::Min, Kind::Max);

#[inline(always)]
pub(crate) const fn slot_index(axis: Axis, kind: Kind) -> usize {
    cycle_rules::slot_index(axis as usize, kind)
}

const _: () = assert!(X as usize == 0 && Y as usize == 1);

#[derive(Debug, Clone, Copy)]
pub(crate) struct Slot<I> {
    pub node: I,
    pub axis: Axis,
    pub kind: Kind,
}

#[derive(Clone, Copy)]
pub(crate) struct OpenSlot<I> {
    slot: Slot<I>,
    previous: f32,
    #[cfg(feature = "incremental")]
    outer_level: u16,
}

#[derive(Clone, Copy)]
pub(crate) enum SizingTask<I> {
    Enter(Slot<I>),
    Finish(OpenSlot<I>, bool),
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct NodeFlags(u32);

impl NodeFlags {
    pub(crate) const EMPTY: NodeFlags = NodeFlags(0);

    const IN_CYCLE_X: u32 = 1 << (2 * N_SLOTS);
    const IN_CYCLE_Y: u32 = 1 << (2 * N_SLOTS + 1);
    const FLEX_CHILD_X: u32 = 1 << (2 * N_SLOTS + 2);
    const FLEX_CHILD_Y: u32 = 1 << (2 * N_SLOTS + 3);
    const GRID_SPANS: u32 = 1 << (2 * N_SLOTS + 4);
    const BLOCK_ITEM: u32 = 1 << (2 * N_SLOTS + 5);
    const BLOCK_PARENT_AUTO_HEIGHT: u32 = 1 << (2 * N_SLOTS + 6);
    const BLOCK_CONTAINER: u32 = 1 << (2 * N_SLOTS + 7);
    const WRAP_CONTAINER: u32 = 1 << (2 * N_SLOTS + 8);
    const WRAP_LINE_START: u32 = 1 << (2 * N_SLOTS + 9);
    const DESCENDANTS_NEED_SOLVE: u32 = 1 << (2 * N_SLOTS + 10);
    const FIXED_LEAF: u32 = 1 << (2 * N_SLOTS + 11);

    pub(crate) fn is_block_item(self) -> bool {
        self.0 & Self::BLOCK_ITEM != 0
    }

    #[cfg(feature = "incremental")]
    pub(crate) fn has_cycle(self) -> bool {
        self.0 & (Self::IN_CYCLE_X | Self::IN_CYCLE_Y) != 0
    }

    #[cfg(feature = "incremental")]
    pub(crate) fn has_flow(self) -> bool {
        self.0 & (Self::BLOCK_CONTAINER | Self::WRAP_CONTAINER) != 0
    }

    #[cfg(feature = "incremental")]
    pub(crate) fn is_block_container(self) -> bool {
        self.0 & Self::BLOCK_CONTAINER != 0
    }

    pub(crate) fn starts_wrap_line(self) -> bool {
        wrap_metrics::is_start(self.0, Self::WRAP_LINE_START)
    }

    #[inline(always)]
    fn in_cycle(axis: Axis) -> u32 {
        match axis {
            X => NodeFlags::IN_CYCLE_X,
            Y => NodeFlags::IN_CYCLE_Y,
        }
    }

    #[inline(always)]
    fn flex_child(axis: Axis) -> u32 {
        match axis {
            X => NodeFlags::FLEX_CHILD_X,
            Y => NodeFlags::FLEX_CHILD_Y,
        }
    }

    #[inline(always)]
    pub(crate) fn check_state(self, axis: Axis, kind: Kind) -> u32 {
        cycle_rules::read_state(self.0, slot_index(axis, kind) as u32)
    }

    #[inline(always)]
    pub(crate) fn set_state(&mut self, axis: Axis, kind: Kind, state: u32) {
        self.0 = cycle_rules::write_state(self.0, slot_index(axis, kind) as u32, state);
    }
}

const _: () = assert!(2 * N_SLOTS + 12 <= 32, "The slot states and the flags don't fit in NodeFlags");

const EMPTY_VALUES: [f32; N_SLOTS] = {
    let mut values = [f32::from_bits(cycle_rules::provisional_bits(false)); N_SLOTS];
    values[slot_index(X, Kind::Max)] = f32::from_bits(cycle_rules::provisional_bits(true));
    values[slot_index(Y, Kind::Max)] = f32::from_bits(cycle_rules::provisional_bits(true));
    values
};


impl Size {
    #[inline(always)]
    pub(crate) fn dependency_form(self) -> Form {
        match self {
            Size::Pixels(_) => Form::Constant,
            Size::AspectRatio(_) => Form::Ratio,
            Size::Frac(_) => Form::Fraction,
            Size::Fill => Form::Fill,
            Size::FitContent | Size::Auto => Form::Intrinsic,
        }
    }

    #[inline(always)]
    pub(crate) fn is_fill(&self) -> bool {
        *self == Size::Fill
    }

    #[inline(always)]
    pub(crate) fn is_flex(&self) -> bool {
        matches!(self, Size::Frac(_) | Size::Fill)
    }
}

impl LayoutParams {
    #[inline(always)]
    fn text_wraps_on(&self, axis: Axis) -> bool {
        axis == Y && self.text == TextContent::Wrapping && !matches!(self.size.x, Size::AspectRatio(_))
    }

    #[inline(always)]
    pub(crate) fn intrinsic_reads_other_axis(&self, axis: Axis) -> bool {
        self.text_wraps_on(axis) || self.content_measure.reads_other_axis(axis)
    }
}

macro_rules! for_each_layout_child {
    ($solver:expr, $i:expr, $child:ident, $body:block) => {
        for_each_layout_child!(@from $solver, $solver.first_child($i), $child, $body)
    };
    (@from $solver:expr, $first:expr, $child:ident, $body:block) => {{
        let mut next = $first;
        walk_siblings!(; (next, $child); {}; $solver.next_sibling($child); $solver.node_layout_params($child).disabled; $body);
    }};
    (@until $solver:expr, $first:expr, $stop:expr, $child:ident, $body:block) => {{
        let mut next = $first;
        let stop = $stop;
        walk_siblings!(; (next, $child); { if Some($child) == stop { break; } };
            $solver.next_sibling($child); $solver.node_layout_params($child).disabled; $body);
    }};
}

/// Per-node data used by the layout solver.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct NodeLayoutData {
    // Traversal reads the flags, placement work, cached style, and Final sizes
    // together. Keep those fields ahead of the dependency levels and ticket.
    /// The state of every slot.
    pub(crate) flags: NodeFlags,
    #[cfg(feature = "incremental")]
    pub(crate) placement: PlacementWork,
    #[cfg(feature = "incremental")]
    pub(crate) structural_change: StructuralChange,
    // Prepared from live declarations only for the owned tree. Declaration and
    // inherited visibility changes clear it along with the fixed-pixel marker.
    #[cfg(feature = "incremental")]
    fixed_leaf_summary: FixedLeafSummary,
    /// The value of every slot. Mapped by `slot_index()`.
    pub(crate) values: [f32; N_SLOTS],
    /// A grid item's two cell coordinates, or a wrap item's line metric.
    parent_flow: [u32; 2],
    /// How many children aren't free-placement.
    pub(crate) n_placed_children: u32,
    /// The dependency level of every slot. Mapped by `slot_index()`.
    /// 
    /// The "level" is the longest chain of dependencies of dependencies flowing into a slot. This is used for efficient incremental relayout.
    #[cfg(feature = "incremental")]
    pub(crate) levels: [u16; N_SLOTS],
    // Identifies this record in a custom adapter's last solved topology.
    #[cfg(feature = "incremental")]
    pub(crate) topology_index: u64,
}

#[cfg(feature = "incremental")]
#[inline]
fn fixed_leaf_summary(params: &LayoutParams) -> FixedLeafSummary {
    if params.free_placement {
        fixed_leaf_cache::record(true, false, false)
    } else {
        let spans = params.grid_span.x > 1 || params.grid_span.y > 1;
        let simple_start = params.position == Xy::new_symm(Pos::Start)
            && params.margin == Xy::new_symm([Margin::ZERO; 2]);
        fixed_leaf_cache::record(false, spans, simple_start)
    }
}

impl NodeLayoutData {
    #[cfg(feature = "incremental")]
    const FIXED_REGISTERED_FLAGS: u32 = {
        assert!(slot_index(X, Kind::Regular) == 0 && slot_index(Y, Kind::Regular) == 1
            && slot_index(X, Kind::Final) == 2 && slot_index(Y, Kind::Final) == 3);
        assert!(SOLVED < 4 && NodeFlags::FIXED_LEAF & 0xff == 0);
        fixed_leaf_cache::registered_flags(NodeFlags::FIXED_LEAF, SOLVED)
    };

    /// Creates a new empty [`NodeLayoutData`].
    pub const fn new() -> Self {
        NodeLayoutData {
            #[cfg(feature = "incremental")]
            topology_index: 0,
            #[cfg(feature = "incremental")]
            structural_change: StructuralChange::Clean,
            #[cfg(feature = "incremental")]
            placement: PlacementWork::Clean,
            #[cfg(feature = "incremental")]
            fixed_leaf_summary: FixedLeafSummary::EMPTY,
            values: EMPTY_VALUES,
            flags: NodeFlags::EMPTY,
            #[cfg(feature = "incremental")]
            levels: [0; N_SLOTS],
            n_placed_children: 0,
            parent_flow: wrap_metrics::INITIAL_WORDS,
        }
    }

    #[cfg(feature = "incremental")]
    pub(crate) fn forget_fixed_pixels(&mut self) {
        fixed_leaf_cache::invalidate(&mut self.flags.0, NodeFlags::FIXED_LEAF, &mut self.fixed_leaf_summary);
    }

    // LayoutTree clears the marker on every declaration change, even with a full
    // solve pending. The caller has also checked that this is still an ordinary leaf.
    #[cfg(feature = "incremental")]
    #[inline]
    fn reuse_registered_pixels(&mut self) -> bool {
        fixed_leaf_cache::reuse_registered(self.flags.0, Self::FIXED_REGISTERED_FLAGS, &self.parent_flow,
            &mut self.structural_change)
    }

    #[cfg(feature = "incremental")]
    #[inline]
    pub(crate) fn cached_stack_start(&self) -> bool {
        self.fixed_leaf_summary.stack_start()
    }

    /// Initializes independent pixel slots and returns whether both final sizes are ready.
    #[inline(always)]
    fn seed_pixels(&mut self, params: &LayoutParams, block_item: bool, width_grid_axis: Option<Axis>) -> bool {
        let mut both_axes_fixed = true;
        for axis in [X, Y] {
            let Size::Pixels(pixels) = params.size[axis] else {
                both_axes_fixed = false;
                continue;
            };
            self.publish_slot(slot_index(axis, Kind::Regular), pixels);
            if cycle_rules::ready_pixel_finals(
                pixels.is_finite(), params.min_size[axis].is_some(), params.max_size[axis].is_some(),
                block_item, width_grid_axis == Some(axis),
            )
            {
                let final_size = slot_index(axis, Kind::Final);
                self.publish_slot(final_size, pixels);
                #[cfg(feature = "incremental")]
                {
                    // A pixel value has no dependencies, and Final reads only Regular.
                    self.levels[final_size] = 1;
                }
            } else {
                both_axes_fixed = false;
            }
        }
        both_axes_fixed
    }

    /// Resolve a leaf's cross-axis Fill or Frac against its stack’s fixed inner
    /// extent. Its own aspect ratio can read that result without visiting the parent.
    #[inline]
    fn seed_stack_leaf(&mut self, params: &LayoutParams, cross: Axis, inner_cross: f32) -> bool {
        if params.min_size[cross].is_some() || params.max_size[cross].is_some() { return false; }
        let cross_size = match params.size[cross] {
            Size::Fill => {
                let [start, end] = margins(params, cross);
                let margin = start + end;
                if margin == 0.0 || params.free_placement { inner_cross } else { (inner_cross - margin).max(0.0) }
            }
            Size::Frac(fraction) => inner_cross * fraction,
            _ => return false,
        };
        if !cross_size.is_finite() { return false; }
        // The parent's pixel Regular and Final have levels zero and one.
        self.seed_unbounded_axis(cross, cross_size, 2);
        let main = cross.other();
        if let Size::AspectRatio(ratio) = params.size[main]
            && params.min_size[main].is_none() && params.max_size[main].is_none()
        {
            let size = if main == X { cross_size * ratio } else { cross_size / ratio };
            if size.is_finite() { self.seed_unbounded_axis(main, size, 4); }
        }
        self.flags.check_state(main, Kind::Final) == SOLVED
    }

    #[inline]
    fn seed_unbounded_axis(&mut self, axis: Axis, size: f32, _regular_level: u16) {
        self.publish_axis(axis, size, size, _regular_level);
    }

    #[inline(always)]
    fn publish_slot(&mut self, index: usize, value: f32) {
        cycle_rules::publish_finished_slot(&mut self.flags.0, &mut self.values[index], index as u32, value);
    }

    #[inline(always)]
    fn publish_axis(&mut self, axis: Axis, regular: f32, resolved: f32, _regular_level: u16) {
        let regular_index = slot_index(axis, Kind::Regular);
        let final_index = slot_index(axis, Kind::Final);
        cycle_rules::publish_finished_pair(
            &mut self.flags.0, &mut self.values, (regular_index, regular), (final_index, resolved),
        );
        #[cfg(feature = "incremental")]
        dependency_rules::publish_levels(&mut self.levels, regular_index, final_index, _regular_level);
    }

    #[inline]
    fn reset_fixed_leaf(&mut self, mut prepared: Self) {
        prepared.flags.0 |= NodeFlags::FIXED_LEAF;
        // A fallback can occur between updating Regular and Final. Compare all four
        // slots, including the sign of zero. Grid and wrap may have set parent_flow.
        let pixel_bits = |data: &Self| {
            [slot_index(X, Kind::Regular), slot_index(Y, Kind::Regular),
             slot_index(X, Kind::Final), slot_index(Y, Kind::Final)].map(|i| data.values[i].to_bits())
        };
        if self.flags == prepared.flags && self.parent_flow == [0; 2] && pixel_bits(self) == pixel_bits(&prepared) {
            #[cfg(feature = "incremental")]
            if self.fixed_leaf_summary != prepared.fixed_leaf_summary {
                self.fixed_leaf_summary = prepared.fixed_leaf_summary;
            }
            #[cfg(feature = "incremental")]
            if self.structural_change != StructuralChange::Clean {
                self.structural_change = StructuralChange::Clean;
            }
            return;
        }
        *self = prepared;
    }

    /// The live declaration proves these four slots independent if both pixel sizes
    /// still match. Recreate the remaining flags from the current children and parent.
    #[cfg(feature = "incremental")]
    pub(crate) fn unchanged_pixel_box(&self, params: &LayoutParams, leaf: bool) -> Option<Self> {
        if params.disabled || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. }) { return None; }
        let mut data = Self::new();
        if !data.seed_pixels(params, false, None) { return None; }
        for axis in [X, Y] {
            for kind in [Kind::Regular, Kind::Final] {
                let slot = slot_index(axis, kind);
                if self.flags.check_state(axis, kind) != SOLVED || self.values[slot].to_bits() != data.values[slot].to_bits() {
                    return None;
                }
            }
        }
        if leaf {
            data.flags.0 |= NodeFlags::FIXED_LEAF;
        }
        Some(data)
    }

    /// Carry forward only slots whose entire dependency chain stays inside this leaf.
    /// The parent can change the space available on either axis, or the leaf's grid
    /// cell or wrap line, without changing any of these values or dependency levels.
    #[cfg(feature = "incremental")]
    fn retain_leaf_slots(&mut self, old: &Self, params: &LayoutParams) -> u32 {
        let block_context = NodeFlags::BLOCK_ITEM | NodeFlags::BLOCK_PARENT_AUTO_HEIGHT;
        if !matches!(old.structural_change, StructuralChange::Clean | StructuralChange::Moved)
            || old.n_placed_children != 0
            || old.flags.has_cycle() || (old.flags.0 ^ self.flags.0) & block_context != 0
            || old.flags.check_state(X, Kind::Final) != SOLVED || old.flags.check_state(Y, Kind::Final) != SOLVED
        {
            return 0;
        }
        let declarations = |axis| [Some(params.size[axis]), params.min_size[axis], params.max_size[axis]];
        let block_item = self.flags.is_block_item();
        let input = |axis, kind, size: Size| {
            let form = match size {
                Size::Auto if axis == X && kind == Kind::Regular && block_item => Form::Fill,
                Size::Auto => Form::Intrinsic,
                size => size.dependency_form(),
            };
            leaf_retention::input(form, form == Form::Intrinsic && params.intrinsic_reads_other_axis(axis))
        };
        // At most one cross-axis step can close an acyclic dependency inside a leaf.
        let independent = |axis| {
            DECLARED_SIZES.into_iter().zip(declarations(axis)).all(|(kind, size)| {
                size.is_none_or(|size| input(axis, kind, size).stable(false))
            })
        };
        let independent = Xy::new(independent(X), independent(Y));
        let mut retained = 0;
        for axis in [X, Y] {
            let mut all_local = true;
            for (kind, size) in DECLARED_SIZES.into_iter().zip(declarations(axis)) {
                let Some(size) = size else { continue };
                let stable = input(axis, kind, size).stable(independent[axis.other()]);
                if stable && old.flags.check_state(axis, kind) == SOLVED {
                    retained += self.retain_slot(old, axis, kind);
                } else {
                    all_local = false;
                    if matches!(size, Size::FitContent | Size::Auto) && params.intrinsic_reads_other_axis(axis)
                        && !params.intrinsic_reads_other_axis(axis.other())
                        && !(size == Size::Auto && axis == X && kind == Kind::Regular && block_item)
                        && old.flags.check_state(axis, kind) == SOLVED
                    {
                        // This leaf only ever needs one opposite-axis constraint. Check it
                        // after the new grid cells, fill shares or wrap lines are known.
                        self.values[slot_index(Y, Kind::Flow)] = old.values[slot_index(axis.other(), Kind::Final)];
                        let index = slot_index(axis, kind);
                        self.values[index] = old.values[index];
                        self.flags.set_state(axis, kind, CHECK_INTRINSIC);
                    }
                }
            }
            // Leave warning-producing Final slots to the solver so it emits them again.
            if all_local && old.values[slot_index(axis, Kind::Final)].is_finite()
                && old.values[slot_index(axis, Kind::Min)] <= old.values[slot_index(axis, Kind::Max)]
            {
                retained += self.retain_slot(old, axis, Kind::Final);
            }
        }
        retained
    }

    #[cfg(feature = "incremental")]
    fn retain_slot(&mut self, old: &Self, axis: Axis, kind: Kind) -> u32 {
        if self.flags.check_state(axis, kind) == SOLVED { return 0; }
        let index = slot_index(axis, kind);
        self.publish_slot(index, old.values[index]);
        self.levels[index] = old.levels[index];
        1
    }

    /// A common fill item needs only its parent's new share. Keep its measured
    /// cross-axis slots in place as we invalidate the two slots that read the share.
    #[cfg(feature = "incremental")]
    fn reset_intrinsic_fill_leaf(&mut self, intrinsic: Axis) -> bool {
        let solved_axis = |axis| (SOLVED << (2 * slot_index(axis, Kind::Regular)))
            | (SOLVED << (2 * slot_index(axis, Kind::Final)));
        if self.structural_change != StructuralChange::Clean
            || self.flags.0 & !NodeFlags::WRAP_LINE_START != (solved_axis(X) | solved_axis(Y))
            || self.n_placed_children != 0 || !self.values[slot_index(intrinsic, Kind::Final)].is_finite()
        {
            return false;
        }
        self.flags = NodeFlags(solved_axis(intrinsic));
        self.parent_flow = wrap_metrics::INITIAL_WORDS;
        for kind in [Kind::Regular, Kind::Final] {
            let index = slot_index(intrinsic.other(), kind);
            self.values[index] = 0.0;
            self.levels[index] = 0;
        }
        true
    }

    pub(crate) fn size(&self) -> Xy<f32> {
        let values = &self.values;
        Xy::new(values[slot_index(X, Kind::Final)], values[slot_index(Y, Kind::Final)])
    }

    pub(crate) fn grid_cell(&self) -> Xy<f32> {
        let (x, y) = grid_state::published_cell(self.parent_flow);
        Xy::new(f32::from_bits(x), f32::from_bits(y))
    }

    fn set_grid_cell(&mut self, main: Axis, position: usize, line: u64) {
        self.parent_flow = grid_state::physical_pair(
            (position as f32).to_bits(), (line as f32).to_bits(), main == Y,
        );
    }

    // Grids use neither the stack EvenShare slot nor the block/wrap Flow slot.
    // They hold the track dimensions until sizing and placement consume them.
    fn set_grid_lines(&mut self, lines: Xy<f32>) {
        grid_state::publish_tracks(
            &mut self.values, slot_index(X, Kind::EvenShare), slot_index(Y, Kind::Flow), (lines.x, lines.y),
        );
    }

    pub(crate) fn grid_lines(&self) -> Xy<f32> {
        let (x, y) = grid_state::published_tracks(
            &self.values, slot_index(X, Kind::EvenShare), slot_index(Y, Kind::Flow),
        );
        Xy::new(x, y)
    }

    #[cfg(feature = "incremental")]
    pub(crate) fn grid_line_bits(&self) -> (u32, u32) {
        let lines = self.grid_lines();
        (lines.x.to_bits(), lines.y.to_bits())
    }

    pub(crate) fn block_margin_index(&self) -> Option<usize> {
        if self.flags.0 & NodeFlags::BLOCK_CONTAINER == 0 {
            return None;
        }
        margin_storage::margin_index(self.values[slot_index(X, Kind::EvenShare)].to_bits())
    }

    #[cfg(feature = "incremental")]
    pub(crate) fn set_block_margin_index(&mut self, index: usize) {
        self.set_block_margin_word(margin_storage::margin_word(index));
    }

    fn set_block_margin_word(&mut self, word: u32) {
        self.values[slot_index(X, Kind::EvenShare)] = f32::from_bits(word);
    }

    fn wrap_line_metric(&self, kind: wrap_metrics::Metric) -> f32 {
        f32::from_bits(wrap_metrics::read_metric(&self.parent_flow, kind))
    }

    pub(crate) fn set_wrap_metric(&mut self, kind: wrap_metrics::Metric, bits: u32) {
        wrap_metrics::store_metric(&mut self.parent_flow, kind, bits);
    }
}

impl Default for NodeLayoutData {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Default)]
pub(crate) struct RetainedSizing {
    #[cfg(feature = "incremental")]
    slots: u32,
    #[cfg(feature = "incremental")]
    blocks: usize,
    /// Ordinary leaves solve exactly their declared bounds in addition to Regular and Final.
    #[cfg(feature = "incremental")]
    leaf_bounds: u32,
    #[cfg(feature = "incremental")]
    inspect_descendants: bool,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct PrepareFrame<I> {
    node: I,
    next: Option<I>,
    retain: bool,
    children_layout: ChildrenLayout,
    block_parent: Option<bool>,
    block_children: Option<bool>,
    stack_axis: Option<Axis>,
    spacing: f32,
    pixel_fit_axis: Option<Axis>,
    extent: f32,
    fixed_cross: Option<(Axis, f32)>,
    n_placed_children: u32,
    n_nodes: u32,
    flags: u32,
}

impl<I> PrepareFrame<I> {
    #[inline]
    fn include_child(&mut self, params: &LayoutParams, child_nodes: u32, needs_solve: bool) {
        self.n_nodes = cycle_rules::add_count(self.n_nodes, child_nodes);
        if needs_solve {
            self.flags |= NodeFlags::DESCENDANTS_NEED_SOLVE;
        }
        if let Some(axis) = self.pixel_fit_axis && !params.disabled && !params.free_placement {
            if let Size::Pixels(size) = params.size[axis]
                && params.min_size[axis].is_none() && params.max_size[axis].is_none()
            {
                let [start, end] = margins(params, axis);
                let child_extent = with_margin(size, start + end);
                self.extent = if Some(axis) == self.stack_axis {
                    self.extent + child_extent
                } else {
                    self.extent.max(child_extent)
                };
            } else {
                self.pixel_fit_axis = None;
            }
        }
        summarize_child(params, &mut self.n_placed_children, &mut self.flags);
    }
}

pub(crate) enum Prepare<I> {
    Done(u32, bool),
    Children(PrepareFrame<I>),
}

#[cfg(feature = "incremental")]
struct BranchCacheAccess<'a, T: ?Sized> {
    tree: &'a mut T,
    counts: &'a mut SubtreeCounts,
}

#[cfg(feature = "incremental")]
impl<T: Solve + ?Sized> retained_branch::CacheModel for BranchCacheAccess<'_, T> {
    type Id = T::NodeId;
}

#[cfg(feature = "incremental")]
impl<T: Solve + ?Sized> retained_branch::BranchCache for BranchCacheAccess<'_, T> {
    #[inline]
    fn status(&self, node: Self::Id) -> retained_branch::CachedBranch {
        use retained_branch::CachedBranch;
        let data = self.tree.node_layout_data(node);
        if !region_policy::clean_branch_root(data.structural_change, data.flags.has_cycle()) {
            return CachedBranch::Reject;
        }
        if self.tree.node_layout_params(node).disabled {
            return CachedBranch::Hidden;
        }
        if data.flags.check_state(X, Kind::Final) == SOLVED && data.flags.check_state(Y, Kind::Final) == SOLVED {
            CachedBranch::Ready
        } else {
            CachedBranch::Reject
        }
    }

    #[inline]
    fn first(&self, node: Self::Id) -> Option<Self::Id> {
        self.tree.first_child(node)
    }

    #[inline]
    fn next(&self, node: Self::Id) -> Option<Self::Id> {
        self.tree.next_sibling(node)
    }

    #[inline]
    fn include(&mut self, node: Self::Id) {
        self.counts.include(self.tree.node_layout_data(node).flags);
    }

    #[inline]
    fn dirty_children(&mut self, node: Self::Id) {
        self.tree.node_layout_data_mut(node).mark_children_changed();
    }
}

/// A `Fill` child of a stack, in `solve_even_share`.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct FillChild {
    min: f32,
    max: f32,
    weight: f32,
}

impl FillChild {
    fn new(content: Option<f32>, min: Option<f32>, max: Option<f32>, capped_by_content: bool, weight: f32) -> Self {
        // f32::min/max ignore a NaN bound. Fold the intrinsic constraint into the
        // interval once, preserving the declared minimum's precedence over the maximum.
        // If a target is NaN, its violation (size minus target) is NaN for any size
        // and the distribution loop can never freeze that child.
        let mut min = min.unwrap_or(f32::NAN);
        let mut max = max.unwrap_or(f32::NAN);
        if let Some(content) = content.filter(|value| !value.is_nan()) {
            if capped_by_content {
                max = max.min(content);
            } else {
                min = min.max(content.min(max));
            }
        }
        Self { min, max, weight }
    }

    fn size(&self, target: f32) -> f32 {
        // An absent bound is NaN, so its comparison is false. A NaN target
        // produces a NaN violation and never freezes.
        let capped = if self.max < target { self.max } else { target };
        if self.min > capped { self.min } else { capped }
    }

    #[inline]
    fn resolve(self, share: f32) -> (f32, f32) {
        let target = share * self.weight;
        let size = self.size(target);
        (size, size - target)
    }
}

const MAX_FIT_STACK_FRAC: f32 = 0.999;
const MAX_FIT_STACK_STEPS: usize = 64;
const FIT_STACK_EPSILON: f32 = 1e-6;
const EVEN_SHARE_EPSILON: f32 = 1e-3;

#[inline(always)]
fn clamp(size: f32, min: Option<f32>, max: Option<f32>) -> f32 {
    let size = max.map_or(size, |max| size.min(max));
    min.map_or(size, |min| size.max(min))
}

#[inline(always)]
fn inner(size: f32, padding: f32) -> f32 {
    (size - padding).max(0.0)
}

#[derive(Clone, Copy)]
struct GridTrack {
    count: f32,
    cell: f32,
    spacing: f32,
}

impl GridTrack {
    #[inline]
    fn new(inner: f32, n: f32, spacing: f32) -> Self {
        let count = n.max(1.0);
        let cell = ((inner - spacing * (n - 1.0)) / count).max(0.0);
        Self { count, cell, spacing }
    }

    #[inline]
    fn extent(self, span: u16) -> f32 {
        let span = f32::from(span.max(1)).min(self.count);
        span * self.cell + (span - 1.0) * self.spacing
    }
}

#[inline]
fn fill_inside_margins(size: f32, params: &LayoutParams, axis: Axis) -> f32 {
    let [start, end] = margins(params, axis);
    let margin = start + end;
    if margin == 0.0 { size } else { (size - margin).max(0.0) }
}

#[inline(always)]
fn summarize_child(params: &LayoutParams, n_placed: &mut u32, flags: &mut u32) {
    if !params.disabled && !params.free_placement {
        *n_placed = cycle_rules::add_count(*n_placed, 1);
        if params.size.x.is_flex() {
            *flags |= NodeFlags::FLEX_CHILD_X;
        }
        if params.size.y.is_flex() {
            *flags |= NodeFlags::FLEX_CHILD_Y;
        }
        if params.grid_span.x > 1 || params.grid_span.y > 1 {
            *flags |= NodeFlags::GRID_SPANS;
        }
    }
}

pub(crate) trait Solve: TreeAdapter {
    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn tree_traversal_next(&self, i: Self::NodeId) -> Option<Self::NodeId> {
        self.traversal_next(self.root(), i, !self.node_layout_params(i).disabled)
    }

    #[inline(always)]
    fn traversal_next(&self, root: Self::NodeId, i: Self::NodeId, descend: bool) -> Option<Self::NodeId> {
        crate::tree_walk::next(
            i, descend, |node| self.first_child(node), |node| self.next_sibling(node),
            |node| self.parent(node), |node| node == root,
        )
    }

    #[inline(always)]
    fn read_size(&self, i: Self::NodeId, axis: Axis, kind: Kind) -> Option<Size> {
        let node = self.node_layout_params(i);
        let size = match kind {
            Kind::Min => node.min_size[axis],
            Kind::Max => node.max_size[axis],
            Kind::Regular => Some(node.size[axis]),
            Kind::Final | Kind::EvenShare | Kind::Flow => unreachable!(),
        };
        match size {
            Some(Size::Auto) => {
                let inline = axis == X && kind == Kind::Regular;
                let block_item = inline && self.node_layout_data(i).flags.is_block_item();
                Some(if block_schedule::inline_auto(axis == X, kind == Kind::Regular, block_item) {
                    Size::Fill
                } else {
                    Size::FitContent
                })
            }
            Some(size) if axis == Y && size.is_flex()
                && block_schedule::flex_uses_content_height(
                    true, true, self.node_layout_data(i).flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0,
                ) => (kind == Kind::Regular).then_some(Size::FitContent),
            size => size,
        }
    }

    #[inline(always)]
    fn any_size_is_fill(&self, i: Self::NodeId, axis: Axis) -> bool {
        let is_fill = |size: Option<Size>| size.is_some_and(|size| size.is_fill());
        is_fill(self.read_size(i, axis, Kind::Regular)) || is_fill(self.read_size(i, axis, Kind::Min)) || is_fill(self.read_size(i, axis, Kind::Max))
    }

    #[inline(always)]
    fn text_wraps(&self, i: Self::NodeId, axis: Axis) -> bool {
        self.node_layout_params(i).text_wraps_on(axis)
    }

    #[inline(always)]
    fn stack_axis(&self, i: Self::NodeId) -> Option<Axis> {
        match self.node_layout_params(i).children_layout {
            ChildrenLayout::Stack { axis, .. } | ChildrenLayout::Wrap { axis, .. } => Some(axis),
            _ => None,
        }
    }

    /// The parent of `i`, if `i` is placed in a stack on `axis`.
    #[inline(always)]
    fn stack_parent(&self, i: Self::NodeId, axis: Axis) -> Option<Self::NodeId> {
        let parent = self.parent(i)?;
        (self.stack_axis(parent) == Some(axis) && ! self.node_layout_params(i).free_placement).then_some(parent)
    }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn is_in_stack(&self, i: Self::NodeId, axis: Axis) -> bool {
        self.stack_parent(i, axis).is_some()
    }

    #[cfg(feature = "incremental")]
    fn size_depends_on_children(&self, i: Self::NodeId) -> bool {
        [X, Y].into_iter().any(|axis| DECLARED_SIZES.into_iter().any(|kind| {
            self.read_size(i, axis, kind).is_some_and(|size| size.dependency_form().reads_children())
        }))
    }

    /// Updates child counts and flags in one sibling scan when their sizes are independent.
    #[cfg(feature = "incremental")]
    fn try_refresh_independent_parent(&mut self, i: Self::NodeId) -> bool {
        let data = self.node_layout_data(i);
        // An enclosing block's margin collapse can depend on this item's child count.
        let block_item = data.flags.is_block_item();
        let finals_solved = [X, Y].into_iter().all(|axis| data.flags.check_state(axis, Kind::Final) == SOLVED);
        let reads_children = !block_item && finals_solved && self.size_depends_on_children(i);
        if !region_policy::can_refresh(block_item, finals_solved, reads_children) {
            return false;
        }
        let stack = match self.node_layout_params(i).children_layout {
            ChildrenLayout::Free => None,
            ChildrenLayout::Stack { axis, .. } if data.flags.check_state(axis, Kind::EvenShare) == UNSOLVED => Some(axis),
            _ => return false,
        };
        let mut n_placed = 0;
        let mut next = self.first_child(i);
        let mut flags = if next.is_some() { NodeFlags::DESCENDANTS_NEED_SOLVE } else { 0 };
        while let Some(child) = next {
            next = self.next_sibling(child);
            let params = self.node_layout_params(child);
            // Stack shares and the space available to percentages depend on siblings.
            if let Some(axis) = stack && region_policy::stack_reads_child_list(
                !params.disabled, !params.free_placement,
                params.size[axis].is_flex() || params.min_size[axis].is_some_and(|size| size.is_flex())
                    || params.max_size[axis].is_some_and(|size| size.is_flex()),
            )
            {
                return false;
            }
            summarize_child(params, &mut n_placed, &mut flags);
        }
        let data = self.node_layout_data_mut(i);
        data.flags.0 &= !(NodeFlags::FLEX_CHILD_X | NodeFlags::FLEX_CHILD_Y | NodeFlags::GRID_SPANS
            | NodeFlags::DESCENDANTS_NEED_SOLVE | NodeFlags::FIXED_LEAF);
        data.flags.0 |= flags;
        data.n_placed_children = n_placed;
        true
    }

    #[inline]
    fn prepare_leaf<const RETAIN: bool, const REGISTERED_PIXELS: bool>(&mut self, child: Self::NodeId, fixed_cross: Option<(Axis, f32)>, _retained: &mut RetainedSizing) -> bool {
        #[cfg(feature = "incremental")]
        if REGISTERED_PIXELS && self.node_layout_data_mut(child).reuse_registered_pixels() {
            if self.node_layout_data(child).fixed_leaf_summary.is_empty() {
                let summary = fixed_leaf_summary(self.node_layout_params(child));
                self.node_layout_data_mut(child).fixed_leaf_summary = summary;
            }
            return true;
        }
        #[cfg(feature = "incremental")]
        if RETAIN {
            let params = self.node_layout_params(child);
            let intrinsic = match params.size {
                Xy { x: Size::FitContent, y: Size::Fill } => Some(X),
                Xy { x: Size::Fill, y: Size::FitContent } => Some(Y),
                _ => None,
            };
            if let Some(axis) = intrinsic && !params.intrinsic_reads_other_axis(axis)
                && params.min_size == Xy::new_symm(None) && params.max_size == Xy::new_symm(None)
                && self.node_layout_data_mut(child).reset_intrinsic_fill_leaf(axis)
            {
                _retained.slots = cycle_rules::add_count(_retained.slots, 2);
                return false;
            }
            if !_retained.inspect_descendants {
                let p = self.node_layout_params(child);
                for axis in [X, Y] {
                    let bounds = u32::from(p.min_size[axis].is_some()) + u32::from(p.max_size[axis].is_some());
                    _retained.leaf_bounds = cycle_rules::add_count(_retained.leaf_bounds, bounds);
                }
            }
        }
        let params = self.node_layout_params(child);
        let mut data = NodeLayoutData::new();
        if data.seed_pixels(params, false, None) {
            #[cfg(feature = "incremental")]
            if REGISTERED_PIXELS {
                data.fixed_leaf_summary = fixed_leaf_summary(params);
            }
            self.node_layout_data_mut(child).reset_fixed_leaf(data);
            return true;
        }
        #[cfg(feature = "incremental")]
        if RETAIN {
            let slots = data.retain_leaf_slots(self.node_layout_data(child), params);
            _retained.slots = cycle_rules::add_count(_retained.slots, slots);
        }
        let ready = fixed_cross.is_some_and(|(axis, inner)| data.seed_stack_leaf(params, axis, inner));
        *self.node_layout_data_mut(child) = data;
        ready
    }

    fn prepare<const RETAIN: bool, const REGISTERED_PIXELS: bool>(&mut self, i: Self::NodeId, block_parent: Option<bool>, retained: &mut RetainedSizing) -> (u32, bool) {
        let mut work = self.begin_prepare::<RETAIN>(i, block_parent, retained);
        let mut parents = work_stack::work_stack::<_, 8>(std::mem::take(&mut self.layout_data().prepare_stack));
        loop {
            let mut frame = match work {
                Prepare::Done(nodes, needs_solve) => {
                    let Some((mut frame, child)) = parents.pop() else {
                        self.layout_data().prepare_stack = parents.into_spill();
                        return (nodes, needs_solve);
                    };
                    frame.include_child(self.node_layout_params(child), nodes, needs_solve);
                    frame
                }
                Prepare::Children(frame) => frame,
            };
            while let Some(child) = frame.next {
                frame.next = self.next_sibling(child);
                let prepared = if RETAIN && frame.retain {
                    self.prepare_direct_child::<true, REGISTERED_PIXELS>(&mut frame, child, retained)
                } else {
                    self.prepare_direct_child::<false, REGISTERED_PIXELS>(&mut frame, child, retained)
                };
                if prepared {
                    continue;
                }
                #[cfg(feature = "incremental")]
                if frame.retain {
                    retained.inspect_descendants = true;
                }
                let subtree = if RETAIN && frame.retain {
                    self.begin_prepare::<true>(child, frame.block_children, retained)
                } else {
                    self.begin_prepare::<false>(child, frame.block_children, retained)
                };
                match subtree {
                    Prepare::Done(nodes, needs_solve) => {
                        frame.include_child(self.node_layout_params(child), nodes, needs_solve);
                    }
                    Prepare::Children(child_frame) => {
                        parents.push((frame, child));
                        frame = child_frame;
                    }
                }
            }
            let (nodes, needs_solve) = self.finish_prepare(frame, retained);
            work = Prepare::Done(nodes, needs_solve);
        }
    }

    fn begin_prepare<const RETAIN: bool>(&mut self, i: Self::NodeId, block_parent: Option<bool>, _retained: &mut RetainedSizing) -> Prepare<Self::NodeId> {
        let params = self.node_layout_params(i);
        if params.disabled {
            *self.node_layout_data_mut(i) = NodeLayoutData::new();
            return Prepare::Done(0, false);
        }
        #[cfg(feature = "incremental")]
        let retain = if RETAIN && self.node_layout_data(i).flags.check_state(X, Kind::Final) != SOLVED {
            // A newly enabled/new region can contain old, unreachable solver data.
            _retained.inspect_descendants = true;
            false
        } else {
            RETAIN
        };
        #[cfg(not(feature = "incremental"))]
        let retain = false;

        let children_layout = params.children_layout;
        let block_parent = block_schedule::in_flow_parent(block_parent,params.free_placement);
        #[cfg(feature = "incremental")]
        if retain && self.node_layout_data(i).structural_change == StructuralChange::Moved {
            // The planner has included both parents. This node can now retain its
            // local slots or, at a fixed-size boundary, its complete clean subtree.
            self.node_layout_data_mut(i).structural_change = StructuralChange::Clean;
        }
        #[cfg(feature = "incremental")]
        let params = self.node_layout_params(i);
        #[cfg(feature = "incremental")]
        if retain && block_parent.is_none() && !self.node_layout_data(i).flags.is_block_item()
            && self.node_layout_data(i).structural_change == StructuralChange::Clean
            && [X, Y].into_iter().all(|axis| matches!(params.size[axis], Size::Pixels(value) if value.is_finite())
                && params.min_size[axis].is_none() && params.max_size[axis].is_none())
            && self.first_child(i).is_some()
        {
            let mut counts = SubtreeCounts::default();
            // Deep branches take the iterative preparation path.
            if retained_branch::check_branch(&mut BranchCacheAccess { tree: self, counts: &mut counts }, i, 24) {
                let data = self.node_layout_data_mut(i);
                data.structural_change = StructuralChange::Retained;
                // Parent grid and wrap metadata will be assigned for the new list.
                wrap_metrics::clear_parent_line(&mut data.flags.0, NodeFlags::WRAP_LINE_START, &mut data.parent_flow);
                _retained.slots = _retained.slots.saturating_add(counts.nodes.saturating_mul(4));
                _retained.blocks = _retained.blocks.saturating_add(counts.blocks);
                self.layout_data().has_flow |= counts.has_flow;
                // Keep a traversal path to this boundary so the statistics pass releases it.
                return Prepare::Done(counts.nodes, true);
            }
        }
        let params = self.node_layout_params(i);
        let block_children = (children_layout == ChildrenLayout::Block).then(|| {
            block_schedule::auto_content_height(
                matches!(params.size.y, Size::Auto | Size::FitContent),
                params.size.y.is_flex(),
                block_parent == Some(true),
            )
        });
        // A stack can fit an axis here when every in-flow child contributes an
        // unbounded pixel size. Those Regular slots have no dependencies.
        let (stack_axis, spacing) = match children_layout {
            ChildrenLayout::Stack { axis, spacing, .. } => (Some(axis), spacing),
            _ => (None, 0.0),
        };
        let pixel_fit_axis = stack_axis.and_then(|main| {
            if params.text != TextContent::None || params.content_measure != ContentMeasure::None {
                None
            } else if params.size[main.other()] == Size::FitContent {
                Some(main.other())
            } else {
                (params.size[main] == Size::FitContent).then_some(main)
            }
        });
        let fixed_cross = match children_layout {
            ChildrenLayout::Stack { axis, .. } if !retain && block_parent.is_none() => {
                let cross = axis.other();
                match params.size[cross] {
                    Size::Pixels(size) if size.is_finite() && params.min_size[cross].is_none() && params.max_size[cross].is_none() => {
                        Some((cross, inner(size, self.total_padding(i, cross))))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let aspect_on_both_axes = matches!(params.size, Xy { x: Size::AspectRatio(_), y: Size::AspectRatio(_) });
        if aspect_on_both_axes {
            self.warn(LayoutWarning::AspectRatioOnBothAxes { node: i });
        }
        #[cfg(feature = "incremental")]
        if matches!(children_layout, ChildrenLayout::Block | ChildrenLayout::Wrap { .. }) {
            self.layout_data().has_flow = true;
        }

        Prepare::Children(PrepareFrame {
            node: i, next: self.first_child(i), retain, children_layout, block_parent, block_children,
            stack_axis, spacing, pixel_fit_axis, extent: 0.0, fixed_cross,
            n_placed_children: 0, n_nodes: 1, flags: 0,
        })
    }

    #[inline]
    fn prepare_direct_child<const RETAIN: bool, const REGISTERED_PIXELS: bool>(
        &mut self, frame: &mut PrepareFrame<Self::NodeId>, child: Self::NodeId, retained: &mut RetainedSizing,
    ) -> bool {
        let no_parent_specialty = frame.pixel_fit_axis.is_none() && frame.block_children.is_none();
        #[cfg(feature = "incremental")]
        if REGISTERED_PIXELS && !RETAIN && no_parent_specialty && self.first_child(child).is_none() {
            let data = self.node_layout_data_mut(child);
            let summary = data.fixed_leaf_summary;
            if summary.is_ready() && data.reuse_registered_pixels() {
                frame.n_nodes = cycle_rules::add_count(frame.n_nodes, 1);
                frame.n_placed_children = cycle_rules::add_count(frame.n_placed_children, u32::from(summary.in_flow()));
                if summary.spans() { frame.flags |= NodeFlags::GRID_SPANS; }
                return true;
            }
        }
        let params = self.node_layout_params(child);
        // Fixed leaves in a full solve need no child frame or flex flags.
        if !RETAIN && !REGISTERED_PIXELS && no_parent_specialty
            && matches!(params.size, Xy { x: Size::Pixels(_), y: Size::Pixels(_) })
            && !params.disabled && matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
            && self.first_child(child).is_none()
        {
            let mut leaf = NodeLayoutData::new();
            if leaf.seed_pixels(params, false, None) {
                if !params.free_placement {
                    frame.n_placed_children = cycle_rules::add_count(frame.n_placed_children, 1);
                    if params.grid_span.x > 1 || params.grid_span.y > 1 { frame.flags |= NodeFlags::GRID_SPANS; }
                }
                frame.n_nodes = cycle_rules::add_count(frame.n_nodes, 1);
                self.node_layout_data_mut(child).reset_fixed_leaf(leaf);
                return true;
            }
        }
        if frame.block_children.is_none() && !params.disabled
            && matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
            && self.first_child(child).is_none()
            && !matches!(params.size, Xy { x: Size::AspectRatio(_), y: Size::AspectRatio(_) })
        {
            let ready = self.prepare_leaf::<RETAIN, REGISTERED_PIXELS>(child, frame.fixed_cross, retained);
            frame.include_child(self.node_layout_params(child), 1, !ready);
            return true;
        }
        false
    }

    fn finish_prepare(&mut self, frame: PrepareFrame<Self::NodeId>, _retained: &mut RetainedSizing) -> (u32, bool) {
        let PrepareFrame { node: i, children_layout, block_parent, block_children, stack_axis, spacing,
            pixel_fit_axis, extent, n_placed_children, n_nodes, flags, .. } = frame;
        let params = self.node_layout_params(i);
        let mut data = NodeLayoutData::new();
        data.n_placed_children = n_placed_children;
        data.flags.0 = flags;
        if let Some(auto_height) = block_parent {
            data.flags.0 |= NodeFlags::BLOCK_ITEM;
            if auto_height {
                data.flags.0 |= NodeFlags::BLOCK_PARENT_AUTO_HEIGHT;
            }
        }
        if block_children.is_some() {
            data.flags.0 |= NodeFlags::BLOCK_CONTAINER;
        }
        if matches!(children_layout, ChildrenLayout::Wrap { .. }) {
            data.flags.0 |= NodeFlags::WRAP_CONTAINER;
        }
        let width_grid_axis = match children_layout {
            ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } => Some(main_axis),
            _ => None,
        };
        let both_axes_fixed = data.seed_pixels(params, block_parent.is_some(), width_grid_axis);
        if let Some(axis) = pixel_fit_axis {
            let own = params.image.map_or(0.0, |extent| 0.0f32.max(extent[axis]));
            let index = slot_index(axis, Kind::Regular);
            let gaps = if Some(axis) == stack_axis { spacing * (n_placed_children as f32 - 1.0).max(0.0) } else { 0.0 };
            data.publish_slot(index, extent.max(own) + gaps + self.total_padding(i, axis));
            #[cfg(feature = "incremental")]
            { data.levels[index] = u16::from(n_placed_children != 0); }
        }
        #[cfg(feature = "incremental")]
        if frame.retain && !both_axes_fixed && self.first_child(i).is_none()
            && matches!(children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        {
            let slots = data.retain_leaf_slots(self.node_layout_data(i), params);
            _retained.slots = cycle_rules::add_count(_retained.slots, slots);
        }
        *self.node_layout_data_mut(i) = data;

        if let ChildrenLayout::Grid { columns: MainAxisCellSize::Count(n), main_axis, backfill, .. } = children_layout {
            self.assign_grid_cells(i, n.max(1) as usize, n.max(1) as f32, main_axis, backfill);
        }
        let needs_solve = !both_axes_fixed
            || data.flags.0 & (NodeFlags::DESCENDANTS_NEED_SOLVE | NodeFlags::BLOCK_CONTAINER | NodeFlags::WRAP_CONTAINER) != 0;
        (n_nodes, needs_solve)
    }

    #[inline(always)]
    fn width_grid_main_axis(&self, i: Self::NodeId) -> Option<Axis> {
        match self.node_layout_params(i).children_layout {
            ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } => Some(main_axis),
            _ => None,
        }
    }

    #[cfg(all(test, feature = "incremental"))]
    fn solve_all_dependencies(&mut self, slot: Slot<Self::NodeId>) {
        self.request_dependencies(slot, &mut |tree: &mut Self, dependency: Slot<Self::NodeId>| {
            tree.solve_slot(dependency.node, dependency.axis, dependency.kind);
        });
    }

    fn request_dependencies(
        &mut self, slot: Slot<Self::NodeId>, request: &mut impl FnMut(&mut Self, Slot<Self::NodeId>),
    ) {
        let Slot { node: i, axis, kind } = slot;
        match kind {
            Kind::Final => {
                for kind in DECLARED_SIZES {
                    if self.read_size(i, axis, kind).is_some() {
                        request(self, Slot { node: i, axis, kind });
                    }
                }
            }
            Kind::EvenShare => wrap_schedule::request_flow_inputs(
                &mut FlowDependencies { tree: self, parent: i, main: axis, request },
                wrap_schedule::Producer::Share,
            ),
            Kind::Flow => self.request_flow_dependencies(i, request),
            declared => {
                let form = self.read_size(i, axis, declared).unwrap().dependency_form();
                let stack = if matches!(form, Form::Fill) { self.stack_parent(i, axis) } else { None };
                match form.input(stack.is_some()) {
                    Input::None => {}
                    Input::OppositeFinal => request(self, Slot { node: i, axis: axis.other(), kind: Kind::Final }),
                    Input::ParentFinal => self.request_available_from_parent(slot, request),
                    Input::ParentShare => request(self, Slot { node: stack.unwrap(), axis, kind: Kind::EvenShare }),
                    Input::IntrinsicChildren => self.request_intrinsic_dependencies(i, axis, request),
                }
            }
        }
    }

    fn request_intrinsic_dependencies(
        &mut self, i: Self::NodeId, axis: Axis, request: &mut impl FnMut(&mut Self, Slot<Self::NodeId>),
    ) {
        match self.node_layout_params(i).children_layout {
            ChildrenLayout::Block if axis == Y => request(self, Slot { node: i, axis: Y, kind: Kind::Flow }),
            ChildrenLayout::Wrap { axis: main, .. } if main != axis => {
                request(self, Slot { node: i, axis, kind: Kind::Flow });
            }
            _ => for_each_layout_child!(self, i, child, {
                if !self.node_layout_params(child).free_placement {
                    for kind in DECLARED_SIZES {
                        if let Some(size) = self.read_size(child, axis, kind) && size.dependency_form().contributes_to_intrinsic() {
                            request(self, Slot { node: child, axis, kind });
                        }
                    }
                }
            }),
        }
        let other = axis.other();
        if dependency_rules::reads_intrinsic_constraint(
            self.node_layout_params(i).intrinsic_reads_other_axis(axis), self.width_grid_main_axis(i) == Some(other),
        ) {
            request(self, Slot { node: i, axis: other, kind: Kind::Final });
        }
    }

    fn request_flow_dependencies(
        &mut self, i: Self::NodeId, request: &mut impl FnMut(&mut Self, Slot<Self::NodeId>),
    ) {
        match self.node_layout_params(i).children_layout {
            ChildrenLayout::Wrap { axis, .. } => {
                wrap_schedule::request_flow_inputs(
                    &mut FlowDependencies { tree: self, parent: i, main: axis, request },
                    wrap_schedule::Producer::Cross,
                );
            }
            ChildrenLayout::Block => block_schedule::request_block_inputs(&mut BlockDependencies { tree: self, parent: i, request }),
            _ => unreachable!(),
        }
    }

    /// Solves what `available_from_parent` reads. The root reads the window size, which is an input.
    #[inline(always)]
    fn request_available_from_parent(
        &mut self, slot: Slot<Self::NodeId>, request: &mut impl FnMut(&mut Self, Slot<Self::NodeId>),
    ) {
        use dependency_rules::request_parent_inputs;
        let i = slot.node;
        let Some(parent) = self.parent(i) else {
            return;
        };
        request_parent_inputs!(
            !self.node_layout_params(i).free_placement
                && matches!(self.node_layout_params(parent).children_layout, ChildrenLayout::Wrap { axis, .. } if axis != slot.axis);
            dependency_rules::reads_parent_axis(false, !self.node_layout_params(i).free_placement,
                self.width_grid_main_axis(parent) == Some(slot.axis.other()));
            other => {
                let axis = if other { slot.axis.other() } else { slot.axis };
                request(self, Slot { node: parent, axis, kind: Kind::Final });
            };
            { request(self, Slot { node: parent, axis: slot.axis, kind: Kind::Flow }); }
        );
    }

    fn measure_sizes<const REGISTERED_PIXELS: bool>(&mut self, window_size: Xy<f32>) {
        self.layout_data().window_size = window_size;
        self.layout_data().block_margins.clear();
        #[cfg(feature = "incremental")]
        {
            let data = self.layout_data();
            data.has_cycle = false;
            data.has_flow = false;
            data.pending_full_solve = None;
        }
        let _summary = self.prepare::<false, REGISTERED_PIXELS>(self.root(), None, &mut RetainedSizing::default());
        #[cfg(feature = "incremental")]
        {
            self.layout_data().n_nodes_solved = _summary.0;
        }
        self.solve_subtree::<false>(self.root());
    }

    /// Rebuilds an isolated sizing region using its parent's already-solved inputs.
    /// The caller includes the parent in the region if the edit changes those inputs.
    #[cfg(feature = "incremental")]
    fn measure_subtree(&mut self, root: Self::NodeId) -> (u32, u32, usize) {
        let parent_layout = self.parent(root).map(|parent| self.node_layout_params(parent).children_layout);
        let params = self.node_layout_params(root);
        let in_flow = !params.disabled && !params.free_placement;
        debug_assert!(!region_policy::attached_flow_child(
            in_flow, matches!(parent_layout, Some(ChildrenLayout::Wrap { .. } | ChildrenLayout::Block)),
        ));
        // The enclosing grid has already assigned the region's unchanged cell.
        let grid_cell = grid_state::preserve_parent_cell(
            in_flow, matches!(parent_layout, Some(ChildrenLayout::Grid { .. })),
            self.node_layout_data(root).parent_flow,
        );
        let mut retained = RetainedSizing::default();
        let (nodes, needs_solve) = self.prepare::<true, false>(root, None, &mut retained);
        if let Some(cell) = grid_cell {
            self.node_layout_data_mut(root).parent_flow = cell;
        }
        // Every enabled node publishes Regular and Final on both axes, including
        // the pixel slots seeded by prepare. Other slots are evaluated on demand.
        let mut slots = nodes.saturating_mul(4);
        let mut blocks = retained.blocks;
        if needs_solve {
            self.solve_subtree::<true>(root);
            if !retained.inspect_descendants {
                slots = slots.saturating_add(retained.leaf_bounds);
            }
            let mut next = Some(root);
            while let Some(node) = next {
                if self.node_layout_data(node).structural_change == StructuralChange::Retained {
                    self.node_layout_data_mut(node).structural_change = StructuralChange::Clean;
                    next = self.traversal_next(root, node, false);
                    continue;
                }
                let flags = self.node_layout_data(node).flags;
                const SOLVED_BITS: u32 = 0xaaaa_aaaa & ((1 << (2 * N_SLOTS)) - 1);
                slots = slots.saturating_add((flags.0 & SOLVED_BITS).count_ones().saturating_sub(4));
                blocks += usize::from(flags.0 & NodeFlags::BLOCK_CONTAINER != 0);
                next = self.traversal_next(root, node, retained.inspect_descendants
                    && flags.0 & NodeFlags::DESCENDANTS_NEED_SOLVE != 0);
            }
        }
        (nodes, slots.saturating_sub(retained.slots), blocks)
    }

    fn solve_subtree<const RETAIN: bool>(&mut self, root: Self::NodeId) {
        let mut next = Some(root);
        while let Some(node) = next {
            #[cfg(feature = "incremental")]
            if RETAIN && self.node_layout_data(node).structural_change == StructuralChange::Retained {
                next = self.traversal_next(root, node, false);
                continue;
            }
            let flags = self.node_layout_data(node).flags;
            if flags == NodeFlags::EMPTY && self.node_layout_params(node).disabled {
                next = self.traversal_next(root, node, false);
                continue;
            }
            let [first_axis, second_axis] = cycle_rules::canonical_axes(X, Y);
            visit_sizing_roots!(
                first_axis, second_axis;
                axis => {
                    if flags.check_state(axis, Kind::Final) != SOLVED && !self.finish_wrapped_fill(node, axis) {
                        self.solve_slot(node, axis, Kind::Final);
                    }
                };
                flags.0 & NodeFlags::BLOCK_CONTAINER != 0 => {
                    self.solve_slot(node, Y, Kind::Flow);
                };
                flags.0 & NodeFlags::WRAP_CONTAINER != 0 => {
                    let axis = self.stack_axis(node).unwrap();
                    self.solve_slot(node, axis, Kind::EvenShare);
                }
            );
            let descend = flags.0 & NodeFlags::DESCENDANTS_NEED_SOLVE != 0 && !self.solve_fill_items(node);
            next = self.traversal_next(root, node, descend);
        }
    }

    /// A wrapped leaf can read its line extent directly once flow has solved.
    fn finish_wrapped_fill(&mut self, child: Self::NodeId, cross: Axis) -> bool {
        let params = self.node_layout_params(child);
        if params.size[cross] != Size::Fill || params.free_placement
            || params.min_size[cross].is_some() || params.max_size[cross].is_some()
            || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
            || self.first_child(child).is_some()
        {
            return false;
        }
        let data = self.node_layout_data(child);
        if data.flags.check_state(cross, Kind::Regular) != UNSOLVED || data.flags.check_state(cross, Kind::Final) != UNSOLVED { return false; }
        let Some(parent) = self.parent(child) else { return false; };
        let parent_data = self.node_layout_data(parent);
        if parent_data.flags.check_state(cross, Kind::Flow) != SOLVED
            || !matches!(self.node_layout_params(parent).children_layout, ChildrenLayout::Wrap { axis, .. } if axis != cross)
        {
            return false;
        }
        let size = fill_inside_margins(data.wrap_line_metric(wrap_metrics::Metric::Cross), params, cross);
        // Resolve non-finite sizes through the usual slots so their warnings are emitted.
        if !size.is_finite() { return false; }
        #[cfg(feature = "incremental")]
        let level = dependency_rules::next_level(parent_data.levels[slot_index(cross, Kind::Flow)]);
        #[cfg(not(feature = "incremental"))]
        let level = 0;
        self.node_layout_data_mut(child).seed_unbounded_axis(cross, size, level);
        true
    }

    /// Resolves fill items together once their parent's geometry is known.
    fn solve_fill_items(&mut self, node: Self::NodeId) -> bool {
        let axis = match self.node_layout_params(node).children_layout {
            ChildrenLayout::Stack { axis, .. } => axis,
            ChildrenLayout::Grid { columns: MainAxisCellSize::Count(_), spacing_x, spacing_y, .. } => {
                return self.solve_grid_fill_leaves(node, Xy::new(spacing_x, spacing_y));
            }
            _ => return false,
        };
        let flags = self.node_layout_data(node).flags;
        if flags.0 & NodeFlags::flex_child(axis) == 0 || flags.check_state(axis, Kind::EvenShare) != UNSOLVED {
            return false;
        }
        self.solve_simple_fill_items::<false>(node, axis)
    }

    fn solve_grid_fill_leaves(&mut self, node: Self::NodeId, spacing: Xy<f32>) -> bool {
        let parent = self.node_layout_data(node);
        let flex = NodeFlags::FLEX_CHILD_X | NodeFlags::FLEX_CHILD_Y;
        if parent.flags.0 & flex != flex { return false; }
        let lines = parent.grid_lines();
        let track = |axis| {
            let size = self.get_solved_value(node, axis, Kind::Final);
            GridTrack::new(inner(size, self.total_padding(node, axis)), lines[axis], spacing[axis])
        };
        let tracks = Xy::new(track(X), track(Y));
        #[cfg(feature = "incremental")]
        let levels = Xy::new(dependency_rules::next_level(parent.levels[slot_index(X, Kind::Final)]), dependency_rules::next_level(parent.levels[slot_index(Y, Kind::Final)]));
        #[cfg(not(feature = "incremental"))]
        let levels = Xy::new_symm(0);

        for_each_layout_child!(self, node, child, {
            let params = self.node_layout_params(child);
            if params.free_placement || params.size != Xy::new_symm(Size::Fill)
                || params.min_size != Xy::new_symm(None) || params.max_size != Xy::new_symm(None)
                || !matches!(params.children_layout, ChildrenLayout::Stack { .. } | ChildrenLayout::Free)
                || self.first_child(child).is_some() || self.node_layout_data(child).flags != NodeFlags::EMPTY
            {
                return false;
            }
            // Each Regular reads only the parent Final on its own axis for a count grid.
            // The ordinary traversal can resume after a resolved prefix in a mixed grid.
            let width = fill_inside_margins(tracks.x.extent(params.grid_span.x), params, X);
            let height = fill_inside_margins(tracks.y.extent(params.grid_span.y), params, Y);
            if !width.is_finite() || !height.is_finite() { return false; }
            let data = self.node_layout_data_mut(child);
            data.seed_unbounded_axis(X, width, levels.x);
            data.seed_unbounded_axis(Y, height, levels.y);
        });
        true
    }

    fn solve_simple_fill_items<const PIXEL_BOUNDS: bool>(&mut self, node: Self::NodeId, axis: Axis) -> bool {
        let first = self.first_child(node);
        let own = inner(self.get_solved_value(node, axis, Kind::Final), self.total_padding(node, axis));
        let mut budget = fill_budget::after_gaps(own, self.stack_gaps(node, axis));
        let mut total_weight = 0.0;
        let mut needs_cross = false;
        for_each_layout_child!(@from self, first, child, {
            let params = self.node_layout_params(child);
            let flags = self.node_layout_data(child).flags;
            if params.free_placement || params.size[axis] != Size::Fill
                || flags.0 & (NodeFlags::DESCENDANTS_NEED_SOLVE | NodeFlags::BLOCK_CONTAINER | NodeFlags::WRAP_CONTAINER) != 0
                || self.width_grid_main_axis(child) == Some(axis)
            {
                return false;
            }
            if !PIXEL_BOUNDS && (params.min_size[axis].is_some() || params.max_size[axis].is_some()) {
                // Keep the common unbounded loop free of per-item clamp and bound-slot work.
                return self.solve_simple_fill_items::<true>(node, axis);
            }
            needs_cross |= flags.check_state(axis.other(), Kind::Final) != SOLVED;
            if PIXEL_BOUNDS {
                for (kind, bound) in [(Kind::Min, params.min_size[axis]), (Kind::Max, params.max_size[axis])] {
                    if let Some(bound) = bound {
                        let Size::Pixels(pixels) = bound else { return false };
                        // Pixel declarations have no dependencies or measurement callbacks.
                        let data = self.node_layout_data_mut(child);
                        let index = slot_index(axis, kind);
                        data.publish_slot(index, pixels);
                        #[cfg(feature = "incremental")]
                        { data.levels[index] = 0; }
                    }
                }
            } else {
                let [start, end] = margins(params, axis);
                budget = fill_budget::charge(budget, start + end);
                total_weight += params.fill_weight;
            }
        });
        let share = if PIXEL_BOUNDS {
            self.distribute_fill(axis, budget, first, None)
        } else {
            fill_budget::share(fill_budget::nonnegative(budget), 0.0, total_weight)
        };
        let data = self.node_layout_data_mut(node);
        data.publish_slot(slot_index(axis, Kind::EvenShare), share);
        #[cfg(feature = "incremental")]
        let share_level = {
            let level = dependency_rules::next_level(data.levels[slot_index(axis, Kind::Final)]);
            data.levels[slot_index(axis, Kind::EvenShare)] = level;
            level
        };
        for_each_layout_child!(@from self, first, child, {
            let value = share * self.node_layout_params(child).fill_weight;
            let (min, max) = if PIXEL_BOUNDS { self.solved_bounds(child, axis, |_| false) } else { (None, None) };
            let final_size = clamp(value, min, max);
            if !final_size.is_finite() || matches!((min, max), (Some(a), Some(b)) if a > b) {
                // Keep the ordinary diagnostic and callback order for exceptional inputs.
                self.solve_slot(child, X, Kind::Final);
                self.solve_slot(child, Y, Kind::Final);
                continue;
            }
            #[cfg(feature = "incremental")]
            let level = dependency_rules::next_level(share_level);
            #[cfg(not(feature = "incremental"))]
            let level = 0;
            let data = self.node_layout_data_mut(child);
            data.publish_axis(axis, value, final_size, level);
            if needs_cross && data.flags.check_state(axis.other(), Kind::Final) != SOLVED {
                self.solve_slot(child, axis.other(), Kind::Final);
            }
        });
        true
    }

    fn solve_slot(&mut self, node: Self::NodeId, axis: Axis, kind: Kind) {
        self.solve_slot_with_budget(Slot { node, axis, kind }, sizing_stack::NATIVE_DEPTH);
    }

    fn solve_slot_with_budget(&mut self, slot: Slot<Self::NodeId>, budget: u8) {
        match self.enter_slot(slot) {
            Entry::CheckIntrinsic => self.solve_unsolved_slot::<{ cfg!(feature = "incremental") }>(slot, budget),
            Entry::Compute => self.solve_unsolved_slot::<false>(slot, budget),
            Entry::Reuse | Entry::BackEdge => {}
        }
    }

    #[inline(always)]
    fn enter_slot(&mut self, slot: Slot<Self::NodeId>) -> Entry {
        let Slot { node, axis, kind } = slot;
        let entry = cycle_rules::enter(self.node_layout_data(node).flags.check_state(axis, kind));
        match entry {
            Entry::Reuse => {
                #[cfg(feature = "incremental")]
                {
                    let level = self.node_layout_data(node).levels[slot_index(axis, kind)];
                    let data = self.layout_data();
                    data.current_level = data.current_level.max(dependency_rules::next_level(level));
                }
            }
            Entry::BackEdge => {
                #[cfg(feature = "incremental")]
                {
                    self.layout_data().has_cycle = true;
                }
                self.record_cycle(node, axis);
            }
            Entry::CheckIntrinsic | Entry::Compute => {}
        }
        entry
    }

    #[inline]
    fn solve_unsolved_slot<const CHECK: bool>(&mut self, slot: Slot<Self::NodeId>, budget: u8) {
        let opened = self.open_slot::<CHECK>(slot);
        if let Some(budget) = sizing_stack::descend(budget) {
            self.request_dependencies(slot, &mut |tree: &mut Self, dependency| {
                tree.solve_slot_with_budget(dependency, budget);
            });
            self.finish_open_slot::<CHECK>(opened);
        } else {
            self.finish_slots_on_worklist(opened, CHECK);
        }
    }

    #[inline]
    fn open_slot<const CHECK: bool>(&mut self, slot: Slot<Self::NodeId>) -> OpenSlot<Self::NodeId> {
        let Slot { node, axis, kind } = slot;
        let data = self.node_layout_data_mut(node);
        data.flags.set_state(axis, kind, IN_PROGRESS);
        let index = slot_index(axis, kind);
        // A dependency cycle can read an in-progress slot. It must see its normal
        // initial value while we check whether the previous constraint still holds.
        let previous = if CHECK {
            cycle_rules::erase_cached_slot(&mut data.values[index], EMPTY_VALUES[index])
        } else { 0.0 };
        #[cfg(feature = "incremental")]
        let outer_level = std::mem::replace(&mut self.layout_data().current_level, 0);
        OpenSlot { slot, previous, #[cfg(feature = "incremental")] outer_level }
    }

    #[inline]
    fn finish_open_slot<const CHECK: bool>(&mut self, opened: OpenSlot<Self::NodeId>) {
        let Slot { node, axis, kind } = opened.slot;
        let data = self.node_layout_data(node);
        if CHECK && cycle_rules::same_intrinsic_constraint(
            data.flags.check_state(axis.other(), Kind::Final),
            data.values[slot_index(axis.other(), Kind::Final)].to_bits(),
            data.values[slot_index(Y, Kind::Flow)].to_bits(),
        ) {
            let data = self.node_layout_data_mut(node);
            data.publish_slot(slot_index(axis, kind), opened.previous);
        } else {
            self.finish_slot(opened.slot);
        }
        #[cfg(feature = "incremental")]
        {
            let level = self.layout_data().current_level;
            self.layout_data().current_level = opened.outer_level.max(dependency_rules::next_level(level));
            self.node_layout_data_mut(node).levels[slot_index(axis, kind)] = level;
        }
    }

    #[cold]
    #[inline(never)]
    fn finish_slots_on_worklist(&mut self, opened: OpenSlot<Self::NodeId>, check: bool) {
        let mut tasks = Vec::new();
        self.push_sizing_tasks(&mut tasks, opened, check);
        while let Some(task) = tasks.pop() {
            match task {
                SizingTask::Enter(slot) => match self.enter_slot(slot) {
                    Entry::Reuse | Entry::BackEdge => {}
                    Entry::CheckIntrinsic if cfg!(feature = "incremental") => {
                        let opened = self.open_slot::<true>(slot);
                        self.push_sizing_tasks(&mut tasks, opened, true);
                    }
                    Entry::Compute | Entry::CheckIntrinsic => {
                        let opened = self.open_slot::<false>(slot);
                        self.push_sizing_tasks(&mut tasks, opened, false);
                    }
                },
                SizingTask::Finish(opened, false) => self.finish_open_slot::<false>(opened),
                SizingTask::Finish(opened, true) => self.finish_open_slot::<true>(opened),
            }
        }
    }

    fn push_sizing_tasks(
        &mut self, tasks: &mut Vec<SizingTask<Self::NodeId>>, opened: OpenSlot<Self::NodeId>, check: bool,
    ) {
        tasks.push(SizingTask::Finish(opened, check));
        let start = tasks.len();
        // The scheduler reads stable declarations, links and prepared flow
        // context. Enter the requests separately to preserve DFS cycle and rank
        // updates and the order in which warnings and measurements are emitted.
        self.request_dependencies(opened.slot, &mut |_, slot| tasks.push(SizingTask::Enter(slot)));
        sizing_stack::reverse_requests(tasks, start);
    }

    /// Computes the value of a slot whose dependencies are solved, and marks it as solved.
    fn finish_slot(&mut self, slot: Slot<Self::NodeId>) {
        let Slot { node, axis, kind } = slot;
        let size = self.solve_slot_inner(slot);
        if kind == Kind::Final && ! size.is_finite() {
            self.warn(LayoutWarning::NotFinite { node, axis });
        }
        let data = self.node_layout_data_mut(node);
        data.publish_slot(slot_index(axis, kind), size);
        if kind == Kind::Final && grid_state::writes_width_grid(true, self.width_grid_main_axis(node) == Some(axis)) {
            self.assign_width_grid_cells(node);
        }
    }

    /// Keeps the user's callback out of the hot code.
    #[cold]
    #[inline(never)]
    fn warn(&mut self, warning: LayoutWarning<Self::NodeId>) {
        self.layout_warning(warning);
    }

    #[cold]
    #[inline(never)]
    fn record_cycle(&mut self, node: Self::NodeId, axis: Axis) {
        let flags = &mut self.node_layout_data_mut(node).flags;
        if flags.0 & NodeFlags::in_cycle(axis) == 0 {
            flags.0 |= NodeFlags::in_cycle(axis);
            self.layout_warning(LayoutWarning::Cycle { node, axis });
        }
    }

    #[inline(always)]
    fn get_solved_value(&self, i: Self::NodeId, axis: Axis, kind: Kind) -> f32 {
        let data = self.node_layout_data(i);
        debug_assert!(data.flags.check_state(axis, kind) != UNSOLVED, "Slot {axis:?} {kind:?} of node {i:?} read before it is solved.");
        data.values[slot_index(axis, kind)]
    }

    fn solve_slot_inner(&mut self, slot: Slot<Self::NodeId>) -> f32 {
        let i = slot.node;
        let axis = slot.axis;
        match slot.kind {
            Kind::Final => {
                let (min, max) = self.solved_bounds(i, axis, |_| false);
                if let (Some(min), Some(max)) = (min, max) && min > max {
                    self.warn(LayoutWarning::MinAboveMax { node: i, axis });
                }
                let mut size = clamp(self.get_solved_value(i, axis, Kind::Regular), min, max);
                let flags = self.node_layout_data(i).flags;
                if flags.is_block_item() {
                    size = size.max(self.total_padding(i, axis));
                }
                let has_flex_child = flags.0 & NodeFlags::flex_child(axis) != 0;
                if has_flex_child && size <= self.total_padding(i, axis)
                    && self.node_layout_params(i).size[axis] == Size::FitContent
                    && !matches!(self.node_layout_params(i).children_layout, ChildrenLayout::Block | ChildrenLayout::Wrap { .. })
                {
                    self.warn(LayoutWarning::FitContentCollapsed { node: i, axis });
                }
                size
            }
            Kind::EvenShare => self.solve_even_share(i, axis),
            Kind::Flow => self.solve_flow(i),
            declared => match self.read_size(i, axis, declared).unwrap() {
                Size::Pixels(pixels) => pixels,
                Size::AspectRatio(aspect) => {
                    let other = self.get_solved_value(i, axis.other(), Kind::Final);
                    match axis {
                        X => other * aspect,
                        Y => other / aspect,
                    }
                }
                Size::FitContent => self.solve_fitcontent(i, axis),
                Size::Frac(frac) => self.available_from_parent(i, axis, false) * frac,

                Size::Fill => {
                    if let Some(parent) = self.stack_parent(i, axis) {
                        let flags = self.node_layout_data(parent).flags;
                        let share = if flags.0 & NodeFlags::WRAP_CONTAINER == 0 {
                            self.get_solved_value(parent, axis, Kind::EvenShare)
                        } else {
                            wrap_metrics::ready_metric(flags.check_state(axis, Kind::EvenShare) == SOLVED, wrap_metrics::Metric::Share)
                                .map_or(0.0, |metric| self.node_layout_data(i).wrap_line_metric(metric))
                        };
                        share * self.node_layout_params(i).fill_weight
                    } else {
                        self.available_from_parent(i, axis, true)
                    }
                },
                Size::Auto => unreachable!("read_size resolves Auto"),
            },
        }
    }

    #[inline(always)]
    fn solved_bounds(&self, i: Self::NodeId, axis: Axis, ignore_bounds_rule: impl Fn(Size) -> bool) -> (Option<f32>, Option<f32>) {
        let min = if let Some(bound) = self.read_size(i, axis, Kind::Min) && ! ignore_bounds_rule(bound) {
            Some(self.get_solved_value(i, axis, Kind::Min))
        } else { None };
        let max = if let Some(bound) = self.read_size(i, axis, Kind::Max) && ! ignore_bounds_rule(bound) {
            Some(self.get_solved_value(i, axis, Kind::Max))
        } else { None };
        (min, max)
    }

    fn available_from_parent(&mut self, i: Self::NodeId, axis: Axis, fill: bool) -> f32 {
        let Some(parent) = self.parent(i) else {
            return self.layout_data().window_size[axis];
        };
        let params = self.node_layout_params(i);
        let children_layout = self.node_layout_params(parent).children_layout;
        let subtract_margin = |size: f32| {
            if !fill || params.free_placement || children_layout == ChildrenLayout::Free {
                return size;
            }
            fill_inside_margins(size, params, axis)
        };
        if !params.free_placement
            && let ChildrenLayout::Wrap { axis: main, .. } = children_layout
            && main != axis
        {
            let solved = self.node_layout_data(parent).flags.check_state(axis, Kind::Flow) == SOLVED;
            let extent = wrap_metrics::ready_metric(solved, wrap_metrics::Metric::Cross)
                .map_or(0.0, |metric| self.node_layout_data(i).wrap_line_metric(metric));
            return subtract_margin(extent);
        }
        let inner = inner(self.get_solved_value(parent, axis, Kind::Final), self.total_padding(parent, axis));
        if params.free_placement {
            return inner;
        }
        let available = match children_layout {
            ChildrenLayout::Grid { spacing_x, spacing_y, .. } => {
                let spacing = Xy::new(spacing_x, spacing_y)[axis];
                GridTrack::new(inner, self.node_layout_data(parent).grid_lines()[axis], spacing).extent(params.grid_span[axis])
            }
            ChildrenLayout::Stack { axis: stack_axis, .. } if stack_axis == axis => {
                (inner - self.stack_gaps(parent, axis)).max(0.0)
            }
            _ => inner,
        };
        subtract_margin(available)
    }

    fn solve_flow(&mut self, i: Self::NodeId) -> f32 {
        match self.node_layout_params(i).children_layout {
            ChildrenLayout::Wrap { axis, spacing, line_spacing, .. } => {
                // A back edge to EvenShare has not published line starts.
                let marks_ready = self.node_layout_data(i).flags.check_state(axis, Kind::EvenShare) == SOLVED;
                let mut next = self.first_child(i);
                let mut extent = 0.0;
                while next.is_some() {
                    let line = if marks_ready {
                        self.wrap_line::<true>(next, axis, None, spacing)
                    } else {
                        self.wrap_line::<false>(next, axis, None, spacing)
                    };
                    wrap_metrics::publish_metrics(
                        self, next, line.next, wrap_metrics::Metric::Cross, line.cross.to_bits(),
                    );
                    next = line.next;
                    extent += line.cross;
                    if next.is_some() {
                        extent += line_spacing;
                    }
                }
                extent
            }
            ChildrenLayout::Block => {
                let mut flow = self.block_flow(i);
                for_each_layout_child!(self, i, child, {
                    if !self.node_layout_params(child).free_placement {
                        flow.push(self.block_item(child));
                    }
                });
                let (height, margins) = flow.finish();
                let layout = self.node_layout_data(i);
                if layout.flags.is_block_item() && !margins.is_implicit(layout.n_placed_children == 0) {
                    let word = margin_storage::publish_margin(&mut self.layout_data().block_margins,margins);
                    self.node_layout_data_mut(i).set_block_margin_word(word);
                }
                height
            }
            _ => unreachable!(),
        }
    }

    fn solve_fitcontent(&mut self, i: Self::NodeId, axis: Axis) -> f32 {
        let (children, gaps) = match self.node_layout_params(i).children_layout {
            ChildrenLayout::Grid { columns, spacing_x, spacing_y, main_axis, .. } => {
                let spacing = Xy::new(spacing_x, spacing_y)[axis];
                let (n, cell) = match columns {
                    MainAxisCellSize::Width(w) if axis == main_axis => (1.0, w),
                    _ => {
                        let n = self.node_layout_data(i).grid_lines()[axis];
                        let mut cell = 0.0f32;
                        for_each_layout_child!(self, i, child, {
                            if ! self.node_layout_params(child).free_placement {
                                let span = (self.node_layout_params(child).grid_span[axis].max(1) as f32).min(n.max(1.0));
                                let [start, end] = margins(self.node_layout_params(child), axis);
                                let extent = with_margin(self.pre_grow_size(child, axis), start + end);
                                cell = cell.max((extent - (span - 1.0) * spacing) / span);
                            }
                        });
                        (n, cell)
                    }
                };
                ((n * cell + spacing * (n - 1.0)).max(0.0), 0.0)
            }
            ChildrenLayout::Stack { axis: stack_axis, .. } | ChildrenLayout::Wrap { axis: stack_axis, .. } if stack_axis == axis => {
                (self.fit_stack_main(i, axis), self.stack_gaps(i, axis))
            }
            ChildrenLayout::Block if axis == Y => (self.get_solved_value(i, axis, Kind::Flow), 0.0),
            ChildrenLayout::Wrap { .. } => (self.get_solved_value(i, axis, Kind::Flow), 0.0),
            layout => {
                let mut biggest = 0.0f32;
                for_each_layout_child!(self, i, child, {
                    if ! self.node_layout_params(child).free_placement {
                        let size = self.pre_grow_size(child, axis);
                        let extent = if layout == ChildrenLayout::Free {
                            size
                        } else {
                            let [start, end] = margins(self.node_layout_params(child), axis);
                            with_margin(size, start + end)
                        };
                        biggest = biggest.max(extent);
                    }
                });
                (biggest, 0.0)
            }
        };

        let mut own_content = match self.node_layout_params(i).text {
            TextContent::None => 0.0,
            _ => {
                #[cfg(feature = "incremental")]
                { self.layout_data().track_topology = true; }
                if self.text_wraps(i, axis) {
                    let width = inner(self.get_solved_value(i, X, Kind::Final), self.total_padding(i, X));
                    self.measure_text_height(i, Some(width))
                } else {
                    match axis {
                        X => self.measure_text_width(i),
                        Y => self.measure_text_height(i, None),
                    }
                }
            }
        };
        if let Some(image) = self.node_layout_params(i).image {
            own_content = own_content.max(image[axis]);
        }
        if self.node_layout_params(i).content_measure != ContentMeasure::None {
            let measured = self.custom_intrinsic_size(i, axis);
            own_content = own_content.max(measured);
        }

        children.max(own_content) + gaps + self.total_padding(i, axis)
    }

    fn custom_intrinsic_size(&mut self, i: Self::NodeId, axis: Axis) -> f32 {
        #[cfg(feature = "incremental")]
        { self.layout_data().track_topology = true; }
        let params = self.node_layout_params(i);
        let mut known_dimensions = Xy::new_symm(None);
        if params.content_measure.reads_other_axis(axis) {
            let other = axis.other();
            known_dimensions[other] = Some(inner(self.get_solved_value(i, other, Kind::Final), self.total_padding(i, other)));
        }
        let pixel_max = |axis| match params.max_size[axis] {
            Some(Size::Pixels(pixels)) => Some(inner(pixels, self.total_padding(i, axis))),
            _ => None,
        };
        let max_size = Xy::new(pixel_max(X), pixel_max(Y));
        self.measure_content(i, ContentMeasureInput { axis, known_dimensions, max_size })[axis]
    }

    fn fit_stack_main(&mut self, i: Self::NodeId, axis: Axis) -> f32 {
        let mut estimate = 0.0f32;
        let mut overflow = false;
        for _ in 0..MAX_FIT_STACK_STEPS {
            let mut fixed = 0.0f32;
            let mut free_frac = 0.0f32;
            let mut has_frac = false;
            for_each_layout_child!(self, i, child, {
                if self.node_layout_params(child).free_placement {
                    // Nothing
                } else if let Some(Size::Frac(frac)) = self.read_size(child, axis, Kind::Regular) {
                    let [start, end] = margins(self.node_layout_params(child), axis);
                    fixed += start + end;
                    has_frac = true;
                    let wanted = estimate * frac;
                    let (min, max) = self.solved_bounds(child, axis, |bound| bound.is_flex());
                    let allowed = clamp(wanted, min, max);
                    match allowed == wanted {
                        true => free_frac += frac,
                        false => fixed += allowed,
                    }
                } else {
                    let [start, end] = margins(self.node_layout_params(child), axis);
                    fixed += with_margin(self.pre_grow_size(child, axis), start + end);
                }
            });

            if ! has_frac {
                return fixed;
            }

            let next = match free_frac <= MAX_FIT_STACK_FRAC {
                true => fixed / (1.0 - free_frac),
                false => {
                    overflow = true;
                    fixed
                }
            };
            let settled = (next - estimate).abs() <= FIT_STACK_EPSILON * next.abs().max(1.0);
            estimate = next;
            if settled {
                break;
            }
        }
        if overflow {
            self.warn(LayoutWarning::ImpossibleFracChildren { node: i, axis });
        }
        estimate
    }

    #[inline(always)]
    fn pre_grow_size(&self, child: Self::NodeId, axis: Axis) -> f32 {
        let size = match self.read_size(child, axis, Kind::Regular).unwrap() {
            Size::Fill | Size::Frac(_) => 0.0,
            _ => self.get_solved_value(child, axis, Kind::Regular),
        };
        let (min, max) = self.solved_bounds(child, axis, |bound| bound.is_flex());
        clamp(size, min, max)
    }

    fn solve_even_share(&mut self, i: Self::NodeId, axis: Axis) -> f32 {
        let own = inner(self.get_solved_value(i, axis, Kind::Final), self.total_padding(i, axis));
        let first = self.first_child(i);
        if let ChildrenLayout::Wrap { spacing, .. } = self.node_layout_params(i).children_layout {
            let mut first = first;
            while first.is_some() {
                let line = self.wrap_line::<false>(first, axis, Some(own), spacing);
                if let Some(next) = line.next {
                    let flags = &mut self.node_layout_data_mut(next).flags.0;
                    *flags = wrap_metrics::mark_start(*flags, NodeFlags::WRAP_LINE_START);
                }
                if line.has_fill {
                    let gaps = spacing * line.count.saturating_sub(1) as f32;
                    let share = self.distribute_fill(axis, (own - gaps).max(0.0), first, line.next);
                    wrap_metrics::publish_metrics(
                        self, first, line.next, wrap_metrics::Metric::Share, share.to_bits(),
                    );
                }
                first = line.next;
            }
            return 0.0;
        }
        let budget = fill_budget::after_gaps(own, self.stack_gaps(i, axis));
        self.distribute_fill(axis, budget, first, None)
    }

    fn wrap_fill_base(&self, child: Self::NodeId, axis: Axis) -> f32 {
        let content = if self.read_size(child, axis, Kind::Regular) == Some(Size::Fill) {
            0.0
        } else {
            self.get_solved_value(child, axis, Kind::Regular)
        };
        let (min, max) = self.solved_bounds(child, axis, |bound| bound.is_fill());
        clamp(content, min, max)
    }

    fn distribute_fill(
        &mut self,
        axis: Axis,
        budget: f32,
        mut next: Option<Self::NodeId>,
        end: Option<Self::NodeId>,
    ) -> f32 {

        let mut fills = Vec::new();
        let mut inline = [FillChild::default(); 8];
        let mut fill_count = 0;
        let mut collection = fill_collection::FillCollection::new(budget);
        while let Some(child) = next {
            if Some(child) == end { break; }
            next = self.next_sibling(child);
            let node = self.node_layout_params(child);
            if node.free_placement || node.disabled {
                // Nothing
            } else {
                let [start, end] = margins(node, axis);
                collection.margin(start,end);
                if self.any_size_is_fill(child, axis) {
                    let content = if self.read_size(child, axis, Kind::Regular) != Some(Size::Fill) {
                        Some(self.get_solved_value(child, axis, Kind::Regular))
                    } else { None };
                    let weight = node.fill_weight;
                    collection.weight(weight);
                    let (min, max) = self.solved_bounds(child, axis, |bound| bound.is_fill());
                    if fill_collection::has_constraint(content,min,max) {
                        let capped_by_content = content.is_some() && self.read_size(child, axis, Kind::Max) == Some(Size::Fill);
                        let fill = FillChild::new(content, min, max, capped_by_content, weight);
                        if fill_count < inline.len() {
                            inline[fill_count] = fill;
                        } else {
                            if fill_count == inline.len() {
                                fills = std::mem::take(&mut self.layout_data().fills_scratch);
                                fills.reserve(2 * inline.len());
                                fills.extend_from_slice(&inline);
                            }
                            fills.push(fill);
                        }
                        fill_count += 1;
                    } else {
                        collection.mark_unconstrained(weight);
                    }
                } else {
                    collection.fixed(self.get_solved_value(child, axis, Kind::Final));
                }
            }
        }

        let (budget, unfrozen_weight, max_unconstrained_weight) = collection.finish();
        if fill_count <= inline.len() {
            return resolve_fill_share(&mut inline[..fill_count], budget, unfrozen_weight, max_unconstrained_weight);
        }
        let share = resolve_fill_share(&mut fills, budget, unfrozen_weight, max_unconstrained_weight);
        fills.clear();
        self.layout_data().fills_scratch = fills;
        share
    }

    /// Assigns the cells of a grid with `MainAxisCellSize::Width` columns, from its `Final` size on the main axis.
    fn assign_width_grid_cells(&mut self, i: Self::NodeId) {
        let ChildrenLayout::Grid { columns: MainAxisCellSize::Width(w), spacing_x, spacing_y, main_axis: main, backfill } = self.node_layout_params(i).children_layout else {
            unreachable!();
        };
        let spacing = Xy::new(spacing_x, spacing_y)[main];
        let inner_main = inner(self.get_solved_value(i, main, Kind::Final), self.total_padding(i, main));
        let count = grid_state::width_key(inner_main, w, spacing);
        self.assign_grid_cells(i, count as usize, count, main, backfill);
    }

    fn assign_grid_cells(&mut self, i: Self::NodeId, n_main: usize, main_tracks: f32, main_axis: Axis, backfill: bool) {
        use grid_state::AssignmentPath;
        let data = self.node_layout_data(i);
        let has_spans = data.flags.0 & NodeFlags::GRID_SPANS != 0;
        let n_lines = match grid_state::assignment_path(n_main, data.n_placed_children as usize, has_spans) {
            AssignmentPath::Sequential => self.assign_grid_cells_in_order(i, n_main, main_axis) as u64,
            AssignmentPath::OneRow => {
                // Even the widest possible spans fit side-by-side. The unused
                // tracks still affect geometry without needing occupancy storage.
                let mut pos = 0;
                let mut height = 0;
                for_each_layout_child!(self, i, child, {
                    if !self.node_layout_params(child).free_placement {
                        let span = self.node_layout_params(child).grid_span;
                        self.node_layout_data_mut(child).set_grid_cell(main_axis, pos, 0);
                        (pos, height) = grid_state::extend_one_row(pos, height,
                            usize::from(span[main_axis].max(1)), usize::from(span[main_axis.other()].max(1)));
                    }
                });
                height as u64
            }
            AssignmentPath::Search => self.assign_grid_cells_with_spans(i, n_main, main_axis, backfill),
        };

        let [x, y] = grid_state::physical_pair(main_tracks, n_lines as f32, main_axis == Y);
        self.node_layout_data_mut(i).set_grid_lines(Xy::new(x, y));
    }

    /// Without spans, the children go into predictable positions and `backfill` has no effect, because there are no holes.
    fn assign_grid_cells_in_order(&mut self, i: Self::NodeId, n_main: usize, main_axis: Axis) -> usize {
        let mut line = 0;
        let mut pos = 0;
        for_each_layout_child!(self, i, child, {
            if ! self.node_layout_params(child).free_placement {
                self.node_layout_data_mut(child).set_grid_cell(main_axis, pos, line as u64);
                (line, pos) = grid_search::next_cell(line, pos, n_main);
            }
        });
        line + usize::from(pos != 0)
    }

    fn assign_grid_cells_with_spans(&mut self, i: Self::NodeId, n_main: usize, main_axis: Axis, backfill: bool) -> u64 {
        let words_per_line = n_main.div_ceil(GRID_WORD_BITS);
        let count = self.node_layout_data(i).n_placed_children;
        let row_budget = grid_state::packed_row_budget(words_per_line);
        if row_budget < u64::from(count) * u64::from(u16::MAX) {
            // Each item can start at or before the current last row. Their
            // total cross span bounds every intermediate occupancy length.
            let mut height = 0;
            for_each_layout_child!(self, i, child, {
                let item = self.node_layout_params(child);
                if !item.free_placement {
                    height += u64::from(item.grid_span[main_axis.other()].max(1));
                    if height > row_budget {
                        return self.assign_grid_cells_sparse(i, n_main, main_axis, backfill);
                    }
                }
            });
        }
        let mut occupied = std::mem::take(&mut self.layout_data().occupied_scratch);
        // Start each row on a word boundary so the same masks apply to every row of a span.
        if backfill {
            // Each in-flow child occupies at least one cell, including children with spans.
            let min_rows = (count as usize).div_ceil(n_main);
            occupied.reserve(min_rows * words_per_line);
        }
        let mut cursor = grid_search::new_span_cursor();
        for_each_layout_child!(self, i, child, {
            if !self.node_layout_params(child).free_placement {
                let span = self.node_layout_params(child).grid_span;
                let span_pos = usize::from(span[main_axis].max(1)).min(n_main);
                let span_line = usize::from(span[main_axis.other()].max(1));
                let (line, pos) = cursor.place(&mut occupied, n_main, words_per_line, span_line, span_pos, backfill);

                self.node_layout_data_mut(child).set_grid_cell(main_axis, pos, line as u64);
            }
        });
        occupied.clear();
        self.layout_data().occupied_scratch = occupied;
        cursor.rows as u64
    }

    #[cold]
    fn assign_grid_cells_sparse(&mut self, i: Self::NodeId, n_main: usize, main_axis: Axis, backfill: bool) -> u64 {
        let mut occupied = Vec::new();
        let mut rows = 0;
        let mut start = (0, 0);
        for_each_layout_child!(self, i, child, {
            let item = self.node_layout_params(child);
            if !item.free_placement {
                let h = u64::from(item.grid_span[main_axis.other()].max(1));
                let w = usize::from(item.grid_span[main_axis].max(1)).min(n_main);
                let (line, pos) = grid_sparse::find_cell(&occupied, n_main, start, rows, h, w);
                rows = rows.max(line + h);
                let end = pos + w;
                occupied.push(grid_sparse::Occupied { rows: (line, line + h), cols: (pos, end) });
                if !backfill {
                    start = (line, end);
                }
                self.node_layout_data_mut(child).set_grid_cell(main_axis, pos, line);
            }
        });
        rows
    }

    #[inline(always)]
    fn total_padding(&self, i: Self::NodeId, axis: Axis) -> f32 {
        let [start, end] = self.node_layout_params(i).padding[axis];
        start + end
    }

    #[inline(always)]
    fn stack_gaps(&self, i: Self::NodeId, axis: Axis) -> f32 {
        let (ChildrenLayout::Stack { axis: stack_axis, spacing, .. } | ChildrenLayout::Wrap { axis: stack_axis, spacing, .. }) = self.node_layout_params(i).children_layout else {
            return 0.0;
        };
        if stack_axis != axis {
            return 0.0;
        }
        let n = self.node_layout_data(i).n_placed_children as f32;
        spacing * (n - 1.0).max(0.0)
    }
}

struct BlockDependencies<'a, T: Solve + ?Sized, F> {
    tree: &'a mut T,
    parent: T::NodeId,
    request: &'a mut F,
}

impl<T: Solve + ?Sized, F> ScheduleModel for BlockDependencies<'_, T, F> {
    type Id = T::NodeId;
}

impl<T: Solve + ?Sized, F: FnMut(&mut T, Slot<T::NodeId>)> BlockSchedule for BlockDependencies<'_, T, F> {
    #[inline]
    fn first_child(&self) -> Option<Self::Id> {
        self.tree.first_child(self.parent)
    }

    #[inline]
    fn read_child(&self, id: Self::Id) -> (Option<Self::Id>, bool, bool) {
        let params = self.tree.node_layout_params(id);
        let in_flow = !params.disabled && !params.free_placement;
        (self.tree.next_sibling(id), in_flow, in_flow
            && self.tree.node_layout_data(id).flags.0 & NodeFlags::BLOCK_CONTAINER != 0)
    }

    #[inline]
    fn request(&mut self, request: BlockRequest<Self::Id>) {
        let (node, kind) = match request {
            BlockRequest::Height(child) => (child, Kind::Final),
            BlockRequest::Margins(child) => (child, Kind::Flow),
        };
        (self.request)(self.tree, Slot { node, axis: Y, kind });
    }
}

struct FlowDependencies<'a, T: Solve + ?Sized, F> {
    tree: &'a mut T,
    parent: T::NodeId,
    main: Axis,
    request: &'a mut F,
}

impl<T: Solve + ?Sized, F> wrap_schedule::Model for FlowDependencies<'_, T, F> {
    type Id = T::NodeId;
}

impl<T: Solve + ?Sized, F: FnMut(&mut T, Slot<T::NodeId>)> wrap_schedule::FlowRequestSchedule for FlowDependencies<'_, T, F> {
    #[inline(always)]
    fn first(&self) -> Option<Self::Id> {
        self.tree.first_child(self.parent)
    }

    #[inline(always)]
    fn row(&self, child: Self::Id) -> (Option<Self::Id>, bool) {
        let params = self.tree.node_layout_params(child);
        (self.tree.next_sibling(child), !params.disabled && !params.free_placement)
    }

    #[inline(always)]
    fn fills(&self, child: Self::Id) -> bool {
        self.tree.any_size_is_fill(child, self.main)
    }

    #[inline(always)]
    fn declaration(&self, child: Self::Id, producer: wrap_schedule::Producer, index: usize) -> bool {
        use wrap_schedule::Producer;
        let axis = match producer { Producer::Share => self.main, Producer::Cross => self.main.other() };
        self.tree.read_size(child, axis, DECLARED_SIZES[index]).is_some_and(|size| {
            let form = size.dependency_form();
            match producer {
                Producer::Share => form.contributes_to_share(),
                Producer::Cross => form.contributes_to_intrinsic(),
            }
        })
    }

    #[inline(always)]
    fn request(&mut self, request: wrap_schedule::Request<Self::Id>) {
        use wrap_schedule::Request;
        let (node, axis, kind) = match request {
            Request::ParentMainFinal => (self.parent, self.main, Kind::Final),
            Request::ParentShare => (self.parent, self.main, Kind::EvenShare),
            Request::MainFinal(child) => (child, self.main, Kind::Final),
            Request::MainDeclaration(child, index) => (child, self.main, DECLARED_SIZES[index]),
            Request::CrossDeclaration(child, index) => (child, self.main.other(), DECLARED_SIZES[index]),
        };
        (self.request)(self.tree, Slot { node, axis, kind });
    }
}

impl<T: TreeAdapter + ?Sized> Solve for T {}

fn resolve_fill_share(fills: &mut [FillChild], budget: f32, mut unfrozen_weight: f32, max_unconstrained_weight: Option<f32>) -> f32 {
    let mut active = fills;
    let mut frozen_total = 0.0;
    let mut share = 0.0;

    while !active.is_empty() || max_unconstrained_weight.is_some() {
        share = fill_budget::share(budget, frozen_total, unfrozen_weight);
        if active.is_empty() {
            break;
        }
        // Unconstrained children never freeze. Their target minus itself is zero
        // for finite targets and NaN otherwise.
        let initial_violation = if max_unconstrained_weight.is_some_and(|weight| !(share * weight).is_finite()) {
            f32::NAN
        } else {
            0.0
        };
        let total_violation = fill_compaction::fold(active, initial_violation,
            |child| child.resolve(share).1, |total, violation| total + violation);
        if total_violation.abs() < EVEN_SHARE_EPSILON {
            break;
        }

        // Retain constraints in sibling order so later shares use identical rounding.
        let should_freeze = |violation: f32| if total_violation > 0.0 {
            violation > EVEN_SHARE_EPSILON
        } else {
            violation < -EVEN_SHARE_EPSILON
        };
        let (remaining, totals) = fill_compaction::compact(active, (frozen_total, unfrozen_weight),
            |child| {
                let (size, violation) = child.resolve(share);
                (should_freeze(violation), (size, child.weight))
            },
            |(total, weight), (size, frozen_weight)| (total + size, weight - frozen_weight),
        );
        (frozen_total, unfrozen_weight) = totals;
        if !fill_compaction::continue_freezing(active.len(), remaining) {
            break;
        }
        active = &mut active[..remaining];
    }
    share
}

const GRID_WORD_BITS: usize = u64::BITS as usize;

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng, rngs::StdRng};

    #[test]
    fn sizing_worklist_preserves_slot_bits_ranks_and_callback_order() {
        #[derive(Clone)]
        struct DependencyTree {
            params: [LayoutParams; 4],
            nodes: [NodeLayoutData; 4],
            layout: LayoutData<usize>,
            measurements: Vec<(usize, measurement::Request)>,
            warnings: Vec<LayoutWarning<usize>>,
        }

        impl TreeAdapter for DependencyTree {
            type NodeId = usize;
            fn root(&self) -> usize { 0 }
            fn parent(&self, id: usize) -> Option<usize> { [None, Some(0), Some(0), Some(2)][id] }
            fn first_child(&self, id: usize) -> Option<usize> { [Some(1), None, Some(3), None][id] }
            fn next_sibling(&self, id: usize) -> Option<usize> { [None, Some(2), None, None][id] }
            fn node_layout_params(&self, id: usize) -> &LayoutParams { &self.params[id] }
            fn node_layout_data(&self, id: usize) -> &NodeLayoutData { &self.nodes[id] }
            fn node_layout_data_mut(&mut self, id: usize) -> &mut NodeLayoutData { &mut self.nodes[id] }
            fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }
            fn write_output_rect(&mut self, _: usize, _: XyRect, _: XyRect) {}
            fn measure_content(&mut self, id: usize, input: ContentMeasureInput) -> Xy<f32> {
                self.measurements.push((id, input.into()));
                Xy::new(6.25, 9.5)
            }
            fn layout_warning(&mut self, warning: LayoutWarning<usize>) { self.warnings.push(warning); }
        }

        for children_layout in [
            ChildrenLayout::Free,
            ChildrenLayout::Stack { axis: X, arrange: Arrange::Start, spacing: 1.25 },
            ChildrenLayout::Wrap { axis: X, arrange: Arrange::Start, spacing: 2.0, line_spacing: 1.0 },
            ChildrenLayout::Grid { main_axis: X, columns: MainAxisCellSize::Width(14.0), spacing_x: 1.0, spacing_y: 2.0, backfill: true },
            ChildrenLayout::Block,
        ] {
            let mut tree = DependencyTree {
                params: [
                    LayoutParams { size: Xy::new_symm(Size::FitContent), children_layout, ..LayoutParams::DEFAULT },
                    LayoutParams { size: Xy::new(Size::AspectRatio(2.0), Size::FitContent),
                        content_measure: ContentMeasure::HeightForWidth, ..LayoutParams::DEFAULT },
                    LayoutParams { size: Xy::new_symm(Size::FitContent), children_layout: ChildrenLayout::Block,
                        ..LayoutParams::DEFAULT },
                    LayoutParams { size: Xy::new_symm(Size::FitContent), content_measure: ContentMeasure::Independent,
                        ..LayoutParams::DEFAULT },
                ],
                nodes: [NodeLayoutData::new(); 4],
                layout: LayoutData::new(),
                measurements: Vec::new(),
                warnings: Vec::new(),
            };
            tree.layout.window_size = Xy::new_symm(100.0);
            tree.prepare::<false, false>(0, None, &mut RetainedSizing::default());
            let mut spill = tree.clone();
            for node in 0..tree.nodes.len() {
                for axis in [X, Y] {
                    let slot = Slot { node, axis, kind: Kind::Final };
                    tree.solve_slot_with_budget(slot, sizing_stack::NATIVE_DEPTH);
                    spill.solve_slot_with_budget(slot, 0);
                }
            }
            for (recursive, explicit) in tree.nodes.iter().zip(&spill.nodes) {
                assert_eq!(recursive.values.map(f32::to_bits), explicit.values.map(f32::to_bits));
                assert_eq!(recursive.flags, explicit.flags);
                assert_eq!(recursive.parent_flow, explicit.parent_flow);
                #[cfg(feature = "incremental")]
                assert_eq!(recursive.levels, explicit.levels);
            }
            assert!(!tree.measurements.is_empty());
            assert!(tree.warnings.iter().any(|w| matches!(w, LayoutWarning::Cycle { .. })));
            assert_eq!(tree.measurements, spill.measurements);
            assert_eq!(tree.warnings, spill.warnings);
        }
    }

    #[cfg(all(feature = "incremental", not(target_family = "wasm")))]
    #[test]
    fn deep_intrinsic_layout_fits_a_small_native_stack() {
        std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
            let mut tree: LayoutTree = LayoutTree::new();
            let root = tree.root();
            let branch = LayoutParams { size: Xy::new_symm(Size::FitContent), ..LayoutParams::DEFAULT };
            tree.update_node_params(&root, branch).unwrap();
            let mut parent = root.clone();
            for _ in 0..4096 {
                parent = tree.add_node(&parent, branch).unwrap().into();
            }
            let leaf = tree.add_node(&parent, LayoutParams {
                size: Xy::new(Size::Pixels(17.0), Size::Pixels(11.0)), ..LayoutParams::DEFAULT
            }).unwrap();
            tree.solve_layout(Xy::new_symm(100.0));
            let bounds = tree.layout(&root).unwrap();
            assert_eq!([X, Y].map(|axis| bounds[axis][1] - bounds[axis][0]), [17.0, 11.0]);
            assert_eq!(tree.layout(&leaf).unwrap(), bounds);
        }).unwrap().join().unwrap();
    }

    #[test]
    fn fixed_leaf_reset_restores_both_slots_and_discards_parent_flow() {
        let params = LayoutParams { size: Xy::new(Size::Pixels(-0.0), Size::Pixels(12.0)), ..LayoutParams::DEFAULT };
        let mut prepared = NodeLayoutData::new();
        assert!(prepared.seed_pixels(&params, false, None));
        let mut leaf = NodeLayoutData::new();
        leaf.reset_fixed_leaf(prepared);

        for kind in [Kind::Regular, Kind::Final] {
            let slot = slot_index(X, kind);
            leaf.values[slot] = 0.0;
            leaf.reset_fixed_leaf(prepared);
            assert_eq!(leaf.values[slot].to_bits(), (-0.0f32).to_bits());
        }
        leaf.set_grid_cell(X, 3, 1);
        leaf.reset_fixed_leaf(prepared);
        assert_eq!(leaf.parent_flow, [0; 2]);
        leaf.flags.0 |= NodeFlags::WRAP_LINE_START;
        leaf.reset_fixed_leaf(prepared);
        assert!(!leaf.flags.starts_wrap_line());
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn cyclic_width_grid_rebuilds_track_state_after_an_append() {
        let window = Xy::new(100.0, 100.0);
        let mut tree = LayoutTree::<()>::new();
        let grid = tree.add_node(&tree.root(), LayoutParams {
            size: Xy::new(Size::AspectRatio(2.0), Size::FitContent),
            min_size: Xy::new(None, Some(Size::Pixels(20.0))),
            children_layout: ChildrenLayout::Grid {
                columns: MainAxisCellSize::Width(12.0), main_axis: X,
                spacing_x: 0.0, spacing_y: 0.0, backfill: true,
            },
            position: Xy::new_symm(Pos::Start),
            ..LayoutParams::DEFAULT
        }).unwrap();
        let item = LayoutParams {
            size: Xy::new(Size::Pixels(5.0), Size::Pixels(30.0)),
            position: Xy::new_symm(Pos::Start),
            ..LayoutParams::DEFAULT
        };
        let wide = tree.add_node(&grid, LayoutParams { grid_span: Xy::new(2, 1), ..item }).unwrap();
        let same_row = tree.add_node(&grid, item).unwrap();
        tree.solve_layout(window);
        assert!(tree.warnings().iter().any(|warning| matches!(warning, LayoutWarning::Cycle { .. })));
        assert_eq!(tree.layout(&grid).unwrap(), Xy::new([0.0, 40.0], [0.0, 20.0]));
        let new_row = tree.add_node(&grid, item).unwrap();
        let mut full = tree.clone();
        full.invalidate();
        full.solve_layout(window);
        assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
        for node in [&grid, &wide, &same_row, &new_row] {
            assert_eq!(tree.layout(node).unwrap(), full.layout(&full.node_id(node.key())).unwrap());
        }
        // X asks for Y while its grid has only its fresh, provisional counts.
        // The completed X slot subsequently assigns the third child to row two.
        assert_eq!(tree.layout(&grid).unwrap(), Xy::new([0.0, 40.0], [0.0, 20.0]));
        assert_eq!(tree.layout(&new_row).unwrap(), Xy::new([0.0, 5.0], [10.0, 40.0]));
    }

    #[test]
    fn fill_interval_preserves_content_and_bound_precedence() {
        let bounds = [None, Some(-5.0), Some(0.0), Some(3.0), Some(f32::NEG_INFINITY), Some(f32::INFINITY), Some(f32::NAN)];
        for content in bounds {
            for min in bounds {
                for max in bounds {
                    for capped in [false, true] {
                        let fill = FillChild::new(content, min, max, capped, 1.0);
                        for target in [-7.0, -0.0, 2.5, 8.0, f32::NEG_INFINITY, f32::INFINITY] {
                            let raw = match content {
                                Some(content) if capped => content.min(target),
                                Some(content) => content.max(target),
                                None => target,
                            };
                            assert_eq!(fill.size(target), clamp(raw, min, max));
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn packed_fill_constraints_keep_the_sibling_sum_order() {
        // At share 1 the violations are [1e8, 0.5, -1e8, 0.25]. In sibling order
        // they sum to 0.25 and the minima freeze. A pairwise SIMD sum gives zero.
        let mut fills = [
            FillChild::new(None, Some(2e8), None, false, 1e8),
            FillChild::new(None, Some(1.5), None, false, 1.0),
            FillChild::new(None, None, Some(0.0), false, 1e8),
            FillChild::new(None, Some(1.25), None, false, 1.0),
        ];
        assert_eq!(resolve_fill_share(&mut fills, 2e8, 2e8, Some(1.0)), 0.0);
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn grid_fill_leaves_match_ordinary_traversal() {
        for axis in [X, Y] {
            for spacing in [2.25, -0.75, f32::INFINITY] {
                for mixed in [false, true] {
                    let run = |force_ordinary: bool| {
                        let mut tree: LayoutTree = LayoutTree::new();
                        let grid = tree.add_node(&tree.root(), LayoutParams {
                            size: Xy::new(Size::Frac(0.75), Size::Fill),
                            padding: Xy::new([2.75, 1.5], [0.0, 3.0]),
                            children_layout: ChildrenLayout::Grid {
                                columns: MainAxisCellSize::Count(3), spacing_x: spacing, spacing_y: 1.25,
                                main_axis: axis, backfill: false,
                            },
                            ..LayoutParams::DEFAULT
                        }).unwrap();
                        // A free guard bypasses the bulk path without taking a grid cell.
                        tree.add_node(&grid, LayoutParams {
                            disabled: !force_ordinary, free_placement: true, size: Xy::new_symm(Size::Pixels(1.0)),
                            ..LayoutParams::DEFAULT
                        }).unwrap();
                        let mut nodes = Vec::new();
                        for i in 0..6 {
                            let mut p = LayoutParams {
                                grid_span: Xy::new(i % 2 + 1, i),
                                margin: Xy::new([Margin::px(-0.375).unwrap(), Margin::px(2.25).unwrap()], [Margin::AUTO, Margin::ZERO]),
                                ..LayoutParams::DEFAULT
                            };
                            if mixed && i == 3 { p.min_size.y = Some(Size::Pixels(11.0)); }
                            nodes.push(tree.add_node(&grid, p).unwrap());
                        }
                        tree.solve_layout(Xy::new(139.5, 91.25));
                        let slots = nodes.iter().map(|n| {
                            let d = tree.nodes[n.key()].layout;
                            let rect = tree.layout(n).unwrap();
                            (d.values.map(f32::to_bits), d.levels, d.flags, rect.x.map(f32::to_bits), rect.y.map(f32::to_bits))
                        }).collect::<Vec<_>>();
                        let warnings = tree.warnings().iter().cloned()
                            .map(|warning| warning.map_node(|id| id.key())).collect::<Vec<_>>();
                        (slots, warnings)
                    };
                    assert_eq!(run(false), run(true));
                }
            }
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn cross_axis_pixel_fit_tracks_in_flow_children_and_levels() {
        for main in [X, Y] {
            let axis = main.other();
            let mut tree: LayoutTree = LayoutTree::new();
            let mut stack = LayoutParams {
                children_layout: ChildrenLayout::Stack { axis: main, arrange: Arrange::Start, spacing: 0.0 },
                image: Some(Xy::new_symm(9.0)),
                ..LayoutParams::DEFAULT
            };
            stack.size[axis] = Size::FitContent;
            stack.padding[axis] = [1.5, 2.0];
            let parent = tree.add_node(&tree.root(), stack).unwrap();
            let mut item = LayoutParams::DEFAULT;
            item.size[axis] = Size::Pixels(17.5);
            item.margin[axis] = [Margin::px(3.0).unwrap(), Margin::px(-1.0).unwrap()];
            let child = tree.add_node(&parent, item).unwrap();
            for (disabled, free_placement) in [(true, false), (false, true)] {
                tree.add_node(&parent, LayoutParams { size: Xy::new_symm(Size::Pixels(100.0)), disabled, free_placement, ..item }).unwrap();
            }
            let window = Xy::new_symm(100.0);
            let slot = slot_index(axis, Kind::Regular);
            tree.solve_layout(window);
            assert_eq!(tree.nodes[parent.key()].layout.values[slot], 23.0);
            assert_eq!(tree.nodes[parent.key()].layout.levels[slot], 1);

            item.max_size[axis] = Some(Size::Pixels(10.0));
            tree.update_node_params(&child, item).unwrap();
            tree.solve_layout(window);
            assert_eq!(tree.nodes[parent.key()].layout.values[slot], 15.5);

            tree.remove(&child).unwrap();
            tree.solve_layout(window);
            assert_eq!(tree.nodes[parent.key()].layout.values[slot], 12.5);
            assert_eq!(tree.nodes[parent.key()].layout.levels[slot], 0);
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn cross_axis_pixel_fit_matches_the_general_path_at_float_edges() {
        for (pixels, margin, padding, image) in [
            (-0.0, Margin::AUTO, [-0.0; 2], -0.0),
            (f32::NAN, Margin::ZERO, [2.25, -1.0], 3.0),
            (f32::INFINITY, Margin::px(-3.0).unwrap(), [0.5, 1.0], f32::NAN),
            (-f32::MAX, Margin::px(-f32::MAX).unwrap(), [f32::MAX; 2], f32::NEG_INFINITY),
        ] {
            let solve = |text| {
                let mut tree: LayoutTree = LayoutTree::new();
                let parent = tree.add_node(&tree.root(), LayoutParams {
                    children_layout: ChildrenLayout::Stack { axis: X, arrange: Arrange::Start, spacing: 3.0 },
                    size: Xy::new(Size::Fill, Size::FitContent),
                    padding: Xy::new([0.0; 2], padding),
                    image: Some(Xy::new(0.0, image)),
                    text,
                    ..LayoutParams::DEFAULT
                }).unwrap();
                tree.add_node(&parent, LayoutParams {
                    size: Xy::new(Size::Fill, Size::Pixels(pixels)),
                    margin: Xy::new([Margin::ZERO; 2], [margin; 2]),
                    ..LayoutParams::DEFAULT
                }).unwrap();
                tree.solve_layout(Xy::new_symm(100.0));
                let data = &tree.nodes[parent.key()].layout;
                let warnings = tree.warnings().iter().cloned()
                    .map(|warning| warning.map_node(|id| id.key())).collect::<Vec<_>>();
                (data.values.map(f32::to_bits), data.levels, warnings)
            };
            // Fixed text measures zero here, and routes through ordinary intrinsic measurement.
            assert_eq!(solve(TextContent::None), solve(TextContent::Fixed));
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn wrapped_fill_follows_its_line_after_structural_edits() {
        for axis in [X, Y] {
            let cross = axis.other();
            let mut tree: LayoutTree = LayoutTree::new();
            let mut wrap = LayoutParams {
                children_layout: ChildrenLayout::Wrap { axis, arrange: Arrange::Start, spacing: 0.0, line_spacing: 0.0 },
                ..LayoutParams::DEFAULT
            };
            wrap.size[axis] = Size::Pixels(20.0);
            wrap.size[cross] = Size::FitContent;
            let parent = tree.add_node(&tree.root(), wrap).unwrap();
            let mut item = LayoutParams { size: Xy::new_symm(Size::Pixels(10.0)), ..LayoutParams::DEFAULT };
            item.size[cross] = Size::Pixels(30.0);
            let fixed = tree.add_node(&parent, item).unwrap();
            item.size[cross] = Size::Fill;
            item.margin[cross] = [Margin::px(2.5).unwrap(), Margin::px(-0.5).unwrap()];
            let fill = tree.add_node(&parent, item).unwrap();
            for (remove_fixed, expected) in [(false, 28.0), (true, 0.0)] {
                if remove_fixed { tree.remove(&fixed).unwrap(); }
                tree.solve_layout(Xy::new_symm(100.0));
                let flow_level = tree.nodes[parent.key()].layout.levels[slot_index(cross, Kind::Flow)];
                let data = &tree.nodes[fill.key()].layout;
                for (kind, level) in [(Kind::Regular, flow_level + 1), (Kind::Final, flow_level + 2)] {
                    let index = slot_index(cross, kind);
                    assert_eq!(data.flags.check_state(cross, kind), SOLVED);
                    assert_eq!(data.values[index], expected);
                    assert_eq!(data.levels[index], level);
                }
            }
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn wrap_rebuild_clears_a_retained_childs_old_line_start() {
        for axis in [X, Y] {
            let cross = axis.other();
            let mut tree: LayoutTree = LayoutTree::new();
            let mut wrap = LayoutParams {
                children_layout: ChildrenLayout::Wrap { axis, arrange: Arrange::Start, spacing: 2.0, line_spacing: 3.0 },
                ..LayoutParams::DEFAULT
            };
            wrap.size[axis] = Size::Pixels(20.0);
            wrap.size[cross] = Size::FitContent;
            let parent = tree.add_node(&tree.root(), wrap).unwrap();
            let mut item = LayoutParams { size: Xy::new_symm(Size::Pixels(9.0)), ..LayoutParams::DEFAULT };
            item.size[cross] = Size::Pixels(4.0);
            let first = tree.add_node(&parent, item).unwrap();
            let second = tree.add_node(&parent, item).unwrap();
            let free = tree.add_node(&parent, LayoutParams { free_placement: true, ..item }).unwrap();
            let disabled = tree.add_node(&parent, LayoutParams { disabled: true, ..item }).unwrap();
            item.size[cross] = Size::Pixels(8.0);
            let moved_up = tree.add_node(&parent, item).unwrap();
            tree.add_node(&moved_up, item).unwrap();
            let window = Xy::new_symm(120.0);
            tree.solve_layout(window);
            assert!(tree.nodes[moved_up.key()].layout.flags.starts_wrap_line());
            assert_eq!(tree.nodes[second.key()].layout.wrap_line_metric(wrap_metrics::Metric::Cross), 4.0);
            assert_eq!(tree.layout(&moved_up).unwrap()[cross][0] - tree.layout(&parent).unwrap()[cross][0], 7.0);

            tree.remove(&first).unwrap();
            let mut full = tree.clone();
            full.invalidate();
            full.solve_layout(window);
            tree.solve_layout(window);
            assert!(!tree.nodes[moved_up.key()].layout.flags.starts_wrap_line());
            assert_eq!(tree.nodes[second.key()].layout.wrap_line_metric(wrap_metrics::Metric::Cross), 8.0);
            assert_eq!(tree.nodes[moved_up.key()].layout.wrap_line_metric(wrap_metrics::Metric::Cross), 8.0);
            for id in [&second, &free, &moved_up] {
                assert_eq!(tree.layout(id).unwrap(), full.layout(&full.node_id(id.key())).unwrap());
            }
            assert_eq!(tree.layout(&disabled), Err(TreeError::LayoutUnavailable));
            assert_eq!(full.layout(&full.node_id(disabled.key())), Err(TreeError::LayoutUnavailable));
            assert_eq!(tree.layout(&moved_up).unwrap()[cross][0] - tree.layout(&parent).unwrap()[cross][0], 0.0);
            assert_eq!(tree.layout(&moved_up).unwrap()[axis][0] - tree.layout(&parent).unwrap()[axis][0], 11.0);
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn cyclic_wrap_does_not_overwrite_its_solved_cross_extent() {
        let mut tree: LayoutTree = LayoutTree::new();
        let root = tree.root();
        tree.update_node_params(&root, LayoutParams {
            size: Xy::new(Size::FitContent, Size::Pixels(100.0)),
            children_layout: ChildrenLayout::Wrap { axis: X, arrange: Arrange::Start, spacing: 0.0, line_spacing: 0.0 },
            ..LayoutParams::DEFAULT
        }).unwrap();
        // X Fit -> first child's ratio -> its Final X bound -> the parent's
        // share. The second ratio then enters cross Flow while share is active.
        tree.add_node(&root, LayoutParams {
            size: Xy::new_symm(Size::AspectRatio(1.0)),
            min_size: Xy::new(Some(Size::Fill), None),
            ..LayoutParams::DEFAULT
        }).unwrap();
        tree.add_node(&root, LayoutParams {
            size: Xy::new(Size::AspectRatio(1.0), Size::Fill),
            ..LayoutParams::DEFAULT
        }).unwrap();
        tree.add_node(&root, LayoutParams {
            size: Xy::new(Size::Fill, Size::Pixels(50.0)),
            ..LayoutParams::DEFAULT
        }).unwrap();
        let fill = tree.add_node(&root, LayoutParams {
            size: Xy::new(Size::Pixels(0.0), Size::Fill),
            ..LayoutParams::DEFAULT
        }).unwrap();
        let window = Xy::new_symm(120.0);
        tree.solve_layout(window);
        assert!(tree.warnings().iter().any(|warning| matches!(warning, LayoutWarning::Cycle { .. })));
        let [start, end] = tree.layout(&fill).unwrap().y;
        assert_eq!(end - start, 50.0);

        let extra = tree.add_node(&root, LayoutParams {
            size: Xy::new(Size::Pixels(0.0), Size::Pixels(64.0)),
            ..LayoutParams::DEFAULT
        }).unwrap();
        for (remove, height) in [(false, 64.0), (true, 50.0)] {
            if remove { tree.remove(&extra).unwrap(); }
            let mut full = tree.clone();
            full.invalidate();
            full.solve_layout(window);
            assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
            for id in tree.children(&root).unwrap() {
                let actual = tree.layout(&id).unwrap();
                let expected = full.layout(&full.node_id(id.key())).unwrap();
                assert_eq!(actual.x.map(f32::to_bits), expected.x.map(f32::to_bits));
                assert_eq!(actual.y.map(f32::to_bits), expected.y.map(f32::to_bits));
            }
            let [start, end] = tree.layout(&fill).unwrap().y;
            assert_eq!(end - start, height);
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn fixed_stack_extent_seeds_fraction_and_ratio_at_their_dependency_levels() {
        for main in [X, Y] {
            let cross = main.other();
            let mut tree: LayoutTree = LayoutTree::new();
            let mut stack = LayoutParams {
                children_layout: ChildrenLayout::Stack { axis: main, arrange: Arrange::Start, spacing: 3.0 },
                ..LayoutParams::DEFAULT
            };
            stack.size[cross] = Size::Pixels(100.);
            stack.padding[cross] = [4., 8.];
            let parent = tree.add_node(&tree.root(), stack).unwrap();
            let mut leaf = LayoutParams::DEFAULT;
            leaf.size[cross] = Size::Frac(0.5);
            leaf.size[main] = Size::AspectRatio(2.);
            let id = tree.add_node(&parent, leaf).unwrap();
            let window = Xy::new_symm(100.);
            tree.solve_layout(window);
            let data = &tree.nodes[id.key()].layout;
            let ratio = |size: f32| if main == X { size * 2. } else { size / 2. };
            for (axis, size, level) in [(cross, 44., 2), (main, ratio(44.), 4)] {
                for (kind, level) in [(Kind::Regular, level), (Kind::Final, level + 1)] {
                    let index = slot_index(axis, kind);
                    assert_eq!(data.flags.check_state(axis, kind), SOLVED);
                    assert_eq!(data.values[index], size);
                    assert_eq!(data.levels[index], level);
                }
            }
            stack.size[cross] = Size::Pixels(128.);
            tree.update_node_params(&parent, stack).unwrap();
            tree.solve_layout(window);
            assert_eq!(tree.nodes[id.key()].layout.size()[main], ratio(58.));
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn main_axis_pixel_fit_preserves_sum_order_before_gaps_and_padding() {
        let mut tree: LayoutTree = LayoutTree::new();
        let parent = tree.add_node(&tree.root(), LayoutParams {
            size: Xy::new(Size::FitContent, Size::Pixels(8.)),
            children_layout: ChildrenLayout::Stack { axis: X, arrange: Arrange::Start, spacing: 0.25 },
            padding: Xy::new([1., 2.], [0.; 2]),
            ..LayoutParams::DEFAULT
        }).unwrap();
        for width in [1e8, 1., -1e8, 2.5] {
            tree.add_node(&parent, LayoutParams { size: Xy::new(Size::Pixels(width), Size::Fill), ..LayoutParams::DEFAULT }).unwrap();
        }
        tree.solve_layout(Xy::new_symm(100.));
        let data = &tree.nodes[parent.key()].layout;
        assert_eq!(data.values[slot_index(X, Kind::Regular)], 6.25);
        assert_eq!(data.levels[slot_index(X, Kind::Regular)], 1);
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn fill_redistributes_space_after_the_last_constraint_freezes() {
        let mut tree: LayoutTree = LayoutTree::new();
        let root = tree.root();
        tree.update_node_params(&root, LayoutParams {
            children_layout: ChildrenLayout::Stack { arrange: Arrange::Start, axis: X, spacing: 0.0 },
            ..LayoutParams::DEFAULT
        }).unwrap();
        let constrained = tree.add_node(&root, LayoutParams {
            min_size: Xy::new(Some(Size::Pixels(80.0)), None),
            ..LayoutParams::DEFAULT
        }).unwrap();
        let unconstrained = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();

        tree.solve_layout(Xy::new(100.0, 100.0));
        assert_eq!(tree.layout(&constrained).unwrap().x, [0.0, 80.0]);
        assert_eq!(tree.layout(&unconstrained).unwrap().x, [80.0, 100.0]);
        let share_level = tree.nodes[root.key()].layout.levels[slot_index(X, Kind::EvenShare)];
        let bounded = &tree.nodes[constrained.key()].layout;
        assert_eq!(bounded.values[slot_index(X, Kind::Regular)], 20.0);
        assert_eq!(bounded.levels[slot_index(X, Kind::Min)], 0);
        assert_eq!(bounded.levels[slot_index(X, Kind::Regular)], share_level + 1);
        assert_eq!(bounded.levels[slot_index(X, Kind::Final)], share_level + 2);
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn grids_preserve_large_track_counts_and_cell_coordinates() {
        for main in [X, Y] {
            let cross = main.other();
            for backfill in [true, false] {
                for count in [65_535, 65_536, 65_537] {
                    let mut tree = LayoutTree::<()>::new();
                    let root = tree.root();
                    tree.update_node_params(&root, LayoutParams {
                        children_layout: ChildrenLayout::Grid {
                            columns: MainAxisCellSize::Count(count), main_axis: main, backfill,
                            spacing_x: 0.0, spacing_y: 0.0,
                        },
                        ..LayoutParams::DEFAULT
                    }).unwrap();
                    let mut item = LayoutParams::DEFAULT;
                    item.grid_span[main] = u16::MAX;
                    tree.add_node(&root, item).unwrap();
                    let second = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
                    let third = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
                    let mut window = Xy::new_symm(if count == 65_537 { 1.0 } else { 2.0 });
                    window[main] = count as f32;
                    tree.solve_layout(window);
                    for (index, id) in [(65_535, second), (65_536, third)] {
                        let (col, row) = ((index % count) as f32, (index / count) as f32);
                        assert_eq!(tree.layout(&id).unwrap()[main], [col, col + 1.0]);
                        assert_eq!(tree.layout(&id).unwrap()[cross], [row, row + 1.0]);
                    }
                }
                let mut tree = LayoutTree::<()>::new();
                let root = tree.root();
                tree.update_node_params(&root, LayoutParams {
                    children_layout: ChildrenLayout::Grid {
                        columns: MainAxisCellSize::Count(1), main_axis: main, backfill,
                        spacing_x: 0.0, spacing_y: 0.0,
                    },
                    ..LayoutParams::DEFAULT
                }).unwrap();
                let mut item = LayoutParams::DEFAULT;
                item.grid_span[cross] = u16::MAX;
                tree.add_node(&root, item).unwrap();
                let second = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
                let third = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
                let mut window = Xy::new_symm(1.0);
                window[cross] = 65_537.0;
                tree.solve_layout(window);
                assert_eq!(tree.layout(&second).unwrap()[cross], [65_535.0, 65_536.0]);
                assert_eq!(tree.layout(&third).unwrap()[cross], [65_536.0, 65_537.0]);
            }
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn width_grid_reflows_at_the_binary32_integer_boundary() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let window = Xy::new(16_777_216.0, 20.0);
        let grid = |track_width| LayoutParams {
            children_layout: ChildrenLayout::Grid {
                columns: MainAxisCellSize::Width(track_width), main_axis: X, backfill: false,
                spacing_x: 0.0, spacing_y: 0.0,
            },
            ..LayoutParams::DEFAULT
        };
        let container = tree.add_node(&root, grid(1.0)).unwrap();
        let mut item = LayoutParams::DEFAULT;
        item.grid_span.x = u16::MAX;
        for _ in 0..256 { tree.add_node(&container, item).unwrap(); }
        item.grid_span.x = 257;
        let last = tree.add_node(&container, item).unwrap();
        // Keep the localized width change below the incremental queue's full-solve crossover.
        for _ in 0..2048 {
            tree.add_node(&root, LayoutParams { size: Xy::new_symm(Size::Pixels(1.0)), ..LayoutParams::DEFAULT }).unwrap();
        }
        tree.solve_layout(window);
        assert_eq!(tree.layout(&last).unwrap().y, [10.0, 20.0]);
        tree.update_node_params(&container, grid(1.0 - f32::EPSILON)).unwrap();
        assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
        let incremental = tree.layout(&last).unwrap();
        assert_eq!(incremental.y, [0.0, 20.0]);
        tree.invalidate();
        tree.solve_layout(window);
        assert_eq!(tree.layout(&last).unwrap(), incremental);
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn sparse_wide_grids_keep_the_full_track_count_without_allocating_unused_columns() {
        for backfill in [true, false] {
            for (columns, count) in [
                (MainAxisCellSize::Count(u32::MAX), u32::MAX as f32),
                (MainAxisCellSize::Width(f32::MIN_POSITIVE), usize::MAX as f32),
            ] {
                let mut tree = LayoutTree::<()>::new();
                let root = tree.root();
                tree.update_node_params(&root, LayoutParams {
                    children_layout: ChildrenLayout::Grid {
                        columns, main_axis: X, backfill, spacing_x: 0.0, spacing_y: 0.0,
                    },
                    ..LayoutParams::DEFAULT
                }).unwrap();
                let mut item = LayoutParams::DEFAULT;
                item.grid_span = Xy::new(5, 3);
                let a = tree.add_node(&root, item).unwrap();
                item.grid_span = Xy::new(2, 7);
                let b = tree.add_node(&root, item).unwrap();
                tree.solve_layout(Xy::new(count, 7.0));
                assert_eq!(tree.layout(&a).unwrap(), Xy::new([0.0, 5.0], [0.0, 3.0]));
                assert_eq!(tree.layout(&b).unwrap(), Xy::new([5.0, 7.0], [0.0, 7.0]));
                assert_eq!(tree.layout_data.occupied_scratch.capacity(), 0);
            }
        }
    }

    #[cfg(feature = "incremental")]
    #[test]
    fn wide_tall_grid_uses_sparse_occupancy() {
        let span = u16::MAX;
        for main in [X, Y] {
            for backfill in [true, false] {
                let mut tree = LayoutTree::<()>::new();
                let root = tree.root();
                tree.update_node_params(&root, LayoutParams {
                    children_layout: ChildrenLayout::Grid {
                        columns: MainAxisCellSize::Count(400_000), main_axis: main, backfill,
                        spacing_x: 0.0, spacing_y: 0.0,
                    },
                    ..LayoutParams::DEFAULT
                }).unwrap();
                let mut ids = Vec::new();
                for _ in 0..7 {
                    ids.push(tree.add_node(&root, LayoutParams {
                        grid_span: Xy::new_symm(span),
                        ..LayoutParams::DEFAULT
                    }).unwrap());
                }
                let mut window = Xy::new_symm(2.0 * f32::from(span));
                window[main] = 400_000.0;
                tree.solve_layout(window);
                assert_eq!(tree.layout_data.occupied_scratch.capacity(), 0);
                for (index, id) in ids.into_iter().enumerate() {
                    let span = f32::from(span);
                    let col = (index % 6) as f32 * span;
                    let row = (index / 6) as f32 * span;
                    assert_eq!(tree.layout(&id).unwrap()[main], [col, col + span]);
                    assert_eq!(tree.layout(&id).unwrap()[main.other()], [row, row + span]);
                }
            }
        }
    }

    #[test]
    fn packed_grid_matches_cell_by_cell_search() {
        let mut rng = StdRng::seed_from_u64(314);
        for columns in [1_usize, 12, 63, 64, 65, 97, 129, 257] {
            let words_per_line = columns.div_ceil(GRID_WORD_BITS);
            for backfill in [false, true] {
                let mut packed = Vec::new();
                let mut sparse = Vec::new();
                let mut cells = Vec::<Vec<bool>>::new();
                let mut cursor = (0, 0);
                #[cfg(feature = "incremental")]
                let mut placements = Vec::new();
                for child in 0..150 {
                    let height = rng.random_range(1..=8);
                    let width = match child % 4 {
                        0 => rng.random_range(1..=columns),
                        _ => rng.random_range(1..=columns.min(7)),
                    };
                    let (mut line, mut pos) = cursor;
                    loop {
                        if pos + width > columns {
                            line += 1;
                            pos = 0;
                        }
                        let blocked = cells.iter().skip(line).take(height)
                            .any(|row| row[pos..pos + width].contains(&true));
                        if ! blocked {
                            break;
                        }
                        pos += 1;
                    }

                    assert_eq!(
                        find_grid_cell(&packed, columns, words_per_line, cells.len(), cursor, height, width),
                        (line, pos),
                        "columns={columns} backfill={backfill} cursor={cursor:?} span={width}x{height}",
                    );
                    assert_eq!(
                        grid_sparse::find_cell(&sparse, columns, (cursor.0 as u64, cursor.1),
                            cells.len() as u64, height as u64, width),
                        (line as u64, pos),
                        "columns={columns} backfill={backfill} cursor={cursor:?} span={width}x{height}",
                    );
                    sparse.push(grid_sparse::Occupied {
                        rows: (line as u64, (line + height) as u64), cols: (pos, pos + width),
                    });
                    #[cfg(feature = "incremental")]
                    placements.push((line, pos, height, width));
                    let end = line + height;
                    if end > cells.len() {
                        cells.resize_with(end, || vec![false; columns]);
                        packed.resize(end * words_per_line, 0);
                    }
                    for row in &mut cells[line..end] {
                        row[pos..pos + width].fill(true);
                    }
                    let words = &mut packed[line * words_per_line..end * words_per_line];
                    grid_search::occupy_span(words, words_per_line, pos, width);
                    if ! backfill {
                        cursor = (line, pos + width);
                    }
                }
                #[cfg(feature = "incremental")]
                check_grid_layout(columns, cells.len(), backfill, &placements);
            }
        }
    }

    #[cfg(feature = "incremental")]
    fn check_grid_layout(columns: usize, rows: usize, backfill: bool, placements: &[(usize, usize, usize, usize)]) {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        tree.update_node_params(&root, LayoutParams {
            children_layout: ChildrenLayout::Grid {
                columns: MainAxisCellSize::Count(columns as u32),
                main_axis: X, backfill, spacing_x: 0.0, spacing_y: 0.0,
            },
            ..LayoutParams::DEFAULT
        }).unwrap();
        let ids: Vec<_> = placements.iter().map(|&(_, _, height, width)| tree.add_node(&root, LayoutParams {
            grid_span: Xy::new(width as u16, height as u16),
            ..LayoutParams::DEFAULT
        }).unwrap()).collect();
        tree.solve_layout(Xy::new(columns as f32, rows as f32));
        for (&(line, pos, height, width), id) in placements.iter().zip(ids) {
            let expected = Xy::new([pos as f32, (pos + width) as f32], [line as f32, (line + height) as f32]);
            assert_eq!(tree.layout(&id).unwrap(), expected);
        }
    }
}
