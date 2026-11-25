#[path = "grid_search.rs"]
mod grid_search;
#[cfg(test)]
use grid_search::find_grid_cell;
#[path = "grid_words.rs"]
mod grid_words;
#[path = "grid_sparse.rs"]
pub(crate) mod grid_sparse;
#[path = "grid_state.rs"]
pub(crate) mod grid_state;
#[cfg(feature = "incremental")]
#[path = "grid_width.rs"]
mod grid_width;
#[path = "fill_collection.rs"]
mod fill_collection;
#[path = "fill_compaction.rs"]
pub(crate) mod fill_compaction;
#[path = "sizing_stack.rs"]
mod sizing_stack;
#[path = "sizing_child.rs"]
mod sizing_child;
#[path = "sizing_requests.rs"]
pub(crate) mod sizing_requests;
#[path = "sizing_finish.rs"]
pub(crate) mod sizing_finish;
#[path = "sizing_fill.rs"]
pub(crate) mod sizing_fill;
#[path = "prepare_walk.rs"]
pub(crate) mod prepare_walk;
use crate::*;
use crate::flow::wrap_metrics;
use crate::prepare_nodes;
#[cfg(test)]
use crate::prepare_nodes::RetainedSizing;
use crate::vec_memory::{RustVec, VecMemory};
#[path = "wrap_schedule.rs"]
mod wrap_schedule;
#[cfg(any(feature = "incremental", test))]
use crate::Axis::X;
use crate::Axis::Y;
use crate::placement_geometry::RustFloat;
use sizing_finish::phase::{self, OpenSlot};

pub(crate) type SizingTask<I> = sizing_stack::Task<sizing_requests::Request<I>, OpenSlot<I>>;

#[path = "dependency_rules.rs"]
pub(crate) mod dependency_rules;
#[path = "block_schedule.rs"]
pub(crate) mod block_schedule;
use dependency_rules::Form;
#[cfg(feature = "incremental")]
#[path = "leaf_retention.rs"]
pub(crate) mod leaf_retention;
#[path = "cycle_rules.rs"]
pub(crate) mod cycle_rules;
pub(crate) use cycle_rules::{Kind, N_SLOTS, SOLVED, UNSOLVED};
#[cfg(test)]
use cycle_rules::Entry;
pub(crate) const DECLARED_SIZES: [Kind; 3] = cycle_rules::declaration_order(Kind::Regular, Kind::Min, Kind::Max);

pub(crate) use crate::node_flags::NodeFlags;
#[cfg(any(feature = "incremental", test))]
pub(crate) use crate::node_flags::slot_index;
pub use crate::node_data::NodeLayoutData;
use crate::node_data::EMPTY_VALUES;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Slot<I> {
    pub node: I,
    pub axis: Axis,
    pub kind: Kind,
}

impl NodeLayoutData {
    #[cfg(feature = "incremental")]
    #[inline]
    pub(crate) fn cached_stack_start(&self) -> bool {
        self.fixed_leaf_summary.stack_start()
    }

    /// Initializes independent pixel slots and returns whether both final sizes are ready.
    #[cfg(any(feature = "incremental", test))]
    #[inline(always)]
    fn seed_pixels(&mut self, params: &LayoutParams, block_item: bool, width_grid_axis: Option<Axis>) -> bool {
        prepare_nodes::seed_pixels::<RustFloat>(self, params, block_item, width_grid_axis)
    }

    #[cfg(test)]
    #[inline]
    fn reset_fixed_leaf(&mut self, prepared: Self) {
        prepare_nodes::install_fixed::<RustFloat>(self, prepared);
    }

    /// The live declaration proves these four slots independent if both pixel sizes
    /// still match. Recreate the remaining flags from the current children and parent.
    #[cfg(feature = "incremental")]
    pub(crate) fn unchanged_pixel_box(&self, params: &LayoutParams, leaf: bool) -> Option<Self> {
        if params.disabled || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. }) { return None; }
        let mut data = Self::new();
        if !data.seed_pixels(params, false, None) { return None; }
        if !cycle_rules::same_solved_pixels(self.flags.0, &self.values, &data.values) { return None; }
        if leaf {
            data.flags.0 |= NodeFlags::FIXED_LEAF;
        }
        Some(data)
    }

    #[cfg(all(test, feature = "incremental"))]
    fn wrap_line_metric(&self, kind: wrap_metrics::Metric) -> f32 {
        f32::from_bits(wrap_metrics::read_metric(&self.parent_flow, kind))
    }

}

impl Default for NodeLayoutData {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Solve + ?Sized> prepare_nodes::StartActions for T {
    #[cfg(feature = "incremental")]
    type LeafMemory = RustVec;

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn packed_stack_leaves(&mut self) -> &mut crate::packed_stack_leaf::PackedStackLeaves<Self::Id> {
        &mut self.layout_data().packed_stack_leaves
    }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn stack_leaf_hint(&mut self) -> Option<u32> {
        #[cfg(feature = "batch-pilot")]
        let first = self.first_stack_population_hint();
        #[cfg(not(feature = "batch-pilot"))]
        let first = 0;
        let data = self.layout_data();
        let hint = data.n_nodes_solved.max(first);
        data.pixel_scale.is_none().then_some(hint)
    }

    #[inline(always)]
    fn warn_both_axes_ratio(&mut self, node: Self::Id) {
        self.warn(LayoutWarning::AspectRatioOnBothAxes { node });
    }

    #[cfg(feature = "incremental")]
    fn known_width_grid(&mut self, node: Self::Id) -> Option<crate::prepare_frame::KnownStack> {
        let parent = self.parent(node)?;
        if self.parent(parent).is_some() { return None; }
        let window = self.layout_data().window_size;
        grid_width::preview::<RustFloat, grid_state::RustWidthRounding>(
            self.node_layout_params(node), self.node_layout_params(parent), window,
        )
    }

    #[cfg(feature = "incremental")]
    #[inline]
    fn finish_prepared_axis(&mut self, node: Self::Id, axis: Axis) {
        let params = self.node_layout_params(node);
        if !matches!(params.children_layout, ChildrenLayout::Free) || !matches!(params.size[axis], Size::FitContent) {
            self.solve_slot(node, axis, Kind::Final);
            return;
        }
        let read_opposite = params.intrinsic_reads_other_axis(axis);
        let data = self.node_layout_data(node);
        let index = slot_index(axis, Kind::Regular);
        let (value, rank) = if data.flags.check_state(axis, Kind::Regular) == SOLVED {
            (data.values[index], data.levels[index])
        } else {
            let rank = if read_opposite { data.levels[slot_index(axis.other(), Kind::Final)].saturating_add(1) } else { 0 };
            let slot = sizing_requests::target(node, axis == Y, Kind::Regular);
            let value = sizing_finish::intrinsic_content(&mut SizingFinisher { tree: self, retain_grid_cells: false }, slot, 0.0, 0.0);
            (value, rank)
        };
        if !value.is_finite() { self.warn(LayoutWarning::NotFinite { node, axis }); }
        self.node_layout_data_mut(node).publish_axis(axis, value, value, rank);
    }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn note_flow(&mut self, has_flow: bool) { self.layout_data().has_flow |= has_flow; }

    fn assign_fixed_grid(&mut self, node: Self::Id, columns: u32, axis: Axis, backfill: bool) {
        self.assign_grid_cells(node, columns as usize, columns as f32, axis, backfill);
    }

    #[inline(always)]
    fn prepare_scratch(&mut self) -> &mut Vec<(crate::prepare_frame::PrepareFrame<Self::Id>, Self::Id)> {
        &mut self.layout_data().prepare_stack
    }
}

impl<T: Solve + ?Sized> sizing_pass::Access for T {
    type Margin = BlockMargins;

    #[inline(always)]
    fn root_id(&self) -> Self::Id { self.root() }

    #[inline(always)]
    fn sizing_window(&mut self) -> &mut Xy<f32> { &mut self.layout_data().window_size }

    #[inline(always)]
    fn margins(&mut self) -> &mut Vec<Self::Margin> { &mut self.layout_data().block_margins }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn margin_scratch(&mut self) -> &mut Vec<Self::Margin> { &mut self.layout_data().margin_scratch }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn sizing_flags(&mut self) -> (&mut bool, &mut bool, &mut Option<IncrementalRelayoutOutcome>) {
        let data = self.layout_data();
        (&mut data.has_cycle, &mut data.has_flow, &mut data.pending_full_solve)
    }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn prepared_nodes(&mut self) -> &mut u32 { &mut self.layout_data().n_nodes_solved }

    #[inline(always)]
    fn slot(&mut self, node: Self::Id, axis: Axis, kind: Kind) { self.solve_slot(node, axis, kind); }

    #[inline(always)]
    fn fill_children(&mut self, node: Self::Id) -> bool { self.solve_fill_items(node) }

    #[inline(always)]
    fn parent_id(&self, node: Self::Id) -> Option<Self::Id> { self.parent(node) }

    #[inline(always)]
    fn same_id(&self, left: Self::Id, right: Self::Id) -> bool { left == right }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn ones(word: u32) -> u32 { word.count_ones() }
}

impl<T: Solve + ?Sized> sizing_fill::Access for T {
    #[inline(always)]
    fn declaration(&self, node: Self::Id, axis: Axis, kind: Kind) -> Option<Size> {
        self.read_size(node, axis, kind)
    }

    #[inline(always)]
    fn bounded_share(&mut self, axis: Axis, budget: f32, first: Option<Self::Id>) -> f32 {
        self.distribute_fill(axis, budget, first, None)
    }
}

pub(crate) use fill_compaction::FillChild;
#[cfg(test)]
use fill_compaction::resolve_fill_share;

#[cfg(test)]
#[inline(always)]
fn clamp(size: f32, min: Option<f32>, max: Option<f32>) -> f32 {
    sizing_finish::clamp::<crate::placement_geometry::RustFloat>(size, min, max)
}

#[inline(always)]
fn inner(size: f32, padding: f32) -> f32 {
    sizing_finish::inner::<RustFloat>(size, padding)
}

pub(crate) trait Solve: TreeAdapter {
    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn tree_traversal_next(&self, i: Self::NodeId) -> Option<Self::NodeId> {
        self.traversal_next(self.root(), i, !self.node_layout_params(i).disabled)
    }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn traversal_next(&self, root: Self::NodeId, i: Self::NodeId, descend: bool) -> Option<Self::NodeId> {
        let child = if descend { self.first_child(i) } else { None };
        crate::tree_walk::next_forward(self, root, i, child)
    }

    #[inline(always)]
    fn read_size(&self, i: Self::NodeId, axis: Axis, kind: Kind) -> Option<Size> {
        sizing_requests::read_declaration(self, sizing_requests::target(i, axis == Y, kind))
    }

    #[inline(always)]
    fn any_size_is_fill(&self, i: Self::NodeId, axis: Axis) -> bool {
        sizing_child::any_fill(self, i, axis == Y)
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
    fn size_depends_on_children(&self, i: Self::NodeId) -> bool {
        [X, Y].into_iter().any(|axis| DECLARED_SIZES.into_iter().any(|kind| {
            self.read_size(i, axis, kind).is_some_and(|size| size.dependency_form().reads_children())
        }))
    }

    #[cfg(test)]
    fn prepare<const RETAIN: bool, const REGISTERED_PIXELS: bool>(&mut self, i: Self::NodeId, block_parent: Option<bool>, retained: &mut RetainedSizing) -> (u32, bool) {
        prepare_nodes::prepare::<_, RustVec, RETAIN, REGISTERED_PIXELS>(self, i, block_parent, retained)
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

    #[cfg(test)]
    fn request_dependencies(
        &mut self, slot: Slot<Self::NodeId>, request: &mut impl FnMut(&mut Self, Slot<Self::NodeId>),
    ) {
        let _ = sizing_requests::request_inputs(
            SizingDependencies { tree: self, request },
            sizing_request(slot),
        );
    }

    /// Rebuild an isolated sizing region using its already-solved parent.
    #[cfg(feature = "incremental")]
    fn measure_subtree(&mut self, root: Self::NodeId) -> Option<(u32, u32, usize)> {
        sizing_pass::measure_region::<_, RustVec, false>(self, root)
            .map(|measured| (measured.nodes, measured.slots, measured.blocks))
    }

    /// Resolves fill items together once their parent's geometry is known.
    fn solve_fill_items(&mut self, node: Self::NodeId) -> bool {
        sizing_fill::children(self, node)
    }

    fn solve_slot(&mut self, node: Self::NodeId, axis: Axis, kind: Kind) {
        let slot = sizing_requests::target(node, axis == Y, kind);
        let _ = sizing_stack::drive(NativeSizing { tree: self }, slot);
    }

    #[cold]
    #[inline(never)]
    fn finish_slots_on_worklist(&mut self, opened: OpenSlot<Self::NodeId>, check: bool) {
        let scratch = RustVec::take(&mut self.layout_data().sizing_stack);
        let mut tasks = sizing_stack::task_buffer(scratch);
        sizing_stack::finish_worklist(self, opened, check, &mut tasks);
        self.layout_data().sizing_stack = tasks.recycle();
    }

    /// Computes the value of a slot whose dependencies are solved, and marks it as solved.
    fn finish_slot(&mut self, slot: Slot<Self::NodeId>) -> sizing_finish::StoredSize<Self::NodeId> {
        sizing_finish::finish_size(&mut SizingFinisher { tree: self, retain_grid_cells: false }, sizing_request(slot))
    }

    /// Numeric work reuses the stable in-flow order of the settled grid.
    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn finish_numeric_slot(&mut self, slot: sizing_requests::Request<Self::NodeId>) -> sizing_finish::StoredSize<Self::NodeId> {
        sizing_finish::finish_size(&mut SizingFinisher { tree: self, retain_grid_cells: true }, slot)
    }

    /// Keeps the user's callback out of the hot code.
    #[cold]
    #[inline(never)]
    fn warn(&mut self, warning: LayoutWarning<Self::NodeId>) {
        #[cfg(feature = "incremental")]
        { self.layout_data().sizing_warned = true; }
        self.layout_warning(warning);
    }

    #[inline(always)]
    fn get_solved_value(&self, i: Self::NodeId, axis: Axis, kind: Kind) -> f32 {
        let data = self.node_layout_data(i);
        // In-progress cycle reads see the initialized provisional value.
        cycle_rules::read_slot(&data.values, axis.index(), kind)
    }

    #[inline(always)]
    fn pre_grow_size(&self, child: Self::NodeId, axis: Axis) -> f32 {
        sizing_child::pre_growth::<_, fill_compaction::RustFloat>(self, child, axis == Y, true)
    }

    #[cfg(feature = "incremental")]
    fn solve_even_share(&mut self, node: Self::NodeId, axis: Axis) -> f32 {
        sizing_finish::measure_share(
            &mut SizingFinisher { tree: self, retain_grid_cells: false },
            sizing_requests::target(node, axis == Y, Kind::EvenShare),
        )
    }

    fn wrap_fill_base(&self, child: Self::NodeId, axis: Axis) -> f32 {
        sizing_child::pre_growth::<_, fill_compaction::RustFloat>(self, child, axis == Y, false)
    }

    fn distribute_fill(
        &mut self,
        axis: Axis,
        budget: f32,
        next: Option<Self::NodeId>,
        end: Option<Self::NodeId>,
    ) -> f32 {
        fill_compaction::distribute(&mut FillInputs { tree: self, axis }, next, end, budget)
    }

    /// Assigns the cells of a grid with `MainAxisCellSize::Width` columns, from its `Final` size on the main axis.
    fn assign_width_grid_cells(
        &mut self, i: Self::NodeId, main: Axis, width: f32, spacing: f32, backfill: bool, retain: bool,
    ) {
        let inner_main = inner(self.get_solved_value(i, main, Kind::Final), self.total_padding(i, main));
        let key = grid_state::width_key::<grid_state::RustWidthRounding>(inner_main, width, spacing);
        let retained = if retain {
            Some(self.node_layout_data(i).grid_lines()[main].to_bits())
        } else {
            None
        };
        if !grid_state::reuse_width_cells(retained, key.tracks.to_bits()) {
            self.assign_grid_cells(i, key.columns, key.tracks, main, backfill);
        }
    }

    fn assign_grid_cells(&mut self, i: Self::NodeId, n_main: usize, main_tracks: f32, main_axis: Axis, backfill: bool) {
        let data = self.node_layout_data(i);
        let has_spans = data.flags.0 & NodeFlags::GRID_SPANS != 0;
        let count = data.n_placed_children;
        let n_lines = grid_search::assign_grid(
            &mut GridInput { tree: self, parent: i, main: main_axis }, n_main, count, has_spans, backfill,
        ).as_float();
        let [x, y] = grid_state::physical_pair(main_tracks, n_lines, main_axis == Y);
        self.node_layout_data_mut(i).set_grid_lines(Xy::new(x, y));
    }

    #[inline(always)]
    fn total_padding(&self, i: Self::NodeId, axis: Axis) -> f32 {
        sizing_finish::padding(self.node_layout_params(i), axis)
    }
}

struct NativeSizing<'a, T: Solve + ?Sized> {
    tree: &'a mut T,
}

impl<T: Solve + ?Sized> sizing_stack::NativeModel for NativeSizing<'_, T> {
    type Id = T::NodeId;
    type Opened = OpenSlot<T::NodeId>;
    type View = T;
}

impl<T: Solve + ?Sized> sizing_stack::NativeAccess for NativeSizing<'_, T> {
    #[inline(always)]
    fn view(&self) -> &T { self.tree }

    #[inline(always)]
    fn start(&mut self, slot: sizing_requests::Request<Self::Id>) -> Option<(Self::Opened, bool)> {
        phase::start_slot(self.tree, slot)
    }

    #[inline(always)]
    fn finish(&mut self, opened: Self::Opened, check: bool) -> sizing_finish::StoredSize<Self::Id> {
        phase::resume_slot(self.tree, opened, check)
    }

    #[inline(always)]
    fn spill(&mut self, opened: Self::Opened, check: bool) {
        self.tree.finish_slots_on_worklist(opened, check);
    }
}

impl<T: Solve + ?Sized> sizing_stack::WorkModel for T {
    type Slot = sizing_requests::Request<T::NodeId>;
    type Opened = OpenSlot<T::NodeId>;
    type Storage = sizing_stack::TaskBuffer<Self::Slot, Self::Opened, RustVec>;
}

impl<T: Solve + ?Sized> sizing_stack::SizingWork for T {
    #[inline]
    fn enter(&mut self, slot: Self::Slot) -> Option<bool> {
        phase::enter_slot(self, slot)
    }

    #[inline]
    fn open(&mut self, slot: Self::Slot, check: bool) -> Self::Opened {
        if check { phase::open_slot::<_, true>(self, slot) } else { phase::open_slot::<_, false>(self, slot) }
    }

    #[inline]
    fn finish(&mut self, opened: Self::Opened, check: bool) {
        phase::resume_slot(self, opened, check);
    }

    #[inline]
    fn slot(&self, opened: Self::Opened) -> Self::Slot { opened.slot }

    #[inline]
    fn append_requests(&self, slot: Self::Slot, tasks: &mut Self::Storage) {
        let pending = core::mem::replace(tasks, sizing_stack::task_buffer(Vec::new()));
        *tasks = sizing_stack::append_inputs(self, slot, pending);
    }
}

#[inline(always)]
fn sizing_request<I>(slot: Slot<I>) -> sizing_requests::Request<I> {
    sizing_requests::Request { node: slot.node, vertical: slot.axis == Y, kind: slot.kind }
}

#[inline(always)]
fn solve_slot<I: Copy>(request: sizing_requests::Request<I>) -> Slot<I> {
    Slot { node: request.node, axis: request.axis(), kind: request.kind }
}

impl<T: Solve + ?Sized> phase::PhaseAccess for T {
    type Id = T::NodeId;
    type Float = RustFloat;

    #[inline(always)]
    fn node_record(&self, node: Self::Id) -> &NodeLayoutData {
        self.node_layout_data(node)
    }

    #[inline(always)]
    fn edit_record(&mut self, node: Self::Id) -> &mut NodeLayoutData {
        self.node_layout_data_mut(node)
    }

    #[inline(always)]
    fn initial_values() -> &'static [f32; N_SLOTS] { &EMPTY_VALUES }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn current_level(&mut self) -> &mut u16 { &mut self.layout_data().current_level }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn saw_cycle(&mut self) { self.layout_data().has_cycle = true; }

    #[inline(always)]
    fn warn_cycle(&mut self, node: Self::Id, axis: Axis) {
        self.layout_warning(LayoutWarning::Cycle { node, axis });
    }

    #[inline(always)]
    fn recompute(&mut self, slot: sizing_requests::Request<Self::Id>) -> sizing_finish::StoredSize<Self::Id> {
        self.finish_slot(solve_slot(slot))
    }
}

impl<T: Solve + ?Sized> sizing_requests::DeclarationModel for T {
    type Id = T::NodeId;
}

impl<T: Solve + ?Sized> sizing_requests::Declarations for T {
    #[inline(always)]
    fn params(&self, node: Self::Id) -> &LayoutParams {
        self.node_layout_params(node)
    }

    #[inline(always)]
    fn is_block_item(&self, node: Self::Id) -> bool {
        self.node_layout_data(node).flags.is_block_item()
    }

    #[inline(always)]
    fn block_parent_auto_height(&self, node: Self::Id) -> bool {
        self.node_layout_data(node).flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0
    }
}

impl<T: Solve + ?Sized> sizing_child::ValueModel for T {}

impl<T: Solve + ?Sized> sizing_child::Values for T {
    #[inline(always)]
    fn words(&self, node: Self::Id) -> &[f32; N_SLOTS] {
        &self.node_layout_data(node).values
    }
}

struct SizingFinisher<'a, T: Solve + ?Sized> {
    tree: &'a mut T,
    retain_grid_cells: bool,
}

impl<T: Solve + ?Sized> sizing_finish::FinishModel for SizingFinisher<'_, T> {
    type Id = T::NodeId;
    type Float = crate::placement_geometry::RustFloat;
}

impl<T: Solve + ?Sized> sizing_finish::FinishAccess for SizingFinisher<'_, T> {
    #[inline(always)]
    fn declaration(&self, slot: sizing_requests::Request<Self::Id>) -> Option<Size> {
        self.tree.read_size(slot.node, slot.axis(), slot.kind)
    }

    #[inline(always)]
    fn words(&self, slot: sizing_requests::Request<Self::Id>) -> &[f32; N_SLOTS] {
        &self.tree.node_layout_data(slot.node).values
    }

    #[inline(always)]
    fn stack_parent(&self, slot: sizing_requests::Request<Self::Id>) -> Option<Self::Id> {
        self.tree.stack_parent(slot.node, slot.axis())
    }

    #[inline(always)]
    fn params(&self, node: Self::Id) -> &LayoutParams {
        self.tree.node_layout_params(node)
    }

    #[inline(always)]
    fn flags(&self, node: Self::Id) -> NodeFlags {
        self.tree.node_layout_data(node).flags
    }

    #[inline(always)]
    fn line_words(&self, node: Self::Id) -> &[u32; 2] {
        &self.tree.node_layout_data(node).parent_flow
    }

    #[inline(always)]
    fn parent(&self, node: Self::Id) -> Option<Self::Id> {
        self.tree.parent(node)
    }

    #[inline(always)]
    fn parent_context(
        &self, slot: sizing_requests::Request<Self::Id>, parent: Self::Id,
    ) -> sizing_finish::ParentContext<'_> {
        let child = self.tree.node_layout_params(slot.node);
        let layout = self.tree.node_layout_params(parent).children_layout;
        sizing_finish::ParentContext { child, layout }
    }

    #[inline(always)]
    fn window_extent(&mut self, axis: Axis) -> f32 {
        self.tree.layout_data().window_size[axis]
    }

    #[inline(always)]
    fn placed_child_count(&self, node: Self::Id) -> u32 {
        self.tree.node_layout_data(node).n_placed_children
    }

    #[inline(always)]
    fn margins(params: &LayoutParams, axis: Axis) -> [f32; 2] {
        margins(params, axis)
    }

    #[inline(always)]
    fn warn(&mut self, slot: sizing_requests::Request<Self::Id>, warning: sizing_finish::Warning) {
        let node = slot.node;
        let axis = slot.axis();
        self.tree.warn(match warning {
            sizing_finish::Warning::MinAboveMax => LayoutWarning::MinAboveMax { node, axis },
            sizing_finish::Warning::FitContentCollapsed => LayoutWarning::FitContentCollapsed { node, axis },
            sizing_finish::Warning::NotFinite => LayoutWarning::NotFinite { node, axis },
            sizing_finish::Warning::ImpossibleFracChildren => LayoutWarning::ImpossibleFracChildren { node, axis },
        });
    }
}

impl<T: Solve + ?Sized> sizing_finish::IntrinsicContent for SizingFinisher<'_, T> {
    #[inline(always)]
    fn wrapping_text(&self, slot: sizing_requests::Request<Self::Id>) -> bool {
        self.tree.text_wraps(slot.node, slot.axis())
    }

    #[inline(always)]
    fn content_needs_constraint(&self, slot: sizing_requests::Request<Self::Id>, params: &LayoutParams) -> bool {
        params.content_measure.reads_other_axis(slot.axis())
    }

    #[inline(always)]
    fn track_content(&mut self) {
        #[cfg(feature = "incremental")]
        { self.tree.layout_data().track_topology = true; }
    }

    #[inline(always)]
    fn text_width(&mut self, node: Self::Id) -> f32 {
        self.tree.measure_text_width(node)
    }

    #[inline(always)]
    fn text_height(&mut self, node: Self::Id, width: Option<f32>) -> f32 {
        self.tree.measure_text_height(node, width)
    }

    #[inline(always)]
    fn content_size(&mut self, node: Self::Id, axis: Axis, known_dimensions: Xy<Option<f32>>, max_size: Xy<Option<f32>>) -> f32 {
        self.tree.measure_content(node, ContentMeasureInput { axis, known_dimensions, max_size })[axis]
    }
}

impl<T: Solve + ?Sized> sizing_finish::IntrinsicRows for SizingFinisher<'_, T> {
    #[inline(always)]
    fn intrinsic_layout(&self, slot: sizing_requests::Request<Self::Id>) -> ChildrenLayout {
        self.tree.node_layout_params(slot.node).children_layout
    }

    #[inline(always)]
    fn first_child(&self, parent: Self::Id) -> Option<Self::Id> {
        self.tree.first_child(parent)
    }

    #[inline(always)]
    fn child(&self, _parent: Self::Id, child: Self::Id) -> (Option<Self::Id>, bool) {
        let following = self.tree.next_sibling(child);
        let params = self.tree.node_layout_params(child);
        (following, !params.disabled && !params.free_placement)
    }
}

impl<T: Solve + ?Sized> sizing_finish::block::Model<T::NodeId> for SizingFinisher<'_, T> {
    type Block = f32;
    type BlockMemory = RustVec;
}

impl<T: Solve + ?Sized> sizing_finish::FlowShareModel for SizingFinisher<'_, T> {
    type ShareFloat = fill_compaction::RustFloat;
    type MetricFloat = RustFloat;
    type ShareMemory = RustVec;
    type ShareSpill = fill_compaction::VecSpill;
}

impl<T: Solve + ?Sized> sizing_finish::FlowAccess for SizingFinisher<'_, T> {

    #[inline(always)]
    fn flow_layout(&self, parent: Self::Id) -> ChildrenLayout {
        self.tree.node_layout_params(parent).children_layout
    }

    type MarkedScan<'a> = crate::flow::SolverLine<'a, T, true> where Self: 'a;
    type FreshScan<'a> = crate::flow::SolverLine<'a, T, false> where Self: 'a;

    #[inline(always)]
    fn marked_scan<'a>(
        &'a self, _slot: sizing_requests::Request<Self::Id>, axis: Axis, _first: Option<Self::Id>, _available: Option<f32>, spacing: f32,
    ) -> Self::MarkedScan<'a> {
        crate::flow::SolverLine::new(self.tree, axis, spacing)
    }

    #[inline(always)]
    fn fresh_scan<'a>(
        &'a self, _slot: sizing_requests::Request<Self::Id>, axis: Axis, _first: Option<Self::Id>, _available: Option<f32>, spacing: f32,
    ) -> Self::FreshScan<'a> {
        crate::flow::SolverLine::new(self.tree, axis, spacing)
    }

    #[inline(always)]
    fn mark_line(&mut self, next: Self::Id) {
        self.tree.node_layout_data_mut(next).mark_wrap_start();
    }

    type LineRecords<'a> = crate::flow::WrapRecords<'a, T> where Self: 'a;

    #[inline(always)]
    fn stamp_source<'a>(&'a mut self, _slot: sizing_requests::Request<Self::Id>, _first: Option<Self::Id>, _stop: Option<Self::Id>,
        _metric: wrap_metrics::Metric, _value: f32,
    ) -> Self::LineRecords<'a> {
        crate::flow::WrapRecords { tree: self.tree }
    }

    #[inline(always)]
    fn first_fill(&self, parent: Self::Id, _axis: Axis) -> Option<Self::Id> {
        self.tree.first_child(parent)
    }

    #[inline(always)]
    fn fill_row(&self, child: Self::Id, axis: Axis, stop: Option<Self::Id>)
        -> Option<(Option<Self::Id>, Option<fill_compaction::ChildTerms<fill_compaction::FillNumber<Self::ShareFloat>>>)> {
        read_fill_row(self.tree, axis, child, stop)
    }

    #[inline(always)]
    fn take_fill_spill(&mut self) -> Vec<FillChild> {
        RustVec::take(&mut self.tree.layout_data().fills_scratch)
    }

    #[inline(always)]
    fn return_fill_spill(&mut self, spill: Vec<FillChild>) {
        self.tree.layout_data().fills_scratch = spill;
    }

    #[inline(always)]
    fn block_record(&self, node: Self::Id) -> &NodeLayoutData { self.tree.node_layout_data(node) }

    #[inline(always)]
    fn edit_block_record(&mut self, node: Self::Id) -> &mut NodeLayoutData { self.tree.node_layout_data_mut(node) }

    #[inline(always)]
    fn block_margins(&mut self) -> &mut Vec<BlockMargins> { &mut self.tree.layout_data().block_margins }

    #[inline(always)]
    fn lift_block(value: f32) -> f32 { value }

    #[inline(always)]
    fn lower_block(value: f32) -> f32 { value }
}

impl<T: Solve + ?Sized> sizing_finish::FinishPublication for SizingFinisher<'_, T> {
    #[inline(always)]
    fn finite(value: f32) -> bool { value.is_finite() }

    #[inline(always)]
    fn publish(&mut self, slot: sizing_requests::Request<Self::Id>, value: f32) -> sizing_finish::StoredSize<Self::Id> {
        sizing_finish::store_size(self.tree.node_layout_data_mut(slot.node), slot, value)
    }

    #[inline(always)]
    fn assign_width_grid(
        &mut self, slot: sizing_requests::Request<Self::Id>, width: f32, spacing: f32, backfill: bool,
    ) {
        self.tree.assign_width_grid_cells(slot.node, slot.axis(), width, spacing, backfill, self.retain_grid_cells);
    }
}

#[cfg(test)]
struct SizingDependencies<'a, T: Solve + ?Sized, F> {
    tree: &'a mut T,
    request: &'a mut F,
}

#[cfg(test)]
impl<T: Solve + ?Sized, F> sizing_requests::RequestModel for SizingDependencies<'_, T, F> {
    type Id = T::NodeId;
    type Source = T;
}

#[cfg(test)]
impl<T: Solve + ?Sized, F: FnMut(&mut T, Slot<T::NodeId>)> sizing_requests::RequestAccess for SizingDependencies<'_, T, F> {
    #[inline(always)]
    fn source(&self) -> &T { self.tree }

    #[inline(always)]
    fn emit(&mut self, slot: sizing_requests::Request<Self::Id>) {
        (self.request)(self.tree, Slot { node: slot.node, axis: slot.axis(), kind: slot.kind });
    }
}

impl<T: Solve + ?Sized> sizing_requests::RequestView for T {
    type Id = T::NodeId;
}

impl<T: Solve + ?Sized> sizing_requests::RequestSource for T {
    #[inline(always)]
    fn form(&self, slot: sizing_requests::Request<Self::Id>) -> Option<Form> {
        self.read_size(slot.node, slot.axis(), slot.kind).map(Size::dependency_form)
    }

    #[inline(always)]
    fn final_declarations(&self, slot: sizing_requests::Request<Self::Id>) -> (bool, bool, bool) {
        sizing_requests::final_presence(self, slot)
    }

    #[inline(always)]
    fn stack_parent(&self, slot: sizing_requests::Request<Self::Id>) -> Option<Self::Id> {
        Solve::stack_parent(self, slot.node, slot.axis())
    }

    #[inline(always)]
    fn parent(&self, node: Self::Id) -> Option<Self::Id> {
        TreeAdapter::parent(self, node)
    }

    #[inline(always)]
    fn parent_uses_flow(&self, slot: sizing_requests::Request<Self::Id>, parent: Self::Id) -> bool {
        !self.node_layout_params(slot.node).free_placement
            && matches!(self.node_layout_params(parent).children_layout,
                ChildrenLayout::Wrap { axis, .. } if axis != slot.axis())
    }

    #[inline(always)]
    fn parent_uses_other_axis(&self, slot: sizing_requests::Request<Self::Id>, parent: Self::Id) -> bool {
        dependency_rules::reads_parent_axis(false, !self.node_layout_params(slot.node).free_placement,
            self.width_grid_main_axis(parent) == Some(slot.axis().other()))
    }

    #[inline(always)]
    fn intrinsic_uses_flow(&self, slot: sizing_requests::Request<Self::Id>) -> bool {
        match self.node_layout_params(slot.node).children_layout {
            ChildrenLayout::Block => slot.vertical,
            ChildrenLayout::Wrap { axis, .. } => axis != slot.axis(),
            _ => false,
        }
    }

    #[inline(always)]
    fn intrinsic_uses_other_axis(&self, slot: sizing_requests::Request<Self::Id>) -> bool {
        dependency_rules::reads_intrinsic_constraint(
            self.node_layout_params(slot.node).intrinsic_reads_other_axis(slot.axis()),
            self.width_grid_main_axis(slot.node) == Some(slot.axis().other()),
        )
    }

    #[inline(always)]
    fn first_child(&self, parent: Self::Id) -> Option<Self::Id> {
        TreeAdapter::first_child(self, parent)
    }

    #[inline(always)]
    fn child(&self, _: Self::Id, child: Self::Id) -> (Option<Self::Id>, bool) {
        let next = self.next_sibling(child);
        let params = self.node_layout_params(child);
        (next, !params.disabled && !params.free_placement)
    }

    #[inline(always)]
    fn flow_mode(&self, parent: Self::Id) -> sizing_requests::FlowMode {
        match self.node_layout_params(parent).children_layout {
            ChildrenLayout::Wrap { axis, .. } => sizing_requests::FlowMode::Wrap(axis == Y),
            ChildrenLayout::Block => sizing_requests::FlowMode::Block,
            _ => sizing_requests::FlowMode::Other,
        }
    }

    #[inline(always)]
    fn block_child(&self, _: Self::Id, child: Self::Id) -> (Option<Self::Id>, bool, bool) {
        let params = self.node_layout_params(child);
        let in_flow = !params.disabled && !params.free_placement;
        (self.next_sibling(child), in_flow, in_flow
            && self.node_layout_data(child).flags.0 & NodeFlags::BLOCK_CONTAINER != 0)
    }

    #[inline(always)]
    fn wrap_child(&self, _: Self::Id, _: bool, child: Self::Id) -> (Option<Self::Id>, bool) {
        let params = self.node_layout_params(child);
        (self.next_sibling(child), !params.disabled && !params.free_placement)
    }
}

impl<T: TreeAdapter + ?Sized> Solve for T {}

#[inline]
fn read_fill_row<T: Solve + ?Sized>(tree: &T, axis: Axis, child: T::NodeId, end: Option<T::NodeId>)
    -> Option<(Option<T::NodeId>, Option<fill_compaction::ChildTerms<fill_compaction::FillNumber<fill_compaction::RustFloat>>>)> {
    use fill_compaction::{ChildTerms, FillNumber};
    if Some(child) == end {
        return None;
    }
    let next = tree.next_sibling(child);
    let node = tree.node_layout_params(child);
    if node.free_placement || node.disabled {
        return Some((next, None));
    }
    let margins = margins(node, axis).map(FillNumber::new);
    let terms = sizing_child::fill_terms::<_, fill_compaction::RustFloat>(tree, child, axis == Y, node.fill_weight);
    Some((next, Some(ChildTerms { margins, terms })))
}

struct FillInputs<'a, T: Solve + ?Sized> {
    tree: &'a mut T,
    axis: Axis,
}

impl<T: Solve + ?Sized> fill_compaction::ChildrenModel for FillInputs<'_, T> {
    type Child = T::NodeId;
    type Number = fill_compaction::FillNumber<fill_compaction::RustFloat>;
}

impl<T: Solve + ?Sized> fill_compaction::Children for FillInputs<'_, T> {
    #[inline]
    fn read(&self, child: Self::Child, end: Option<Self::Child>) -> Option<(Option<Self::Child>, Option<fill_compaction::ChildTerms<Self::Number>>)> {
        read_fill_row(self.tree, self.axis, child, end)
    }

    #[inline]
    fn take_spill(&mut self) -> Vec<FillChild> {
        RustVec::take(&mut self.tree.layout_data().fills_scratch)
    }

    #[inline]
    fn return_spill(&mut self, spill: Vec<FillChild>) {
        self.tree.layout_data().fills_scratch = spill;
    }
}

struct GridInput<'a, T: Solve + ?Sized> {
    tree: &'a mut T,
    parent: T::NodeId,
    main: Axis,
}

impl<T: Solve + ?Sized> grid_sparse::InputModel for GridInput<'_, T> {
    type Id = T::NodeId;
}

impl<T: Solve + ?Sized> grid_sparse::Inputs for GridInput<'_, T> {
    #[inline]
    fn inspect(&self, child: Self::Id) -> (Option<Self::Id>, Option<(u16, u16)>) {
        let next = self.tree.next_sibling(child);
        let item = self.tree.node_layout_params(child);
        (next, grid_state::assignment_item(item.disabled, item.free_placement, item.grid_span.x, item.grid_span.y, self.main == Y))
    }

    #[inline]
    fn publish(&mut self, child: Self::Id, (line, position): (u128, usize)) {
        self.tree.node_layout_data_mut(child).set_grid_cell::<RustFloat>(self.main, position as f32, line as f32);
    }
}

impl<T: Solve + ?Sized> grid_search::GridBuffers for GridInput<'_, T> {
    #[inline]
    fn first_child(&self) -> Option<Self::Id> {
        self.tree.first_child(self.parent)
    }

    #[inline]
    fn take_bitmap(&mut self) -> Vec<u64> {
        RustVec::take(&mut self.tree.layout_data().occupied_scratch)
    }

    #[inline]
    fn return_bitmap(&mut self, words: Vec<u64>) {
        self.tree.layout_data().occupied_scratch = words;
    }
}

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
                    let entry = cycle_rules::enter(tree.nodes[node].flags.check_state(axis, Kind::Final));
                    tree.solve_slot(node, axis, Kind::Final);
                    let _ = sizing_stack::drive_spill(NativeSizing { tree: &mut spill }, sizing_request(slot));
                    if matches!(entry, Entry::Compute | Entry::CheckIntrinsic) {
                        for tree in [&mut tree, &mut spill] {
                            tree.request_dependencies(slot, &mut |tree, dependency| {
                                assert_eq!(tree.nodes[dependency.node].flags.check_state(dependency.axis, dependency.kind), SOLVED);
                            });
                        }
                    }
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
        leaf.set_grid_cell::<RustFloat>(X, 3.0, 1.0);
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
    fn spilled_fill_constraints_preserve_child_order_and_share() {
        let mut tree: LayoutTree = LayoutTree::new();
        let root = tree.root();
        tree.update_node_params(&root, LayoutParams {
            children_layout: ChildrenLayout::Stack { arrange: Arrange::Start, axis: X, spacing: 0.0 },
            ..LayoutParams::DEFAULT
        }).unwrap();
        let mut children = Vec::new();
        for i in 0..12 {
            let minimum = if i == 0 { 16.0 } else { 1.0 };
            children.push(tree.add_node(&root, LayoutParams {
                min_size: Xy::new(Some(Size::Pixels(minimum)), None),
                ..LayoutParams::DEFAULT
            }).unwrap());
        }
        children.push(tree.add_node(&root, LayoutParams::DEFAULT).unwrap());

        tree.solve_layout(Xy::new(112.0, 40.0));
        let mut left = 0.0;
        for (i, child) in children.iter().enumerate() {
            let right = left + if i == 0 { 16.0 } else { 8.0 };
            assert_eq!(tree.layout(child).unwrap().x, [left, right]);
            left = right;
        }
        assert!(tree.layout_data.fills_scratch.is_empty());
        assert!(tree.layout_data.fills_scratch.capacity() >= 12);
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
            let words_per_line = grid_state::row_stride(columns);
            for backfill in [false, true] {
                let mut packed = Vec::new();
                let mut sparse = Vec::new();
                let mut sparse_cursor = grid_sparse::new_cursor();
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
                        sparse_cursor.place(&mut sparse, columns, height as u16, width, backfill),
                        (line as u128, pos),
                        "columns={columns} backfill={backfill} cursor={cursor:?} span={width}x{height}",
                    );
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
