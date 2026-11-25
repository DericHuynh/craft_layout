//! Native preparation operations over individual initialized layout records.
#![allow(unexpected_cfgs)]

#[path = "prepare_fill_stack.rs"]
mod fill_stack;
#[path = "prepare_ratio_stack.rs"]
mod ratio_stack;
#[path = "wrap_ready.rs"]
mod wrap_ready;

use crate::declarations::{Axis, ChildrenLayout, LayoutParams, MainAxisCellSize, Size, Xy};
use crate::node_data::NodeLayoutData;
use crate::node_flags::{NodeFlags, slot_index};
use crate::prepare_frame::{self, FrameFloat, KnownAxis, KnownStack, PrepareFrame};
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::placement_geometry::Arrange;
#[cfg(verus_keep_ghost)]
use crate::placement::geometry::Arrange;
use crate::prepare_walk::{self, ChildStep, State};
use crate::vec_memory::VecMemory;
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::{packed_stack_leaf::{PackedStackLeaves, PreparedStackLeaf, StackLeafGroup}, vec_memory::{FallibleVecMemory, try_append}};
use crate::work_stack;
use core::marker::PhantomData;
#[cfg(verus_keep_ghost)]
use crate::prepare_frame::{FrameWords, Order, frame_live, remaining};
#[cfg(verus_keep_ghost)]
use crate::placement::{node::PlacementLinks, modes::{leaf_path, leaf_path_push, packed_ids, packed_ids_push}};
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::{Pos, declarations::{X, Y}};
#[cfg(not(verus_keep_ghost))]
use crate::solve::{block_schedule, cycle_rules, sizing_fill::{self, BoundRecords}, sizing_finish};
#[cfg(not(verus_keep_ghost))]
use crate::fill_budget;
#[cfg(verus_keep_ghost)]
use crate::{dependencies::sizing_finish, fill::budget as fill_budget, sizing_pass};
#[cfg(not(verus_keep_ghost))]
use crate::placement_geometry::FloatBounds;
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::{StructuralChange, fixed_leaf_cache, flow::wrap_metrics};
#[cfg(verus_keep_ghost)]
use crate::{block_schedule::kernel as block_schedule, cycles::kernel as cycle_rules, sizing_fill::{self, BoundRecords},
    fixed_leaf_cache::runtime as fixed_leaf_cache, placement::geometry::FloatBounds, structural::kernel::StructuralChange,
    wrap_metrics::kernel as wrap_metrics};
#[cfg(verus_keep_ghost)]
use crate::prepare_leaf::{no_bounds, intrinsic_fill_axis, intrinsic_fill_admitted, reset_keeps_intrinsic};
use cycle_rules::Kind;

#[path = "prepare_pair.rs"]
mod prepare_pair;
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::retained_branch as cached_branch;
#[cfg(verus_keep_ghost)]
use crate::retained_branch::kernel as cached_branch;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Default)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct RetainedSizing {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) slots: u32,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) blocks: usize,
    // Ordinary leaves solve their declared bounds in addition to Regular and Final.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) leaf_bounds: u32,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) inspect_descendants: bool,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) leaf_only: bool,
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
impl RetainedSizing {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.can_retain_leaf(mark), no_unwind))]
    pub(crate) fn can_retain_leaf(&self, mark: StructuralChange) -> bool {
        !self.leaf_only || matches!(mark, StructuralChange::Clean)
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Summary {
    pub(crate) nodes: u32,
    pub(crate) needs_solve: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn empty_retained() -> RetainedSizing {
    RetainedSizing {
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        slots: 0,
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        blocks: 0,
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        leaf_bounds: 0,
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        inspect_descendants: false,
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        leaf_only: false,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait RecordModel {
    type Id: Copy;
    type Float: FrameFloat;

    spec fn order(&self) -> Order<Self::Id>;
    spec fn layout_params(&self, node: Self::Id) -> LayoutParams;
    spec fn layout_record(&self, node: Self::Id) -> NodeLayoutData;
    spec fn packed_state(&self) -> PackedStackLeaves<Self::Id>;
    spec fn root_calls(&self) -> Seq<(Self::Id, Axis, Kind)>;
}

pub(crate) open spec fn live<T: RecordModel + ?Sized>(tree: &T, node: T::Id) -> bool {
    (tree.order().live)(node)
}

fn save_order<T: RecordModel + ?Sized>(tree: &T) -> (order: Ghost<Order<T::Id>>)
    ensures order@ == tree.order(),
    no_unwind
{ Ghost(tree.order()) }

pub(crate) open spec fn fit_leaf_span<T: Records + ?Sized>(
    tree: &T, first: Option<T::Id>, next: Option<T::Id>, start: u32,
) -> bool {
    let rows = tree.packed_state().rows@;
    start <= rows.len()
        && leaf_path(PlacementLinks::from_order(tree.order()), |_: T::Id| false, first,
            packed_ids(rows, start as int, rows.len() as int), next)
}

fn save_packed_rows<T: Records + ?Sized>(tree: &T) -> (out: Ghost<Seq<PreparedStackLeaf<T::Id>>>)
    ensures out@ == tree.packed_state().rows@,
    no_unwind
{ Ghost(tree.packed_state().rows@) }

proof fn append_fit_leaf<I>(order: Order<I>, first: Option<I>, prior: Seq<PreparedStackLeaf<I>>, start: int,
    row: PreparedStackLeaf<I>, after: Seq<PreparedStackLeaf<I>>, next: Option<I>,
)
    requires
        0 <= start <= prior.len(), after == prior.push(row),
        leaf_path(PlacementLinks::from_order(order), |_: I| false, first,
            packed_ids(prior, start, prior.len() as int), Some(row.id)),
        (order.first)(row.id).is_none(), next == (order.sibling)(row.id),
    ensures leaf_path(PlacementLinks::from_order(order), |_: I| false, first,
        packed_ids(after, start, after.len() as int), next),
{
    let links = PlacementLinks::from_order(order);
    let old = packed_ids(prior, start, prior.len() as int);
    assert(old =~= packed_ids(after, start, prior.len() as int));
    packed_ids_push(after, start, prior.len() as int);
    leaf_path_push(links, |_: I| false, first, old, row.id);
}

}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait RecordModel {
    type Id: Copy;
    type Float: FrameFloat;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Records: RecordModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(params =>
        requires live(self, node), ensures *params == self.layout_params(node), no_unwind
    ))]
    fn params(&self, node: Self::Id) -> &LayoutParams;

    #[cfg_attr(verus_keep_ghost, verus_spec(data =>
        requires live(self, node), ensures *data == self.layout_record(node), no_unwind
    ))]
    fn record(&self, node: Self::Id) -> &NodeLayoutData;

    #[cfg_attr(verus_keep_ghost, verus_spec(data =>
        requires live(old(self), node),
        ensures final(self).order() == old(self).order(),
            forall |id: Self::Id| #[trigger] final(self).layout_params(id) == old(self).layout_params(id),
            final(self).packed_state() == old(self).packed_state(),
            final(self).root_calls() == old(self).root_calls(),
            *data == old(self).layout_record(node), final(self).layout_record(node) == *final(data),
            forall |other: Self::Id| other != node ==>
                #[trigger] final(self).layout_record(other) == old(self).layout_record(other),
        no_unwind
    ))]
    fn edit(&mut self, node: Self::Id) -> &mut NodeLayoutData;

    #[cfg_attr(verus_keep_ghost, verus_spec(child =>
        requires live(self, node),
        ensures child == (self.order().first)(node),
        no_unwind
    ))]
    fn first(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(sibling =>
        requires live(self, node),
        ensures sibling == (self.order().sibling)(node), sibling.is_some() ==> live(self, sibling.unwrap()),
        no_unwind
    ))]
    fn sibling(&self, node: Self::Id) -> Option<Self::Id>;

    // Construct the statically initialized words used by NodeLayoutData::new.
    #[cfg_attr(verus_keep_ghost, verus_spec(data =>
        ensures data.placement == crate::placement::kernel::PlacementWork::Clean, data.prepared_placement == 0,
        no_unwind
    ))]
    fn empty_record() -> NodeLayoutData;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait StartActions: BoundRecords {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    type LeafMemory: FallibleVecMemory + VecMemory;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(packed =>
        ensures final(self).order() == old(self).order(), *packed == old(self).packed_state(),
            final(self).packed_state() == *final(packed),
            forall |id: Self::Id| #[trigger] final(self).layout_params(id) == old(self).layout_params(id),
            forall|id: Self::Id| #[trigger] final(self).layout_record(id) == old(self).layout_record(id),
        no_unwind
    ))]
    fn packed_stack_leaves(&mut self) -> &mut PackedStackLeaves<Self::Id>;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), final(self).packed_state() == old(self).packed_state(),
            forall |id: Self::Id| #[trigger] final(self).layout_params(id) == old(self).layout_params(id),
        no_unwind
    ))]
    fn stack_leaf_hint(&mut self) -> Option<u32>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node),
        ensures final(self).order() == old(self).order(),
        no_unwind
    ))]
    fn warn_both_axes_ratio(&mut self, node: Self::Id);

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node),
        ensures final(self).order() == old(self).order(),
        no_unwind
    ))]
    // Exact main-axis track from the current declarations and window.
    // The width-grid Final still publishes its cell assignment in the normal pass.
    fn known_width_grid(&mut self, node: Self::Id) -> Option<KnownStack>;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node),
        ensures final(self).order() == old(self).order(),
        no_unwind
    ))]
    fn finish_prepared_axis(&mut self, node: Self::Id, axis: Axis);

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(),
        no_unwind
    ))]
    fn note_flow(&mut self, has_flow: bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node), columns != 0,
        ensures final(self).order() == old(self).order(),
        no_unwind
    ))]
    fn assign_fixed_grid(&mut self, node: Self::Id, columns: u32, axis: Axis, backfill: bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(),
        no_unwind
    ))]
    fn prepare_scratch(&mut self) -> &mut Vec<(PrepareFrame<Self::Id>, Self::Id)>;
}

#[cfg(not(verus_keep_ghost))]
impl<T: crate::TreeAdapter + ?Sized> RecordModel for T {
    type Id = T::NodeId;
    type Float = crate::placement_geometry::RustFloat;
}

#[cfg(not(verus_keep_ghost))]
impl<T: crate::TreeAdapter + ?Sized> Records for T {
    #[inline(always)]
    fn params(&self, node: Self::Id) -> &LayoutParams { self.node_layout_params(node) }

    #[inline(always)]
    fn record(&self, node: Self::Id) -> &NodeLayoutData { self.node_layout_data(node) }

    #[inline(always)]
    fn edit(&mut self, node: Self::Id) -> &mut NodeLayoutData { self.node_layout_data_mut(node) }

    #[inline(always)]
    fn first(&self, node: Self::Id) -> Option<Self::Id> { self.first_child(node) }

    #[inline(always)]
    fn sibling(&self, node: Self::Id) -> Option<Self::Id> { self.next_sibling(node) }

    #[inline(always)]
    fn empty_record() -> NodeLayoutData { NodeLayoutData::new() }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(ready =>
    ensures ready == (prepare_frame::pixel_final::<F>(*params, X, block_item, width_grid_axis)
                       && prepare_frame::pixel_final::<F>(*params, Y, block_item, width_grid_axis)),
        ready ==> ({
            let x = F::word(prepare_frame::pixel_decl(*params, X).unwrap());
            let y = F::word(prepare_frame::pixel_decl(*params, Y).unwrap());
            &&& prepare_frame::pixel_slots::<F>(final(data).values, X) == (x, x)
            &&& prepare_frame::pixel_slots::<F>(final(data).values, Y) == (y, y)
            &&& final(data).flags.0 == (old(data).flags.0 & !0xffu32) | 0xaau32
            &&& final(data).levels@[0] == old(data).levels@[0] && final(data).levels@[1] == old(data).levels@[1]
            &&& final(data).levels@[2] == 1 && final(data).levels@[3] == 1
        }),
        *final(data) == (NodeLayoutData { flags: final(data).flags, values: final(data).values,
            levels: final(data).levels, ..*old(data) }),
    no_unwind
))]
pub(crate) fn seed_pixels<F: FrameFloat>(data: &mut NodeLayoutData, params: &LayoutParams, block_item: bool, width_grid_axis: Option<Axis>) -> bool {
    prepare_frame::seed_pixels::<F>(params, block_item, width_grid_axis, &mut data.flags.0, &mut data.values,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] &mut data.levels)
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(summary =>
    ensures summary.describes(params.free_placement, params.grid_span.x > 1 || params.grid_span.y > 1,
        params.position.x is Start && params.position.y is Start
        && params.margin.x[0].is_zero() && params.margin.x[1].is_zero()
        && params.margin.y[0].is_zero() && params.margin.y[1].is_zero()),
    no_unwind
))]
pub(crate) fn fixed_leaf_summary(params: &LayoutParams) -> fixed_leaf_cache::Summary {
    if params.free_placement {
        fixed_leaf_cache::record(true, false, false)
    } else {
        let spans = params.grid_span.x > 1 || params.grid_span.y > 1;
        let [left, right] = params.margin.x;
        let [top, bottom] = params.margin.y;
        let simple_start = matches!(params.position.x, Pos::Start) && matches!(params.position.y, Pos::Start)
            && left.is_zero() && right.is_zero() && top.is_zero() && bottom.is_zero();
        fixed_leaf_cache::record(false, spans, simple_start)
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(same =>
    ensures same == (prepare_frame::pixel_slots::<F>(left.values, X) == prepare_frame::pixel_slots::<F>(right.values, X)
                  && prepare_frame::pixel_slots::<F>(left.values, Y) == prepare_frame::pixel_slots::<F>(right.values, Y)),
    no_unwind
))]
fn identical_fixed_pixels<F: FrameFloat>(left: &NodeLayoutData, right: &NodeLayoutData) -> bool {
    let regular_x = slot_index(crate::declarations::X, Kind::Regular);
    let regular_y = slot_index(crate::declarations::Y, Kind::Regular);
    let final_x = slot_index(crate::declarations::X, Kind::Final);
    let final_y = slot_index(crate::declarations::Y, Kind::Final);
    F::bits(left.values[regular_x]) == F::bits(right.values[regular_x])
        && F::bits(left.values[regular_y]) == F::bits(right.values[regular_y])
        && F::bits(left.values[final_x]) == F::bits(right.values[final_x])
        && F::bits(left.values[final_y]) == F::bits(right.values[final_y])
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(record).flags.0 == prepared.flags.0 | NodeFlags::FIXED_LEAF,
        prepare_frame::pixel_slots::<F>(final(record).values, X) == prepare_frame::pixel_slots::<F>(prepared.values, X),
        prepare_frame::pixel_slots::<F>(final(record).values, Y) == prepare_frame::pixel_slots::<F>(prepared.values, Y),
        final(record).fixed_leaf_summary == prepared.fixed_leaf_summary,
        old(record).placement is Clean && prepared.placement is Clean ==> final(record).placement is Clean,
        prepared.structural_change is Clean ==> final(record).structural_change is Clean,
        prepared.parent_flow@[0] == 0 && prepared.parent_flow@[1] == 0 ==>
            final(record).parent_flow@[0] == 0 && final(record).parent_flow@[1] == 0,
        old(record).levels == prepared.levels ==> final(record).levels == prepared.levels,
    no_unwind
))]
pub(crate) fn install_fixed<F: FrameFloat>(record: &mut NodeLayoutData, mut prepared: NodeLayoutData) {
    prepared.flags.0 |= NodeFlags::FIXED_LEAF;
    // Compare exact words, including the sign of zero. Other modes can have written parent_flow.
    let [first, second] = record.parent_flow;
    if record.flags.0 == prepared.flags.0 && first == 0 && second == 0 && identical_fixed_pixels::<F>(record, &prepared) {
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        {
            if record.fixed_leaf_summary.0 != prepared.fixed_leaf_summary.0 {
                record.fixed_leaf_summary = prepared.fixed_leaf_summary;
            }
            if !matches!(record.structural_change, StructuralChange::Clean) {
                record.structural_change = StructuralChange::Clean;
            }
        }
    } else {
        *record = prepared;
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(reused =>
    ensures reused == fixed_leaf_cache::matches_fixed_pixels(old(record).flags.0,
            fixed_leaf_cache::registered_flags(NodeFlags::FIXED_LEAF, cycle_rules::SOLVED), old(record).parent_flow),
        *final(record) == (NodeLayoutData {
            structural_change: if reused { StructuralChange::Clean } else { old(record).structural_change },
            ..*old(record)
        }),
    no_unwind
))]
pub(crate) fn reuse_registered_pixels(record: &mut NodeLayoutData) -> bool {
    let flags = fixed_leaf_cache::registered_flags(NodeFlags::FIXED_LEAF, cycle_rules::SOLVED);
    fixed_leaf_cache::reuse_registered(record.flags.0, flags, &record.parent_flow, &mut record.structural_change)
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out <= 2, (out == 0) == no_bounds(*params, axis),
    no_unwind
))]
fn count_bounds(params: &LayoutParams, axis: Axis) -> u32 {
    let min = if params.min_size.component(axis).is_some() { 1 } else { 0 };
    let max = if params.max_size.component(axis).is_some() { 1 } else { 0 };
    min + max
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn independent_pixel<F: FrameFloat>(params: &LayoutParams, axis: Axis) -> bool {
    matches!(*params.size.component(axis), Size::Pixels(value) if F::finite(value))
        && count_bounds(params, axis) == 0
}


#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(tree, parent), tree.order().ordered(),
        first.is_some() ==> tree.order().child(parent, first.unwrap()),
    no_unwind
))]
fn plain_fill_share<T: Records + ?Sized>(
    tree: &T, parent: T::Id, first: Option<T::Id>, axis: Axis, inner: f32, spacing: f32,
) -> Option<f32> {
    let _ = parent;
    let mut next = first;
    let mut count = 0u32;
    let mut weight = 0.0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant live(tree, parent), tree.order().ordered(),
            next.is_some() ==> tree.order().child(parent, next.unwrap()),
        decreases sizing_pass::remaining(tree.order(), parent, next),
    ))]
    while let Some(child) = next {
        #[cfg(verus_keep_ghost)]
        proof! { tree.order().node_facts(child); }
        next = tree.sibling(child);
        let params = tree.params(child);
        if params.disabled { continue; }
        let [start, end] = *params.margin.component(axis);
        if params.free_placement || !matches!(*params.size.component(axis), Size::Fill)
            || params.min_size.component(axis).is_some() || params.max_size.component(axis).is_some()
            || !start.is_zero() || !end.is_zero() || !(params.fill_weight > 0.0)
        {
            return None;
        }
        count = cycle_rules::add_count(count, 1);
        weight += params.fill_weight;
    }
    let gaps = spacing * T::Float::max(count as f32 - 1.0, 0.0);
    let share = fill_budget::share(fill_budget::after_gaps(inner, gaps), 0.0, weight);
    if count > 0 && T::Float::finite(weight) && T::Float::finite(share) { Some(share) } else { None }
}


/// An old child count is only a shape hint. The ordinary preparation walk
/// rewrites any provisional records if a current child or count disagrees.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires frame_live(frame, old(tree).order()),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn prepare_fill_leaf_line<T: StartActions + ?Sized>(
    tree: &mut T, frame: PrepareFrame<T::Id>, own: KnownAxis, inner: f32, retained: &mut RetainedSizing,
) -> Option<Summary> {
    match own.axis {
        Axis::X => prepare_fill_leaf_line_axis::<T, false>(tree, frame, own, inner, retained),
        Axis::Y => prepare_fill_leaf_line_axis::<T, true>(tree, frame, own, inner, retained),
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(span =>
    requires live(old(tree), parent),
    ensures final(tree).order() == old(tree).order(),
        span.is_some() ==> span.unwrap().0 <= span.unwrap().1,
        final(tree).packed_state().rows@ == old(tree).packed_state().rows@,
        span.is_some() ==> span.unwrap().0 == old(tree).packed_state().rows.len()
            && span.unwrap().1 == span.unwrap().0 + count,
    no_unwind
))]
fn reserve_leaf_rows<T: StartActions + ?Sized>(tree: &mut T, parent: T::Id, count: u32) -> Option<(u32, u32)> {
    if count == 0 || count > 16_777_216 { return None; }
    let params = tree.params(parent);
    if params.children_origin_flipped.x || params.children_origin_flipped.y
        || !matches!(params.children_layout, ChildrenLayout::Stack { arrange: Arrange::Start, .. })
    {
        return None;
    }
    let hint = tree.stack_leaf_hint()? as usize;
    let workspace = tree.packed_stack_leaves();
    let rows = &mut workspace.rows;
    let len = rows.len();
    if len > u32::MAX as usize { return None; }
    let start = len as u32;
    let required = count as usize;
    if required == 0 || required as u32 != count { return None; }
    let end = start.checked_add(count)?;
    let target = if len == 0 && hint > required { hint } else { required };
    if !T::LeafMemory::try_reserve(rows, target)
        && !(target > required && T::LeafMemory::try_reserve(rows, required))
    {
        return None;
    }
    let estimated_groups = hint / required;
    if workspace.groups.len() == 0
        && !T::LeafMemory::try_reserve(&mut workspace.groups, if estimated_groups == 0 { 1 } else { estimated_groups })
        && !T::LeafMemory::try_reserve(&mut workspace.groups, 1)
    {
        return None;
    }
    Some((start, end))
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), rows.is_some() ==> rows.unwrap().0 <= rows.unwrap().1,
    ensures final(tree).order() == old(tree).order(),
        final(tree).packed_state().rows@ == old(tree).packed_state().rows@,
        final(tree).packed_state().groups@ == old(tree).packed_state().groups@
            || rows.is_some() && final(tree).packed_state().groups@ == old(tree).packed_state().groups@.push(
                StackLeafGroup { parent: node, span: [rows.unwrap().0, rows.unwrap().1] }),
    no_unwind
))]
fn finish_leaf_rows<T: StartActions + ?Sized>(
    tree: &mut T, node: T::Id, rows: Option<(u32, u32)>, count: u32,
) {
    if let Some((start, end)) = rows {
        if end - start != count || count == 0 { return; }
        let packed = tree.packed_stack_leaves();
        // The reserved run ends at the last row appended by this sizing walk.
        if end as usize != packed.rows.len() { return; }
        let group = StackLeafGroup { parent: node, span: [start, end] };
        if try_append::<_, T::LeafMemory>(&mut packed.groups, group) {
            tree.edit(node).prepared_placement |= NodeLayoutData::PREPARED_FIT_LEAVES;
        }
    }
}

#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires frame_live(frame, old(tree).order()),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn prepare_fill_leaf_line_axis<T: StartActions + ?Sized, const VERTICAL: bool>(
    tree: &mut T, mut frame: PrepareFrame<T::Id>, own: KnownAxis, inner: f32, retained: &mut RetainedSizing,
) -> Option<Summary> {
    let parent = frame.node;
    let expected = tree.record(parent).n_placed_children;
    // Summing this many unit weights in source order is exact in binary32.
    if expected == 0 || expected > 16_777_216 { return None; }
    let mut count = 0;
    let mut next = frame.next;
    let axis = if VERTICAL { Axis::Y } else { Axis::X };
    let cross = axis.other();
    let gaps = frame.spacing * T::Float::max(expected as f32 - 1.0, 0.0);
    let size = fill_budget::share(fill_budget::after_gaps(inner, gaps), 0.0, expected as f32);
    if !T::Float::finite(size) { return None; }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut rows: Option<(u32, u32)> = None;
    let mut record = T::empty_record();
    record.publish_axis(axis, size, size, own.rank.saturating_add(3));
    record.publish_axis(cross, 0.0, 0.0, 0);
    let regular = slot_index(cross, Kind::Regular);
    let resolved = slot_index(cross, Kind::Final);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), live(tree, frame.node), tree.order().ordered(),
            count <= expected, expected <= 16_777_216, frame.node == parent,
            regular < cycle_rules::N_SLOTS, resolved < cycle_rules::N_SLOTS,
            rows.is_some() ==> rows.unwrap().0 <= rows.unwrap().1,
            rows.is_some() ==> fit_leaf_span(tree, frame.next, next, rows.unwrap().0),
            count == 0 ==> next == frame.next,
            rows.is_some() ==> rows.unwrap().0 + count == tree.packed_state().rows.len(),
            next.is_some() ==> tree.order().child(frame.node, next.unwrap()),
        ensures next.is_none(),
        decreases sizing_pass::remaining(tree.order(), frame.node, next),
    ))]
    while let Some(child) = next {
        #[cfg(verus_keep_ghost)]
        proof! { tree.order().node_facts(child); }
        if count == expected { return None; }
        let params = tree.params(child);
        let [left, right] = *params.margin.component(axis);
        let (Size::Fill, Size::Pixels(pixels)) = (*params.size.component(axis), *params.size.component(cross)) else {
            return None;
        };
        let unsupported = params.disabled | params.free_placement | params.min_size.x.is_some()
            | params.min_size.y.is_some() | params.max_size.x.is_some() | params.max_size.y.is_some()
            | !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
            | !left.is_zero() | !right.is_zero() | !T::Float::finite(pixels) | (params.fill_weight != 1.0);
        if unsupported || tree.first(child).is_some()
        {
            return None;
        }
        let [start, end] = *params.margin.component(cross);
        let (cross_start, extent) = if start.is_zero() & end.is_zero() {
            (0.0f32, pixels)
        } else {
            let leading = T::Float::margin(start);
            let margin = leading + T::Float::margin(end);
            (leading, if margin == 0.0 { pixels } else { pixels + margin })
        };
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let packed_style = matches!(*params.position.component(cross), Pos::Start);
        #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
        let _ = cross_start;
        frame.extent = T::Float::max(frame.extent, extent);
        if (params.grid_span.x | params.grid_span.y) > 1 { frame.flags |= NodeFlags::GRID_SPANS; }
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let pack = if packed_style && rows.is_some() {
            true
        } else if packed_style && count == 0 {
            rows = reserve_leaf_rows(tree, frame.node, expected);
            rows.is_some()
        } else {
            false
        };
        record.values[regular] = pixels;
        record.values[resolved] = pixels;
        *tree.edit(child) = record;
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if pack {
            #[cfg(verus_keep_ghost)]
            proof! { assert(tree.order().child(frame.node, child)); }
            let Xy { x, y } = record.size();
            let row = PreparedStackLeaf::stack::<T::Float>(child, [x, y], !VERTICAL, [0.0, 0.0], cross_start, frame.spacing);
            #[cfg(verus_keep_ghost)]
            proof! {
                let published = tree.layout_record(child).values;
                assert(published == record.values);
                assert(row.size@[0] == published@[cycle_rules::slot_index(X.index(), Kind::Final) as int]);
                assert(row.size@[1] == published@[cycle_rules::slot_index(Y.index(), Kind::Final) as int]);
            }
            #[cfg(verus_keep_ghost)]
            let prior = save_packed_rows(tree);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(rows.is_some());
                let start = rows.unwrap().0;
                if count == 0 {
                    assert(start == prior@.len());
                    assert(frame.next == Some(child));
                    assert(packed_ids(prior@, start as int, prior@.len() as int) =~= Seq::<T::Id>::empty());
                    reveal(leaf_path);
                }
                assert(fit_leaf_span(tree, frame.next, Some(child), start));
            }
            if !try_append::<_, T::LeafMemory>(&mut tree.packed_stack_leaves().rows, row) { rows = None; }
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Some((start, _)) = rows {
                    append_fit_leaf(tree.order(), frame.next, prior@, start as int, row,
                        tree.packed_state().rows@, (tree.order().sibling)(child));
                }
            }
        } else { rows = None; }
        count += 1;
        next = tree.sibling(child);
    }
    if count != expected { return None; }
    frame.next = None;
    frame.n_placed_children = count;
    frame.n_nodes = count.saturating_add(1);
    frame.flags |= NodeFlags::flex_child(axis);
    frame.known = Some(KnownStack { own, child_space: Some(size) });
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { frame.fit_level = 1; }
    let summary = finish::<T, false>(tree, frame, retained);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    finish_leaf_rows(tree, frame.node, rows, count);
    Some(summary)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires frame_live(frame, old(tree).order()),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn prepare_cross_fill_line<T: StartActions + ?Sized>(
    tree: &mut T, frame: PrepareFrame<T::Id>, cross: Axis, inner: f32, retained: &mut RetainedSizing,
) -> Option<Summary> {
    match cross {
        Axis::X => prepare_cross_fill_line_axis::<T, false>(tree, frame, inner, retained),
        Axis::Y => prepare_cross_fill_line_axis::<T, true>(tree, frame, inner, retained),
    }
}

/// A fixed cross extent lets preparation size the leaves and fold their main
/// extents together. The ordinary walk rewrites any rejected prefix.
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires frame_live(frame, old(tree).order()),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn prepare_cross_fill_line_axis<T: StartActions + ?Sized, const VERTICAL: bool>(
    tree: &mut T, mut frame: PrepareFrame<T::Id>, inner: f32, retained: &mut RetainedSizing,
) -> Option<Summary> {
    if !T::Float::finite(inner) { return None; }
    #[cfg(verus_keep_ghost)]
    let parent = frame.node;
    let mut count = 0u32;
    let mut next = frame.next;
    let cross = if VERTICAL { Axis::Y } else { Axis::X };
    let main = cross.other();
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let expected = tree.record(frame.node).n_placed_children;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut rows: Option<(u32, u32)> = None;
    let mut record = T::empty_record();
    record.publish_axis(cross, inner, inner, 2);
    record.publish_axis(main, 0.0, 0.0, 0);
    let cross_regular = slot_index(cross, Kind::Regular);
    let cross_resolved = slot_index(cross, Kind::Final);
    let main_regular = slot_index(main, Kind::Regular);
    let main_resolved = slot_index(main, Kind::Final);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), live(tree, frame.node), tree.order().ordered(),
            frame.node == parent, cross_regular < cycle_rules::N_SLOTS, cross_resolved < cycle_rules::N_SLOTS,
            main_regular < cycle_rules::N_SLOTS, main_resolved < cycle_rules::N_SLOTS,
            rows.is_some() ==> rows.unwrap().0 <= rows.unwrap().1,
            rows.is_some() ==> fit_leaf_span(tree, frame.next, next, rows.unwrap().0),
            count == 0 ==> next == frame.next,
            rows.is_some() ==> rows.unwrap().0 + count == tree.packed_state().rows.len(),
            next.is_some() ==> tree.order().child(frame.node, next.unwrap()),
        ensures next.is_none(),
        decreases sizing_pass::remaining(tree.order(), frame.node, next),
    ))]
    while let Some(child) = next {
        #[cfg(verus_keep_ghost)]
        proof! { tree.order().node_facts(child); }
        next = tree.sibling(child);
        #[cfg(verus_keep_ghost)]
        proof! { assert(next == (tree.order().sibling)(child)); }
        let params = tree.params(child);
        let (Size::Fill, Size::Pixels(pixels)) = (*params.size.component(cross), *params.size.component(main)) else {
            return None;
        };
        let unsupported = params.disabled | params.free_placement | params.min_size.x.is_some()
            | params.min_size.y.is_some() | params.max_size.x.is_some() | params.max_size.y.is_some()
            | !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
            | !T::Float::finite(pixels);
        if unsupported || tree.first(child).is_some() { return None; }

        let [start, end] = *params.margin.component(cross);
        let (cross_start, width) = if start.is_zero() & end.is_zero() {
            (0.0f32, inner)
        } else {
            let leading = T::Float::margin(start);
            let available = sizing_finish::inside_margins::<T::Float>(inner, [leading, T::Float::margin(end)]);
            if !T::Float::finite(available) { return None; }
            (leading, available)
        };

        let [start, end] = *params.margin.component(main);
        let (main_margins, extent) = if start.is_zero() & end.is_zero() {
            ([0.0f32, 0.0f32], pixels)
        } else {
            let margins = [T::Float::margin(start), T::Float::margin(end)];
            let margin = margins[0] + margins[1];
            (margins, if margin == 0.0 { pixels } else { pixels + margin })
        };
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let packed_style = matches!(*params.position.component(cross), Pos::Start) && count < expected;
        #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
        let _ = (cross_start, main_margins);

        frame.extent += extent;
        if (params.grid_span.x | params.grid_span.y) > 1 { frame.flags |= NodeFlags::GRID_SPANS; }
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let pack = if packed_style && rows.is_some() {
            true
        } else if packed_style && count == 0 {
            rows = reserve_leaf_rows(tree, frame.node, expected);
            rows.is_some()
        } else {
            false
        };
        record.values[cross_regular] = width;
        record.values[cross_resolved] = width;
        record.values[main_regular] = pixels;
        record.values[main_resolved] = pixels;
        *tree.edit(child) = record;
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if pack {
            #[cfg(verus_keep_ghost)]
            proof! { assert(tree.order().child(frame.node, child)); }
            let Xy { x, y } = record.size();
            let row = PreparedStackLeaf::stack::<T::Float>(child, [x, y], VERTICAL, main_margins, cross_start, frame.spacing);
            #[cfg(verus_keep_ghost)]
            proof! {
                let published = tree.layout_record(child).values;
                assert(published == record.values);
                assert(row.size@[0] == published@[cycle_rules::slot_index(X.index(), Kind::Final) as int]);
                assert(row.size@[1] == published@[cycle_rules::slot_index(Y.index(), Kind::Final) as int]);
            }
            #[cfg(verus_keep_ghost)]
            let prior = save_packed_rows(tree);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(rows.is_some());
                let start = rows.unwrap().0;
                if count == 0 {
                    assert(start == prior@.len());
                    assert(frame.next == Some(child));
                    assert(packed_ids(prior@, start as int, prior@.len() as int) =~= Seq::<T::Id>::empty());
                    reveal(leaf_path);
                }
                assert(fit_leaf_span(tree, frame.next, Some(child), start));
            }
            if !try_append::<_, T::LeafMemory>(&mut tree.packed_stack_leaves().rows, row) { rows = None; }
            #[cfg(verus_keep_ghost)]
            proof! {
                if let Some((start, _)) = rows {
                    append_fit_leaf(tree.order(), frame.next, prior@, start as int, row,
                        tree.packed_state().rows@, next);
                }
            }
        } else { rows = None; }
        count = cycle_rules::add_count(count, 1);
    }
    if count == 0 { return None; }
    frame.next = None;
    frame.n_placed_children = count;
    frame.n_nodes = count.saturating_add(1);
    frame.flags |= NodeFlags::flex_child(cross);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { frame.fit_level = 1; }
    let summary = finish::<T, false>(tree, frame, retained);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    finish_leaf_rows(tree, frame.node, rows, count);
    Some(summary)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn inherited_axis<F: FrameFloat, I>(frame: &PrepareFrame<I>, params: &LayoutParams) -> Option<KnownAxis> {
    let known = frame.known?;
    let inner = known.child_space?;
    let axis = known.own.axis;
    if params.disabled || params.free_placement || !matches!(*params.size.component(axis), Size::Fill)
        || params.min_size.component(axis).is_some() || params.max_size.component(axis).is_some()
        || frame.stack_axis.is_none() && *params.grid_span.component(axis) > 1
    {
        return None;
    }
    let (size, increment) = if matches!(frame.stack_axis, Some(main) if main.index() == axis.index()) {
        (inner * params.fill_weight, 3)
    } else {
        let [start, end] = *params.margin.component(axis);
        (sizing_finish::inside_margins::<F>(inner, [F::margin(start), F::margin(end)]), 2)
    };
    if !F::finite(size) { return None; }
    Some(KnownAxis { axis, size, rank: known.own.rank.saturating_add(increment) })
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(state =>
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
        match state {
            State::Children(frame) => frame.node == node && frame_live(frame, final(tree).order()),
            State::Done(_) => true,
        },
    no_unwind
))]
pub(crate) fn begin<T: StartActions + ?Sized, const RETAIN: bool, const REGISTERED_PIXELS: bool>(
    tree: &mut T, node: T::Id, block_parent: Option<bool>, _retained: &mut RetainedSizing, inherited: Option<KnownAxis>,
) -> State<PrepareFrame<T::Id>, Summary> {
    let params = tree.params(node);
    if params.disabled {
        let record = tree.edit(node);
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if RETAIN && record.has_dormant_grid() {
            record.structural_change = StructuralChange::Clean;
            return State::Done(Summary { nodes: 0, needs_solve: false });
        }
        *record = T::empty_record();
        return State::Done(Summary { nodes: 0, needs_solve: false });
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let retain = if RETAIN {
        let record = tree.record(node);
        let reset_branch = _retained.leaf_only
            && matches!(record.structural_change, StructuralChange::Moved | StructuralChange::Retained);
        if reset_branch || record.flags.check_state(X, Kind::Final) != cycle_rules::SOLVED {
            // A newly enabled or newly allocated region can contain formerly unreachable state.
            _retained.inspect_descendants = true;
            false
        } else {
            true
        }
    } else {
        false
    };
    #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
    let retain = false;

    let children_layout = params.children_layout;
    let block_parent = block_schedule::in_flow_parent(block_parent, params.free_placement);
    if !RETAIN && block_parent.is_none() {
        if let Some(summary) = fill_stack::try_prepare::<T, REGISTERED_PIXELS>(tree, node) {
            return State::Done(summary);
        }
        if !REGISTERED_PIXELS {
            if let Some(summary) = ratio_stack::try_prepare(tree, node) {
                return State::Done(summary);
            }
        }
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if retain && matches!(tree.record(node).structural_change, StructuralChange::Moved) {
        // Planning included both parents. This boundary can retain its local slots.
        tree.edit(node).structural_change = StructuralChange::Clean;
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    {
        let params = tree.params(node);
        if retain && !_retained.leaf_only && block_parent.is_none() && !tree.record(node).flags.is_block_item()
            && matches!(tree.record(node).structural_change, StructuralChange::Clean)
            && independent_pixel::<T::Float>(params, X) && independent_pixel::<T::Float>(params, Y)
            && tree.first(node).is_some()
        {
            if let Some((nodes, blocks, has_flow)) = cached_branch::counts(tree, node) {
                let data = tree.edit(node);
                data.structural_change = StructuralChange::Retained;
                wrap_metrics::clear_parent_line(&mut data.flags.0, NodeFlags::WRAP_LINE_START, &mut data.parent_flow);
                _retained.slots = cycle_rules::add_count(_retained.slots, nodes.saturating_mul(4));
                _retained.blocks = _retained.blocks.saturating_add(blocks);
                tree.note_flow(has_flow);
                return State::Done(Summary { nodes, needs_solve: true });
            }
        }
    }
    let params = tree.params(node);
    let block_children = if matches!(children_layout, ChildrenLayout::Block) {
        Some(block_schedule::auto_content_height(
            matches!(params.size.y, Size::Auto | Size::FitContent), params.size.y.is_flex(),
            matches!(block_parent, Some(true)),
        ))
    } else { None };
    let (stack_axis, spacing) = match children_layout {
        ChildrenLayout::Stack { axis, spacing, .. } => (Some(axis), spacing),
        _ => (None, 0.0),
    };
    let pixel_fit_axis = prepare_frame::pixel_fit(params, stack_axis);
    let fixed_cross = match prepare_frame::stack_cross_pixels::<T::Float>(params, children_layout, retain, block_parent) {
        Some((axis, size)) => {
            let [start, end] = *tree.params(node).padding.component(axis);
            Some((axis, T::Float::max(size - (start + end), 0.0)))
        }
        None => None,
    };
    if matches!(params.size, Xy { x: Size::AspectRatio(_), y: Size::AspectRatio(_) }) {
        tree.warn_both_axes_ratio(node);
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if matches!(children_layout, ChildrenLayout::Block | ChildrenLayout::Wrap { .. }) { tree.note_flow(true); }

    if !RETAIN && !REGISTERED_PIXELS && block_parent.is_none()
        && matches!(children_layout, ChildrenLayout::Wrap { .. })
    {
        if let Some(nodes) = wrap_ready::try_leaf_wrap(tree, node) {
            return State::Done(Summary { nodes, needs_solve: true });
        }
    }
    let next = tree.first(node);
    #[cfg(verus_keep_ghost)]
    let order = save_order(tree);
    #[cfg(verus_keep_ghost)]
    proof! { order@.node_facts(node); }
    let mut known = None;
    if !RETAIN && block_parent.is_none() {
        if let (Some(fit), Some(main)) = (pixel_fit_axis, stack_axis) {
            let axis = fit.other();
            let params = tree.params(node);
            let prepared = match inherited {
                Some(value) if value.axis.index() == axis.index() => Some(value),
                _ => match *params.size.component(axis) {
                    Size::Pixels(size) if T::Float::finite(size) && params.min_size.component(axis).is_none()
                        && params.max_size.component(axis).is_none() => Some(KnownAxis { axis, size, rank: 0 }),
                    _ => None,
                },
            };
            if let Some(prepared) = prepared {
                let inner = sizing_finish::inner::<T::Float>(prepared.size, sizing_finish::padding(tree.params(node), prepared.axis));
                let children = if prepared.axis.index() == main.index() {
                    if matches!(next, Some(child) if tree.first(child).is_none()) {
                        let frame = PrepareFrame {
                            node, next, retain, block_parent, block_children,
                            stack_axis, spacing, pixel_fit_axis, extent: 0.0, fixed_cross, known: None,
                            #[cfg(any(feature = "incremental", verus_keep_ghost))] fit_level: 0,
                            #[cfg(verus_keep_ghost)] order,
                            n_placed_children: 0, n_nodes: 1, flags: 0,
                        };
                        if let Some(summary) = prepare_fill_leaf_line(tree, frame, prepared, inner, _retained) {
                            return State::Done(summary);
                        }
                        None
                    } else {
                        plain_fill_share(tree, node, next, main, inner, spacing)
                    }
                } else {
                    if let (Some((cross, available)), Some(_)) = (fixed_cross, next) {
                        let frame = PrepareFrame {
                            node, next, retain, block_parent, block_children,
                            stack_axis, spacing, pixel_fit_axis, extent: 0.0, fixed_cross, known: None,
                            #[cfg(any(feature = "incremental", verus_keep_ghost))] fit_level: 0,
                            #[cfg(verus_keep_ghost)] order,
                            n_placed_children: 0, n_nodes: 1, flags: 0,
                        };
                        if let Some(summary) = prepare_cross_fill_line(tree, frame, cross, available, _retained) {
                            return State::Done(summary);
                        }
                    }
                    Some(inner)
                };
                known = Some(KnownStack { own: prepared, child_space: children });
            }
        }
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if known.is_none() && block_parent.is_none() {
        if let (Some(own), Some(main)) = (inherited, stack_axis) {
            let child_space = if own.axis.index() != main.index() {
                Some(sizing_finish::inner::<T::Float>(own.size, sizing_finish::padding(tree.params(node), own.axis)))
            } else {
                None
            };
            known = Some(KnownStack { own, child_space });
        }
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if retain && block_parent.is_none() && matches!(children_layout, ChildrenLayout::Grid {
        columns: MainAxisCellSize::Width(_), ..
    }) {
        known = tree.known_width_grid(node);
    }
    State::Children(PrepareFrame {
        node, next, retain, block_parent, block_children,
        #[cfg(verus_keep_ghost)] order,
        stack_axis, spacing, pixel_fit_axis, extent: 0.0, fixed_cross, known,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] fit_level: 0,
        n_placed_children: 0, n_nodes: 1, flags: 0,
    })
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(ready =>
    requires live(old(tree), child),
    ensures final(tree).order() == old(tree).order(),
        RETAIN && !REGISTERED_PIXELS ==> forall |axis: Axis|
            #[trigger] intrinsic_fill_admitted::<T::Float>(
                old(tree).layout_record(child), old(tree).layout_params(child), axis,
            ) ==> {
                &&& !ready
                &&& final(_retained).slots == vstd::math::min(old(_retained).slots as int + 2, u32::MAX as int)
                &&& reset_keeps_intrinsic(old(tree).layout_record(child), final(tree).layout_record(child), axis)
            },
    no_unwind
))]
pub(crate) fn leaf<T: Records + ?Sized, const RETAIN: bool, const REGISTERED_PIXELS: bool>(
    tree: &mut T, child: T::Id, fixed_cross: Option<(Axis, f32)>, _retained: &mut RetainedSizing,
) -> bool {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if REGISTERED_PIXELS && reuse_registered_pixels(tree.edit(child)) {
        if tree.record(child).fixed_leaf_summary.is_empty() {
            let summary = fixed_leaf_summary(tree.params(child));
            tree.edit(child).fixed_leaf_summary = summary;
        }
        return true;
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if RETAIN {
        let params = tree.params(child);
        let intrinsic = match params.size {
            Xy { x: Size::FitContent, y: Size::Fill } => Some(X),
            Xy { x: Size::Fill, y: Size::FitContent } => Some(Y),
            _ => None,
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(intrinsic == intrinsic_fill_axis(*params)); }
        if let Some(axis) = intrinsic {
            if !params.intrinsic_reads_other_axis(axis) && count_bounds(params, X) == 0 && count_bounds(params, Y) == 0
                && tree.edit(child).reset_intrinsic_fill_leaf::<T::Float>(axis)
            {
                _retained.slots = cycle_rules::add_count(_retained.slots, 2);
                return false;
            }
        }
        if !_retained.inspect_descendants {
            let p = tree.params(child);
            _retained.leaf_bounds = cycle_rules::add_count(_retained.leaf_bounds, count_bounds(p, X) + count_bounds(p, Y));
        }
    }
    let params = tree.params(child);
    let mut data = T::empty_record();
    if seed_pixels::<T::Float>(&mut data, params, false, None) {
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if REGISTERED_PIXELS { data.fixed_leaf_summary = fixed_leaf_summary(params); }
        install_fixed::<T::Float>(tree.edit(child), data);
        return true;
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if RETAIN {
        let old = tree.record(child);
        if _retained.can_retain_leaf(old.structural_change) {
            let slots = data.retain_leaf_slots::<T::Float>(old, params);
            _retained.slots = cycle_rules::add_count(_retained.slots, slots);
        }
    }
    let ready = match fixed_cross {
        Some((axis, inner)) => data.seed_stack_leaf::<T::Float>(params, axis, inner),
        None => false,
    };
    *tree.edit(child) = data;
    ready || RETAIN
        && data.flags.check_state(Axis::X, Kind::Final) == cycle_rules::SOLVED
        && data.flags.check_state(Axis::Y, Kind::Final) == cycle_rules::SOLVED
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), child),
    ensures final(tree).order() == old(tree).order(),
        final(frame).node == old(frame).node, final(frame).next == old(frame).next, final(frame).order@ == old(frame).order@,
    no_unwind
))]
pub(crate) fn direct_child<T: Records + ?Sized, const RETAIN: bool, const REGISTERED_PIXELS: bool>(
    tree: &mut T, frame: &mut PrepareFrame<T::Id>, child: T::Id, retained: &mut RetainedSizing,
) -> bool {
    let no_parent_specialty = frame.pixel_fit_axis.is_none() && frame.block_children.is_none();
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if REGISTERED_PIXELS && !RETAIN && no_parent_specialty && tree.first(child).is_none() {
        let data = tree.edit(child);
        let summary = data.fixed_leaf_summary;
        if summary.is_ready() && reuse_registered_pixels(data) {
            frame.n_nodes = cycle_rules::add_count(frame.n_nodes, 1);
            let in_flow = if summary.in_flow() { 1 } else { 0 };
            frame.n_placed_children = cycle_rules::add_count(frame.n_placed_children, in_flow);
            if summary.spans() { frame.flags |= NodeFlags::GRID_SPANS; }
            return true;
        }
    }
    let params = tree.params(child);
    // Fixed leaves in a full solve need no child frame or flex flags.
    if !RETAIN && !REGISTERED_PIXELS && no_parent_specialty
        && matches!(params.size, Xy { x: Size::Pixels(_), y: Size::Pixels(_) })
        && !params.disabled && matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        && tree.first(child).is_none()
    {
        let mut record = T::empty_record();
        if seed_pixels::<T::Float>(&mut record, params, false, None) {
            if !params.free_placement {
                frame.n_placed_children = cycle_rules::add_count(frame.n_placed_children, 1);
                if params.grid_span.x > 1 || params.grid_span.y > 1 { frame.flags |= NodeFlags::GRID_SPANS; }
            }
            frame.n_nodes = cycle_rules::add_count(frame.n_nodes, 1);
            install_fixed::<T::Float>(tree.edit(child), record);
            return true;
        }
    }
    if frame.block_children.is_none() && !params.disabled
        && matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        && tree.first(child).is_none()
        && !matches!(params.size, Xy { x: Size::AspectRatio(_), y: Size::AspectRatio(_) })
    {
        if let (false, Some((cross, inner))) = (RETAIN, frame.fixed_cross) {
            let mut data = T::empty_record();
            if let Some((size, independent)) = data.seed_ready_stack_leaf::<T::Float>(params, cross, inner) {
                frame.n_nodes = cycle_rules::add_count(frame.n_nodes, 1);
                if !params.free_placement {
                    frame.n_placed_children = cycle_rules::add_count(frame.n_placed_children, 1);
                    frame.flags |= NodeFlags::flex_child(cross);
                    if params.grid_span.x > 1 || params.grid_span.y > 1 { frame.flags |= NodeFlags::GRID_SPANS; }
                    if let Some(axis) = frame.pixel_fit_axis {
                        if !independent || axis.index() == cross.index() {
                            frame.pixel_fit_axis = None;
                        } else {
                            let [start, end] = *params.margin.component(axis);
                            let margin = T::Float::margin(start) + T::Float::margin(end);
                            let extent = if margin == 0.0 { size } else { size + margin };
                            frame.extent = match frame.stack_axis {
                                Some(main) if main.index() == axis.index() => frame.extent + extent,
                                _ => T::Float::max(frame.extent, extent),
                            };
                            #[cfg(any(feature = "incremental", verus_keep_ghost))]
                            if frame.fit_level == 0 { frame.fit_level = 1; }
                        }
                    }
                }
                *tree.edit(child) = data;
                return true;
            }
        }
        let ready = leaf::<T, RETAIN, REGISTERED_PIXELS>(tree, child, frame.fixed_cross, retained);
        frame.include_child::<T::Float>(tree.params(child), 1, !ready, None);
        return true;
    }
    false
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), frame.node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
pub(crate) fn finish<T: Records + ?Sized, const RETAIN: bool>(tree: &mut T, frame: PrepareFrame<T::Id>, _retained: &mut RetainedSizing) -> Summary {
    let node = frame.node;
    let params = tree.params(node);
    let mut data = T::empty_record();
    let children_layout = params.children_layout;
    let (flags, count, width_grid_axis) = frame.mode_flags(children_layout);
    data.n_placed_children = count;
    data.flags.0 = flags;
    let mut both_axes_fixed = seed_pixels::<T::Float>(&mut data, params, frame.block_parent.is_some(), width_grid_axis);
    // A previewed width grid still needs its normal Final to assign cells.
    if let Some(KnownStack { own, child_space }) = if width_grid_axis.is_some() { None } else { frame.known } {
        data.publish_axis(own.axis, own.size, own.size, own.rank);
        both_axes_fixed = data.flags.check_state(own.axis.other(), Kind::Final) == cycle_rules::SOLVED;
        if matches!(frame.stack_axis, Some(main) if main.index() == own.axis.index()) {
            if let Some(share) = child_space {
                let index = slot_index(own.axis, Kind::EvenShare);
                data.publish_slot(index, share);
                #[cfg(any(feature = "incremental", verus_keep_ghost))]
                { data.levels[index] = own.rank.saturating_add(2); }
            }
        }
    }
    if let Some(axis) = frame.pixel_fit_axis {
        let [padding_start, padding_end] = *tree.params(node).padding.component(axis);
        prepare_frame::publish_fit::<T::Float>(axis, frame.extent, params.image, frame.stack_axis, frame.spacing,
            frame.n_placed_children, padding_start + padding_end, &mut data.flags.0, &mut data.values,
            #[cfg(any(feature = "incremental", verus_keep_ghost))] &mut data.levels,
            #[cfg(any(feature = "incremental", verus_keep_ghost))] frame.fit_level);
        let regular = slot_index(axis, Kind::Regular);
        let size = data.values[regular];
        if (!frame.retain || frame.known.is_some() && frame.stack_axis.is_some()) && frame.block_parent.is_none()
            && params.min_size.component(axis).is_none() && params.max_size.component(axis).is_none()
            && data.flags.0 & NodeFlags::flex_child(axis) == 0 && T::Float::finite(size)
        {
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            let rank = data.levels[regular];
            #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
            let rank = 0;
            data.publish_axis(axis, size, size, rank);
            both_axes_fixed = data.flags.check_state(axis.other(), Kind::Final) == cycle_rules::SOLVED;
        }
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if frame.retain && _retained.can_retain_leaf(tree.record(node).structural_change)
        && !both_axes_fixed && tree.first(node).is_none()
        && matches!(children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
    {
        let slots = data.retain_leaf_slots::<T::Float>(tree.record(node), params);
        _retained.slots = cycle_rules::add_count(_retained.slots, slots);
    }
    if !RETAIN && matches!(children_layout, ChildrenLayout::Wrap { .. }) {
        wrap_ready::try_prepare(tree, node, &mut data);
    }
    *tree.edit(node) = data;
    let needs_solve = !both_axes_fixed
        || data.flags.0 & (NodeFlags::DESCENDANTS_NEED_SOLVE | NodeFlags::BLOCK_CONTAINER | NodeFlags::WRAP_CONTAINER) != 0;
    Summary { nodes: frame.n_nodes, needs_solve }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Engine<'a, T: StartActions + ?Sized, const RETAIN: bool, const REGISTERED_PIXELS: bool> {
    retained: &'a mut RetainedSizing,
    adapter: PhantomData<T>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<T: StartActions + ?Sized, const RETAIN: bool, const REGISTERED_PIXELS: bool> prepare_walk::Model
    for Engine<'_, T, RETAIN, REGISTERED_PIXELS>
{
    type Child = T::Id;
    type Frame = PrepareFrame<T::Id>;
    type Summary = Summary;
    type Context = T;
    type Topology = Order<T::Id>;

    closed spec fn remaining(frame: Self::Frame) -> nat { remaining(frame) }
    closed spec fn topology(&self, tree: &T) -> Self::Topology { tree.order() }
    closed spec fn valid(&self, _tree: &T) -> bool { true }

    closed spec fn coherent(&self, _tree: &T, _active: Option<Self::Frame>,
        _suspended: Seq<(Self::Frame, Self::Child)>) -> bool { true }

    closed spec fn admissible(tree: &T) -> (spec_fn(Self::Frame) -> bool, spec_fn(Self::Child) -> bool) {
        let order = tree.order();
        (|frame| frame_live(frame, order), order.live)
    }
}

fn snapshot_frame<I>(frame: &PrepareFrame<I>) -> (saved: Ghost<PrepareFrame<I>>)
    ensures saved@ == *frame,
    no_unwind
{ Ghost(*frame) }

proof fn transferred_progress<I>(order: Order<I>, before: PrepareFrame<I>, after: PrepareFrame<I>, child: I, branch: PrepareFrame<I>)
    requires frame_live(before, order), frame_live(after, order), frame_live(branch, order),
        before.next == Some(child), after.node == before.node, after.next == (order.sibling)(child), branch.node == child,
    ensures remaining(after) + remaining(branch) + 2 < remaining(before),
{
    order.node_facts(child);
    let bounds = order.interval;
    let start = bounds(child).0;
    let end = bounds(child).1;
    let parent_end = bounds(before.node).1;
    let resume = match after.next { Some(next) => bounds(next).0, None => parent_end };
    let first = match branch.next { Some(next) => bounds(next).0, None => end };
    prepare_walk::suffix_and_descendant_budget(start, end, parent_end, resume, first);
}
}

#[cfg(not(verus_keep_ghost))]
impl<T: StartActions + ?Sized, const RETAIN: bool, const REGISTERED_PIXELS: bool> prepare_walk::Model
    for Engine<'_, T, RETAIN, REGISTERED_PIXELS>
{
    type Child = T::Id;
    type Frame = PrepareFrame<T::Id>;
    type Summary = Summary;
    type Context = T;
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires frame_live(*old(frame), old(tree).order()), live(old(tree), child),
    ensures final(tree).order() == old(tree).order(), frame_live(*final(frame), final(tree).order()),
        final(frame).node == old(frame).node, final(frame).next == old(frame).next,
    no_unwind
))]
fn include_ready_pair<T: StartActions + ?Sized>(tree: &mut T, frame: &mut PrepareFrame<T::Id>, child: T::Id) -> bool {
    let Some((axis, size)) = prepare_pair::ready(tree, child) else { return false; };
    let fit_child = match frame.pixel_fit_axis {
        Some(fit) if fit.index() == axis.index() => Some((size, 1)),
        _ => None,
    };
    frame.include_child::<T::Float>(tree.params(child), 3, false, fit_child);
    true
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns independent_row_leaf(params), no_unwind))]
pub(crate) fn independent_row_leaf(params: &LayoutParams) -> bool {
    !params.disabled
        && matches!(params.children_layout, ChildrenLayout::Free)
        && matches!(params.size.x, Size::Pixels(_) | Size::FitContent)
        && matches!(params.size.y, Size::Pixels(_) | Size::FitContent)
        && params.min_size.x.is_none() && params.min_size.y.is_none()
        && params.max_size.x.is_none() && params.max_size.y.is_none()
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(count =>
    requires live(tree, node), tree.order().ordered(),
    ensures count.is_some() ==> 2 <= count.unwrap() <= 9,
    no_unwind
))]
fn ready_independent_row<T: Records + ?Sized>(tree: &T, node: T::Id) -> Option<u32> {
    let Some(mut child) = tree.first(node) else { return None; };
    let mut nodes = 1u32;
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(node); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant live(tree, child), 1 <= nodes <= 9,
        decreases 9 - nodes,
    ))]
    loop {
        if nodes == 9 { return None; }
        let params = tree.params(child);
        let record = tree.record(child);
        if !independent_row_leaf(params) || tree.first(child).is_some()
            || !matches!(record.structural_change, StructuralChange::Clean)
            || record.flags.has_cycle() || record.flags.is_block_item()
            || record.flags.check_state(X, Kind::Final) != cycle_rules::SOLVED
            || record.flags.check_state(Y, Kind::Final) != cycle_rules::SOLVED
            || !T::Float::finite(record.values[slot_index(X, Kind::Final)])
            || !T::Float::finite(record.values[slot_index(Y, Kind::Final)])
        {
            return None;
        }
        nodes += 1;
        let Some(following) = tree.sibling(child) else { return Some(nodes); };
        child = following;
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), child), live(old(tree), frame.node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(), final(frame).node == old(frame).node,
        final(frame).next == old(frame).next, final(frame).order@ == old(frame).order@,
    no_unwind
))]
fn include_retained_grid_child<T: StartActions + ?Sized>(
    tree: &mut T, frame: &mut PrepareFrame<T::Id>, child: T::Id, retained: &mut RetainedSizing,
) -> bool {
    let Some(grid) = frame.known else { return false; };
    let axis = grid.own.axis;
    let Some(space) = grid.child_space else { return false; };
    let params = tree.params(child);
    if params.disabled || params.free_placement
        || !matches!(*params.size.component(axis), Size::Fill)
        || !matches!(*params.size.component(axis.other()), Size::FitContent | Size::Pixels(_))
        || params.min_size.x.is_some() || params.min_size.y.is_some()
        || params.max_size.x.is_some() || params.max_size.y.is_some()
        || *params.grid_span.component(axis) > 1
        || matches!(params.children_layout, ChildrenLayout::Block | ChildrenLayout::Wrap { .. })
    {
        return false;
    }
    let old = tree.record(child);
    let parked = if matches!(old.structural_change, StructuralChange::DormantGrid)
        && matches!(tree.params(frame.node).children_layout, ChildrenLayout::Grid {
            columns: MainAxisCellSize::Width(_), main_axis, ..
        } if main_axis.index() == axis.index())
    {
        old.dormant_grid_flags(axis)
    } else {
        None
    };
    if (!matches!(old.structural_change, StructuralChange::Clean) && parked.is_none()) || old.flags.is_block_item()
    {
        return false;
    }
    let [before, after] = *params.margin.component(axis);
    let next = sizing_finish::inside_margins::<T::Float>(space, [T::Float::margin(before), T::Float::margin(after)]);
    let regular = slot_index(axis, Kind::Regular);
    let completed = slot_index(axis, Kind::Final);
    let rank = grid.own.rank.saturating_add(2);
    if old.levels[regular] != rank || old.levels[completed] != rank.saturating_add(1) {
        return false;
    }
    let changed = T::Float::bits(old.values[regular]) != T::Float::bits(next)
        || T::Float::bits(old.values[completed]) != T::Float::bits(next);
    let nodes = if changed {
        if !T::Float::finite(next) || old.flags.has_cycle() || old.flags.0 & NodeFlags::WRAP_LINE_START != 0
            || !matches!(*params.size.component(axis.other()), Size::Pixels(size) if T::Float::finite(size))
            || !matches!(params.children_layout, ChildrenLayout::Stack { .. })
            || old.flags.check_state(axis, Kind::Final) != cycle_rules::SOLVED
            || old.flags.check_state(axis.other(), Kind::Final) != cycle_rules::SOLVED
        {
            return false;
        }
        let Some(nodes) = ready_independent_row(tree, child) else { return false; };
        tree.edit(child).publish_axis(axis, next, next, rank);
        nodes
    } else {
        if let Some(flags) = parked {
            let data = tree.edit(child);
            data.flags = flags;
            data.structural_change = StructuralChange::Clean;
        }
        let Some((nodes, 0, false)) = cached_branch::counts(tree, child) else {
            if parked.is_some() {
                let data = tree.edit(child);
                *data = T::empty_record();
                data.mark_subtree_changed();
            }
            return false;
        };
        tree.edit(child).clear_dormant_grid();
        nodes
    };
    tree.edit(child).flags.0 &= !NodeFlags::DESCENDANTS_NEED_SOLVE;
    let slots = nodes.saturating_mul(4).saturating_sub(if changed { 2 } else { 0 });
    retained.slots = cycle_rules::add_count(retained.slots, slots);
    frame.include_child::<T::Float>(tree.params(child), nodes, false, None);
    true
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), child),
    ensures final(tree).order() == old(tree).order(), final(frame).node == old(frame).node,
        final(frame).next == old(frame).next, final(frame).order@ == old(frame).order@,
    no_unwind
))]
fn include_known_grid_leaf<T: StartActions + ?Sized>(
    tree: &mut T, frame: &mut PrepareFrame<T::Id>, child: T::Id, retained: &mut RetainedSizing,
) -> bool {
    let params = tree.params(child);
    let Some(known) = inherited_axis::<T::Float, _>(frame, params) else { return false; };
    let cross = known.axis.other();
    if !matches!(*params.size.component(cross), Size::FitContent | Size::Pixels(_))
        || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        || (*params.min_size.component(cross)).is_some() || (*params.max_size.component(cross)).is_some()
    {
        return false;
    }
    let mut data = T::empty_record();
    seed_pixels::<T::Float>(&mut data, params, false, None);
    data.publish_axis(known.axis, known.size, known.size, known.rank);
    let old = tree.record(child);
    if frame.retain && retained.can_retain_leaf(old.structural_change) {
        let slots = data.retain_leaf_slots::<T::Float>(old, params);
        retained.slots = cycle_rules::add_count(retained.slots, slots);
    }
    let cross_ready = data.flags.check_state(cross, Kind::Final) == cycle_rules::SOLVED;
    *tree.edit(child) = data;
    if !cross_ready { tree.finish_prepared_axis(child, cross); }
    let index = slot_index(cross, Kind::Regular);
    let data = tree.record(child);
    let fit_child = Some((data.values[index], data.levels[index]));
    frame.include_child::<T::Float>(tree.params(child), 1, false, fit_child);
    true
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<T: StartActions + ?Sized, const RETAIN: bool, const REGISTERED_PIXELS: bool> prepare_walk::Driver
    for Engine<'_, T, RETAIN, REGISTERED_PIXELS>
{
    #[inline(always)]
    fn advance(&mut self, tree: &mut T, frame: &mut Self::Frame,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>) -> ChildStep<Self::Child, Self::Frame> {
        let Some(child) = frame.next else { return ChildStep::End; };
        #[cfg(verus_keep_ghost)]
        let before = snapshot_frame(frame);
        frame.next = tree.sibling(child);
        #[cfg(verus_keep_ghost)]
        proof! {
            let order = tree.order();
            order.node_facts(child);
            assert(frame_live(*frame, order));
            assert(remaining(*frame) < remaining(before@));
        }
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let known_branch = if RETAIN && frame.known.is_some() {
            let is_branch = tree.first(child).is_some();
            let prepared = if is_branch {
                frame.retain && include_retained_grid_child(tree, frame, child, self.retained)
            } else {
                include_known_grid_leaf(tree, frame, child, self.retained)
            };
            if prepared { return ChildStep::Prepared; }
            is_branch
        } else {
            false
        };
        #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
        let known_branch = false;
        let try_pair = !RETAIN && frame.block_children.is_none();
        let tried_pair = try_pair && match frame.pixel_fit_axis {
            Some(axis) => matches!(*tree.params(child).size.component(axis), Size::FitContent),
            None => false,
        };
        if tried_pair && include_ready_pair(tree, frame, child) { return ChildStep::Prepared; }
        let retain = RETAIN && frame.retain;
        let prepared = if known_branch {
            false
        } else if retain {
            direct_child::<T, true, REGISTERED_PIXELS>(tree, frame, child, self.retained)
        } else {
            direct_child::<T, false, REGISTERED_PIXELS>(tree, frame, child, self.retained)
        };
        if prepared { return ChildStep::Prepared; }
        if try_pair && !tried_pair && include_ready_pair(tree, frame, child) { return ChildStep::Prepared; }
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if frame.retain { self.retained.inspect_descendants = true; }
        let subtree = if retain {
            let inherited = inherited_axis::<T::Float, _>(frame, tree.params(child));
            begin::<T, true, REGISTERED_PIXELS>(tree, child, frame.block_children, self.retained, inherited)
        } else {
            let inherited = inherited_axis::<T::Float, _>(frame, tree.params(child));
            begin::<T, false, REGISTERED_PIXELS>(tree, child, frame.block_children, self.retained, inherited)
        };
        match subtree {
            State::Done(summary) => {
                self.include(tree, frame, child, summary, #[cfg(verus_keep_ghost)] suspended);
                ChildStep::Prepared
            }
            State::Children(branch) => {
                #[cfg(verus_keep_ghost)]
                proof! { transferred_progress(tree.order(), before@, *frame, child, branch); }
                ChildStep::Descend(child, branch)
            }
        }
    }

    #[inline(always)]
    fn include(&mut self, tree: &mut T, parent: &mut Self::Frame, child: Self::Child, summary: Self::Summary,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>) {
        let params = tree.params(child);
        let mut fit_child = None;
        if !RETAIN || parent.known.is_some() && parent.stack_axis.is_some() {
            if let Some(axis) = parent.pixel_fit_axis {
                if matches!(*params.size.component(axis), Size::FitContent) && !params.disabled && !params.free_placement {
                    let data = tree.record(child);
                    if data.flags.check_state(axis, Kind::Regular) == cycle_rules::SOLVED {
                        let index = slot_index(axis, Kind::Regular);
                        #[cfg(any(feature = "incremental", verus_keep_ghost))]
                        let rank = data.levels[index];
                        #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
                        let rank = 0;
                        fit_child = Some((data.values[index], rank));
                    }
                }
            }
        }
        parent.include_child::<T::Float>(params, summary.nodes, summary.needs_solve, fit_child);
    }

    #[inline]
    fn finish(&mut self, tree: &mut T, frame: Self::Frame,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>) -> Self::Summary {
        let children_layout = tree.params(frame.node).children_layout;
        let mut summary = finish::<T, RETAIN>(tree, frame, self.retained);
        if let ChildrenLayout::Grid { columns: MainAxisCellSize::Count(columns), main_axis, backfill, .. } = children_layout {
            tree.assign_fixed_grid(frame.node, if columns == 0 { 1 } else { columns }, main_axis, backfill);
        }
        if !RETAIN && frame.flags & NodeFlags::DESCENDANTS_NEED_SOLVE != 0
            && frame.flags & (NodeFlags::FLEX_CHILD_X | NodeFlags::FLEX_CHILD_Y) == 0
            && frame.n_placed_children <= 4 && frame.block_parent.is_none()
            && matches!(children_layout, ChildrenLayout::Stack { .. })
            && sizing_fill::ready_bounded_children(tree, frame.node)
        {
            let data = tree.edit(frame.node);
            data.flags.0 &= !NodeFlags::DESCENDANTS_NEED_SOLVE;
            summary.needs_solve = data.flags.check_state(crate::declarations::X, Kind::Final) != cycle_rules::SOLVED
                || data.flags.check_state(crate::declarations::Y, Kind::Final) != cycle_rules::SOLVED;
        }
        summary
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires match start {
        State::Children(frame) => frame_live(frame, old(tree).order()),
        State::Done(_) => true,
    },
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
pub(crate) fn finish_tree<T: StartActions + ?Sized, M: VecMemory, const RETAIN: bool, const REGISTERED_PIXELS: bool>(
    tree: &mut T, start: State<PrepareFrame<T::Id>, Summary>, retained: &mut RetainedSizing,
    spill: Vec<(PrepareFrame<T::Id>, T::Id)>,
) -> (Summary, Vec<(PrepareFrame<T::Id>, T::Id)>) {
    let mut parents = work_stack::work_stack::<_, 8, M>(spill);
    let mut engine = Engine::<T, RETAIN, REGISTERED_PIXELS> { retained, adapter: PhantomData };
    let result = prepare_walk::run::<_, 8, M>(&mut engine, tree, start, &mut parents);
    (result, parents.into_spill())
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
pub(crate) fn prepare<T: StartActions + ?Sized, M: VecMemory, const RETAIN: bool, const REGISTERED_PIXELS: bool>(
    tree: &mut T, node: T::Id, block_parent: Option<bool>, retained: &mut RetainedSizing,
) -> (u32, bool) {
    let start = begin::<T, RETAIN, REGISTERED_PIXELS>(tree, node, block_parent, retained, None);
    let spill = M::take(tree.prepare_scratch());
    let (summary, spill) = finish_tree::<T, M, RETAIN, REGISTERED_PIXELS>(tree, start, retained, spill);
    *tree.prepare_scratch() = spill;
    (summary.nodes, summary.needs_solve)
}
