//! Read and write a Block producer's packed inputs and margin summary.
#![allow(unexpected_cfgs)]
use super::*;
use crate::prepare_frame::FrameFloat;
#[cfg(not(verus_keep_ghost))]
use crate::margin_storage;
#[cfg(verus_keep_ghost)]
use crate::{block_flow as model, margin_storage::kernel as margin_storage};

#[cfg(not(verus_keep_ghost))]
pub(crate) trait Model<I> {
    type Block: Scalar;
    type BlockMemory: VecMemory;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait Model<I> {
    type Block: Scalar;
    type BlockMemory: VecMemory;
    spec fn lift(value: f32) -> Self::Block;
    spec fn lower(value: Self::Block) -> f32;
    spec fn block_record_value(&self, node: I) -> NodeLayoutData;
    spec fn block_margin_arena(&self) -> Seq<BlockMargins<Self::Block>>;
}

pub(crate) open spec fn zero<F: FrameFloat>(value: f32) -> bool {
    F::word(value) & 0x7fff_ffff == 0
}

pub(crate) open spec fn zero_bound<F: FrameFloat>(bound: Option<Size>) -> bool {
    match bound {
        None => true,
        Some(Size::Pixels(v) | Size::Frac(v)) => zero::<F>(v),
        _ => false,
    }
}

pub(crate) open spec fn saved_margin_index<F: FrameFloat>(record: NodeLayoutData) -> Option<usize> {
    if record.flags.0 & NodeFlags::BLOCK_CONTAINER == 0 { None } else {
        margin_storage::margin_index(F::word(record.values@[cycle_rules::slot_index(0, Kind::EvenShare) as int]),
            record.n_placed_children)
    }
}

pub(crate) open spec fn saved_margin<F: FrameFloat, B: Scalar>(
    record: NodeLayoutData, arena: Seq<BlockMargins<B>>,
) -> Option<BlockMargins<B>> {
    match saved_margin_index::<F>(record) {
        Some(index) if index < arena.len() => Some(arena[index as int]),
        _ => None,
    }
}

pub(crate) open spec fn child_word_has_flow(record: NodeLayoutData) -> bool {
    if record.flags.0 & NodeFlags::BLOCK_CONTAINER != 0 {
        margin_storage::block_has_children(record.n_placed_children)
    } else { record.n_placed_children != 0 }
}

pub(crate) open spec fn edge_words<F: FrameFloat>(params: LayoutParams, flags: NodeFlags) -> (bool, bool) {
    let adjoining = flags.is_block_item() && params.block_margins_can_collapse();
    let y = sizing_requests::resolved_size(params, true, Kind::Regular, flags.is_block_item(),
        flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0);
    (adjoining && zero::<F>(params.padding.y[0]),
        adjoining && zero::<F>(params.padding.y[1]) && y is Some && y.unwrap() is FitContent
            && (params.min_size.y is Some && params.min_size.y.unwrap() is Pixels
                || zero_bound::<F>(sizing_requests::resolved_size(params, true, Kind::Min, flags.is_block_item(),
                    flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0))))
}

pub(crate) open spec fn edges<A: FlowAccess>(access: &A, node: A::Id) -> (bool, bool) {
    edge_words::<A::Float>(access.finish_layout(node), access.finish_flags(node))
}

pub(crate) open spec fn explicit<A: FlowAccess>(record: NodeLayoutData, margins: BlockMargins<A::Block>) -> bool {
    record.flags.is_block_item()
        && !implicit_edges([
            zero::<A::Float>(A::lower(margins.before.positive)), zero::<A::Float>(A::lower(margins.before.negative)),
            zero::<A::Float>(A::lower(margins.after.positive)), zero::<A::Float>(A::lower(margins.after.negative)),
        ], margins.all_through, !child_word_has_flow(record))
}

pub(crate) open spec fn item_words<F: FrameFloat, B: Scalar>(
    params: LayoutParams, record: NodeLayoutData, arena: Seq<BlockMargins<B>>, lift: spec_fn(f32) -> B,
) -> BlockItem<B> {
    let size = record.values@[cycle_rules::slot_index(1, Kind::Final) as int];
    let adjoining = item_adjoins(zero::<F>(size),
        [zero::<F>(params.padding.y[0]), zero::<F>(params.padding.y[1])],
        params.block_margins_can_collapse(), zero_bound::<F>(sizing_requests::resolved_size(params, true, Kind::Min, record.flags.is_block_item(),
            record.flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0)));
    model::item_from_edges(lift(F::margin_value(params.margin.y[0])),
        lift(F::margin_value(params.margin.y[1])), lift(size), adjoining,
        !child_word_has_flow(record), saved_margin::<F, B>(record, arena))
}

pub(crate) open spec fn item<A: FlowAccess>(access: &A, child: A::Id) -> BlockItem<A::Block> {
    item_words::<A::Float, A::Block>(access.finish_layout(child), access.block_record_value(child),
        access.block_margin_arena(), |value: f32| A::lift(value))
}

}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == zero_bound::<F>(bound), no_unwind))]
fn minimum_zero<F: FrameFloat>(bound: Option<Size>) -> bool {
    match bound {
        None => true,
        Some(Size::Pixels(value) | Size::Frac(value)) => F::is_zero(value),
        _ => false,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == model::initial::<A::Block>(edges(access, node).0, edges(access, node).1), no_unwind
))]
pub(super) fn start<A: FlowAccess>(access: &A, node: A::Id) -> BlockFlow<A::Block> {
    let params = access.params(node);
    let margins_adjoin = access.block_record(node).flags.is_block_item() && params.block_margins_can_collapse();
    let fit = matches!(access.declaration(target(node, true, Kind::Regular)), Some(Size::FitContent));
    BlockFlow::from_edges(
        edge_adjoins(margins_adjoin, A::Float::is_zero(params.padding.y[0])),
        edge_adjoins(margins_adjoin, A::Float::is_zero(params.padding.y[1])) && fit && (matches!(params.min_size.y, Some(Size::Pixels(_))) ||
            minimum_zero::<A::Float>(access.declaration(target(node, true, Kind::Min)))),
    )
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == item(old(access), child), final(access).topology() == old(access).topology(),
        final(access).ready() == old(access).ready(), final(access).wrap_effects() == old(access).wrap_effects(),
        final(access).block_margin_arena() == old(access).block_margin_arena(),
        forall |id: A::Id| #[trigger] final(access).block_record_value(id) == old(access).block_record_value(id),
        forall |id: A::Id| #[trigger] final(access).finish_layout(id) == old(access).finish_layout(id),
    no_unwind
))]
pub(super) fn read_child<A: FlowAccess>(access: &mut A, child: A::Id) -> BlockItem<A::Block> {
    let index = access.block_record(child).block_margin_index::<A::Float>();
    let nested = match index {
        Some(index) => margin_storage::read_margin(access.block_margins().as_slice(), index),
        None => None,
    };
    let params = access.params(child);
    let record = access.block_record(child);
    let [before, after] = params.margin.y;
    let size = cycle_rules::read_slot(&record.values, 1, Kind::Final);
    let adjoining = item_adjoins(A::Float::is_zero(size),
        [A::Float::is_zero(params.padding.y[0]), A::Float::is_zero(params.padding.y[1])],
        params.block_margins_can_collapse(), minimum_zero::<A::Float>(access.declaration(target(child, true, Kind::Min))));
    BlockItem::from_edges(A::lift_block(A::Float::margin(before)), A::lift_block(A::Float::margin(after)),
        A::lift_block(size), adjoining, !record.has_in_flow_children(), nested)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        final(access).wrap_effects() == old(access).wrap_effects(),
        final(access).block_margin_arena() == if explicit::<A>(old(access).block_record_value(node), margins) {
            old(access).block_margin_arena().push(margins)
        } else { old(access).block_margin_arena() },
        final(access).block_record_value(node).flags == old(access).block_record_value(node).flags,
        explicit::<A>(old(access).block_record_value(node), margins)
            && old(access).block_record_value(node).flags.0 & NodeFlags::BLOCK_CONTAINER != 0
            ==> saved_margin::<A::Float, A::Block>(final(access).block_record_value(node), final(access).block_margin_arena()) == Some(margins),
        !explicit::<A>(old(access).block_record_value(node), margins)
            ==> final(access).block_record_value(node) == old(access).block_record_value(node),
    no_unwind
))]
pub(super) fn store<A: FlowAccess>(access: &mut A, node: A::Id, margins: BlockMargins<A::Block>) {
    let record = access.block_record(node);
    let empty = !record.has_in_flow_children();
    if record.flags.is_block_item() && !implicit_edges([
        A::Float::is_zero(A::lower_block(margins.before.positive)), A::Float::is_zero(A::lower_block(margins.before.negative)),
        A::Float::is_zero(A::lower_block(margins.after.positive)), A::Float::is_zero(A::lower_block(margins.after.negative)),
    ], margins.all_through, empty)
    {
        let index = margin_storage::append_margin::<_, A::BlockMemory>(access.block_margins(), margins);
        access.edit_block_record(node).set_block_margin_index::<A::Float>(Some(index));
    }
}
