//! Prepare runs of percentage and aspect-ratio leaves under fixed stacks.
#![allow(unexpected_cfgs)]

use crate::declarations::{ChildrenLayout, LayoutParams, Size, X, Y};
use crate::node_flags::{NodeFlags, slot_index};
use crate::prepare_frame::FrameFloat;
use crate::prepare_leaf::aspect_size;
use crate::prepare_nodes::{StartActions, Summary};
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::{Pos, packed_stack_leaf::PreparedStackLeaf, vec_memory::try_append};
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use super::{reserve_leaf_rows, finish_leaf_rows};
#[cfg(not(verus_keep_ghost))]
use crate::solve::{cycle_rules::Kind, sizing_finish::{inner, padding}};
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel::{Kind, N_SLOTS}, dependencies::sizing_finish::{inner, padding},
    prepare_nodes::live, sizing_pass::remaining};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn no_bounds(params: &LayoutParams) -> bool {
    params.min_size.x.is_none() & params.min_size.y.is_none()
        & params.max_size.x.is_none() & params.max_size.y.is_none()
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), parent), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
pub(crate) fn try_prepare<T: StartActions + ?Sized>(tree: &mut T, parent: T::Id) -> Option<Summary> {
    let params = tree.params(parent);
    let ChildrenLayout::Stack { axis, spacing, .. } = params.children_layout else { return None; };
    let (Size::Pixels(width), Size::Pixels(height)) = (params.size.x, params.size.y) else { return None; };
    if !no_bounds(params) || !T::Float::finite(width) || !T::Float::finite(height) { return None; }
    let first = tree.first(parent)?;
    let available = match axis {
        X => inner::<T::Float>(height, padding(params, Y)),
        Y => inner::<T::Float>(width, padding(params, X)),
    };
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(parent); }
    match axis {
        X => prepare::<T, false>(tree, parent, first, width, height, available, spacing),
        Y => prepare::<T, true>(tree, parent, first, width, height, available, spacing),
    }
}

/// A rejected prefix is rebuilt by the ordinary full preparation.
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), parent), old(tree).order().ordered(), old(tree).order().child(parent, first),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn prepare<T: StartActions + ?Sized, const VERTICAL: bool>(
    tree: &mut T, parent: T::Id, first: T::Id, width: f32, height: f32, available: f32, _spacing: f32,
) -> Option<Summary> {
    let main = if VERTICAL { Y } else { X };
    let cross = main.other();
    let mut record = T::empty_record();
    record.publish_axis(main, 0.0, 0.0, 4);
    record.publish_axis(cross, 0.0, 0.0, 2);
    let main_regular = slot_index(main, Kind::Regular);
    let main_final = slot_index(main, Kind::Final);
    let cross_regular = slot_index(cross, Kind::Regular);
    let cross_final = slot_index(cross, Kind::Final);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let expected = tree.record(parent).n_placed_children;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut rows: Option<(u32, u32)> = None;
    let mut next = Some(first);
    let mut count = 0u32;
    let mut flags = NodeFlags::flex_child(cross);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(), live(tree, parent),
            next.is_some() ==> tree.order().child(parent, next.unwrap()),
            main_regular < N_SLOTS, main_final < N_SLOTS, cross_regular < N_SLOTS, cross_final < N_SLOTS,
            rows.is_some() ==> rows.unwrap().0 <= rows.unwrap().1,
        decreases remaining(tree.order(), parent, next),
    ))]
    while let Some(child) = next {
        #[cfg(verus_keep_ghost)]
        proof! { tree.order().node_facts(child); }
        let params = tree.params(child);
        let (Size::Frac(fraction), Size::AspectRatio(ratio)) = (*params.size.component(cross), *params.size.component(main))
            else { return None; };
        let unsupported = params.disabled | params.free_placement | !no_bounds(params)
            | !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. });
        if unsupported || tree.first(child).is_some() { return None; }
        let cross_size = T::Float::multiply(available, fraction);
        let main_size = aspect_size::<T::Float>(main, cross_size, ratio);
        if !T::Float::finite(cross_size) | !T::Float::finite(main_size) { return None; }
        if (params.grid_span.x | params.grid_span.y) > 1 { flags |= NodeFlags::GRID_SPANS; }
        record.values[cross_regular] = cross_size;
        record.values[cross_final] = cross_size;
        record.values[main_regular] = main_size;
        record.values[main_final] = main_size;
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let row = if count < expected && !params.has_auto_margin(main) && matches!(*params.position.component(cross), Pos::Start) {
            let [leading, trailing] = *params.margin.component(main);
            let [cross_leading, _] = *params.margin.component(cross);
            let trailing = T::Float::margin(trailing);
            let footprint = if trailing == 0.0 { main_size } else { main_size + trailing };
            Some(PreparedStackLeaf {
                id: child,
                size: if VERTICAL { [cross_size, main_size] } else { [main_size, cross_size] },
                main_leading: T::Float::margin(leading),
                advance: footprint + _spacing,
                cross_leading: T::Float::margin(cross_leading),
            })
        } else { None };
        next = tree.sibling(child);
        *tree.edit(child) = record;
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if let Some(row) = row {
            if count == 0 { rows = reserve_leaf_rows(tree, parent, expected); }
            if rows.is_some() && !try_append::<_, T::LeafMemory>(&mut tree.packed_stack_leaves().rows, row) {
                rows = None;
            }
        } else { rows = None; }
        count = count.saturating_add(1);
    }

    let mut parent_record = T::empty_record();
    parent_record.publish_axis(X, width, width, 0);
    parent_record.publish_axis(Y, height, height, 0);
    parent_record.flags.0 |= flags;
    parent_record.n_placed_children = count;
    *tree.edit(parent) = parent_record;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    finish_leaf_rows(tree, parent, rows, count);
    Some(Summary { nodes: count.saturating_add(1), needs_solve: false })
}
