//! Prepare compatible independent Fill siblings without the general slot walk.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, ChildrenLayout, LayoutParams, Size, X, Y};
use crate::fill_budget;
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::{Pos, node_data::NodeLayoutData};
use crate::node_flags::{NodeFlags, slot_index};
#[cfg(not(verus_keep_ghost))]
use crate::placement_geometry::FloatBounds;
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::placement_geometry::Arrange;
use crate::prepare_frame::FrameFloat;
use crate::prepare_nodes::{Records, StartActions, Summary};
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::prepare_nodes::{install_fixed, seed_pixels};
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::placement_work::PlacementWork;
#[cfg(verus_keep_ghost)]
use crate::placement::kernel::PlacementWork;
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::vec_memory::{CapacityMemory, FallibleVecMemory, VecMemory};
#[cfg(verus_keep_ghost)]
use crate::vec_memory::CapacityModel;
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::Kind;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel::Kind, placement::geometry::{Arrange, FloatBounds}, prepare_frame::Order, prepare_nodes::live, sizing_pass::remaining};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::prepare_nodes::prepare_pair::{pair_marker, ready_pair_records};
#[cfg(verus_keep_ghost)]
use crate::{placement::{node::PlacementLinks, modes::{leaf_path, leaf_path_push}}, prepare_frame::FrameWords};

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn ends_after_pair<I>(order: Order<I>, first: I, next: Option<I>) -> bool {
    match (order.sibling)(first) {
        Some(second) => next == (order.sibling)(second),
        None => false,
    }
}

pub(crate) open spec fn exact_pair<I>(order: Order<I>, parent: I) -> bool {
    crate::placement::node::PlacementLinks::from_order(order).leaf_pair(parent).is_some()
}

pub(crate) open spec fn uniform_size(axis: Axis, width: f32, height: f32, share: f32) -> [f32; 2] {
    if axis is X { [share, height] } else { [width, share] }
}

pub(crate) open spec fn size_words<F: FrameWords>(size: [f32; 2]) -> [u32; 2] {
    [F::word(size[0]), F::word(size[1])]
}

pub(crate) open spec fn final_words<F: FrameFloat>(data: NodeLayoutData) -> [u32; 2] {
    [crate::prepare_frame::pixel_slots::<F>(data.values, X).1, crate::prepare_frame::pixel_slots::<F>(data.values, Y).1]
}

pub(crate) open spec fn uniform_records<T: Records + ?Sized>(tree: &T, rows: Seq<T::Id>, words: [u32; 2]) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> {
        let record = #[trigger] tree.layout_record(rows[i]);
        &&& record.placement == PlacementWork::Clean
        &&& final_words::<T::Float>(record) == words
    }
}

pub(crate) open spec fn visible_roster<I>(order: Order<I>, first: I, rows: Seq<I>, next: Option<I>) -> bool {
    leaf_path(PlacementLinks::from_order(order), |_: I| false, Some(first), rows, next)
}

pub(crate) open spec fn no_margin(params: LayoutParams) -> bool {
    params.margin.x[0].is_zero() && params.margin.x[1].is_zero()
        && params.margin.y[0].is_zero() && params.margin.y[1].is_zero()
}

pub(crate) open spec fn aligned_leaf(params: LayoutParams, cross: Axis) -> bool {
    crate::placement::modes::aligned_start_style(params, cross)
}

pub(crate) open spec fn aligned_roster<T: Records + ?Sized>(tree: &T, rows: Seq<T::Id>, cross: Axis) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> aligned_leaf(#[trigger] tree.layout_params(rows[i]), cross)
}

pub(crate) open spec fn uniform_cache<T: Records + ?Sized>(tree: &T, parent: T::Id, first: T::Id, cross: Axis) -> bool {
    if let Some((owner, size)) = tree.packed_state().uniform_run {
        owner == parent ==> visible_roster(tree.order(), first, tree.packed_state().uniform_ids@, None)
            && uniform_records(tree, tree.packed_state().uniform_ids@, size_words::<T::Float>(size))
            && aligned_roster(tree, tree.packed_state().uniform_ids@, cross)
    } else { true }
}

pub(crate) open spec fn committed_uniform<T: Records + ?Sized>(tree: &T, parent: T::Id) -> bool {
    let workspace = tree.packed_state();
    let params = tree.layout_params(parent);
    &&& workspace.uniform_run.is_some()
    &&& workspace.uniform_run.unwrap().0 == parent
    &&& workspace.uniform_ids@.len() == tree.layout_record(parent).n_placed_children
    &&& workspace.uniform_ids@.len() >= 128
    &&& !params.children_origin_flipped.x && !params.children_origin_flipped.y
    &&& match (params.children_layout, (tree.order().first)(parent)) {
        (ChildrenLayout::Stack { axis, arrange: Arrange::Start, .. }, Some(first)) =>
            uniform_cache(tree, parent, first, axis.other()),
        _ => false,
    }
}

fn save_declaration(params: &LayoutParams) -> (saved: Ghost<LayoutParams>)
    ensures saved@ == *params,
    no_unwind
{ Ghost(*params) }

fn save_ids<I: Copy>(ids: &Vec<I>) -> (out: Ghost<Seq<I>>)
    ensures out@ == ids@,
    no_unwind
{ Ghost(ids@) }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(zero => ensures zero == no_margin(*params), no_unwind))]
fn zero_margins(params: &LayoutParams) -> bool {
    let [left, right] = params.margin.x;
    let [top, bottom] = params.margin.y;
    left.is_zero() && right.is_zero() && top.is_zero() && bottom.is_zero()
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn no_bounds(params: &LayoutParams) -> bool {
    params.min_size.x.is_none() && params.min_size.y.is_none()
        && params.max_size.x.is_none() && params.max_size.y.is_none()
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires tree.order().ordered(), tree.order().child(parent, child),
    ensures next == (tree.order().sibling)(child),
        next.is_some() ==> tree.order().child(parent, next.unwrap()),
        remaining(tree.order(), parent, next) < remaining(tree.order(), parent, Some(child)),
    no_unwind
))]
fn next_child<T: Records + ?Sized>(tree: &T, parent: T::Id, child: T::Id) -> Option<T::Id> {
    let _ = parent;
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(child); }
    tree.sibling(child)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(leaf =>
    requires live(tree, child),
    ensures leaf.is_some() ==> (tree.order().first)(child).is_none()
        && *leaf.unwrap() == tree.layout_params(child)
        && !leaf.unwrap().disabled && !leaf.unwrap().free_placement && no_margin(*leaf.unwrap()),
    no_unwind
))]
fn eligible_leaf<T: Records + ?Sized, const UNIT: bool>(tree: &T, child: T::Id) -> Option<&LayoutParams> {
    let p = tree.params(child);
    if UNIT && T::Float::bits(p.fill_weight) != T::Float::bits(1.0) { return None; }
    if p.disabled || p.free_placement || !matches!((p.size.x, p.size.y), (Size::Fill, Size::Fill))
        || !no_bounds(p) || !zero_margins(p)
        || !matches!(p.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        || p.grid_span.x > 1 || p.grid_span.y > 1
        || (!UNIT && (p.fill_weight <= 0.0 || !T::Float::finite(p.fill_weight)))
        || tree.first(child).is_some()
    {
        return None;
    }
    Some(p)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), parent), old(tree).order().ordered(),
        pair ==> count == 2 && ready_pair_records(old(tree), parent),
    ensures final(tree).order() == old(tree).order(), pair_marker(final(tree), parent) == pair,
        pair ==> ready_pair_records(final(tree), parent),
        final(tree).packed_state() == old(tree).packed_state(),
        final(tree).layout_record(parent).n_placed_children == count,
        final(tree).layout_record(parent).values[crate::cycles::kernel::slot_index(axis.index(), Kind::EvenShare) as int] == share,
        forall|id: T::Id| id != parent ==> #[trigger] final(tree).layout_record(id) == old(tree).layout_record(id),
        forall|id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
    no_unwind
))]
fn finish_parent<T: Records + ?Sized>(
    tree: &mut T, parent: T::Id, axis: Axis, width: f32, height: f32, share: f32, count: u32,
    #[cfg(any(feature = "incremental", verus_keep_ghost))] pair: bool,
) -> Summary {
    let mut data = T::empty_record();
    data.publish_axis(X, width, width, 0);
    data.publish_axis(Y, height, height, 0);
    let share_index = slot_index(axis, Kind::EvenShare);
    data.publish_slot(share_index, share);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { data.levels[share_index] = 2; }
    data.flags.0 |= NodeFlags::FLEX_CHILD_X | NodeFlags::FLEX_CHILD_Y;
    data.n_placed_children = count;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if pair { data.prepared_placement = NodeLayoutData::PREPARED_PAIR; }
    #[cfg(verus_keep_ghost)]
    proof! {
        let marker = data.prepared_placement;
        assert((marker & 2u8 != 0) == pair) by(bit_vector)
            requires marker == if pair { 2u8 } else { 0u8 };
        if pair {
            let (first, second) = crate::placement::node::PlacementLinks::from_order(tree.order()).leaf_pair(parent).unwrap();
            tree.order().node_facts(parent);
            tree.order().node_facts(first);
            assert(first != parent && second != parent);
        }
    }
    *tree.edit(parent) = data;
    Summary { nodes: count.saturating_add(1), needs_solve: false }
}

/// Validate and prepare a large unit-weight group in the same walk.
///
/// The previous count suggests a size. A mismatched count or leaf sends the
/// group through full preparation, which rewrites any provisional records.
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(summary =>
    requires live(old(tree), parent), old(tree).order().ordered(), old(tree).order().child(parent, first),
        0 < expected <= 16_777_216,
        COLLECT ==> old(ids).len() == 0 && T::LeafMemory::capacity(old(ids)) >= expected,
    ensures final(tree).order() == old(tree).order(),
        final(tree).packed_state() == old(tree).packed_state(),
        !COLLECT ==> final(ids)@ == old(ids)@,
        summary.is_some() ==> final(tree).layout_record(parent).n_placed_children == expected,
        forall|id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
        summary.is_some() && COLLECT && final(ids).len() > 0 ==> {
            let share = final(tree).layout_record(parent).values[crate::cycles::kernel::slot_index(axis.index(), Kind::EvenShare) as int];
            &&& aligned_roster(final(tree), final(ids)@, axis.other())
            &&& visible_roster(final(tree).order(), first, final(ids)@, None)
            &&& uniform_records(final(tree), final(ids)@, size_words::<T::Float>(uniform_size(axis, width, height, share)))
            &&& forall|i: int| 0 <= i < final(ids).len() ==> final(tree).order().child(parent, #[trigger] final(ids)@[i])
        },
    no_unwind
))]
fn prepare_unit<T: StartActions + ?Sized, const COLLECT: bool>(
    tree: &mut T, parent: T::Id, first: T::Id, axis: Axis, width: f32, height: f32, expected: u32,
    #[cfg(any(feature = "incremental", verus_keep_ghost))] ids: &mut Vec<T::Id>,
) -> Option<Summary> {
    let (main, cross) = if matches!(axis, Axis::X) { (width, height) } else { (height, width) };
    let share = fill_budget::share(main, 0.0, expected as f32);
    if !T::Float::finite(share) { return None; }
    let mut data = T::empty_record();
    data.publish_axis(axis.other(), cross, cross, 2);
    data.publish_axis(axis, share, share, 3);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(final_words::<T::Float>(data) == size_words::<T::Float>(uniform_size(axis, width, height, share)));
        reveal(leaf_path);
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut aligned = true;
    let mut count = 0;
    let mut next = Some(first);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(), live(tree, parent),
            forall|id: T::Id| #[trigger] tree.layout_params(id) == old(tree).layout_params(id),
            tree.packed_state() == old(tree).packed_state(),
            count <= expected <= 16_777_216, next.is_some() ==> tree.order().child(parent, next.unwrap()),
            COLLECT ==> {
                ids.len() == count && T::LeafMemory::capacity(ids) >= expected
                    && visible_roster(tree.order(), first, ids@, next)
                    && uniform_records(tree, ids@, size_words::<T::Float>(uniform_size(axis, width, height, share)))
            },
            COLLECT ==> forall|i: int| 0 <= i < ids.len() ==> tree.order().child(parent, #[trigger] ids@[i]),
            COLLECT && aligned ==> aligned_roster(tree, ids@, axis.other()),
            !COLLECT ==> ids@ == old(ids)@,
            final_words::<T::Float>(data) == size_words::<T::Float>(uniform_size(axis, width, height, share)),
            data.placement == PlacementWork::Clean,
        ensures next.is_none(),
        decreases remaining(tree.order(), parent, next),
    ))]
    while let Some(child) = next {
        if count == expected { return None; }
        let leaf = eligible_leaf::<T, true>(tree, child)?;
        #[cfg(verus_keep_ghost)]
        let prior = save_ids(ids);
        #[cfg(verus_keep_ghost)]
        let accepted = save_declaration(leaf);
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if COLLECT {
            aligned &= matches!(*leaf.position.component(axis.other()), Pos::Start);
            T::LeafMemory::push_reserved(ids, child);
        }
        let _ = leaf;
        next = next_child(tree, parent, child);
        *tree.edit(child) = data;
        #[cfg(verus_keep_ghost)]
        proof! {
            if COLLECT {
                let links = PlacementLinks::from_order(tree.order());
                leaf_path_push(links, |_: T::Id| false, Some(first), prior@, child);
                let bits = size_words::<T::Float>(uniform_size(axis, width, height, share));
                if aligned {
                    assert(aligned_leaf(accepted@, axis.other()));
                    assert forall|i: int| 0 <= i < ids.len()
                        implies aligned_leaf(#[trigger] tree.layout_params(ids@[i]), axis.other()) by {
                        if i < prior@.len() { assert(prior@[i] == ids@[i]); }
                        else { assert(ids@[i] == child); }
                    };
                }
                assert forall|i: int| 0 <= i < ids.len() implies tree.order().child(parent, #[trigger] ids@[i]) by {
                    if i < prior@.len() { assert(prior@[i] == ids@[i]); }
                    else { assert(ids@[i] == child); }
                };
                assert forall |i: int| 0 <= i < ids@.len() implies {
                    let record = #[trigger] tree.layout_record(ids@[i]);
                    record.placement == PlacementWork::Clean && final_words::<T::Float>(record) == bits
                } by {
                    if ids@[i] != child { assert(prior@[i] == ids@[i]); }
                };
            }
        }
        count += 1;
    }
    if count != expected { return None; }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if COLLECT && !aligned { T::LeafMemory::clear(ids); }
    let summary = finish_parent(tree, parent, axis, width, height, share, count,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] false,
    );
    #[cfg(verus_keep_ghost)]
    proof! {
        if COLLECT && ids.len() > 0 {
            let bits = size_words::<T::Float>(uniform_size(axis, width, height, share));
            assert(visible_roster(tree.order(), first, ids@, None));
            assert forall |i: int| 0 <= i < ids.len() implies {
                let record = #[trigger] tree.layout_record(ids@[i]);
                record.placement == PlacementWork::Clean && final_words::<T::Float>(record) == bits
            } by {
                assert(tree.order().child(parent, ids@[i]));
                assert(ids@[i] != parent);
            };
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if COLLECT && ids.len() > 0 {
            assert(aligned);
            assert(aligned_roster(tree, ids@, axis.other()));
        }
    }
    Some(summary)
}

/// Record just the IDs. Both dimensions are shared by the completed run.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(summary =>
    requires live(old(tree), parent), old(tree).order().ordered(), old(tree).order().child(parent, first),
        0 < expected <= 16_777_216,
        old(tree).packed_state().uniform_run.is_none(),
    ensures final(tree).order() == old(tree).order(),
        final(tree).packed_state().uniform_run.is_some() ==> summary.is_some()
            && final(tree).packed_state().uniform_run.unwrap().0 == parent
            && final(tree).packed_state().uniform_ids@.len() == expected
            && final(tree).layout_record(parent).n_placed_children == expected
            && uniform_cache(final(tree), parent, first, axis.other()),
        forall|id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
    no_unwind
))]
fn prepare_unit_queue<T: StartActions + ?Sized>(
    tree: &mut T, parent: T::Id, first: T::Id, axis: Axis, width: f32, height: f32, expected: u32,
) -> Option<Summary> {
    let mut ids = T::LeafMemory::take(&mut tree.packed_stack_leaves().uniform_ids);
    T::LeafMemory::clear(&mut ids);
    let summary = if T::LeafMemory::try_reserve(&mut ids, expected as usize) {
        prepare_unit::<T, true>(tree, parent, first, axis, width, height, expected, &mut ids)
    } else {
        prepare_unit::<T, false>(tree, parent, first, axis, width, height, expected, &mut ids)
    };
    let size = if summary.is_some() && ids.len() == expected as usize {
        let share = tree.record(parent).values[slot_index(axis, Kind::EvenShare)];
        Some(if matches!(axis, Axis::X) { [share, height] } else { [width, share] })
    } else {
        None
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        if size.is_some() {
            assert(visible_roster(tree.order(), first, ids@, None));
            assert(uniform_records(tree, ids@, size_words::<T::Float>(size.unwrap())));
        }
    }
    return_uniform_ids(tree, parent, ids, size);
    summary
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), parent),
    ensures final(tree).order() == old(tree).order(),
        final(tree).packed_state().uniform_ids@ == if size.is_some() { ids@ } else { Seq::<T::Id>::empty() },
        final(tree).packed_state().uniform_run == if let Some(size) = size {
            Some((parent, size))
        } else { old(tree).packed_state().uniform_run },
        forall|id: T::Id| id != parent ==> #[trigger] final(tree).layout_record(id) == old(tree).layout_record(id),
        final(tree).layout_record(parent).n_placed_children == old(tree).layout_record(parent).n_placed_children,
        forall|id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
    no_unwind
))]
fn return_uniform_ids<T: StartActions + ?Sized>(
    tree: &mut T, parent: T::Id, mut ids: Vec<T::Id>, size: Option<[f32; 2]>,
) {
    if let Some(size) = size {
        tree.packed_stack_leaves().uniform_run = Some((parent, size));
        tree.edit(parent).prepared_placement |= NodeLayoutData::PREPARED_UNIFORM_LEAVES;
    } else {
        T::LeafMemory::clear(&mut ids);
    }
    tree.packed_stack_leaves().uniform_ids = ids;
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(size =>
    ensures size.is_some() ==> aligned_leaf(*params, cross),
        size.is_some() ==> match (params.size.x, params.size.y) {
        (Size::Pixels(x), Size::Pixels(y)) => size == Some([x, y]),
        _ => false,
    },
    no_unwind
))]
fn fixed_size(params: &LayoutParams, cross: Axis) -> Option<[f32; 2]> {
    let (Size::Pixels(width), Size::Pixels(height)) = (params.size.x, params.size.y) else { return None; };
    if params.disabled || params.free_placement || !no_bounds(params) || !zero_margins(params)
        || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        || (params.grid_span.x | params.grid_span.y) > 1
        || !matches!(*params.position.component(cross), Pos::Start)
    {
        return None;
    }
    Some([width, height])
}

/// The ordinary install still preserves compatible fixed records. Only the
/// temporary placement inputs are shared, after checking the current leaf.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(installed =>
    requires live(old(tree), parent), old(tree).order().ordered(), old(tree).order().child(parent, first),
        0 < expected <= 16_777_216, old(ids).len() == 0, T::LeafMemory::capacity(old(ids)) >= expected,
        prepared.placement == PlacementWork::Clean, final_words::<T::Float>(prepared) == bits,
    ensures final(tree).order() == old(tree).order(),
        forall|id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
        final(tree).packed_state() == old(tree).packed_state(),
        installed ==> final(ids).len() == expected,
        installed ==> visible_roster(final(tree).order(), first, final(ids)@, None)
            && uniform_records(final(tree), final(ids)@, bits)
            && aligned_roster(final(tree), final(ids)@, cross),
        installed ==> forall|i: int| 0 <= i < final(ids).len() ==> final(tree).order().child(parent, #[trigger] final(ids)@[i]),
    no_unwind
))]
fn install_fixed_run<T: StartActions + ?Sized>(
    tree: &mut T, parent: T::Id, first: T::Id, cross: Axis, expected: u32,
    bits: [u32; 2], prepared: NodeLayoutData, ids: &mut Vec<T::Id>,
) -> bool {
    let mut count = 0;
    let mut next = Some(first);
    #[cfg(verus_keep_ghost)]
    proof! { reveal(leaf_path); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(), live(tree, parent),
            tree.packed_state() == old(tree).packed_state(),
            forall|id: T::Id| #[trigger] tree.layout_params(id) == old(tree).layout_params(id),
            count <= expected <= 16_777_216, ids.len() == count, T::LeafMemory::capacity(ids) >= expected,
            next.is_some() ==> tree.order().child(parent, next.unwrap()),
            visible_roster(tree.order(), first, ids@, next), uniform_records(tree, ids@, bits),
            aligned_roster(tree, ids@, cross),
            prepared.placement == PlacementWork::Clean, final_words::<T::Float>(prepared) == bits,
            forall|i: int| 0 <= i < ids.len() ==> tree.order().child(parent, #[trigger] ids@[i]),
        ensures next.is_none(),
        decreases remaining(tree.order(), parent, next),
    ))]
    while let Some(child) = next {
        if count == expected { return false; }
        let params = tree.params(child);
        let Some([width, height]) = fixed_size(params, cross) else { return false; };
        if T::Float::bits(width) != bits[0] || T::Float::bits(height) != bits[1] || tree.first(child).is_some() {
            return false;
        }
        #[cfg(verus_keep_ghost)]
        let prior = save_ids(ids);
        next = next_child(tree, parent, child);
        {
            let data = tree.edit(child);
            if !matches!(data.placement, PlacementWork::Clean) { return false; }
            install_fixed::<T::Float>(data, prepared);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(data.placement == PlacementWork::Clean);
                assert(final_words::<T::Float>(*data) == bits);
            }
        }
        T::LeafMemory::push_reserved(ids, child);
        #[cfg(verus_keep_ghost)]
        proof! {
            let links = PlacementLinks::from_order(tree.order());
            let record = tree.layout_record(child);
            assert(aligned_leaf(tree.layout_params(child), cross));
            assert forall|i: int| 0 <= i < ids.len()
                implies aligned_leaf(#[trigger] tree.layout_params(ids@[i]), cross) by {
                if i < prior@.len() { assert(prior@[i] == ids@[i]); }
                else { assert(ids@[i] == child); }
            };
            assert(record.placement == PlacementWork::Clean);
            assert(final_words::<T::Float>(record) == bits);
            leaf_path_push(links, |_: T::Id| false, Some(first), prior@, child);
            assert forall|i: int| 0 <= i < ids.len() implies tree.order().child(parent, #[trigger] ids@[i]) by {
                if i < prior@.len() { assert(prior@[i] == ids@[i]); }
                else { assert(ids@[i] == child); }
            };
            assert forall |i: int| 0 <= i < ids@.len() implies {
                let record = #[trigger] tree.layout_record(ids@[i]);
                record.placement == PlacementWork::Clean && final_words::<T::Float>(record) == bits
            } by {
                if ids@[i] != child { assert(prior@[i] == ids@[i]); }
            };
        }
        count += 1;
    }
    count == expected
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(summary =>
    requires live(old(tree), parent), old(tree).order().ordered(), old(tree).order().child(parent, first),
        0 < expected <= 16_777_216,
    ensures final(tree).order() == old(tree).order(),
        summary.is_some() ==> final(tree).packed_state().uniform_run.is_some()
            && final(tree).packed_state().uniform_run.unwrap().0 == parent
            && final(tree).packed_state().uniform_ids@.len() == expected
            && final(tree).layout_record(parent).n_placed_children == expected
            && uniform_cache(final(tree), parent, first, cross),
        summary.is_none() ==> final(tree).packed_state().uniform_run == old(tree).packed_state().uniform_run,
        forall|id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
    no_unwind
))]
fn prepare_fixed_queue<T: StartActions + ?Sized>(
    tree: &mut T, parent: T::Id, first: T::Id, cross: Axis, expected: u32,
) -> Option<Summary> {
    let params = tree.params(first);
    let size = fixed_size(params, cross)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(crate::prepare_frame::pixel_decl(*params, X) == Some(size[0]));
        assert(crate::prepare_frame::pixel_decl(*params, Y) == Some(size[1]));
    }
    if tree.first(first).is_some() { return None; }
    let mut leaf = T::empty_record();
    if !seed_pixels::<T::Float>(&mut leaf, params, false, None) { return None; }
    let mut parent_record = T::empty_record();
    if !seed_pixels::<T::Float>(&mut parent_record, tree.params(parent), false, None) { return None; }
    let workspace = tree.packed_stack_leaves();
    if !workspace.uniform_capture_open || workspace.uniform_run.is_some() || tree.stack_leaf_hint().is_none() {
        return None;
    }
    let mut ids = T::LeafMemory::take(&mut tree.packed_stack_leaves().uniform_ids);
    T::LeafMemory::clear(&mut ids);
    let bits = [T::Float::bits(size[0]), T::Float::bits(size[1])];
    #[cfg(verus_keep_ghost)]
    proof! { assert(final_words::<T::Float>(leaf) == bits); }
    let prepared = T::LeafMemory::try_reserve(&mut ids, expected as usize)
        && install_fixed_run(tree, parent, first, cross, expected, bits, leaf, &mut ids);
    if prepared {
        parent_record.n_placed_children = expected;
        *tree.edit(parent) = parent_record;
        return_uniform_ids(tree, parent, ids, Some(size));
        Some(Summary { nodes: expected.saturating_add(1), needs_solve: false })
    } else {
        return_uniform_ids(tree, parent, ids, None);
        None
    }
}

/// Read both leaves before publishing their records. The previous result
/// selects this path, but the current sibling chain determines eligibility.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), parent), old(tree).order().ordered(), old(tree).order().child(parent, first),
        (old(tree).order().first)(parent) == Some(first),
    ensures final(tree).order() == old(tree).order(),
        final(tree).packed_state() == old(tree).packed_state(),
        forall|id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
        result.is_some() && pair_marker(final(tree), parent) ==> ready_pair_records(final(tree), parent),
    no_unwind
))]
fn prepare_two<T: Records + ?Sized>(
    tree: &mut T, parent: T::Id, first: T::Id, axis: Axis, width: f32, height: f32,
) -> Option<Summary> {
    let second = next_child(tree, parent, first)?;
    if next_child(tree, parent, second).is_some() { return None; }
    let a = eligible_leaf::<T, false>(tree, first)?;
    let b = eligible_leaf::<T, false>(tree, second)?;
    #[cfg(verus_keep_ghost)]
    proof! {
        tree.order().node_facts(first);
        assert(second != first);
        assert(exact_pair(tree.order(), parent));
    }
    let aw = a.fill_weight;
    let bw = b.fill_weight;
    let total = (0.0 + aw) + bw;
    let (main, cross) = if matches!(axis, Axis::X) { (width, height) } else { (height, width) };
    let share = fill_budget::share(main, 0.0, total);
    let asize = share * aw;
    let bsize = share * bw;
    if !T::Float::finite(total) || !T::Float::finite(asize) || !T::Float::finite(bsize) { return None; }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let pair = matches!(*a.position.component(axis.other()), Pos::Start)
        && matches!(*b.position.component(axis.other()), Pos::Start);

    let mut data = T::empty_record();
    data.publish_axis(axis.other(), cross, cross, 2);
    data.publish_axis(axis, asize, asize, 3);
    *tree.edit(first) = data;
    data.publish_axis(axis, bsize, bsize, 3);
    *tree.edit(second) = data;
    Some(finish_parent(tree, parent, axis, width, height, share, 2,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] pair,
    ))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(summary =>
    requires live(old(tree), parent), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
        old(tree).packed_state().uniform_run.is_none() && final(tree).packed_state().uniform_run.is_some()
            ==> summary.is_some() && committed_uniform(final(tree), parent),
    no_unwind
))]
pub(crate) fn try_prepare<T: StartActions + ?Sized, const REGISTERED_PIXELS: bool>(tree: &mut T, parent: T::Id) -> Option<Summary> {
    let params = tree.params(parent);
    let ChildrenLayout::Stack { axis, spacing, arrange } = params.children_layout else { return None; };
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let forward = !params.children_origin_flipped.x && !params.children_origin_flipped.y
        && matches!(arrange, Arrange::Start);
    #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
    let _ = arrange;
    let (Size::Pixels(width), Size::Pixels(height)) = (params.size.x, params.size.y) else { return None; };
    let [left, right] = params.padding.x;
    let [top, bottom] = params.padding.y;
    if spacing != 0.0 || left != 0.0 || right != 0.0 || top != 0.0 || bottom != 0.0 || !no_bounds(params)
        || width <= 0.0 || height <= 0.0 || !T::Float::finite(width) || !T::Float::finite(height)
    {
        return None;
    }
    let first = tree.first(parent)?;
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(parent); }
    let first_size = tree.params(first).size;
    if !matches!((first_size.x, first_size.y), (Size::Fill, Size::Fill)) {
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if !REGISTERED_PIXELS && forward
            && matches!((first_size.x, first_size.y), (Size::Pixels(_), Size::Pixels(_)))
        {
            let expected = tree.stack_leaf_count_hint(parent);
            if expected >= 128 && expected <= 16_777_216 {
                return prepare_fixed_queue(tree, parent, first, axis.other(), expected);
            }
        }
        return None;
    }
    let expected = tree.stack_leaf_count_hint(parent);
    if expected == 2 {
        if let Some(summary) = prepare_two(tree, parent, first, axis, width, height) {
            return Some(summary);
        }
    }
    // Summing unit weights up to 2^24 is exact in binary32.
    if expected >= 128 && expected <= 16_777_216 {
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let capture = if forward && matches!(eligible_leaf::<T, true>(tree, first),
            Some(leaf) if matches!(*leaf.position.component(axis.other()), Pos::Start))
        {
            let workspace = tree.packed_stack_leaves();
            workspace.uniform_capture_open && workspace.uniform_run.is_none() && tree.stack_leaf_hint().is_some()
        } else { false };
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let prepared = if capture { prepare_unit_queue(tree, parent, first, axis, width, height, expected) }
            else { prepare_unit::<T, false>(tree, parent, first, axis, width, height, expected, &mut T::LeafMemory::empty()) };
        #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
        let prepared = prepare_unit::<T, false>(tree, parent, first, axis, width, height, expected);
        if prepared.is_some() { return prepared; }
    }
    let mut next = Some(first);
    let mut total = 0.0;
    let mut max_weight = 0.0;
    let mut count = 0u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(),
            old(tree).packed_state().uniform_run.is_none() ==> tree.packed_state().uniform_run.is_none(), tree.order().child(parent, first),
            (tree.order().first)(parent) == Some(first),
            count == 0 ==> next == Some(first),
            count == 1 ==> next == (tree.order().sibling)(first),
            count == 2 ==> ends_after_pair(tree.order(), first, next),
            count >= 1 ==> (tree.order().first)(first).is_none(),
            count >= 2 ==> (tree.order().sibling)(first).is_some()
                && (tree.order().first)((tree.order().sibling)(first).unwrap()).is_none(),
            next.is_some() ==> tree.order().child(parent, next.unwrap()),
        ensures next.is_none(), count == 2 ==> exact_pair(tree.order(), parent),
        decreases remaining(tree.order(), parent, next),
    ))]
    while let Some(child) = next {
        let weight = eligible_leaf::<T, false>(tree, child)?.fill_weight;
        count = count.saturating_add(1);
        total += weight;
        max_weight = T::Float::max(max_weight, weight);
        next = next_child(tree, parent, child);
    }
    let (main, cross) = if matches!(axis, Axis::X) { (width, height) } else { (height, width) };
    let share = fill_budget::share(main, 0.0, total);
    if !T::Float::finite(total) || !T::Float::finite(share * max_weight) { return None; }

    // The parent starts at levels 0/1. Its EvenShare reads its Final, then
    // each leaf Regular reads EvenShare and its Final reads Regular.
    let mut base = T::empty_record();
    base.publish_axis(axis.other(), cross, cross, 2);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut pair = count == 2;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let cross_axis = axis.other();
    let mut next = Some(first);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(),
            old(tree).packed_state().uniform_run.is_none() ==> tree.packed_state().uniform_run.is_none(), live(tree, parent),
            tree.order().child(parent, first), (tree.order().first)(parent) == Some(first),
            base.placement == PlacementWork::Clean,
            next.is_some() ==> tree.order().child(parent, next.unwrap()),
            pair ==> count == 2 && exact_pair(tree.order(), parent),
            pair && next != Some(first) ==> tree.layout_record(first).placement == PlacementWork::Clean,
            pair && next.is_none() ==> tree.layout_record((tree.order().sibling)(first).unwrap()).placement == PlacementWork::Clean,
            pair ==> next.is_none() || next == Some(first) || next == (tree.order().sibling)(first),
        ensures next.is_none(),
        decreases remaining(tree.order(), parent, next),
    ))]
    while let Some(child) = next {
        #[cfg(verus_keep_ghost)]
        proof! {
            if pair && child != first {
                tree.order().node_facts(first);
                assert((tree.order().sibling)(first) == Some(child));
                assert(tree.layout_record(first).placement == PlacementWork::Clean);
            }
        }
        let params = tree.params(child);
        let value = share * params.fill_weight;
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        { pair = pair && matches!(*params.position.component(cross_axis), Pos::Start); }
        let mut data = base;
        data.publish_axis(axis, value, value, 3);
        #[cfg(verus_keep_ghost)]
        proof! { assert(data.placement == PlacementWork::Clean); }
        *tree.edit(child) = data;
        #[cfg(verus_keep_ghost)]
        proof! { assert(tree.layout_record(child).placement == PlacementWork::Clean); }
        next = next_child(tree, parent, child);
        #[cfg(verus_keep_ghost)]
        proof! {
            if pair {
                let second = (tree.order().sibling)(first).unwrap();
                assert((tree.order().sibling)(second).is_none());
                assert(child == first || child == second);
                if child == first {
                    assert(next == Some(second));
                    assert(tree.layout_record(first).placement == PlacementWork::Clean);
                } else {
                    assert(next.is_none());
                    assert(tree.layout_record(first).placement == PlacementWork::Clean);
                    assert(tree.layout_record(second).placement == PlacementWork::Clean);
                }
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if pair {
            assert(next.is_none());
            let links = crate::placement::node::PlacementLinks::from_order(tree.order());
            let (a, b) = links.leaf_pair(parent).unwrap();
            assert(a == first && (tree.order().sibling)(first) == Some(b));
            assert(tree.layout_record(a).placement == PlacementWork::Clean);
            assert(tree.layout_record(b).placement == PlacementWork::Clean);
            assert(ready_pair_records(tree, parent));
        }
    }
    Some(finish_parent(tree, parent, axis, width, height, share, count,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] pair,
    ))
}

#[cfg(all(test, feature = "incremental", not(verus_keep_ghost)))]
#[test]
fn uniform_leaf_queue_preserves_order_and_both_rectangles() {
    use crate::{LayoutData, TreeAdapter, Xy, XyRect, place::Place, sizing_pass, vec_memory::RustVec};

    const LEAVES: usize = 128;

    #[derive(Clone)]
    struct Fixture {
        params: [LayoutParams; 2],
        records: Vec<NodeLayoutData>,
        layout: LayoutData<usize>,
        writes: Vec<(usize, [u32; 4], [u32; 4])>,
    }

    fn words(rect: XyRect) -> [u32; 4] {
        [rect.x[0], rect.x[1], rect.y[0], rect.y[1]].map(f32::to_bits)
    }

    impl TreeAdapter for Fixture {
        type NodeId = usize;
        fn root(&self) -> usize { 0 }
        fn parent(&self, node: usize) -> Option<usize> { (node != 0).then_some(0) }
        fn first_child(&self, node: usize) -> Option<usize> { (node == 0).then_some(1) }
        fn next_sibling(&self, node: usize) -> Option<usize> { (node > 0 && node < LEAVES).then_some(node + 1) }
        fn node_layout_params(&self, node: usize) -> &LayoutParams { &self.params[usize::from(node != 0)] }
        fn node_layout_data(&self, node: usize) -> &NodeLayoutData { &self.records[node] }
        fn node_layout_data_mut(&mut self, node: usize) -> &mut NodeLayoutData { &mut self.records[node] }
        fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }
        fn write_output_rect(&mut self, node: usize, absolute: XyRect, local: XyRect) {
            self.writes.push((node, words(absolute), words(local)));
        }
    }

    for (axis, fixed) in [(X, false), (Y, false), (X, true), (Y, true)] {
        let parent = LayoutParams {
            size: Xy::new(Size::Pixels(95.0), Size::Pixels(103.25)),
            children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: -0.0 },
            padding: Xy::new_symm([-0.0, 0.0]),
            ..LayoutParams::DEFAULT
        };
        let leaf = LayoutParams {
            position: Xy::new_symm(Pos::Start),
            size: if fixed { Xy::new(Size::Pixels(-0.0), Size::Pixels(5.75)) } else { Xy::new_symm(Size::Fill) },
            ..LayoutParams::DEFAULT
        };
        let mut tree = Fixture {
            params: [parent, leaf], records: vec![NodeLayoutData::new(); LEAVES + 1],
            layout: LayoutData::new(), writes: Vec::new(),
        };
        tree.records[0].n_placed_children = LEAVES as u32;
        if fixed {
            let mut dirty = tree.clone();
            dirty.records[LEAVES].placement = PlacementWork::Subtree;
            dirty.layout.packed_stack_leaves.clear::<RustVec>();
            sizing_pass::measure_full::<_, RustVec, false>(&mut dirty, Xy::new(190.0, 350.0));
            assert!(dirty.layout.packed_stack_leaves.uniform_run.is_none());
        }
        tree.layout.packed_stack_leaves.clear::<RustVec>();
        sizing_pass::measure_full::<_, RustVec, false>(&mut tree, Xy::new(190.0, 350.0));
        assert_eq!(tree.layout.packed_stack_leaves.uniform_ids.len(), LEAVES);
        let mut ordinary = tree.clone();

        tree.place_nodes_with::<false>(true);
        ordinary.place_nodes_with::<false>(true);
        assert_eq!(tree.writes.len(), LEAVES + 1);
        assert_eq!(tree.writes, ordinary.writes);
        assert!(tree.layout.packed_stack_leaves.uniform_run.is_none());
    }
}
