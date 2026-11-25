//! Prepare a Wrap parent whose children already have independent main sizes.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, ChildrenLayout, LayoutParams, Size};
use crate::node_data::NodeLayoutData;
use crate::node_flags::{NodeFlags, slot_index};
use crate::prepare_frame::FrameFloat;
use crate::prepare_nodes::Records;
use crate::prepare_nodes::StartActions;
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::{
    packed_stack_leaf::{PreparedStackLeaf, StackLeafGroup},
    vec_memory::{FallibleVecMemory, VecMemory, try_append},
};
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::placement_geometry::Arrange;
#[cfg(verus_keep_ghost)]
use crate::placement::geometry::Arrange;

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::placement_geometry::Pos;
#[cfg(not(verus_keep_ghost))]
use crate::{flow::{wrap_lines, wrap_metrics}, placement_geometry::FloatBounds, solve::cycle_rules};
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::solve::dependency_rules;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, dependencies::rules as dependency_rules,
    placement::geometry::{FloatBounds, Pos}, prepare_nodes::live,
    wrap_lines::kernel as wrap_lines, wrap_metrics::kernel as wrap_metrics};
use cycle_rules::{Kind, SOLVED, UNSOLVED};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::prepare_frame::FrameWords;
#[cfg(verus_keep_ghost)]
use crate::placement::{modes, node::{PlacementLinks, finite_from_order}};

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) closed spec fn hidden<T: Records + ?Sized>(tree: &T) -> spec_fn(T::Id) -> bool {
    |id: T::Id| tree.layout_params(id).disabled
}

pub(crate) open spec fn enabled_wrap_children<T: Records + ?Sized>(tree: &T, parent: T::Id) -> bool {
    let links = PlacementLinks::from_order(tree.order());
    modes::enabled_siblings(links, hidden(tree), links.first(parent))
}

fn wrap_projection<T: Records + ?Sized>(tree: &T)
    -> (view: Ghost<(PlacementLinks<T::Id>, spec_fn(T::Id) -> bool)>)
    ensures view@ == (PlacementLinks::from_order(tree.order()), hidden(tree)),
    no_unwind
{
    Ghost((PlacementLinks::from_order(tree.order()), hidden(tree)))
}

fn start_accepted<I>() -> (accepted: Ghost<Seq<I>>)
    ensures accepted@ =~= Seq::<I>::empty(),
    no_unwind
{ Ghost(Seq::empty()) }

fn accept<I>(prior: Ghost<Seq<I>>, child: I) -> (accepted: Ghost<Seq<I>>)
    ensures accepted@ == prior@.push(child),
    no_unwind
{ Ghost(prior@.push(child)) }

proof fn same_wrap_visibility<T: Records + ?Sized>(before: &T, after: &T)
    requires forall |id: T::Id| #[trigger] after.layout_params(id) == before.layout_params(id),
    ensures hidden(before) == hidden(after),
{
    reveal(hidden);
    assert forall |id: T::Id| #[trigger] (hidden(after))(id) == (hidden(before))(id) by {
        assert(after.layout_params(id) == before.layout_params(id));
    };
    assert(hidden(after) =~= hidden(before));
}

pub(crate) open spec fn cursor<T: Records + ?Sized>(tree: &T, parent: T::Id, child: Option<T::Id>) -> bool {
    child.is_some() ==> tree.order().child(parent, child.unwrap())
}

pub(crate) open spec fn remaining<T: Records + ?Sized>(tree: &T, parent: T::Id, child: Option<T::Id>) -> int {
    match child {
        Some(child) => (tree.order().interval)(parent).1 - (tree.order().interval)(child).0,
        None => 0,
    }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires tree.order().ordered(), live(tree, parent),
    ensures cursor(tree, parent, next), next == (tree.order().first)(parent),
    no_unwind
))]
fn first<T: Records + ?Sized>(tree: &T, parent: T::Id) -> Option<T::Id> {
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(parent); }
    tree.first(parent)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires tree.order().ordered(), live(tree, parent), cursor(tree, parent, Some(child)),
    ensures cursor(tree, parent, next), remaining(tree, parent, next) < remaining(tree, parent, Some(child)),
        next == (tree.order().sibling)(child),
    no_unwind
))]
fn following<T: Records + ?Sized>(tree: &T, parent: T::Id, child: T::Id) -> Option<T::Id> {
    let _ = parent;
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(child); }
    tree.sibling(child)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn margin<F: FrameFloat>(params: &LayoutParams, axis: Axis) -> f32 {
    let [start, end] = *params.margin.component(axis);
    F::margin(start) + F::margin(end)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn with_margin(size: f32, margin: f32) -> f32 { if margin == 0.0 { size } else { size + margin } }

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn independent(params: &LayoutParams, axis: Axis) -> bool {
    params.min_size.component(axis).is_none() && params.max_size.component(axis).is_none()
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn starts_on_cross(params: &LayoutParams, cross: Axis) -> bool {
    let [left, right] = params.margin.x;
    let [top, bottom] = params.margin.y;
    matches!(params.position.component(cross), Pos::Start)
        && left.is_zero() && right.is_zero() && top.is_zero() && bottom.is_zero()
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tree).order().ordered(), live(old(tree), parent), cursor(old(tree), parent, next),
    ensures final(tree).order() == old(tree).order(),
        forall |id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
    no_unwind
))]
fn store<T: Records + ?Sized>(tree: &mut T, parent: T::Id, mut next: Option<T::Id>, mut count: u32, cross: Axis, extent: f32, level: u16, has_fills: bool) -> bool {
    let bits = T::Float::bits(extent);
    let mut ready = true;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(),
            forall |id: T::Id| #[trigger] tree.layout_params(id) == old(tree).layout_params(id),
            live(tree, parent), cursor(tree, parent, next),
        decreases count,
    ))]
    while count != 0 {
        let Some(child) = next else { return false; };
        next = following(tree, parent, child);
        count -= 1;
        let size = if has_fills {
            let params = tree.params(child);
            if matches!(params.size.component(cross), Size::Fill) {
                let margin = margin::<T::Float>(params, cross);
                Some(if margin == 0.0 { extent } else { T::Float::max(extent - margin, 0.0) })
            } else { None }
        } else { None };
        let data = tree.edit(child);
        data.set_wrap_metric(wrap_metrics::Metric::Cross, bits);
        if let Some(size) = size {
            if T::Float::finite(size) { data.publish_axis(cross, size, size, level); }
            else { ready = false; }
        }
    }
    ready
}

/// A ready run has no main-axis Fill requests or nonlocal cross declarations.
/// Before writing any line starts or extents, check every child in the run.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tree).order().ordered(), live(old(tree), parent),
    ensures final(tree).order() == old(tree).order(),
        forall |id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
        old(data).prepared_placement & NodeLayoutData::PREPARED_WRAP_START == 0
            && final(data).prepared_placement & NodeLayoutData::PREPARED_WRAP_START != 0
                ==> enabled_wrap_children(final(tree), parent),
    no_unwind
))]
pub(crate) fn try_prepare<T: Records + ?Sized>(tree: &mut T, parent: T::Id, data: &mut NodeLayoutData) {
    if data.n_placed_children < 4 || data.n_placed_children == u32::MAX || data.flags.is_block_item() { return; }
    let params = tree.params(parent);
    let ChildrenLayout::Wrap { axis, spacing, line_spacing, .. } = params.children_layout else { return; };
    let cross = axis.other();
    if !matches!(params.size.component(cross), Size::FitContent | Size::Auto)
        || !matches!(params.size.component(axis), Size::Pixels(_))
        || data.flags.check_state(axis, Kind::Final) != SOLVED
        || !independent(params, axis) || !independent(params, cross)
        || !T::Float::finite(spacing) || !T::Float::finite(line_spacing)
    {
        return;
    }
    let [pad_start, pad_end] = *params.padding.component(axis);
    let main_final = slot_index(axis, Kind::Final);
    let cross_regular = slot_index(cross, Kind::Regular);
    let limit = T::Float::max(data.values[main_final] - (pad_start + pad_end), 0.0);
    if !T::Float::finite(limit) { return; }
    let head = first(tree, parent);
    let mut next = head;
    #[cfg(verus_keep_ghost)]
    let mut accepted = start_accepted::<T::Id>();
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(modes::leaf_path);
        finite_from_order(tree.order());
    }
    let mut children = 0u32;
    let mut has_fills = false;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut direct_start = true;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut share_level = dependency_rules::next_level(data.levels[main_final]);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut cross_level = 0;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order().ordered(), live(tree, parent), cursor(tree, parent, next),
            tree.order() == old(tree).order(),
            forall |id: T::Id| #[trigger] tree.layout_params(id) == old(tree).layout_params(id),
            modes::leaf_path(PlacementLinks::from_order(old(tree).order()), hidden(old(tree)), head, accepted@, next),
            main_final < cycle_rules::N_SLOTS, cross_regular < cycle_rules::N_SLOTS,
        ensures next.is_none(),
        decreases remaining(tree, parent, next),
    ))]
    while let Some(child) = next {
        next = following(tree, parent, child);
        let params = tree.params(child);
        if params.disabled || params.free_placement
            || !matches!(params.size.component(axis), Size::Pixels(_))
            || !matches!(params.size.component(cross), Size::Pixels(_) | Size::Fill)
            || !independent(params, axis) || !independent(params, cross)
            || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
            || tree.first(child).is_some()
        { return; }
        #[cfg(verus_keep_ghost)]
        proof! {
            let links = PlacementLinks::from_order(old(tree).order());
            reveal(hidden);
            assert(!(hidden(old(tree)))(child));
            modes::leaf_path_push(links, hidden(old(tree)), head, accepted@, child);
        }
        #[cfg(verus_keep_ghost)]
        { accepted = accept(accepted, child); }
        let record = tree.record(child);
        let fill = matches!(params.size.component(cross), Size::Fill);
        if record.flags.check_state(axis, Kind::Final) != SOLVED
            || (fill && (record.flags.check_state(cross, Kind::Regular) != UNSOLVED
                || record.flags.check_state(cross, Kind::Final) != UNSOLVED))
            || (!fill && (record.flags.check_state(cross, Kind::Regular) != SOLVED
                || record.flags.check_state(cross, Kind::Final) != SOLVED))
        { return; }
        has_fills |= fill;
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        { direct_start &= starts_on_cross(params, cross); }
        let base = with_margin(record.values[main_final], margin::<T::Float>(params, axis));
        let preferred = if fill { 0.0 } else { record.values[cross_regular] };
        let rise = with_margin(preferred, margin::<T::Float>(params, cross));
        if !T::Float::finite(base) || !T::Float::finite(rise) { return; }
        children = children.saturating_add(1);
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        {
            share_level = dependency_rules::include_level(share_level, record.levels[main_final]);
            if !fill { cross_level = dependency_rules::include_level(cross_level, record.levels[cross_regular]); }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let links = PlacementLinks::from_order(old(tree).order());
        assert(next.is_none());
        assert(modes::consistent_cursor(links, head));
        modes::complete_leaf_path_is_enabled(links, hidden(old(tree)), head, accepted@);
    }
    if children != data.n_placed_children { return; }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let flow_level = dependency_rules::include_level(cross_level, share_level);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let fill_level = dependency_rules::next_level(flow_level);
    #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
    let fill_level = 0;

    let mut head_of_line = head;
    let mut next = head;
    let mut count = 0u32;
    let mut width = 0.0;
    let mut height = 0.0;
    let mut total = 0.0;
    let mut all_ready = true;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(),
            forall |id: T::Id| #[trigger] tree.layout_params(id) == old(tree).layout_params(id),
            live(tree, parent), cursor(tree, parent, next), cursor(tree, parent, head_of_line),
            main_final < cycle_rules::N_SLOTS, cross_regular < cycle_rules::N_SLOTS,
        decreases remaining(tree, parent, next),
    ))]
    while let Some(child) = next {
        next = following(tree, parent, child);
        let params = tree.params(child);
        let record = tree.record(child);
        let base = with_margin(record.values[main_final], margin::<T::Float>(params, axis));
        let preferred = if matches!(params.size.component(cross), Size::Fill) { 0.0 } else { record.values[cross_regular] };
        let rise = with_margin(preferred, margin::<T::Float>(params, cross));
        let combined = if count == 0 { base } else { wrap_lines::extend_main(width, spacing, base) };
        if count != 0 && wrap_lines::beyond_limit(combined, limit) {
            let flags = &mut tree.edit(child).flags.0;
            #[cfg(verus_keep_ghost)]
            proof! { assert(NodeFlags::WRAP_LINE_START != 0) by(compute); }
            *flags = wrap_metrics::mark_start(*flags, NodeFlags::WRAP_LINE_START);
            all_ready &= store(tree, parent, head_of_line, count, cross, height, fill_level, has_fills);
            head_of_line = Some(child);
            total += height;
            total += line_spacing;
            width = base;
            height = T::Float::max(0.0, rise);
            count = 1;
        } else {
            width = combined;
            height = T::Float::max(height, rise);
            count = count.saturating_add(1);
        }
    }
    all_ready &= store(tree, parent, head_of_line, count, cross, height, fill_level, has_fills);
    total += height;
    #[cfg(verus_keep_ghost)]
    proof! { same_wrap_visibility(old(tree), tree); }
    if all_ready {
        data.flags.0 &= !NodeFlags::DESCENDANTS_NEED_SOLVE;
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        {
            data.prepared_placement |= NodeLayoutData::PREPARED_WRAP;
            if direct_start { data.prepared_placement |= NodeLayoutData::PREPARED_WRAP_START; }
        }
    }
    data.publish_slot(slot_index(axis, Kind::EvenShare), 0.0);
    data.publish_slot(slot_index(cross, Kind::Flow), total);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    {
        data.levels[slot_index(axis, Kind::EvenShare)] = share_level;
        data.levels[slot_index(cross, Kind::Flow)] = flow_level;
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
struct PackedRun<I> {
    rows: Vec<PreparedStackLeaf<I>>,
    start: u32,
    recording: bool,
}

#[cfg(verus_keep_ghost)]
verus! {
spec fn admitted<I: Copy>(order: crate::prepare_frame::Order<I>, parent: I, run: &Option<PackedRun<I>>) -> bool {
    if let Some(run) = run {
        &&& run.start <= run.rows.len()
        &&& forall |i: int| run.start <= i < run.rows.len() ==>
            order.child(parent, (#[trigger] run.rows@[i]).id)
    } else { true }
}

spec fn recording<I: Copy>(run: &Option<PackedRun<I>>) -> bool {
    match run { Some(run) => run.recording, None => false }
}

spec fn run_ids<I: Copy>(run: &Option<PackedRun<I>>) -> Seq<I> {
    if let Some(run) = run {
        modes::packed_ids(run.rows@, run.start as int, run.rows.len() as int)
    } else { Seq::empty() }
}

fn save_run<I: Copy>(run: &Option<PackedRun<I>>) -> (saved: Ghost<(Seq<I>, bool)>)
    ensures saved@ == (run_ids(run), recording(run)),
    no_unwind
{ Ghost((run_ids(run), recording(run))) }

#[verifier::opaque]
spec fn line_ids<I>(order: crate::prepare_frame::Order<I>, first: Option<I>, count: nat) -> Seq<I>
    decreases count,
{
    if count == 0 || first.is_none() { Seq::empty() }
    else {
        let id = first.unwrap();
        seq![id] + line_ids(order, (order.sibling)(id), (count - 1) as nat)
    }
}

proof fn leaf_line_ids<I>(order: crate::prepare_frame::Order<I>, hidden: spec_fn(I) -> bool,
    first: Option<I>, ids: Seq<I>, next: Option<I>)
    requires modes::leaf_path(PlacementLinks::from_order(order), hidden, first, ids, next),
    ensures line_ids(order, first, ids.len()) == ids,
    decreases ids.len(),
{
    reveal(modes::leaf_path);
    reveal(line_ids);
    if ids.len() > 0 {
        leaf_line_ids(order, hidden, (order.sibling)(ids.first()), ids.drop_first(), next);
        assert(seq![ids.first()] + ids.drop_first() =~= ids);
    }
}

fn save_line<I: Copy, T: Records<Id = I> + ?Sized>(tree: &T, next: Option<I>, count: u32)
    -> (ids: Ghost<Seq<I>>)
    ensures ids@ == line_ids(tree.order(), next, count as nat),
    no_unwind
{ Ghost(line_ids(tree.order(), next, count as nat)) }

fn save_rows<I: Copy>(rows: &Vec<PreparedStackLeaf<I>>) -> (saved: Ghost<Seq<PreparedStackLeaf<I>>>)
    ensures saved@ == rows@,
    no_unwind
{ Ghost(rows@) }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(run =>
    requires live(old(tree), parent),
    ensures final(tree).order() == old(tree).order(),
        forall |id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id), admitted(final(tree).order(), parent, &run),
        final(tree).packed_state().groups@ == old(tree).packed_state().groups@,
        recording(&run) ==> run_ids(&run).len() == 0,
    no_unwind
))]
fn take_run<T: StartActions + ?Sized>(tree: &mut T, parent: T::Id) -> Option<PackedRun<T::Id>> {
    let expected = tree.record(parent).n_placed_children;
    let params = tree.params(parent);
    if !matches!(params.children_layout, ChildrenLayout::Wrap { arrange: Arrange::Start, .. })
        || params.children_origin_flipped.x || params.children_origin_flipped.y
        || expected < 16
    {
        return None;
    }
    let hint = tree.stack_leaf_hint()?;
    if hint == 0 || expected > hint { return None; }
    let workspace = tree.packed_stack_leaves();
    let len = workspace.rows.len();
    if len > u32::MAX as usize { return None; }
    let start = len as u32;
    let count = expected as usize;
    if count as u32 != expected || start.checked_add(expected).is_none() { return None; }
    if !T::LeafMemory::try_reserve(&mut workspace.rows, count) { return None; }
    let rows = T::LeafMemory::take(&mut workspace.rows);
    Some(PackedRun { rows, start, recording: true })
}

/// Prepare independent main pixels and fixed or Fill cross sizes in one traversal.
/// A rejected prefix is reset by ordinary full preparation starting from the first child.
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(tree).order().ordered(), live(old(tree), parent),
    ensures final(tree).order() == old(tree).order(),
        forall |id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
        result.is_some() ==> enabled_wrap_children(final(tree), parent),
        final(tree).packed_state().groups@ != old(tree).packed_state().groups@ ==>
            final(tree).packed_state().groups@.drop_last() == old(tree).packed_state().groups@,
        final(tree).packed_state().groups@.len() > old(tree).packed_state().groups@.len() ==> {
            let workspace = final(tree).packed_state();
            let group = workspace.groups@.last();
            let [start, end] = group.span;
            let links = PlacementLinks::from_order(final(tree).order());
            &&& result.is_some() && group.parent == parent
            &&& start < end <= workspace.rows@.len()
            &&& modes::leaf_path(links, hidden(final(tree)), links.first(parent),
                modes::packed_ids(workspace.rows@, start as int, end as int), None)
        },
    no_unwind
))]
pub(crate) fn try_leaf_wrap<T: StartActions + ?Sized>(tree: &mut T, parent: T::Id) -> Option<u32> {
    let ChildrenLayout::Wrap { axis, .. } = tree.params(parent).children_layout else { return None; };
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut run = take_run(tree, parent);
    // Keep axis selection outside both child walks.
    let result = match axis {
        Axis::X => prepare_leaf_wrap::<T, true>(tree, parent, #[cfg(any(feature = "incremental", verus_keep_ghost))] &mut run),
        Axis::Y => prepare_leaf_wrap::<T, false>(tree, parent, #[cfg(any(feature = "incremental", verus_keep_ghost))] &mut run),
    };
    #[cfg(verus_keep_ghost)]
    let prepared = wrap_projection(tree);
    #[cfg(verus_keep_ghost)]
    proof! {
        let (links, hidden) = prepared@;
        assert(result.is_some() ==> modes::enabled_siblings(links, hidden, links.first(parent)));
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if let Some(mut run) = run {
        #[cfg(verus_keep_ghost)]
        let before_packed = wrap_projection(tree);
        #[cfg(verus_keep_ghost)]
        let recorded = save_rows(&run.rows);
        let workspace = tree.packed_stack_leaves();
        let end = run.rows.len();
        let start = run.start;
        let mut committed = false;
        if let Some(nodes) = result {
            if run.recording && end <= u32::MAX as usize
                && end.checked_sub(start as usize) == Some(nodes.saturating_sub(1) as usize)
            {
                committed = try_append::<_, T::LeafMemory>(&mut workspace.groups, StackLeafGroup {
                    parent, span: [start, end as u32],
                });
            }
        }
        // Preserve completed groups when this parent falls back.
        if !committed { T::LeafMemory::truncate(&mut run.rows, start as usize); }
        workspace.rows = run.rows;
        #[cfg(verus_keep_ghost)]
        proof! {
            if committed {
                assert(workspace.rows@ == recorded@);
                assert(workspace.groups@.last() == (StackLeafGroup { parent, span: [start, end as u32] }));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(hidden);
            assert forall |id: T::Id| #[trigger] (hidden(tree))(id) == (before_packed@.1)(id) by {};
            assert(hidden(tree) =~= before_packed@.1);
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(PlacementLinks::from_order(tree.order()) == prepared@.0 && hidden(tree) == prepared@.1); }
    result
}

#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(tree).order().ordered(), live(old(tree), parent),
        admitted(old(tree).order(), parent, old(run)),
        recording(old(run)) ==> run_ids(old(run)).len() == 0,
    ensures final(tree).order() == old(tree).order(),
        final(tree).packed_state() == old(tree).packed_state(),
        forall |id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id), admitted(final(tree).order(), parent, final(run)),
        result.is_some() ==> result.unwrap() >= 5 && enabled_wrap_children(final(tree), parent),
        result.is_some() && recording(final(run)) ==> {
            let links = PlacementLinks::from_order(final(tree).order());
            modes::leaf_path(links, hidden(final(tree)),
                links.first(parent), run_ids(final(run)), None)
        },
    no_unwind
))]
fn prepare_leaf_wrap<T: StartActions + ?Sized, const HORIZONTAL: bool>(
    tree: &mut T, parent: T::Id,
    #[cfg(any(feature = "incremental", verus_keep_ghost))] run: &mut Option<PackedRun<T::Id>>,
) -> Option<u32> {
    let params = tree.params(parent);
    let ChildrenLayout::Wrap { spacing, line_spacing, .. } = params.children_layout else { return None; };
    let axis = if HORIZONTAL { Axis::X } else { Axis::Y };
    let cross = axis.other();
    if !matches!(params.size.component(cross), Size::FitContent | Size::Auto)
        || !independent(params, axis) || !independent(params, cross)
        || !T::Float::finite(spacing) || !T::Float::finite(line_spacing)
    { return None; }
    let Size::Pixels(parent_size) = *params.size.component(axis) else { return None; };
    if !T::Float::finite(parent_size) { return None; }
    let [pad_start, pad_end] = *params.padding.component(axis);
    let limit = T::Float::max(parent_size - (pad_start + pad_end), 0.0);
    if !T::Float::finite(limit) { return None; }
    let mut parent_data = T::empty_record();
    crate::prepare_nodes::seed_pixels::<T::Float>(&mut parent_data, params, false, None);
    let mut next = first(tree, parent);
    let mut head = next;
    #[cfg(verus_keep_ghost)]
    let initial = next;
    #[cfg(verus_keep_ghost)]
    let mut accepted = start_accepted::<T::Id>();
    #[cfg(verus_keep_ghost)]
    let mut line = start_accepted::<T::Id>();
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(modes::leaf_path);
        finite_from_order(tree.order());
    }
    let mut later_line = false;
    let mut count = 0u32;
    let mut population = 0u32;
    let mut width = 0.0;
    let mut height = 0.0;
    let mut total = 0.0;
    let mut has_spans = false;
    let mut has_fills = false;
    // A run of zero margins can publish its cross Fill sizes without rereading them.
    let mut line_zero_margins = true;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut direct_start = true;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(),
            tree.packed_state() == old(tree).packed_state(),
            forall |id: T::Id| #[trigger] tree.layout_params(id) == old(tree).layout_params(id),
            live(tree, parent), cursor(tree, parent, next), cursor(tree, parent, head),
            admitted(tree.order(), parent, run),
            modes::leaf_path(PlacementLinks::from_order(old(tree).order()), hidden(old(tree)), initial, accepted@, next),
            modes::leaf_path(PlacementLinks::from_order(old(tree).order()), hidden(old(tree)), head, line@, next),
            line@.len() == count, count <= population, accepted@.len() == population,
            recording(run) ==> accepted@ == run_ids(run) + line@,
        ensures next.is_none(),
        decreases remaining(tree, parent, next),
    ))]
    while let Some(child) = next {
        next = following(tree, parent, child);
        let p = tree.params(child);
        let Size::Pixels(main) = *p.size.component(axis) else { return None; };
        let other = match *p.size.component(cross) {
            Size::Pixels(other) => other,
            Size::Fill => { has_fills = true; 0.0 },
            _ => return None,
        };
        if p.disabled || p.free_placement || !independent(p, axis) || !independent(p, cross)
            || !T::Float::finite(main) || !T::Float::finite(other)
            || !matches!(p.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
            || tree.first(child).is_some()
        { return None; }
        #[cfg(verus_keep_ghost)]
        proof! {
            let links = PlacementLinks::from_order(old(tree).order());
            reveal(hidden);
            assert(!(hidden(old(tree)))(child));
            modes::leaf_path_push(links, hidden(old(tree)), initial, accepted@, child);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let links = PlacementLinks::from_order(old(tree).order());
            leaf_line_ids(old(tree).order(), hidden(old(tree)), head, line@, Some(child));
            modes::leaf_path_push(links, hidden(old(tree)), head, line@, child);
        }
        has_spans |= p.grid_span.x > 1 || p.grid_span.y > 1;
        let [left, right] = p.margin.x;
        let [top, bottom] = p.margin.y;
        let zero_margins = left.is_zero() && right.is_zero() && top.is_zero() && bottom.is_zero();
        #[cfg(verus_keep_ghost)]
        let admitted_rows = save_run(run);
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        {
            direct_start = direct_start && zero_margins && matches!(p.position.component(cross), Pos::Start);
            if !direct_start {
                if let Some(run) = run { run.recording = false; }
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if recording(run) {
                assert(admitted_rows@.1 && run_ids(run) == admitted_rows@.0);
                assert(accepted@ == run_ids(run) + line@);
            }
        }
        let (base, rise) = if zero_margins {
            (main, other)
        } else {
            let base = with_margin(main, margin::<T::Float>(p, axis));
            let rise = with_margin(other, margin::<T::Float>(p, cross));
            if !T::Float::finite(base) || !T::Float::finite(rise) { return None; }
            (base, rise)
        };
        let combined = if count == 0 { base } else { wrap_lines::extend_main(width, spacing, base) };
        if count != 0 && wrap_lines::beyond_limit(combined, limit) {
            if !write_leaf_line::<T, HORIZONTAL>(
                tree, parent, head, count, height, later_line, line_zero_margins,
                #[cfg(any(feature = "incremental", verus_keep_ghost))] run,
                #[cfg(any(feature = "incremental", verus_keep_ghost))] spacing,
            ) { return None; }
            #[cfg(verus_keep_ghost)]
            proof! {
                if recording(run) {
                    assert(run_ids(run) =~= accepted@);
                    assert(run_ids(run) + seq![child] =~= accepted@.push(child));
                }
                let links = PlacementLinks::from_order(old(tree).order());
                reveal_with_fuel(modes::leaf_path, 2);
                assert(modes::leaf_path(links, hidden(old(tree)), Some(child), seq![child], next));
            }
            #[cfg(verus_keep_ghost)]
            { line = accept(start_accepted(), child); }
            later_line = true;
            head = Some(child);
            total += height;
            total += line_spacing;
            width = base;
            height = T::Float::max(0.0, rise);
            count = 1;
            line_zero_margins = zero_margins;
        } else {
            line_zero_margins &= zero_margins;
            width = combined;
            height = T::Float::max(height, rise);
            #[cfg(verus_keep_ghost)]
            proof! {
                if recording(run) {
                    assert(run_ids(run) + line@.push(child) =~= accepted@.push(child));
                }
            }
            #[cfg(verus_keep_ghost)]
            { line = accept(line, child); }
            count = count.saturating_add(1);
        }
        population = population.checked_add(1)?;
        #[cfg(verus_keep_ghost)]
        { accepted = accept(accepted, child); }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let links = PlacementLinks::from_order(old(tree).order());
        assert(next.is_none());
        assert(modes::consistent_cursor(links, initial));
        modes::complete_leaf_path_is_enabled(links, hidden(old(tree)), initial, accepted@);
        leaf_line_ids(old(tree).order(), hidden(old(tree)), head, line@, None);
    }
    if population < 4 { return None; }
    if !write_leaf_line::<T, HORIZONTAL>(
        tree, parent, head, count, height, later_line, line_zero_margins,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] run,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] spacing,
    ) { return None; }
    #[cfg(verus_keep_ghost)]
    proof! { if recording(run) { assert(run_ids(run) =~= accepted@); } }
    total += height;
    parent_data.flags.0 |= NodeFlags::WRAP_CONTAINER;
    if has_spans { parent_data.flags.0 |= NodeFlags::GRID_SPANS; }
    if has_fills { parent_data.flags.0 |= NodeFlags::flex_child(cross); }
    parent_data.n_placed_children = population;
    parent_data.publish_slot(slot_index(axis, Kind::EvenShare), 0.0);
    parent_data.publish_slot(slot_index(cross, Kind::Flow), total);
    #[cfg(feature = "incremental")]
    {
        parent_data.levels[slot_index(axis, Kind::EvenShare)] = 2;
        parent_data.levels[slot_index(cross, Kind::Flow)] = 3;
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    {
        parent_data.prepared_placement |= NodeLayoutData::PREPARED_WRAP;
        if direct_start { parent_data.prepared_placement |= NodeLayoutData::PREPARED_WRAP_START; }
    }
    *tree.edit(parent) = parent_data;
    #[cfg(verus_keep_ghost)]
    proof! { same_wrap_visibility(old(tree), tree); }
    Some(population.saturating_add(1))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(written =>
    requires old(tree).order().ordered(), live(old(tree), parent), cursor(old(tree), parent, next),
        admitted(old(tree).order(), parent, old(run)),
    ensures final(tree).order() == old(tree).order(),
        final(tree).packed_state() == old(tree).packed_state(),
        forall |id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id), admitted(final(tree).order(), parent, final(run)),
        recording(final(run)) ==> recording(old(run)),
        written && recording(final(run)) ==> run_ids(final(run)) == run_ids(old(run))
            + line_ids(old(tree).order(), next, count as nat),
    no_unwind
))]
fn write_leaf_line<T: StartActions + ?Sized, const HORIZONTAL: bool>(
    tree: &mut T, parent: T::Id, mut next: Option<T::Id>, mut count: u32,
    cross: f32, mut line_start: bool, zero_margins: bool,
    #[cfg(any(feature = "incremental", verus_keep_ghost))] run: &mut Option<PackedRun<T::Id>>,
    #[cfg(any(feature = "incremental", verus_keep_ghost))] spacing: f32,
) -> bool {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let mut first = true;
    #[cfg(verus_keep_ghost)]
    let expected = save_line(tree, next, count);
    use crate::declarations::{X, Y};
    let cross_axis = if HORIZONTAL { Y } else { X };
    let metrics = [0, T::Float::bits(cross)];
    #[cfg(feature = "incremental")]
    use crate::StructuralChange;
    #[cfg(verus_keep_ghost)]
    use crate::structural::kernel::StructuralChange;
    #[cfg(feature = "incremental")]
    use crate::fixed_leaf_cache;
    #[cfg(verus_keep_ghost)]
    use crate::fixed_leaf_cache::runtime as fixed_leaf_cache;
    let flags = cycle_rules::write_state(NodeFlags::FIXED_LEAF, slot_index(X, Kind::Regular) as u32, SOLVED);
    let flags = cycle_rules::write_state(flags, slot_index(Y, Kind::Regular) as u32, SOLVED);
    let flags = cycle_rules::write_state(flags, slot_index(X, Kind::Final) as u32, SOLVED);
    let flags = cycle_rules::write_state(flags, slot_index(Y, Kind::Final) as u32, SOLVED);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(),
            tree.packed_state() == old(tree).packed_state(),
            forall |id: T::Id| #[trigger] tree.layout_params(id) == old(tree).layout_params(id),
            live(tree, parent), cursor(tree, parent, next),
            admitted(tree.order(), parent, run),
            recording(run) ==> recording(old(run)),
            recording(run) ==>
                run_ids(run) + line_ids(tree.order(), next, count as nat) == run_ids(old(run)) + expected@,
            metrics@[1] == T::Float::word(cross),
        decreases count,
    ))]
    while let (true, Some(child)) = (count > 0, next) {
        #[cfg(verus_keep_ghost)]
        let remaining = save_line(tree, next, count);
        next = following(tree, parent, child);
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(line_ids);
            assert(remaining@ == seq![child] + line_ids(tree.order(), next, (count - 1) as nat));
        }
        let params = tree.params(child);
        let (x, y, fill) = match (params.size.x, params.size.y) {
            (Size::Pixels(x), Size::Pixels(y)) => (x, y, false),
            (Size::Pixels(x), Size::Fill) if matches!(cross_axis, Y) => {
                let margin = if zero_margins { 0.0 } else { margin::<T::Float>(params, Y) };
                (x, if margin == 0.0 { cross } else { T::Float::max(cross - margin, 0.0) }, true)
            }
            (Size::Fill, Size::Pixels(y)) if matches!(cross_axis, X) => {
                let margin = if zero_margins { 0.0 } else { margin::<T::Float>(params, X) };
                (if margin == 0.0 { cross } else { T::Float::max(cross - margin, 0.0) }, y, true)
            }
            _ => return false,
        };
        if fill {
            // The independent main Final has rank 1. Its Share has rank 2
            // and the cross Flow rank 3. Cross Regular reads that Flow.
            let (x_level, y_level) = if matches!(cross_axis, X) { (4, 0) } else { (0, 4) };
            if !T::Float::finite(x) || !T::Float::finite(y) { return false; }
            let mut desired = T::empty_record();
            desired.publish_axis(X, x, x, x_level);
            desired.publish_axis(Y, y, y, y_level);
            if line_start { desired.flags.0 |= NodeFlags::WRAP_LINE_START; }
            desired.parent_flow = metrics;
            *tree.edit(child) = desired;
        } else {
            let x_bits = T::Float::bits(x);
            let y_bits = T::Float::bits(y);
            let wanted = flags | if line_start { NodeFlags::WRAP_LINE_START } else { 0 };
            let record = tree.record(child);
            if record.flags.0 != wanted || record.parent_flow[0] != metrics[0] || record.parent_flow[1] != metrics[1]
                || T::Float::bits(record.values[slot_index(X, Kind::Regular)]) != x_bits
                || T::Float::bits(record.values[slot_index(Y, Kind::Regular)]) != y_bits
                || T::Float::bits(record.values[slot_index(X, Kind::Final)]) != x_bits
                || T::Float::bits(record.values[slot_index(Y, Kind::Final)]) != y_bits
            {
                let mut desired = T::empty_record();
                desired.publish_axis(X, x, x, 0);
                desired.publish_axis(Y, y, y, 0);
                desired.flags.0 = wanted;
                desired.parent_flow = metrics;
                *tree.edit(child) = desired;
            } else {
                #[cfg(any(feature = "incremental", verus_keep_ghost))]
                if !matches!(record.structural_change, StructuralChange::Clean) || !record.fixed_leaf_summary.is_empty() {
                    let edited = tree.edit(child);
                    edited.structural_change = StructuralChange::Clean;
                    edited.fixed_leaf_summary = fixed_leaf_cache::Summary::EMPTY;
                }
            }
        }
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if let Some(run) = run {
            if run.recording {
                #[cfg(not(verus_keep_ghost))]
                use crate::placement_work::PlacementWork;
                #[cfg(verus_keep_ghost)]
                use crate::placement::kernel::PlacementWork;
                if !matches!(tree.record(child).placement, PlacementWork::Clean) {
                    run.recording = false;
                } else {
                    let horizontal = matches!(cross_axis, Y);
                    let row = PreparedStackLeaf::wrapped::<T::Float>(child, [x, y], horizontal, spacing, first, cross);
                    #[cfg(verus_keep_ghost)]
                    let previous = save_rows(&run.rows);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(tree.order().child(parent, child));
                        let published = tree.layout_record(child);
                        let x = cycle_rules::slot_index(X.index(), Kind::Final) as int;
                        let y = cycle_rules::slot_index(Y.index(), Kind::Final) as int;
                        assert(T::Float::word(row.size@[0]) == T::Float::word(published.values@[x]));
                        assert(T::Float::word(row.size@[1]) == T::Float::word(published.values@[y]));
                        assert(published.parent_flow@[1] == metrics@[1]);
                        assert(T::Float::word(row.cross_leading) == published.parent_flow@[1]);
                        assert(run.start <= previous@.len());
                        assert forall |i: int| run.start <= i < previous@.len() implies
                            tree.order().child(parent, (#[trigger] previous@[i]).id) by {
                            assert(run.rows@[i] == previous@[i]);
                            assert(tree.order().child(parent, run.rows@[i].id));
                        }
                    }
                    run.recording = try_append::<_, T::LeafMemory>(&mut run.rows, row);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        if run.recording {
                            let before_ids = modes::packed_ids(previous@, run.start as int, previous@.len() as int);
                            let after_ids = modes::packed_ids(run.rows@, run.start as int, run.rows.len() as int);
                            assert(before_ids =~= modes::packed_ids(run.rows@, run.start as int, previous@.len() as int));
                            modes::packed_ids_push(run.rows@, run.start as int, previous@.len() as int);
                            assert(after_ids =~= before_ids.push(child));
                            let tail = line_ids(tree.order(), next, (count - 1) as nat);
                            assert(after_ids + tail =~= before_ids + remaining@);
                        }
                        assert forall |i: int| run.start <= i < run.rows.len() implies
                            tree.order().child(parent, (#[trigger] run.rows@[i]).id) by {
                            if i < previous@.len() {
                                assert(run.rows@[i] == previous@[i]);
                                assert(tree.order().child(parent, previous@[i].id));
                            } else {
                                assert(run.rows@[i] == row);
                                assert(row.id == child);
                            }
                        }
                    }
                }
            }
            first = false;
        }
        line_start = false;
        count -= 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(line_ids); }
    count == 0
}
