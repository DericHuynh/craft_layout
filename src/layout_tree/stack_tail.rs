#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(not(verus_keep_ghost))]
use super::*;
use crate::cycle_rules::{self, Kind, N_SLOTS};
use crate::declarations::{Axis, ChildrenLayout, LayoutParams, Size, Xy, XyRect};
use crate::fill_budget;
use crate::prepare_frame::FrameFloat;
#[cfg(not(verus_keep_ghost))]
use crate::placement_geometry::RustFloat;
use crate::structural_changes::{StructuralChange, TailDelta, tail_can_reuse, tail_replaces_prefix};
#[cfg(not(verus_keep_ghost))]
use crate::structural_changes::empty_delta;
use crate::Arrange;

#[cfg_attr(verus_keep_ghost, verus_verify)]
enum ScanError<E> {
    Limit,
    Visit(E),
}

#[cfg(verus_keep_ghost)]
verus! {
struct TailState {
    solved_nodes: u32,
    needs_full: bool,
}

trait TailModel {
    spec fn counts(&self) -> TailState;
    spec fn writes(&self) -> nat;
}

trait TailWritePolicy {
    spec fn may_write() -> bool;
}

impl TailWritePolicy for CheckSuffix {
    spec fn may_write() -> bool { false }
}

impl<I> TailWritePolicy for UpdateSuffix<I> {
    spec fn may_write() -> bool { true }
}
}

#[cfg(not(verus_keep_ghost))]
trait TailModel {}
#[cfg(not(verus_keep_ghost))]
impl<T> TailModel for T {}
#[cfg(not(verus_keep_ghost))]
trait TailWritePolicy {}
#[cfg(not(verus_keep_ghost))]
impl<T> TailWritePolicy for T {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
trait TailVisit<I: Copy, T: TailModel>: TailWritePolicy {
    type Error;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(tree).counts() == old(tree).counts(),
            old(tree).writes() <= final(tree).writes() <= old(tree).writes() + 1,
            !Self::may_write() ==> final(tree).writes() == old(tree).writes(),
        no_unwind
    ))]
    fn visit(&mut self, tree: &mut T, id: I) -> Result<Option<I>, Self::Error>;
}

#[cfg(not(verus_keep_ghost))]
impl<I: Copy, E, F> TailVisit<I, ()> for F
where F: FnMut(I) -> Result<Option<I>, E>,
{
    type Error = E;

    #[inline(always)]
    fn visit(&mut self, _tree: &mut (), id: I) -> Result<Option<I>, E> { self(id) }
}

/// Visit at most the number of live nodes, including when a stored link is corrupt.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(tree).counts() == old(tree).counts(),
        old(tree).writes() <= final(tree).writes() <= old(tree).writes() + limit,
        first.is_none() || !V::may_write() ==> final(tree).writes() == old(tree).writes(),
    no_unwind
))]
fn scan_siblings<I: Copy, T: TailModel, V: TailVisit<I, T>>(tree: &mut T, first: Option<I>, limit: usize, visitor: &mut V)
    -> Result<(), ScanError<V::Error>>
{
    let mut next = first;
    let mut remaining = limit;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining <= limit, tree.counts() == old(tree).counts(),
            old(tree).writes() <= tree.writes() <= old(tree).writes() + limit - remaining,
            first.is_none() ==> next.is_none() && remaining == limit,
            !V::may_write() ==> tree.writes() == old(tree).writes(),
        decreases remaining,
    ))]
    while let Some(id) = next {
        if remaining == 0 {
            return Err(ScanError::Limit);
        }
        remaining -= 1;
        next = match visitor.visit(tree, id) {
            Ok(next) => next,
            Err(error) => return Err(ScanError::Visit(error)),
        };
    }
    Ok(())
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(counts =>
    ensures counts.is_some() == (
        delta.removed <= children && children as int - delta.removed + delta.added <= u32::MAX
            && delta.removed <= solved && solved as int - delta.removed + delta.added <= u32::MAX
    ),
        counts.is_some() ==> counts.unwrap().0 == children as int - delta.removed + delta.added,
        counts.is_some() ==> counts.unwrap().1 == solved as int - delta.removed + delta.added,
    no_unwind
))]
fn tail_counts<I: Copy>(delta: TailDelta<I>, children: u32, solved: u32) -> Option<(u32, u32)> {
    Some((delta.update_count(children)?, delta.update_count(solved)?))
}

// A new tail leaf cannot add a settled declaration read to the parent's share.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns unbounded_fill(regular, min, max), no_unwind))]
pub(crate) fn unbounded_fill(regular: Size, min: Option<Size>, max: Option<Size>) -> bool {
    matches!(regular, Size::Fill) && min.is_none() && max.is_none()
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(values)@ == old(values)@.update(cycle_rules::slot_index(axis.index(), kind) as int, value),
    no_unwind
))]
pub(crate) fn write_tail_slot<T: Copy>(values: &mut [T; N_SLOTS], axis: Axis, kind: Kind, value: T) {
    values[cycle_rules::slot_index(axis.index(), kind)] = value;
}

/// Prepare the packed parent count before measuring its updated sibling group.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(placed) == count, *final(mark) is Clean,
    no_unwind
))]
fn begin_share_record(placed: &mut u32, mark: &mut StructuralChange, count: u32) {
    *placed = count;
    *mark = StructuralChange::Clean;
}

#[cfg(verus_keep_ghost)]
verus! {
/// The count written before measurement equals a count over the live siblings
/// after an admitted batch of tail edits.
pub(crate) fn begin_share_for_tail_batch<I: Copy>(
    placed: &mut u32, mark: &mut StructuralChange, solved: u32, delta: TailDelta<I>,
    original: Ghost<Seq<I>>, edits: Ghost<Seq<(I, bool)>>, in_flow: Ghost<spec_fn(I) -> bool>,
) -> (result: Option<u32>)
    requires
        *old(placed) == crate::structural::count(original@, in_flow@),
        match crate::structural::apply_batch(
            original@, TailDelta { first_added: None, added: 0, removed: 0 }, edits@, in_flow@,
        ) {
            Some((_, planned)) => planned == delta,
            None => false,
        },
    ensures
        result.is_some() ==> {
            let (live, _) = crate::structural::apply_batch(
                original@, TailDelta { first_added: None, added: 0, removed: 0 }, edits@, in_flow@,
            ).unwrap();
            &&& *final(placed) == crate::structural::count(live, in_flow@)
            &&& *final(mark) is Clean
            &&& result.unwrap() == solved as int - delta.removed + delta.added
        },
        result.is_none() ==> *final(placed) == *old(placed) && *final(mark) == *old(mark),
    no_unwind
{
    proof { crate::structural::complete_tail_batch(original@, edits@, in_flow@, 0); }
    let (count, solved) = tail_counts(delta, *placed, solved)?;
    begin_share_record(placed, mark, count);
    Some(solved)
}
}

/// Cached sizing inputs for the recently edited stack. Pushing or popping
/// zero-margin Fill leaves preserves its fixed costs and the existing bounds.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(super) struct TailCache<I: Copy> {
    parent: I,
    fills: u32,
    space_without_gaps: f32,
    independent_fills: bool,
    bounded_fills: bool,
}

#[cfg(not(verus_keep_ghost))]
pub(super) type StackTail = TailCache<NodeKey>;

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct ParentRecord<'a> {
    layout: ChildrenLayout,
    values: &'a [f32; N_SLOTS],
    rect: XyRect,
    count: u32,
    flags: u32,
    block_item: bool,
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
enum TailFailure { Invalidated, Flow }

#[cfg_attr(verus_keep_ghost, verus_verify)]
trait TailFloat {
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn max(left: f32, right: f32) -> f32;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn bits(value: f32) -> u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn finite(value: f32) -> bool;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn margins(params: &LayoutParams, axis: Axis) -> [f32; 2];
}

#[cfg(not(verus_keep_ghost))]
struct RustTailFloat;

#[cfg(not(verus_keep_ghost))]
impl TailFloat for RustTailFloat {
    #[inline(always)]
    fn max(left: f32, right: f32) -> f32 { left.max(right) }
    #[inline(always)]
    fn bits(value: f32) -> u32 { value.to_bits() }
    #[inline(always)]
    fn finite(value: f32) -> bool { value.is_finite() }
    #[inline(always)]
    fn margins(params: &LayoutParams, axis: Axis) -> [f32; 2] { margins(params, axis) }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
trait TailAccess: TailModel {
    type Id: Copy;
    type Float: TailFloat;

    #[cfg_attr(verus_keep_ghost, verus_spec(state =>
        ensures state.is_some() ==> state.unwrap().0 == self.counts().solved_nodes && !self.counts().needs_full,
        no_unwind
    ))]
    fn window_state(&self, window: Xy<f32>) -> Option<(u32, bool)>;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn parent_record(&self, parent: Self::Id) -> Option<ParentRecord<'_>>;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn reads_children(&self, parent: Self::Id) -> bool;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn padding(&self, parent: Self::Id, axis: Axis) -> f32;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn count_nodes(&self) -> usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(cache =>
        ensures cache.is_some() ==> cache.unwrap().parent == parent,
        no_unwind
    ))]
    fn cache(&self, parent: Self::Id) -> Option<TailCache<Self::Id>>;
    #[cfg_attr(verus_keep_ghost, verus_spec(cache =>
        ensures cache.is_some() ==> cache.unwrap().parent == parent,
        no_unwind
    ))]
    fn collect_cache(&self, parent: Self::Id, axis: Axis, inner: f32) -> Option<TailCache<Self::Id>>;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn read_fill(&self, child: Self::Id, axis: Axis) -> Option<(Option<Self::Id>, bool)>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).counts() == old(self).counts(), final(self).writes() == old(self).writes(),
        no_unwind
    ))]
    fn begin_share(&mut self, parent: Self::Id, count: u32) -> Option<()>;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).counts() == old(self).counts(), final(self).writes() == old(self).writes(),
        no_unwind
    ))]
    fn measure_share(&mut self, parent: Self::Id, axis: Axis) -> f32;
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures final(self).counts().needs_full == old(self).counts().needs_full,
            final(self).counts().solved_nodes == if result.is_some() { solved_nodes } else { old(self).counts().solved_nodes },
            final(self).writes() == old(self).writes(),
        no_unwind
    ))]
    fn finish_share(&mut self, cache: TailCache<Self::Id>, axis: Axis, share: f32, solved_nodes: u32) -> Option<()>;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).counts() == old(self).counts(), final(self).writes() == old(self).writes(),
        no_unwind
    ))]
    fn resize_prefix(&mut self, cache: TailCache<Self::Id>, axis: Axis, share: f32, first_added: Option<Self::Id>) -> Option<u32>;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn links(&self, child: Self::Id) -> Option<(Option<Self::Id>, Option<Self::Id>)>;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn rect(&self, child: Self::Id) -> Option<XyRect>;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).counts() == old(self).counts(), final(self).writes() == old(self).writes(),
        no_unwind
    ))]
    fn measure_appended(&mut self, child: Self::Id) -> Option<u32>;
    #[cfg_attr(verus_keep_ghost, verus_spec(placed =>
        ensures final(self).counts() == old(self).counts(),
            final(self).writes() == old(self).writes() + (if placed { 1nat } else { 0nat }),
        no_unwind
    ))]
    fn place_appended(&mut self, parent: Self::Id, child: Self::Id, rect: XyRect, preceding: Option<(Self::Id, XyRect)>) -> bool;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn rounds_output(&self) -> bool;
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn first_child_in_stack(&self, parent: Self::Id) -> Option<Self::Id>;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).counts() == old(self).counts(),
        no_unwind
    ))]
    fn place_tree(&mut self);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).counts() == old(self).counts(),
        no_unwind
    ))]
    fn place_stack(&mut self, parent: Self::Id, first: Self::Id, rect: XyRect, origin: Xy<f32>);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).counts().needs_full, final(self).counts().solved_nodes == old(self).counts().solved_nodes,
            final(self).writes() == old(self).writes(),
        no_unwind
    ))]
    fn request_full(&mut self, reason: TailFailure);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct CheckSuffix {
    axis: Axis,
    independent: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<A: TailAccess> TailVisit<A::Id, A> for CheckSuffix {
    type Error = ();

    #[inline(always)]
    fn visit(&mut self, tree: &mut A, child: A::Id) -> Result<Option<A::Id>, ()> {
        let Some((next, independent)) = tree.read_fill(child, self.axis) else { return Err(()); };
        self.independent &= independent;
        Ok(next)
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct UpdateSuffix<I> {
    parent: I,
    rect: XyRect,
    computed: u32,
    place_all: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<A: TailAccess> TailVisit<A::Id, A> for UpdateSuffix<A::Id> {
    type Error = TailFailure;

    #[inline(always)]
    fn visit(&mut self, tree: &mut A, child: A::Id) -> Result<Option<A::Id>, TailFailure> {
        let Some((next, previous)) = tree.links(child) else { return Err(TailFailure::Invalidated); };
        let Some(slots) = tree.measure_appended(child) else { return Err(TailFailure::Flow); };
        self.computed = cycle_rules::add_count(self.computed, slots);
        if !self.place_all {
            let preceding = match previous {
                Some(id) => match tree.rect(id) {
                    Some(rect) => Some((id, rect)),
                    None => {
                        self.place_all = true;
                        return Ok(next);
                    }
                },
                None => None,
            };
            self.place_all = !tree.place_appended(self.parent, child, self.rect, preceding);
        }
        Ok(next)
    }
}

/// Measure and place one eligible batch, falling back if a cached input is unavailable.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.is_some() ==> !old(tree).counts().needs_full && !final(tree).counts().needs_full
            && delta.removed <= old(tree).counts().solved_nodes
            && final(tree).counts().solved_nodes == old(tree).counts().solved_nodes as int - delta.removed + delta.added,
        result.is_none() && !final(tree).counts().needs_full ==>
            final(tree).counts() == old(tree).counts() && final(tree).writes() == old(tree).writes(),
    no_unwind
))]
fn run_tail<A: TailAccess>(tree: &mut A, parent: A::Id, delta: TailDelta<A::Id>, window: Xy<f32>) -> Option<u32> {
    let (solved_nodes, refresh_output) = tree.window_state(window)?;
    let ParentRecord { layout, values, rect, count, flags, block_item } = tree.parent_record(parent)?;
    let ChildrenLayout::Stack { axis, spacing, arrange } = layout else { return None; };
    let ix = axis.index();
    if !A::Float::finite(spacing) || spacing < 0.0 || block_item || tree.reads_children(parent)
        || cycle_rules::read_state(flags, cycle_rules::slot_index(ix, Kind::EvenShare) as u32) != cycle_rules::SOLVED
    {
        return None;
    }
    let old_share = cycle_rules::read_slot(values, ix, Kind::EvenShare);
    let (count, solved_nodes) = tail_counts(delta, count, solved_nodes)?;
    let inner = A::Float::max(cycle_rules::read_slot(values, ix, Kind::Final) - tree.padding(parent, axis), 0.0);
    let first_added = delta.first_added;
    let cache = if let Some(mut cache) = tree.cache(parent) {
        cache.fills = delta.update_count(cache.fills)?;
        let mut visitor = CheckSuffix { axis, independent: cache.independent_fills };
        let remaining = tree.count_nodes();
        if scan_siblings(tree, first_added, remaining, &mut visitor).is_err() { return None; }
        cache.independent_fills = visitor.independent;
        cache
    } else {
        tree.collect_cache(parent, axis, inner)?
    };
    // Either gaps alone or fixed costs alone can exhaust the budget.
    let gaps = spacing * A::Float::max(count as f32 - 1.0, 0.0);
    let exhausted = !cache.bounded_fills && fill_budget::exhausted(inner, gaps, cache.space_without_gaps);
    let before = A::Float::bits(old_share);
    if cache.fills == 0 || !tail_can_reuse(exhausted, before, cache.independent_fills) { return None; }

    tree.begin_share(parent, count)?;
    let share = if exhausted { 0.0 } else { tree.measure_share(parent, axis) };
    if tree.finish_share(cache, axis, share, solved_nodes).is_none() {
        tree.request_full(TailFailure::Invalidated);
        return None;
    }
    let after = A::Float::bits(share);
    let place_all = tail_replaces_prefix(before, after, refresh_output, matches!(arrange, Arrange::Start));
    let computed = if before != after {
        let Some(updated) = tree.resize_prefix(cache, axis, share, first_added) else {
            tree.request_full(TailFailure::Invalidated);
            return None;
        };
        cycle_rules::add_count(updated, 1)
    } else if exhausted { 0 } else { 1 };
    let remaining = tree.count_nodes();
    let mut suffix = UpdateSuffix { parent, rect, computed, place_all };
    if let Err(error) = scan_siblings(tree, first_added, remaining, &mut suffix) {
        tree.request_full(match error {
            ScanError::Limit => TailFailure::Invalidated,
            ScanError::Visit(reason) => reason,
        });
        return None;
    }
    if suffix.place_all {
        if refresh_output || tree.rounds_output() {
            tree.place_tree();
        } else if let Some(first) = tree.first_child_in_stack(parent) {
            let origin = Xy::new(rect.x[0], rect.y[0]);
            tree.place_stack(parent, first, rect, origin);
        }
    }
    Some(suffix.computed)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn independent_declaration(p: &LayoutParams, axis: Axis, size: Option<Size>) -> bool {
    match size {
        Some(Size::AspectRatio(_)) => false,
        Some(Size::FitContent | Size::Auto) => !p.intrinsic_reads_other_axis(axis),
        _ => true,
    }
}

// Changing a leaf's main size cannot change these cross-axis slots.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn independent_fill(p: &LayoutParams, is_leaf: bool, main: Axis) -> bool {
    let cross = main.other();
    is_leaf && matches!(p.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        && independent_declaration(p, cross, Some(*p.size.component(cross)))
        && independent_declaration(p, cross, *p.min_size.component(cross))
        && independent_declaration(p, cross, *p.max_size.component(cross))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn pixel_bound<F: TailFloat>(bound: Option<Size>) -> bool {
    match bound {
        None => true,
        Some(Size::Pixels(size)) => F::finite(size),
        _ => false,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn collect_child<I: Copy, F: TailFloat>(cache: &mut TailCache<I>, p: &LayoutParams, is_leaf: bool, axis: Axis) -> Option<()> {
    if p.disabled || p.free_placement { return Some(()); }
    if p.has_auto_margin(axis) { return None; }
    let [start, end] = F::margins(p, axis);
    let margin = start + end;
    if margin < 0.0 || !F::finite(margin) { return None; }
    cache.space_without_gaps = fill_budget::charge(cache.space_without_gaps, margin);
    let min = *p.min_size.component(axis);
    let max = *p.max_size.component(axis);
    match *p.size.component(axis) {
        Size::Fill if p.fill_weight > 0.0 && F::finite(p.fill_weight) => {
            if !pixel_bound::<F>(min) || !pixel_bound::<F>(max) { return None; }
            cache.bounded_fills |= min.is_some() || max.is_some();
            cache.fills = cache.fills.checked_add(1)?;
            cache.independent_fills &= independent_fill(p, is_leaf, axis);
        }
        Size::Pixels(size) if F::finite(size) && size >= 0.0 && min.is_none() && max.is_none() => {
            cache.space_without_gaps = fill_budget::charge(cache.space_without_gaps, size);
        }
        _ => return None,
    }
    Some(())
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
enum PrefixFinish { Skip, Bounded, Warn, Done }

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn active_fill(p: LayoutParams, axis: Axis) -> bool {
    !p.disabled && !p.free_placement && (if axis is X { p.size.x } else { p.size.y }) is Fill
}

pub(crate) open spec fn prefix_bounds(p: LayoutParams, axis: Axis) -> bool {
    if axis is X { p.min_size.x.is_some() || p.max_size.x.is_some() }
    else { p.min_size.y.is_some() || p.max_size.y.is_some() }
}

pub(crate) open spec fn resized_prefix<F: FrameFloat>(
    p: LayoutParams, values: Seq<f32>, axis: Axis, share: f32, bounded: bool,
) -> Seq<f32> {
    if !active_fill(p, axis) {
        values
    } else {
        let value = F::product(share, p.fill_weight);
        let regular = values.update(cycle_rules::slot_index(axis.index(), Kind::Regular) as int, value);
        if bounded && prefix_bounds(p, axis) { regular }
        else { regular.update(cycle_rules::slot_index(axis.index(), Kind::Final) as int, value) }
    }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures
        final(values)@ == resized_prefix::<F>(*p, old(values)@, axis, share, bounded),
        (out is Skip) == !active_fill(*p, axis),
        (out is Bounded) == (active_fill(*p, axis) && bounded && prefix_bounds(*p, axis)),
        (out is Warn) == (active_fill(*p, axis) && !(bounded && prefix_bounds(*p, axis))
            && !F::finite_word(F::product(share, p.fill_weight))),
    no_unwind
))]
fn resize_child<F: FrameFloat>(p: &LayoutParams, values: &mut [f32; N_SLOTS], axis: Axis, share: f32, bounded: bool) -> PrefixFinish {
    if p.disabled || p.free_placement || !matches!(*p.size.component(axis), Size::Fill) { return PrefixFinish::Skip; }
    let value = F::multiply(share, p.fill_weight);
    write_tail_slot(values, axis, Kind::Regular, value);
    if bounded && (p.min_size.component(axis).is_some() || p.max_size.component(axis).is_some()) {
        return PrefixFinish::Bounded;
    }
    write_tail_slot(values, axis, Kind::Final, value);
    if F::finite(value) { PrefixFinish::Done } else { PrefixFinish::Warn }
}

#[cfg(verus_keep_ghost)]
verus! {
spec fn tail_leaf_shape(p: &LayoutParams, axis: Axis, last: bool, leaf: bool) -> bool {
    let (size, min, max) = if axis.index() == 0 { (p.size.x, p.min_size.x, p.max_size.x) }
        else { (p.size.y, p.min_size.y, p.max_size.y) };
    &&& last && leaf && !p.disabled && !p.free_placement
    &&& unbounded_fill(size, min, max)
    &&& (p.children_layout is Free || p.children_layout is Stack)
    &&& p.grid_span.x <= 1 && p.grid_span.y <= 1
}
}

/// An admitted edit changes only the terminal leaf suffix of one Stack.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(eligible =>
    ensures eligible == tail_leaf_shape(p, axis, last, leaf),
    no_unwind
))]
fn tail_leaf(p: &LayoutParams, axis: Axis, last: bool, leaf: bool) -> bool {
    last && leaf && !p.disabled && !p.free_placement
        && unbounded_fill(*p.size.component(axis), *p.min_size.component(axis), *p.max_size.component(axis))
        && matches!(p.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        && p.grid_span.x <= 1 && p.grid_span.y <= 1
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(keeps =>
    ensures keeps == (!editing_head && !head.disabled && !head.free_placement
        && (if axis.index() == 0 { head.size.y } else { head.size.x }).is_flex()),
    no_unwind
))]
fn keeps_cross_flex(head: &LayoutParams, axis: Axis, editing_head: bool) -> bool {
    !editing_head && !head.disabled && !head.free_placement && head.size.component(axis.other()).is_flex()
}

#[cfg(not(verus_keep_ghost))]
impl<T> LayoutTree<T> {
    pub(super) fn record_tail_edit(&mut self, id: NodeKey, parent: NodeKey, inserting: bool) {
        if matches!(self.tail_edits, TailEdits::Other) { return; }
        let prior = std::mem::replace(&mut self.tail_edits, TailEdits::Other);
        let (Some(node), Some(parent_node)) = (self.nodes.get(id), self.nodes.get(parent)) else { return; };
        let delta = match prior {
            TailEdits::None => empty_delta(),
            TailEdits::Stack { parent: previous, delta } if parent == previous => delta,
            _ => return,
        };
        let ChildrenLayout::Stack { axis, .. } = parent_node.params.children_layout else { return };
        let p = &node.params;
        if !tail_leaf(p, axis, node.next_sibling.is_none(), node.first_child.is_none())
            || !p.fill_weight.is_finite() || p.fill_weight <= 0.0 || margins(p, axis) != [0.0; 2] || p.has_auto_margin(axis)
        {
            return;
        }
        if p.size[axis.other()].is_flex() {
            // The first sibling keeps the parent's cross-axis flex flag set, even
            // across a sequence of pops. Otherwise let preparation refresh the flag.
            let Some(first) = parent_node.first_child else { return };
            let Some(head) = self.nodes.get(first).map(|head| &head.params) else { return; };
            if !keeps_cross_flex(head, axis, first == id) {
                return;
            }
        }
        if let Some(delta) = delta.record(id, inserting) {
            self.tail_edits = TailEdits::Stack { parent, delta };
        }
    }

    fn stack_tail(&self, parent: NodeKey, axis: Axis, inner: f32) -> Option<StackTail> {
        let mut stack = StackTail { parent, fills: 0, space_without_gaps: inner, independent_fills: true, bounded_fills: false };
        let first = self.nodes.get(parent)?.first_child;
        scan_siblings(&mut (), first, self.nodes.len(), &mut |id| -> Result<_, ()> {
            let node = self.nodes.get(id).ok_or(())?;
            collect_child::<_, RustTailFloat>(&mut stack, &node.params, node.first_child.is_none(), axis).ok_or(())?;
            Ok(node.next_sibling)
        }).ok()?;
        Some(stack)
    }
}

#[cfg(not(verus_keep_ghost))]
impl<T, M, C> Adapter<'_, T, M, C>
where
    M: FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>,
    C: FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
{
    /// All affected leaves already have solved bounds and dependency levels. Their
    /// two main-axis slots are the only measurements in the prefix that can change.
    fn resize_fill_leaves(&mut self, stack: StackTail, axis: Axis, share: f32, first_added: Option<NodeKey>) -> Option<u32> {
        let mut updated: u32 = 0;
        let first = self.first_child(stack.parent);
        scan_siblings(&mut (), first, self.tree.nodes.len(), &mut |id| -> Result<_, ()> {
            if Some(id) == first_added { return Ok(None); }
            let child = self.tree.nodes.get_mut(id).ok_or(())?;
            let next = child.next_sibling;
            match resize_child::<RustFloat>(&child.params, &mut child.layout.values, axis, share, stack.bounded_fills) {
                PrefixFinish::Skip => return Ok(next),
                PrefixFinish::Bounded => {
                    self.finish_slot(Slot { node: id, axis, kind: Kind::Final });
                }
                PrefixFinish::Warn => self.warn(LayoutWarning::NotFinite { node: id, axis }),
                PrefixFinish::Done => {}
            }
            updated = cycle_rules::add_count(updated, 2);
            Ok(next)
        }).ok()?;
        Some(updated)
    }

    pub(super) fn solve_stack_tail(
        &mut self, parent: NodeKey, delta: TailDelta<NodeKey>, window: Xy<f32>,
    ) -> Option<u32> {
        run_tail(self, parent, delta, window)
    }
}

#[cfg(not(verus_keep_ghost))]
impl<T, M, C> TailAccess for Adapter<'_, T, M, C>
where
    M: FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>,
    C: FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
{
    type Id = NodeKey;
    type Float = RustTailFloat;

    #[inline]
    fn window_state(&self, window: Xy<f32>) -> Option<(u32, bool)> {
        let global = &self.tree.layout_data;
        if global.pending_full_solve.is_some() || global.has_cycle || !global.window_size.same_input(&window) { return None; }
        Some((global.n_nodes_solved, global.placement_scale_changed))
    }

    #[inline(always)]
    fn parent_record(&self, parent: NodeKey) -> Option<ParentRecord<'_>> {
        let node = self.tree.nodes.get(parent)?;
        Some(ParentRecord {
            layout: node.params.children_layout, values: &node.layout.values, rect: node.rect,
            count: node.layout.n_placed_children, flags: node.layout.flags.0,
            block_item: node.layout.flags.is_block_item(),
        })
    }

    #[inline(always)]
    fn reads_children(&self, parent: NodeKey) -> bool { self.size_depends_on_children(parent) }

    #[inline(always)]
    fn padding(&self, parent: NodeKey, axis: Axis) -> f32 { self.total_padding(parent, axis) }

    #[inline(always)]
    fn count_nodes(&self) -> usize { self.tree.nodes.len() }

    #[inline(always)]
    fn cache(&self, parent: NodeKey) -> Option<StackTail> { self.tree.tail_stack.filter(|stack| stack.parent == parent) }

    #[inline(always)]
    fn collect_cache(&self, parent: NodeKey, axis: Axis, inner: f32) -> Option<StackTail> {
        self.tree.stack_tail(parent, axis, inner)
    }

    #[inline(always)]
    fn read_fill(&self, id: NodeKey, axis: Axis) -> Option<(Option<NodeKey>, bool)> {
        let child = self.tree.nodes.get(id)?;
        Some((child.next_sibling, independent_fill(&child.params, child.first_child.is_none(), axis)))
    }

    #[inline(always)]
    fn begin_share(&mut self, parent: NodeKey, count: u32) -> Option<()> {
        let layout = &mut self.tree.nodes.get_mut(parent)?.layout;
        begin_share_record(&mut layout.n_placed_children, &mut layout.structural_change, count);
        Some(())
    }

    #[inline(always)]
    fn measure_share(&mut self, parent: NodeKey, axis: Axis) -> f32 {
        self.solve_even_share(parent, axis)
    }

    #[inline(always)]
    fn finish_share(&mut self, cache: StackTail, axis: Axis, share: f32, solved_nodes: u32) -> Option<()> {
        let node = self.tree.nodes.get_mut(cache.parent)?;
        // Appended leaves read EvenShare without contributing a dependency to it.
        write_tail_slot(&mut node.layout.values, axis, Kind::EvenShare, share);
        self.tree.layout_data.n_nodes_solved = solved_nodes;
        self.tree.layout_data.clear();
        self.tree.tail_stack = Some(cache);
        Some(())
    }

    #[inline(always)]
    fn resize_prefix(&mut self, cache: StackTail, axis: Axis, share: f32, first_added: Option<NodeKey>) -> Option<u32> {
        self.resize_fill_leaves(cache, axis, share, first_added)
    }

    #[inline(always)]
    fn links(&self, child: NodeKey) -> Option<(Option<NodeKey>, Option<NodeKey>)> {
        let node = self.tree.nodes.get(child)?;
        Some((node.next_sibling, node.prev_sibling))
    }

    #[inline(always)]
    fn rect(&self, child: NodeKey) -> Option<XyRect> { Some(self.tree.nodes.get(child)?.rect) }

    #[inline(always)]
    fn measure_appended(&mut self, child: NodeKey) -> Option<u32> {
        self.measure_subtree(child).map(|(_, slots, _)| slots)
    }

    #[inline(always)]
    fn place_appended(&mut self, parent: NodeKey, child: NodeKey, rect: XyRect, preceding: Option<(NodeKey, XyRect)>) -> bool {
        self.place_appended_stack_leaf(parent, child, rect, preceding)
    }

    #[inline(always)]
    fn rounds_output(&self) -> bool { self.tree.layout_data.pixel_scale.is_some() }

    #[inline(always)]
    fn first_child_in_stack(&self, parent: NodeKey) -> Option<NodeKey> { self.first_child(parent) }

    #[inline(always)]
    fn place_tree(&mut self) { self.place_nodes::<false>(); }

    #[inline(always)]
    fn place_stack(&mut self, parent: NodeKey, first: NodeKey, rect: XyRect, origin: Xy<f32>) {
        self.place_children::<false>(parent, first, rect, origin, None);
    }

    #[inline(always)]
    fn request_full(&mut self, reason: TailFailure) {
        let reason = match reason {
            TailFailure::Invalidated => IncrementalRelayoutOutcome::FallbackInvalidated,
            TailFailure::Flow => IncrementalRelayoutOutcome::FallbackFlow,
        };
        self.tree.layout_data.request_full_solve(reason);
    }
}
