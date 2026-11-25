//! Select rebuilt subtrees from the real per-node sizing and placement records.
#![allow(unexpected_cfgs)]

use crate::declarations::ChildrenLayout;
#[cfg(verus_keep_ghost)]
use crate::declarations::LayoutParams;
use crate::node_flags::NodeFlags;
use crate::prepare_nodes::Records;
use crate::vec_memory::{FallibleVecMemory, VecMemory, try_append};
use crate::work_stack;
#[cfg(not(verus_keep_ghost))]
use super::region_list;
#[cfg(verus_keep_ghost)]
use super::kernel as region_list;
#[cfg(not(verus_keep_ghost))]
use crate::{StructuralChange, placement_work, region_policy, solve::{cycle_rules, prepare_walk}};
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, placement::kernel as placement_work, prepare_walk,
    prepare_frame::Order, prepare_nodes::live, structural::kernel::StructuralChange,
    structural_plan::policy as region_policy};
use placement_work::PlacementWork;
use prepare_walk::{ChildStep, State};
#[cfg(verus_keep_ghost)]
use region_policy::RefreshModel;
#[cfg(verus_keep_ghost)]
use crate::dependencies::sizing_requests::live::chain;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Disjoint subtrees to measure in document order, plus retained population counts.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Plan<I> {
    pub regions: Vec<I>,
    pub retained: SubtreeCounts,
    pub complete: bool,
}

#[derive(Default, Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct SubtreeCounts {
    pub(crate) nodes: u32,
    pub(crate) blocks: usize,
    pub(crate) has_flow: bool,
    pub(crate) has_cycle: bool,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn empty_counts() -> SubtreeCounts {
    SubtreeCounts { nodes: 0, blocks: 0, has_flow: false, has_cycle: false }
}

impl SubtreeCounts {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn empty() -> Self { empty_counts() }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn include(&mut self, flags: NodeFlags) {
        // A disabled node has no solved slots. An enabled node has both final sizes.
        if flags.0 != 0 {
            self.nodes = cycle_rules::add_count(self.nodes, 1);
            self.blocks = self.blocks.saturating_add(if flags.is_block_container() { 1 } else { 0 });
            self.has_flow |= flags.has_flow();
            self.has_cycle |= flags.has_cycle();
        }
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct Frame<I> {
    node: I,
    next: Option<I>,
    start: usize,
    retained: SubtreeCounts,
    independent: Option<bool>,
    changed_children: bool,
    coupled: bool,
    placement: PlacementWork,
    #[cfg(verus_keep_ghost)]
    order: Ghost<Order<I>>,
}

pub(crate) type Suspended<I> = (Frame<I>, I);

#[cfg(not(verus_keep_ghost))]
pub(crate) trait SourceModel: Records {
    type Refresh: region_policy::RefreshSource<Id = Self::Id> + ?Sized;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait SourceModel: Records {
    type Refresh: region_policy::RefreshSource<Id = Self::Id> + ?Sized;
    spec fn refresh_view(&self) -> &Self::Refresh;
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Source: SourceModel {
    type Memory: VecMemory + FallibleVecMemory;

    #[cfg_attr(verus_keep_ghost, verus_spec(parent =>
        requires live(self, node), self.order().ordered(),
        ensures parent == (self.order().parent)(node),
            parent.is_some() ==> live(self, parent.unwrap()),
        no_unwind
    ))]
    fn parent_id(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(view =>
        requires live(self, node),
        ensures view == self.refresh_view(), view.live(node),
            view.layout(node) == self.layout_params(node), view.parent_flags(node) == self.layout_record(node).flags,
            chain(view.siblings(node), (self.order().first)(node), self.order().sibling),
            forall |i: int| 0 <= i < view.siblings(node).len() ==> view.live(#[trigger] view.siblings(node)[i]),
        no_unwind
    ))]
    fn refresh_source(&self, node: Self::Id) -> &Self::Refresh;
}

#[cfg(verus_keep_ghost)]
verus! {
/// The planner changes markings, placement work and child summaries. The
/// sizing arrays and their phase bits remain the previous physical cache.
#[verifier::reject_recursive_types(I)]
pub(crate) struct SizingCache<I> {
    pub order: Order<I>,
    pub declarations: spec_fn(I) -> LayoutParams,
    pub words: spec_fn(I) -> [f32; cycle_rules::N_SLOTS],
    pub protected_flags: spec_fn(I) -> u32,
}

pub(crate) open spec fn sizing_cache<T: Records + ?Sized>(tree: &T) -> SizingCache<T::Id> {
    SizingCache {
        order: tree.order(),
        declarations: |id: T::Id| tree.layout_params(id),
        words: |id: T::Id| tree.layout_record(id).values,
        protected_flags: |id: T::Id| tree.layout_record(id).flags.0 & !region_policy::REFRESH_FLAGS,
    }
}

pub(crate) open spec fn ready_free_parent<T: Records + ?Sized>(tree: &T, id: T::Id) -> bool {
    let params = tree.layout_params(id);
    let flags = tree.layout_record(id).flags.0;
    &&& params.children_layout is Free
    &&& !params.disabled
    &&& !region_policy::has_intrinsic(&params)
    &&& flags & NodeFlags::BLOCK_ITEM == 0
    &&& cycle_rules::read_state(flags, cycle_rules::slot_index(0, cycle_rules::Kind::Final) as u32) == cycle_rules::SOLVED
    &&& cycle_rules::read_state(flags, cycle_rules::slot_index(1, cycle_rules::Kind::Final) as u32) == cycle_rules::SOLVED
}

pub(crate) open spec fn acyclic_parent<T: Records + ?Sized>(tree: &T, id: T::Id) -> bool {
    tree.layout_record(id).flags.0 & (cycle_rules::CYCLE_X | cycle_rules::CYCLE_Y) == 0
}

pub(crate) open spec fn first_leaf_attachment<T: Records + ?Sized>(tree: &T, parent: T::Id, plan: &Plan<T::Id>) -> Option<T::Id> {
    match (tree.order().first)(parent) {
        Some(child) if plan.complete && plan.regions@.len() == 0
            && tree.layout_record(parent).structural_change is Children
            && ready_free_parent(tree, parent) && acyclic_parent(tree, parent)
            && (tree.order().sibling)(child).is_none() && (tree.order().first)(child).is_none()
            && tree.layout_record(child).structural_change is Subtree => Some(child),
        _ => None,
    }
}

proof fn cache_keeps_cycle_marks<T: Records + ?Sized>(before: &T, after: &T, id: T::Id)
    requires sizing_cache(before) == sizing_cache(after),
    ensures acyclic_parent(before, id) == acyclic_parent(after, id),
{
    let original = before.layout_record(id).flags.0;
    let current = after.layout_record(id).flags.0;
    let preserve = region_policy::REFRESH_FLAGS;
    let cycles = cycle_rules::CYCLE_X | cycle_rules::CYCLE_Y;
    assert(region_policy::REFRESH_FLAGS & (cycle_rules::CYCLE_X | cycle_rules::CYCLE_Y) == 0) by(compute_only);
    let saved = sizing_cache(before);
    let observed = sizing_cache(after);
    assert((observed.protected_flags)(id) == current & !region_policy::REFRESH_FLAGS);
    assert((saved.protected_flags)(id) == original & !region_policy::REFRESH_FLAGS);
    assert((observed.protected_flags)(id) == (saved.protected_flags)(id));
    assert(current & !region_policy::REFRESH_FLAGS == original & !region_policy::REFRESH_FLAGS);
    assert(current & !preserve == original & !preserve);
    assert(current & cycles == original & cycles) by(bit_vector)
        requires current & !preserve == original & !preserve, preserve & cycles == 0;
}

fn save_attachment<A: Source + ?Sized>(tree: &A, parent: A::Id, plan: &Plan<A::Id>)
    -> (saved: Ghost<Option<(A::Id, A::Id)>>)
    ensures saved@ == match first_leaf_attachment(tree, parent, plan) {
        Some(child) => Some((parent, child)), None => None,
    }, no_unwind
{
    Ghost(match first_leaf_attachment(tree, parent, plan) {
        Some(child) => Some((parent, child)), None => None,
    })
}

proof fn cache_unchanged<T: Records + ?Sized>(prior: &T, after: &T)
    requires prior.order() == after.order(),
        forall |id: T::Id| #[trigger] after.layout_params(id) == prior.layout_params(id),
        forall |id: T::Id| #[trigger] after.layout_record(id).values == prior.layout_record(id).values,
        forall |id: T::Id| #[trigger] after.layout_record(id).flags.0 & !region_policy::REFRESH_FLAGS
            == prior.layout_record(id).flags.0 & !region_policy::REFRESH_FLAGS,
    ensures sizing_cache(prior) == sizing_cache(after),
{
    let previous = sizing_cache(prior);
    let next = sizing_cache(after);
    assert(previous.declarations =~= next.declarations);
    assert(previous.words =~= next.words);
    assert(previous.protected_flags =~= next.protected_flags);
}

pub(crate) open spec fn selected_live<I>(plan: &Plan<I>, order: Order<I>) -> bool {
    forall |i: int| 0 <= i < plan.regions.len() ==> (order.live)(#[trigger] plan.regions@[i])
}

/// A promotion preserves all earlier choices and replaces the attempted
/// suffix by the enclosing root. Allocation failure keeps only the prefix.
pub(crate) open spec fn replaced<I>(before: &Plan<I>, after: &Plan<I>, start: usize, root: I) -> bool {
    if before.complete {
        let prefix = before.regions@.take(vstd::math::min(start as int, before.regions.len() as int));
        after.regions@ == if after.complete { prefix.push(root) } else { prefix }
    } else {
        !after.complete && after.regions@ == before.regions@
    }
}

pub(crate) open spec fn covers<I>(regions: Seq<I>, order: Order<I>, node: I) -> bool {
    exists |i: int| 0 <= i < regions.len() && order.inside(#[trigger] regions[i], node)
}

/// Use the actual promotion contract to lift coverage through a parent cut.
/// Its geometric premise is that the discarded suffix was inside that parent.
pub(crate) proof fn promotion_preserves_covered_node<I>(before: &Plan<I>, after: &Plan<I>, start: usize,
    order: Order<I>, parent: I, node: I,
)
    requires before.complete, after.complete, replaced(before, after, start, parent),
        forall |i: int| start <= i < before.regions.len() ==> order.inside(parent, #[trigger] before.regions@[i]),
        covers(before.regions@, order, node),
    ensures covers(after.regions@, order, node),
{
    let regions = before.regions@;
    let at = choose |i: int| 0 <= i < regions.len() && order.inside(#[trigger] regions[i], node);
    let length = vstd::math::min(start as int, regions.len() as int);
    if at < length {
        assert(after.regions@[at] == regions[at]);
    } else {
        assert(order.inside(parent, regions[at]));
        assert(order.inside(parent, node));
        assert(after.regions@[length] == parent);
    }
}

spec fn frame_live<I>(frame: Frame<I>, order: Order<I>) -> bool {
    &&& frame.order@ == order
    &&& order.ordered()
    &&& (order.live)(frame.node)
    &&& frame.next.is_some() ==> order.child(frame.node, frame.next.unwrap())
}

/// Pairwise ordered, disjoint half-open subtree intervals.
pub(crate) open spec fn ordered_cuts<I>(regions: Seq<I>, order: Order<I>) -> bool {
    forall |i: int, j: int| 0 <= i < j < regions.len()
        ==> (order.interval)((#[trigger] regions[i])).1 <= (order.interval)((#[trigger] regions[j])).0
}

spec fn cursor_limit<I>(order: Order<I>, frame: Frame<I>) -> nat {
    match frame.next {
        Some(node) => (order.interval)(node).0,
        None => (order.interval)(frame.node).1,
    }
}

pub(crate) open spec fn before<I>(regions: Seq<I>, order: Order<I>, node: I) -> bool {
    forall |i: int| 0 <= i < regions.len()
        ==> (order.interval)(#[trigger] regions[i]).1 <= (order.interval)(node).0
}

spec fn fits<I>(regions: Seq<I>, order: Order<I>, frame: Frame<I>) -> bool {
    &&& frame_live(frame, order)
    &&& frame.start <= regions.len()
    &&& forall |i: int| 0 <= i < regions.len() ==> {
        let span = (order.interval)(#[trigger] regions[i]);
        if i < frame.start { span.1 <= (order.interval)(frame.node).0 }
        else { (order.interval)(frame.node).0 < span.0 && span.1 <= cursor_limit(order, frame) }
    }
}

spec fn nested<I>(order: Order<I>, inner: Frame<I>, outer: Frame<I>) -> bool {
    &&& outer.start <= inner.start
    &&& (order.interval)(outer.node).0 < (order.interval)(inner.node).0
    &&& (order.interval)(inner.node).1 <= cursor_limit(order, outer)
}

spec fn frontier<I>(regions: Seq<I>, order: Order<I>, active: Option<Frame<I>>, stack: Seq<(Frame<I>, I)>) -> bool {
    &&& ordered_cuts(regions, order)
    &&& forall |i: int| 0 <= i < stack.len() ==> fits(regions, order, (#[trigger] stack[i]).0)
    &&& forall |i: int, j: int| 0 <= i < j < stack.len()
        ==> nested(order, (#[trigger] stack[j]).0, (#[trigger] stack[i]).0)
    &&& if let Some(frame) = active {
        fits(regions, order, frame)
            && forall |i: int| 0 <= i < stack.len() ==> nested(order, frame, (#[trigger] stack[i]).0)
    } else { true }
}

fn save_regions<I>(plan: &Plan<I>) -> (saved: Ghost<Seq<I>>)
    ensures saved@ == plan.regions@,
    no_unwind
{
    Ghost(plan.regions@)
}

proof fn append_keeps_order<I>(regions: Seq<I>, out: Seq<I>, order: Order<I>, node: I)
    requires ordered_cuts(regions, order), before(regions, order, node),
        out == regions || out == regions.push(node),
    ensures ordered_cuts(out, order),
{
    assert forall |i: int, j: int| 0 <= i < j < out.len() implies
        (order.interval)((#[trigger] out[i])).1 <= (order.interval)((#[trigger] out[j])).0 by {
        assert(out[i] == regions[i]);
        if j < regions.len() {
            assert(out[j] == regions[j]);
        } else {
            assert(out[j] == node);
        }
    }
}

proof fn child_start<I>(regions: Seq<I>, order: Order<I>, frame: Frame<I>, child: I)
    requires fits(regions, order, frame), frame.next == Some(child),
    ensures before(regions, order, child),
{
    assert forall |i: int| 0 <= i < regions.len() implies
        (order.interval)(#[trigger] regions[i]).1 <= (order.interval)(child).0 by {
        assert(order.child(frame.node, child));
    }
}

proof fn cursor_progress<I>(order: Order<I>, frame: Frame<I>, resumed: Frame<I>, child: I)
    requires frame_live(frame, order), frame.next == Some(child),
        resumed.node == frame.node, resumed.start == frame.start,
        resumed.next == (order.sibling)(child),
    ensures cursor_limit(order, frame) < (order.interval)(child).1 <= cursor_limit(order, resumed),
{
    order.node_facts(child);
    assert((order.parent)(child) == Some(frame.node));
}

proof fn child_completed<I>(prior: Seq<I>, out: Seq<I>, order: Order<I>,
    frame: Frame<I>, resumed: Frame<I>, child: I, stack: Seq<(Frame<I>, I)>)
    requires frontier(prior, order, Some(frame), stack), frame_live(resumed, order),
        frame.next == Some(child), resumed.next == (order.sibling)(child),
        resumed.node == frame.node, resumed.start == frame.start,
        out == prior || out == prior.push(child),
    ensures frontier(out, order, Some(resumed), stack),
{
    child_start(prior, order, frame, child);
    append_keeps_order(prior, out, order, child);
    cursor_progress(order, frame, resumed, child);
    assert forall |i: int| 0 <= i < out.len() implies {
        let span = (order.interval)(#[trigger] out[i]);
        if i < resumed.start { span.1 <= (order.interval)(resumed.node).0 }
        else { (order.interval)(resumed.node).0 < span.0 && span.1 <= cursor_limit(order, resumed) }
    } by {
        if i < prior.len() { assert(out[i] == prior[i]); }
        else { assert(out[i] == child); }
    }
    assert(fits(out, order, resumed));
    assert forall |k: int| 0 <= k < stack.len() implies fits(out, order, (#[trigger] stack[k]).0) by {
        let outer = stack[k].0;
        assert forall |i: int| 0 <= i < out.len() implies {
            let span = (order.interval)(#[trigger] out[i]);
            if i < outer.start { span.1 <= (order.interval)(outer.node).0 }
            else { (order.interval)(outer.node).0 < span.0 && span.1 <= cursor_limit(order, outer) }
        } by {
            if i < prior.len() { assert(out[i] == prior[i]); }
            else { assert(out[i] == child); }
        }
    }
    assert forall |i: int| 0 <= i < stack.len() implies nested(order, resumed, (#[trigger] stack[i]).0) by {};
}

proof fn descend_frontier<I>(regions: Seq<I>, order: Order<I>, frame: Frame<I>, resumed: Frame<I>,
    child: I, branch: Frame<I>, stack: Seq<(Frame<I>, I)>)
    requires frontier(regions, order, Some(frame), stack), frame_live(resumed, order), frame_live(branch, order),
        frame.next == Some(child), resumed.next == (order.sibling)(child),
        resumed.node == frame.node, resumed.start == frame.start,
        branch.node == child, branch.start == regions.len(),
    ensures frontier(regions, order, Some(branch), stack.push((resumed, child))),
{
    child_completed(regions, regions, order, frame, resumed, child, stack);
    child_start(regions, order, frame, child);
    cursor_progress(order, frame, resumed, child);
    assert(fits(regions, order, branch));
    assert(nested(order, branch, resumed));
    let enlarged = stack.push((resumed, child));
    assert forall |i: int| 0 <= i < enlarged.len() implies fits(regions, order, (#[trigger] enlarged[i]).0) by {
        if i < stack.len() { assert(enlarged[i] == stack[i]); }
        else { assert(enlarged[i] == (resumed, child)); }
    }
    assert forall |i: int, j: int| 0 <= i < j < enlarged.len() implies
        nested(order, (#[trigger] enlarged[j]).0, (#[trigger] enlarged[i]).0) by {
        assert(enlarged[i] == stack[i]);
        if j < stack.len() { assert(enlarged[j] == stack[j]); }
        else { assert(enlarged[j] == (resumed, child)); }
    }
    assert forall |i: int| 0 <= i < enlarged.len() implies nested(order, branch, (#[trigger] enlarged[i]).0) by {
        if i < stack.len() { assert(enlarged[i] == stack[i]); }
        else { assert(enlarged[i] == (resumed, child)); }
    }
}

proof fn finish_frontier<I>(prior: Seq<I>, out: Seq<I>, order: Order<I>, frame: Frame<I>, stack: Seq<(Frame<I>, I)>)
    requires frontier(prior, order, Some(frame), stack),
        out == prior || out == prior.take(frame.start as int) || out == prior.take(frame.start as int).push(frame.node),
    ensures frontier(out, order, None, stack),
{
    if out != prior {
        let prefix = prior.take(frame.start as int);
        assert(out == prefix || out == prefix.push(frame.node));
        assert(ordered_cuts(prefix, order));
        assert(before(prefix, order, frame.node));
        append_keeps_order(prefix, out, order, frame.node);
        assert forall |k: int| 0 <= k < stack.len() implies fits(out, order, (#[trigger] stack[k]).0) by {
            let outer = stack[k].0;
            assert forall |i: int| 0 <= i < out.len() implies {
                let span = (order.interval)(#[trigger] out[i]);
                if i < outer.start { span.1 <= (order.interval)(outer.node).0 }
                else { (order.interval)(outer.node).0 < span.0 && span.1 <= cursor_limit(order, outer) }
            } by {
                if i < prefix.len() { assert(out[i] == prior[i]); }
                else { assert(out[i] == frame.node); }
            }
        }
    }
}

proof fn resume_frontier<I>(regions: Seq<I>, order: Order<I>, old: Frame<I>, resumed: Frame<I>,
    child: I, stack: Seq<(Frame<I>, I)>)
    requires frontier(regions, order, None, stack.push((old, child))), frame_live(resumed, order),
        resumed.node == old.node, resumed.next == old.next, resumed.start == old.start,
    ensures frontier(regions, order, Some(resumed), stack),
{
    let enlarged = stack.push((old, child));
    assert(enlarged[stack.len() as int] == (old, child));
    assert(fits(regions, order, (enlarged[stack.len() as int]).0));
    assert(fits(regions, order, old));
    assert(fits(regions, order, resumed));
    assert forall |i: int| 0 <= i < stack.len() implies fits(regions, order, (#[trigger] stack[i]).0) by {
        assert(enlarged[i] == stack[i]);
    }
    assert forall |i: int, j: int| 0 <= i < j < stack.len() implies
        nested(order, (#[trigger] stack[j]).0, (#[trigger] stack[i]).0) by {
        assert(enlarged[i] == stack[i] && enlarged[j] == stack[j]);
    }
    assert forall |i: int| 0 <= i < stack.len() implies nested(order, resumed, (#[trigger] stack[i]).0) by {
        assert(enlarged[i] == stack[i]);
        assert(nested(order, (enlarged[stack.len() as int]).0, enlarged[i].0));
    }
}

spec fn remaining<I>(frame: Frame<I>) -> nat {
    match frame.next {
        Some(cursor) => (3 * ((frame.order@.interval)(frame.node).1 - (frame.order@.interval)(cursor).0)) as nat,
        None => 0,
    }
}

fn save_order<A: Records + ?Sized>(access: &A) -> (order: Ghost<Order<A::Id>>)
    ensures order@ == access.order(),
    no_unwind
{
    Ghost(access.order())
}

fn save_frame<I>(frame: &Frame<I>) -> (saved: Ghost<Frame<I>>)
    ensures saved@ == *frame,
    no_unwind
{
    Ghost(*frame)
}

proof fn descend_progress<I>(order: Order<I>, before: Frame<I>, after: Frame<I>, child: I, branch: Frame<I>)
    requires frame_live(before, order), frame_live(after, order), frame_live(branch, order),
        before.next == Some(child), after.node == before.node, after.next == (order.sibling)(child), branch.node == child,
    ensures remaining(after) + remaining(branch) + 2 < remaining(before),
{
    order.node_facts(child);
    let bounds = order.interval;
    let start = bounds(child).0;
    let end = bounds(child).1;
    let parent_end = bounds(before.node).1;
    let resume_at = match after.next { Some(next) => bounds(next).0, None => parent_end };
    let first = match branch.next { Some(next) => bounds(next).0, None => end };
    prepare_walk::suffix_and_descendant_budget(start, end, parent_end, resume_at, first);
}
}

/// Run the same physical sibling scan for every kept parent and install
/// its count/flags only on acceptance.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(accepted =>
    requires live(old(tree), node),
    ensures final(tree).order() == old(tree).order(), sizing_cache(final(tree)) == sizing_cache(old(tree)),
        accepted == region_policy::refresh_eligible(old(tree).refresh_view(), node),
        ready_free_parent(old(tree), node) ==> accepted,
        final(tree).layout_record(node).placement == old(tree).layout_record(node).placement,
        forall |id: A::Id| id != node ==> #[trigger] final(tree).layout_record(id) == old(tree).layout_record(id),
    no_unwind
))]
fn refresh_independent_parent<A: Source + ?Sized>(tree: &mut A, node: A::Id) -> bool {
    let source = tree.refresh_source(node);
    #[cfg(verus_keep_ghost)]
    proof! { assert(ready_free_parent(tree, node) ==> region_policy::refresh_eligible(source, node)); }
    let Some(refreshed) = region_policy::refresh_parent(source, node) else { return false; };
    let record = tree.edit(node);
    record.flags = refreshed.flags;
    record.n_placed_children = refreshed.placed_children;
    #[cfg(verus_keep_ghost)]
    proof! { cache_unchanged(old(tree), tree); }
    true
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node),
    ensures final(tree).order() == old(tree).order(), sizing_cache(final(tree)) == sizing_cache(old(tree)),
        final(tree).layout_record(node).placement == old(tree).layout_record(node).placement,
    no_unwind
))]
fn clear_structural_mark<A: Records + ?Sized>(tree: &mut A, node: A::Id) {
    tree.edit(node).structural_change = StructuralChange::Clean;
    #[cfg(verus_keep_ghost)]
    proof! { cache_unchanged(old(tree), tree); }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), old(tree).order().ordered(),
        selected_live(old(plan), old(tree).order()),
    ensures final(tree).order() == old(tree).order(), sizing_cache(final(tree)) == sizing_cache(old(tree)), selected_live(final(plan), old(tree).order()),
        replaced(old(plan), final(plan), start, node), final(tree).layout_record(node).placement is Subtree,
    no_unwind
))]
fn rebuild<A: Source + ?Sized>(
    tree: &mut A, node: A::Id, plan: &mut Plan<A::Id>, start: usize,
) -> bool {
    tree.edit(node).mark_placement_changed();
    #[cfg(verus_keep_ghost)]
    proof! { cache_unchanged(old(tree), tree); }
    plan.complete = plan.complete && region_list::replace_descendants::<_, A::Memory>(&mut plan.regions, start, node);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |i: int| 0 <= i < plan.regions.len() implies
            (tree.order().live)(#[trigger] plan.regions@[i]) by {
            if i < old(plan).regions.len() && i < start {
                assert(plan.regions@[i] == old(plan).regions@[i]);
            } else if old(plan).complete {
                assert(plan.regions@[i] == node);
            } else {
                assert(plan.regions@[i] == old(plan).regions@[i]);
            }
        }
    }
    let params = tree.params(node);
    let in_flow = !params.free_placement;
    let parent_flow = if in_flow {
        match tree.parent_id(node) {
            Some(parent) => matches!(tree.params(parent).children_layout, ChildrenLayout::Wrap { .. } | ChildrenLayout::Block),
            None => false,
        }
    } else {
        false
    };
    let flags = tree.record(node).flags;
    // In Block, the parent is already affected by this child. For other
    // layouts the intrinsic declarations are exactly FitContent and Auto.
    region_policy::affects_parent(
        flags.has_cycle(), region_policy::has_intrinsic(params), flags.is_block_item(),
        region_policy::attached_flow_child(in_flow, parent_flow),
    )
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(state =>
    requires live(old(tree), node), old(tree).order().ordered(),
        selected_live(old(plan), old(tree).order()),
    ensures final(tree).order() == old(tree).order(), sizing_cache(final(tree)) == sizing_cache(old(tree)), selected_live(final(plan), old(tree).order()),
        region_policy::starts_region(old(tree).layout_record(node).structural_change) ==> {
            &&& state == State::Done(true)
            &&& final(tree).layout_record(node).placement is Subtree
            &&& final(plan).complete ==> final(plan).regions@ == old(plan).regions@.push(node)
            &&& !final(plan).complete ==> final(plan).regions@ == old(plan).regions@
        },
        old(tree).layout_record(node).structural_change is Children && ready_free_parent(old(tree), node)
            ==> (state matches State::Children(frame) && frame.independent == Some(true) && frame.changed_children),
        match state {
            State::Children(frame) => frame.node == node && frame_live(frame, old(tree).order())
                && frame.next == (old(tree).order().first)(node)
                && (forall |id: A::Id| id != node ==> #[trigger] final(tree).layout_record(id) == old(tree).layout_record(id))
                && frame.start == old(plan).regions.len()
                && final(plan).regions@ == old(plan).regions@ && final(plan).complete == old(plan).complete,
            State::Done(_) => final(plan).regions@ == old(plan).regions@
                || final(plan).regions@ == old(plan).regions@.push(node),
        },
    no_unwind
))]
fn begin<A: Source + ?Sized>(
    tree: &mut A, node: A::Id, plan: &mut Plan<A::Id>,
) -> State<Frame<A::Id>, bool> {
    let mark = tree.record(node).structural_change;
    if region_policy::starts_region(mark) {
        tree.edit(node).mark_placement_changed();
        #[cfg(verus_keep_ghost)]
        proof! { cache_unchanged(old(tree), tree); }
        plan.complete = plan.complete && try_append::<_, A::Memory>(&mut plan.regions, node);
        #[cfg(verus_keep_ghost)]
        proof! {
            let previous = old(plan).regions@;
            assert(previous.take(previous.len() as int) =~= previous);
            if old(plan).complete {
                assert(replaced(old(plan), plan, old(plan).regions.len(), node));
            }
            assert forall |i: int| 0 <= i < plan.regions.len() implies
                (tree.order().live)(#[trigger] plan.regions@[i]) by {
                if i < old(plan).regions.len() { assert(plan.regions@[i] == old(plan).regions@[i]); }
                else { assert(plan.regions@[i] == node); }
            }
        }
        return State::Done(true);
    }
    if tree.params(node).disabled {
        tree.edit(node).placement = PlacementWork::Clean;
        #[cfg(verus_keep_ghost)]
        proof! { cache_unchanged(old(tree), tree); }
        return State::Done(false);
    }
    let changed_children = matches!(mark, StructuralChange::Children);
    let independent = if changed_children { Some(refresh_independent_parent(tree, node)) } else { None };
    let start = plan.regions.len();
    if let Some(false) = independent {
        let raised = rebuild(tree, node, plan, start);
        #[cfg(verus_keep_ghost)]
        proof! {
            let prior = old(plan).regions@;
            assert(prior.take(start as int) =~= prior);
        }
        return State::Done(raised);
    }
    let retained = plan.retained;
    plan.retained.include(tree.record(node).flags);
    let coupled = !matches!(tree.params(node).children_layout, ChildrenLayout::Free);
    let placement = tree.record(node).placement.for_parent(changed_children, coupled);
    let next = tree.first(node);
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(node); }
    State::Children(Frame {
        node, next, start, retained, independent, changed_children, coupled, placement,
        #[cfg(verus_keep_ghost)]
        order: save_order(tree),
    })
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(tree, child),
    ensures final(frame).node == old(frame).node, final(frame).next == old(frame).next,
        final(frame).order@ == old(frame).order@,
        final(frame).start == old(frame).start,
        final(frame).independent == old(frame).independent,
        final(frame).coupled == old(frame).coupled,
        final(frame).placement == old(frame).placement.with_child(tree.layout_record(child).placement,
            placement_work::coupled_child_changed(old(frame).coupled, changed, tree.layout_params(child).free_placement)),
        (old(frame).placement.visits(false) || tree.layout_record(child).placement.visits(false))
            ==> final(frame).placement.visits(false),
        final(frame).changed_children == (old(frame).changed_children || changed),
    no_unwind
))]
fn include<A: Source + ?Sized>(tree: &A, frame: &mut Frame<A::Id>, child: A::Id, changed: bool) {
    frame.changed_children |= changed;
    if !matches!(frame.placement, PlacementWork::Subtree) {
        let free = changed && frame.coupled && tree.params(child).free_placement;
        let coupled_change = placement_work::coupled_child_changed(frame.coupled, changed, free);
        frame.placement = frame.placement.with_child(tree.record(child).placement, coupled_change);
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires frame_live(frame, old(tree).order()), selected_live(old(plan), old(tree).order()),
    ensures final(tree).order() == old(tree).order(), sizing_cache(final(tree)) == sizing_cache(old(tree)), selected_live(final(plan), old(tree).order()),
        final(tree).layout_record(frame.node).placement == frame.placement
            || final(tree).layout_record(frame.node).placement is Subtree,
        frame.placement.visits(false) ==> final(tree).layout_record(frame.node).placement.visits(false),
        frame.changed_children && frame.independent == Some(true) && acyclic_parent(old(tree), frame.node)
            ==> final(plan).regions@ == old(plan).regions@ && final(plan).complete == old(plan).complete,
        (final(plan).regions@ == old(plan).regions@ && final(plan).complete == old(plan).complete)
            || replaced(old(plan), final(plan), frame.start, frame.node),
    no_unwind
))]
fn finish<A: Source + ?Sized>(
    tree: &mut A, frame: Frame<A::Id>, plan: &mut Plan<A::Id>,
) -> bool {
    let node = frame.node;
    let data = tree.record(node);
    let flags = data.flags;
    if !placement_work::same_work(data.placement, frame.placement) {
        tree.edit(node).placement = frame.placement;
        #[cfg(verus_keep_ghost)]
        proof! { cache_unchanged(old(tree), tree); }
    }
    match region_policy::after_children(frame.changed_children, flags.has_cycle(), plan.regions.len() > frame.start) {
        region_policy::AfterChildren::Keep => return false,
        region_policy::AfterChildren::Refresh => {
            let independent = match frame.independent {
                Some(ready) => ready,
                None => refresh_independent_parent(tree, node),
            };
            if independent {
                clear_structural_mark(tree, node);
                return false;
            }
        }
        region_policy::AfterChildren::Rebuild => {}
    }
    plan.retained = frame.retained;
    rebuild(tree, node, plan, frame.start)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Walker<A: Source + ?Sized> {
    plan: Plan<A::Id>,
    #[cfg(verus_keep_ghost)]
    attachment: Ghost<Option<(A::Id, A::Id)>>,
}

#[cfg(not(verus_keep_ghost))]
impl<A: Source + ?Sized> prepare_walk::Model for Walker<A> {
    type Child = A::Id;
    type Frame = Frame<A::Id>;
    type Summary = bool;
    type Context = A;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn attachment_prefix<I>(plan: &Plan<I>, leaf: I) -> bool {
    plan.regions@ == if plan.complete { seq![leaf] } else { Seq::empty() }
}

spec fn attachment_frontier<A: Source + ?Sized>(
    tree: &A, plan: &Plan<A::Id>, attachment: Option<(A::Id, A::Id)>,
    active: Option<Frame<A::Id>>, suspended: Seq<Suspended<A::Id>>,
) -> bool {
    if let Some((parent, leaf)) = attachment {
        &&& suspended.len() == 0
        &&& acyclic_parent(tree, parent)
        &&& match active {
            Some(frame) => {
                &&& frame.node == parent
                &&& frame.independent == Some(true) && frame.changed_children
                &&& match frame.next {
                    Some(id) => id == leaf && plan.complete && plan.regions@.len() == 0
                        && (tree.order().sibling)(leaf).is_none()
                        && tree.layout_record(leaf).structural_change is Subtree,
                    None => attachment_prefix(plan, leaf),
                }
            },
            None => attachment_prefix(plan, leaf),
        }
    } else { true }
}

impl<A: Source + ?Sized> prepare_walk::Model for Walker<A> {
    type Child = A::Id;
    type Frame = Frame<A::Id>;
    type Summary = bool;
    type Context = A;
    type Topology = (SizingCache<A::Id>, Option<(A::Id, A::Id)>);

    closed spec fn remaining(frame: Self::Frame) -> nat { remaining(frame) }

    closed spec fn topology(&self, tree: &A) -> Self::Topology { (sizing_cache(tree), self.attachment@) }

    closed spec fn valid(&self, tree: &A) -> bool { selected_live(&self.plan, tree.order()) }

    closed spec fn coherent(&self, tree: &A, active: Option<Self::Frame>,
        suspended: Seq<(Self::Frame, Self::Child)>) -> bool {
        frontier(self.plan.regions@, tree.order(), active, suspended)
            && attachment_frontier(tree, &self.plan, self.attachment@, active, suspended)
    }

    closed spec fn admissible(tree: &A) -> (spec_fn(Self::Frame) -> bool, spec_fn(Self::Child) -> bool) {
        let order = tree.order();
        (|frame| frame_live(frame, order), order.live)
    }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<A: Source + ?Sized> prepare_walk::Driver for Walker<A> {
    #[inline]
    fn advance(&mut self, tree: &mut A, frame: &mut Self::Frame,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>) -> ChildStep<Self::Child, Self::Frame> {
        let Some(child) = frame.next else { return ChildStep::End; };
        #[cfg(verus_keep_ghost)]
        let before = save_frame(frame);
        #[cfg(verus_keep_ghost)]
        let prior = save_regions(&self.plan);
        frame.next = tree.sibling(child);
        #[cfg(verus_keep_ghost)]
        proof! {
            let order = tree.order();
            order.node_facts(child);
            assert(frame_live(*frame, order));
            assert(remaining(*frame) < remaining(before@));
        }
        // Clean leaves need no planner frame or cache writes.
        let cached = tree.record(child);
        if matches!(cached.structural_change, StructuralChange::Clean)
            && matches!(cached.placement, PlacementWork::Clean) && tree.first(child).is_none()
        {
            self.plan.retained.include(cached.flags);
            #[cfg(verus_keep_ghost)]
            proof! { child_completed(prior@, self.plan.regions@, tree.order(), before@, *frame, child, suspended@); }
            return ChildStep::Prepared;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if let Some((_, leaf)) = self.attachment@ {
                assert(child == leaf);
                assert(region_policy::starts_region(tree.layout_record(child).structural_change));
                assert(prior@ =~= Seq::empty());
            }
        }
        match begin(tree, child, &mut self.plan) {
            State::Done(changed) => {
                include(tree, frame, child, changed);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(self.plan.regions@ == prior@ || self.plan.regions@ == prior@.push(child));
                    child_completed(prior@, self.plan.regions@, tree.order(), before@, *frame, child, suspended@);
                    if let Some((parent, leaf)) = self.attachment@ {
                        cache_keeps_cycle_marks(old(tree), tree, parent);
                        assert(child == leaf && frame.next.is_none());
                        assert(self.plan.regions@ == if self.plan.complete { prior@.push(child) } else { prior@ });
                        assert(attachment_prefix(&self.plan, leaf));

                    }
                }
                ChildStep::Prepared
            }
            State::Children(branch) => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    descend_progress(tree.order(), before@, *frame, child, branch);
                    descend_frontier(self.plan.regions@, tree.order(), before@, *frame, child, branch, suspended@);
                }
                ChildStep::Descend(child, branch)
            }
        }
    }

    #[inline]
    fn include(&mut self, tree: &mut A, frame: &mut Self::Frame, child: Self::Child, changed: bool,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>) {
        #[cfg(verus_keep_ghost)]
        let before = save_frame(frame);
        include(tree, frame, child, changed);
        #[cfg(verus_keep_ghost)]
        proof! { resume_frontier(self.plan.regions@, tree.order(), before@, *frame, child, suspended@); }
    }

    #[inline]
    fn finish(&mut self, tree: &mut A, frame: Self::Frame,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>) -> Self::Summary {
        #[cfg(verus_keep_ghost)]
        let prior = save_regions(&self.plan);
        let changed = finish(tree, frame, &mut self.plan);
        #[cfg(verus_keep_ghost)]
        proof! {
            finish_frontier(prior@, self.plan.regions@, tree.order(), frame, suspended@);
            if let Some((parent, leaf)) = self.attachment@ {
                cache_keeps_cycle_marks(old(tree), tree, parent);
                assert(frame.next.is_none());
                assert(attachment_prefix(&self.plan, leaf));
            }
        }
        changed
    }
}

/// Plan in postorder, replacing an affected child suffix by its enclosing
/// region when dependent sizing cannot be retained.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), node), old(tree).order().ordered(),
        selected_live(&plan, old(tree).order()), ordered_cuts(plan.regions@, old(tree).order()),
        before(plan.regions@, old(tree).order(), node),
    ensures final(tree).order() == old(tree).order(), sizing_cache(final(tree)) == sizing_cache(old(tree)), selected_live(&result, old(tree).order()),
        ordered_cuts(result.regions@, old(tree).order()),
        first_leaf_attachment(old(tree), node, &plan).is_some() ==> attachment_prefix(&result,
            first_leaf_attachment(old(tree), node, &plan).unwrap()),
    no_unwind
))]
pub(crate) fn run<A: Source + ?Sized>(
    tree: &mut A, node: A::Id, mut plan: Plan<A::Id>, spill: &mut Vec<Suspended<A::Id>>,
) -> Plan<A::Id> {
    #[cfg(verus_keep_ghost)]
    let prior = save_regions(&plan);
    #[cfg(verus_keep_ghost)]
    let attachment = save_attachment(tree, node, &plan);
    let start = begin(tree, node, &mut plan);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(plan.regions@ == prior@ || plan.regions@ == prior@.push(node));
        append_keeps_order(prior@, plan.regions@, tree.order(), node);
        if let State::Children(frame) = start { assert(fits(plan.regions@, tree.order(), frame)); }
    }
    let mut parents = work_stack::work_stack::<_, 8, A::Memory>(A::Memory::take(spill));
    let mut walker = Walker::<A> {
        plan,
        #[cfg(verus_keep_ghost)]
        attachment,
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        if let Some((parent, leaf)) = attachment@ {
            cache_keeps_cycle_marks(old(tree), tree, parent);
            assert(parent == node && start is Children);
            assert(start matches State::Children(frame) && frame.next == Some(leaf));
            assert(attachment_frontier(tree, &walker.plan, attachment@,
                prepare_walk::active_frame::<Walker<A>>(start), parents.items()));
        }
    }
    prepare_walk::run::<_, 8, A::Memory>(&mut walker, tree, start, &mut parents);
    *spill = parents.into_spill();
    walker.plan
}

#[cfg(verus_keep_ghost)]
verus! {
use crate::declarations::{X, Y};
use crate::node_data::NodeLayoutData;
use crate::prepare_frame::{self, FrameFloat, FrameWords};

pub(crate) open spec fn fixed_free_pixels<F: FrameFloat>(params: LayoutParams) -> bool {
    &&& params.children_layout is Free
    &&& !params.disabled
    &&& prepare_frame::pixel_final::<F>(params, X, false, None)
    &&& prepare_frame::pixel_final::<F>(params, Y, false, None)
}

pub(crate) open spec fn seeded_fixed_pixels<F: FrameFloat>(record: NodeLayoutData, params: LayoutParams) -> bool {
    let x = F::word(prepare_frame::pixel_decl(params, X).unwrap());
    let y = F::word(prepare_frame::pixel_decl(params, Y).unwrap());
    &&& prepare_frame::pixel_slots::<F>(record.values, X) == (x, x)
    &&& prepare_frame::pixel_slots::<F>(record.values, Y) == (y, y)
    &&& record.flags.0 & 0xffu32 == 0xaau32
}

/// Compare the boundary retained by the real planner to newly seeded words.
/// The prior solved parent comes from the same source seeder and registration
/// of its child list preserves those words and their phases.
pub(crate) fn fixed_free_parent_boundary<A: Source + ?Sized>(
    tree: &mut A, root: A::Id, parent: A::Id, plan: Plan<A::Id>,
    spill: &mut Vec<Suspended<A::Id>>, prior: Ghost<(LayoutParams, NodeLayoutData)>,
) -> (result: (Plan<A::Id>, NodeLayoutData))
    requires live(old(tree), root), live(old(tree), parent), old(tree).order().ordered(),
        selected_live(&plan, old(tree).order()), ordered_cuts(plan.regions@, old(tree).order()),
        before(plan.regions@, old(tree).order(), root),
        fixed_free_pixels::<A::Float>(prior@.0), seeded_fixed_pixels::<A::Float>(prior@.1, prior@.0),
        old(tree).layout_params(parent) == prior@.0,
        old(tree).layout_record(parent).values == prior@.1.values,
        old(tree).layout_record(parent).flags.0 & !region_policy::REFRESH_FLAGS
            == prior@.1.flags.0 & !region_policy::REFRESH_FLAGS,
    ensures seeded_fixed_pixels::<A::Float>(result.1, prior@.0),
        final(tree).order() == old(tree).order(), selected_live(&result.0, old(tree).order()),
        ordered_cuts(result.0.regions@, old(tree).order()),
        final(tree).layout_params(parent) == prior@.0,
        seeded_fixed_pixels::<A::Float>(final(tree).layout_record(parent), prior@.0),
        prepare_frame::pixel_slots::<A::Float>(final(tree).layout_record(parent).values, X)
            == prepare_frame::pixel_slots::<A::Float>(result.1.values, X),
        prepare_frame::pixel_slots::<A::Float>(final(tree).layout_record(parent).values, Y)
            == prepare_frame::pixel_slots::<A::Float>(result.1.values, Y),
    no_unwind
{
    let mut fresh = A::empty_record();
    let initial_flags = fresh.flags.0;
    let ready = crate::prepare_nodes::seed_pixels::<A::Float>(&mut fresh, tree.params(parent), false, None);
    proof! {
        assert(ready);
        let bits = fresh.flags.0;
        assert(bits & 0xffu32 == 0xaau32) by(bit_vector)
            requires bits == (initial_flags & !0xffu32) | 0xaau32;
    }
    let chosen = run(tree, root, plan, spill);
    proof! {
        let initial = sizing_cache(old(tree));
        let planned = sizing_cache(tree);
        assert((planned.words)(parent) == (initial.words)(parent));
        assert((planned.declarations)(parent) == (initial.declarations)(parent));
        assert((planned.protected_flags)(parent) == (initial.protected_flags)(parent));
        let before = prior@.1.flags.0;
        let after = tree.layout_record(parent).flags.0;
        let mask = region_policy::REFRESH_FLAGS;
        assert(region_policy::REFRESH_FLAGS & 0xffu32 == 0) by(compute_only);
        assert(after & 0xffu32 == before & 0xffu32) by(bit_vector)
            requires mask & 0xffu32 == 0, after & !mask == before & !mask;
    }
    (chosen, fresh)
}
}
