//! Gather a bounded dependency closure without changing any layout record.
#![allow(unexpected_cfgs)]

use super::{intake::{Changes, Model}, readers::{self, NodeChange}, tape::{self, Axes}};
use crate::declarations::{Axis, Y};
use crate::node_data::NodeLayoutData;
use crate::node_flags::slot_index;
use crate::vec_memory::{FallibleVecMemory, VecMemory};
#[cfg(not(verus_keep_ghost))]
use crate::solve::{cycle_rules::{Kind, SOLVED, read_state}, dependency_rules::queueable, sizing_requests::{self, Request}};
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel::{Kind, SOLVED, read_state}, dependencies::{rules::queueable, sizing_requests::{self, Request}}};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::{node_flags::NodeFlags, prepare_frame::Order};

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct Ranked<I> {
    pub rank: u16,
    pub request: Request<I>,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn live_steps<I>(live: Set<I>, steps: Seq<Ranked<I>>) -> bool {
    forall |i: int| 0 <= i < steps.len() ==> live.contains((#[trigger] steps[i]).request.node)
}

pub(crate) open spec fn request_at<I>(steps: Seq<Ranked<I>>, request: Request<I>, end: int) -> bool {
    exists |i: int| 0 <= i < end && (#[trigger] steps[i]).request == request
}

pub(crate) open spec fn owner_at<I>(steps: Seq<Ranked<I>>, node: I, end: int) -> bool {
    exists |i: int| 0 <= i < end && (#[trigger] steps[i]).request.node == node
}

pub(crate) open spec fn owners<I>(steps: Seq<Ranked<I>>) -> Set<I> {
    steps.map_values(|step: Ranked<I>| step.request.node).to_set()
}

pub(crate) open spec fn unique_requests<I>(steps: Seq<Ranked<I>>) -> bool {
    forall |i: int, j: int| 0 <= i < j < steps.len()
        ==> (#[trigger] steps[i]).request != (#[trigger] steps[j]).request
}

/// The membership protected by a capture concerns physical slots, not the
/// transient vector index at which a request was discovered.
pub(crate) open spec fn scheduled<I>(steps: Seq<Ranked<I>>) -> Set<Request<I>> {
    steps.map_values(|step: Ranked<I>| step.request).to_set()
}

pub(crate) proof fn describe_membership<I>(steps: Seq<Ranked<I>>)
    ensures
        forall |node: I| #[trigger] owners(steps).contains(node)
            == owner_at(steps, node, steps.len() as int),
        forall |request: Request<I>| #[trigger] scheduled(steps).contains(request)
            == request_at(steps, request, steps.len() as int),
{
    let ids = steps.map_values(|step: Ranked<I>| step.request.node);
    let slots = steps.map_values(|step: Ranked<I>| step.request);
    ids.to_set_ensures();
    slots.to_set_ensures();
    assert forall |node: I| #[trigger] owners(steps).contains(node)
        == owner_at(steps, node, steps.len() as int) by {
        if ids.contains(node) {
            let i = choose |i: int| 0 <= i < ids.len() && #[trigger] ids[i] == node;
            assert(steps[i].request.node == node);
        } else if owner_at(steps, node, steps.len() as int) {
            let i = choose |i: int| 0 <= i < steps.len() && (#[trigger] steps[i]).request.node == node;
            assert(ids[i] == node);
        }
    }
    assert forall |request: Request<I>| #[trigger] scheduled(steps).contains(request)
        == request_at(steps, request, steps.len() as int) by {
        if slots.contains(request) {
            let i = choose |i: int| 0 <= i < slots.len() && #[trigger] slots[i] == request;
            assert(steps[i].request == request);
        } else if request_at(steps, request, steps.len() as int) {
            let i = choose |i: int| 0 <= i < steps.len() && (#[trigger] steps[i]).request == request;
            assert(slots[i] == request);
        }
    }
}

proof fn append_slot<I>(before: Seq<Ranked<I>>, step: Ranked<I>)
    requires unique_requests(before),
        !request_at(before, step.request, before.len() as int),
    ensures unique_requests(before.push(step)),
        scheduled(before.push(step)) == scheduled(before).insert(step.request),
        owners(before.push(step)) == owners(before).insert(step.request.node),
{
    let after = before.push(step);
    describe_membership(before);
    describe_membership(after);
    assert(scheduled(after) =~= scheduled(before).insert(step.request)) by {
        assert forall |req: Request<I>| scheduled(after).contains(req)
            == (scheduled(before).contains(req) || req == step.request) by {
            if scheduled(after).contains(req) {
                let i = choose |i: int| 0 <= i < after.len() && (#[trigger] after[i]).request == req;
                if i < before.len() { assert(after[i] == before[i]); }
            } else if req == step.request {
                assert(after[before.len() as int].request == req);
            } else if scheduled(before).contains(req) {
                let i = choose |i: int| 0 <= i < before.len() && (#[trigger] before[i]).request == req;
                assert(after[i] == before[i]);
            }
        }
    }
    assert(owners(after) =~= owners(before).insert(step.request.node)) by {
        assert forall |node: I| owners(after).contains(node)
            == (owners(before).contains(node) || node == step.request.node) by {
            if owners(after).contains(node) {
                let i = choose |i: int| 0 <= i < after.len() && (#[trigger] after[i]).request.node == node;
                if i < before.len() { assert(after[i] == before[i]); }
            } else if node == step.request.node {
                assert(after[before.len() as int].request.node == node);
            } else if owners(before).contains(node) {
                let i = choose |i: int| 0 <= i < before.len() && (#[trigger] before[i]).request.node == node;
                assert(after[i] == before[i]);
            }
        }
    }
    assert forall |i: int, j: int| 0 <= i < j < after.len()
        implies (#[trigger] after[i]).request != (#[trigger] after[j]).request by {
        assert(after[i] == before[i]);
        if j == before.len() {
            assert(after[j] == step);
            assert(!request_at(before, step.request, before.len() as int));
        } else { assert(after[j] == before[j]); }
    }
}

pub(crate) open spec fn ordered_prefix<I>(steps: Seq<Ranked<I>>, end: int) -> bool {
    forall |i: int, j: int| 0 <= i < end && i < j < steps.len()
        ==> (#[trigger] steps[i]).rank <= (#[trigger] steps[j]).rank
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Equal<I: Copy> {
    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (left == right), no_unwind))]
    fn same_node(left: I, right: I) -> bool;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn rank_word(record: NodeLayoutData, axis: Axis, kind: Kind) -> Option<u16> {
    let index = crate::cycles::kernel::slot_index(axis.index(), kind);
    if read_state(record.flags.0, index as u32) == SOLVED {
        Some(record.levels@[index as int])
    } else {
        None
    }
}
}

/// Unsolved slots have no derived output to notify. A saturated rank cannot
/// be consumed by a ranked pass.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == rank_word(*record, axis, kind),
    no_unwind
))]
pub(crate) fn settled_rank(record: &NodeLayoutData, axis: Axis, kind: Kind) -> Option<u16> {
    let at = slot_index(axis, kind);
    if read_state(record.flags.0, at as u32) == SOLVED {
        Some(record.levels[at])
    } else {
        None
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Work<I> {
    pub(crate) steps: Vec<Ranked<I>>,
    pub(crate) owners: u32,
    pub(crate) owner_limit: u32,
    pub(crate) lower_rank: u16,
    pub(crate) admitted: bool,
    pub(crate) wrap: bool,
    #[cfg(verus_keep_ghost)]
    pub(crate) live: Ghost<Set<I>>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<I> Work<I> {
    pub(crate) open spec fn safe(&self) -> bool {
        &&& self.steps.len() <= tape::CAPACITY
        &&& self.owners <= self.owner_limit
        &&& live_steps(self.live@, self.steps@)
        &&& unique_requests(self.steps@)
        &&& self.owners == owners(self.steps@).len()
    }
    pub(crate) open spec fn extends(&self, old: &Self) -> bool {
        &&& self.safe()
        &&& forall |i: int| 0 <= i < old.steps.len()
            ==> #[trigger] self.steps@[i] == old.steps@[i]
        &&& self.steps.len() >= old.steps.len()
        &&& self.owner_limit == old.owner_limit
        &&& self.lower_rank == old.lower_rank
        &&& self.wrap == old.wrap
        &&& self.live@ == old.live@
        &&& (!old.admitted ==> !self.admitted)
        &&& forall |i: int| old.steps.len() <= i < self.steps.len()
            ==> self.lower_rank <= (#[trigger] self.steps@[i]).rank
    }
}

fn save_steps<S>(steps: &Vec<S>) -> (prior: Ghost<Seq<S>>)
    ensures prior@ == steps@,
    no_unwind
{ Ghost(steps@) }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<I: Copy> Work<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).safe(), old(self).live@.contains(node),
        ensures final(self).extends(old(self)),
            ({
                let request = sizing_requests::target(node, axis is Y, kind);
                let step = Ranked { rank, request };
                let before = old(self).steps@;
                let after = final(self).steps@;
                let allowed = !(kind is Flow) || old(self).wrap;
                &&& after == before || after == before.push(step)
                &&& after != before ==> allowed && old(self).admitted && final(self).admitted
                    && !request_at(before, request, before.len() as int)
                &&& allowed && final(self).admitted ==> request_at(after, request, after.len() as int)
                &&& (!allowed || !old(self).admitted) ==> *final(self) == *old(self)
            }),
        no_unwind
    ))]
    pub(crate) fn discover<E: Equal<I>, M: FallibleVecMemory>(&mut self, node: I, axis: Axis, kind: Kind, rank: u16) {
        if !self.admitted || (matches!(kind, Kind::Flow) && !self.wrap) { return; }
        let mut seen_owner = false;
        let vertical = matches!(axis, Y);
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.steps.len(), *self == *old(self), self.safe(),
                seen_owner == owner_at(self.steps@, node, index as int),
                !request_at(self.steps@, sizing_requests::target(node, vertical, kind), index as int),
                vertical == (axis is Y),
            decreases self.steps.len() - index,
        ))]
        while index < self.steps.len() {
            let candidate = self.steps[index].request;
            if E::same_node(candidate.node, node) {
                seen_owner = true;
                if candidate.vertical == vertical && same_kind(candidate.kind, kind) {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(self.steps@[index as int].request == sizing_requests::target(node, vertical, kind));
                        assert(request_at(self.steps@, candidate, self.steps.len() as int));
                    }
                    return;
                }
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                let wanted = sizing_requests::target(node, vertical, kind);
                assert(candidate != wanted);
                assert(!request_at(self.steps@, wanted, index as int + 1)) by {
                    if request_at(self.steps@, wanted, index as int + 1) {
                        let at = choose |at: int| 0 <= at < index + 1
                            && (#[trigger] self.steps@[at]).request == wanted;
                        assert(at == index);
                    }
                }
                assert(seen_owner == owner_at(self.steps@, node, index as int + 1)) by {
                    if candidate.node == node {
                        assert(owner_at(self.steps@, node, index as int + 1));
                    } else if owner_at(self.steps@, node, index as int + 1) {
                        let at = choose |at: int| 0 <= at < index + 1
                            && (#[trigger] self.steps@[at]).request.node == node;
                        assert(at < index);
                    } else {
                        assert(!owner_at(self.steps@, node, index as int));
                    }
                }
            }
            index += 1;
        }
        if !queueable(rank) || rank < self.lower_rank || (!seen_owner && self.owners == self.owner_limit) {
            self.admitted = false;
            return;
        }
        let entry = Ranked { rank, request: sizing_requests::target(node, vertical, kind) };
        #[cfg(verus_keep_ghost)]
        let old_steps = save_steps(&self.steps);
        if tape::record::<_, M>(&mut self.steps, entry) {
            if !seen_owner { self.owners += 1; }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(self.steps@.take(old_steps@.len() as int) =~= old_steps@);
                assert(!request_at(old_steps@, entry.request, old_steps@.len() as int));
                assert(self.steps@[old_steps@.len() as int].request == entry.request);
                assert(request_at(self.steps@, entry.request, self.steps.len() as int));
                append_slot(old_steps@, entry);
                describe_membership(old_steps@);
                if seen_owner {
                    assert(owners(old_steps@).contains(node));
                    assert(owners(old_steps@).insert(node) =~= owners(old_steps@));
                } else {
                    assert(!owners(old_steps@).contains(node));
                }
                assert forall |i: int| 0 <= i < self.steps.len() implies
                    self.live@.contains((#[trigger] self.steps@[i]).request.node)
                by {
                    if i < old_steps@.len() { assert(self.steps@[i] == old_steps@[i]); }
                    else { assert(self.steps@[i] == entry); }
                }
            }
        } else {
            self.admitted = false;
        }
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(equal => ensures equal == (a == b), no_unwind))]
fn same_kind(a: Kind, b: Kind) -> bool {
    matches!((a, b),
        (Kind::Regular, Kind::Regular) | (Kind::Min, Kind::Min) | (Kind::Max, Kind::Max)
            | (Kind::Final, Kind::Final) | (Kind::EvenShare, Kind::EvenShare) | (Kind::Flow, Kind::Flow))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires at < old(work).steps.len(), old(work).safe(),
        ordered_prefix(old(work).steps@, at as int),
    ensures final(work).safe(), final(work).steps.len() == old(work).steps.len(),
        final(work).lower_rank == final(work).steps@[at as int].rank,
        final(work).admitted == old(work).admitted, final(work).live@ == old(work).live@,
        final(work).wrap == old(work).wrap, final(work).owner_limit == old(work).owner_limit,
        scheduled(final(work).steps@) == scheduled(old(work).steps@),
        forall |i: int| 0 <= i < final(work).steps.len()
            ==> old(work).steps@.contains(#[trigger] final(work).steps@[i]),
        forall |i: int| 0 <= i < at ==> #[trigger] final(work).steps@[i] == old(work).steps@[i],
        ordered_prefix(final(work).steps@, at + 1),
    no_unwind
))]
fn next_by_rank<I: Copy>(work: &mut Work<I>, at: usize) {
    let mut best = at;
    let mut cursor = at + 1;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant at <= best < cursor <= work.steps.len(), *work == *old(work),
            forall |i: int| at <= i < cursor ==> work.steps@[best as int].rank <= (#[trigger] work.steps@[i]).rank,
        decreases work.steps.len() - cursor,
    ))]
    while cursor < work.steps.len() {
        if work.steps[cursor].rank <= work.steps[best].rank {
            best = cursor;
        }
        cursor += 1;
    }
    let step = work.steps[best];
    if best != at {
        let first = work.steps[at];
        work.steps[best] = first;
        work.steps[at] = step;
    }
    work.lower_rank = step.rank;
    #[cfg(verus_keep_ghost)]
    proof! {
        let old_steps = old(work).steps@;
        let out = work.steps@;
        describe_membership(old_steps);
        describe_membership(out);
        let moved = |i: int| if i == best { at as int } else if i == at { best as int } else { i };
        assert forall |i: int| 0 <= i < out.len() implies
            #[trigger] out[i] == old_steps[moved(i)] by {
            if i == best { assert(out[i] == old_steps[at as int]); }
            else if i == at { assert(out[i] == old_steps[best as int]); }
            else { assert(out[i] == old_steps[i]); }
        }
        assert forall |i: int| 0 <= i < out.len() implies old_steps.contains(#[trigger] out[i]) by {
            assert(0 <= moved(i) < old_steps.len());
            assert(out[i] == old_steps[moved(i)]);
        }
        assert(scheduled(out) =~= scheduled(old_steps)) by {
            assert forall |req: Request<I>| scheduled(out).contains(req)
                == scheduled(old_steps).contains(req) by {
                if scheduled(out).contains(req) {
                    let i = choose |i: int| 0 <= i < out.len() && (#[trigger] out[i]).request == req;
                    assert(out[i] == old_steps[moved(i)]);
                } else if scheduled(old_steps).contains(req) {
                    let i = choose |i: int| 0 <= i < old_steps.len() && (#[trigger] old_steps[i]).request == req;
                    assert(moved(moved(i)) == i);
                    assert(out[moved(i)] == old_steps[i]);
                }
            }
        }
        assert(owners(out) =~= owners(old_steps)) by {
            assert forall |node: I| owners(out).contains(node) == owners(old_steps).contains(node) by {
                if owners(out).contains(node) {
                    let i = choose |i: int| 0 <= i < out.len() && (#[trigger] out[i]).request.node == node;
                    assert(out[i] == old_steps[moved(i)]);
                } else if owners(old_steps).contains(node) {
                    let i = choose |i: int| 0 <= i < old_steps.len() && (#[trigger] old_steps[i]).request.node == node;
                    assert(moved(moved(i)) == i);
                    assert(out[moved(i)] == old_steps[i]);
                }
            }
        }
        assert forall |i: int, j: int| 0 <= i < j < out.len()
            implies (#[trigger] out[i]).request != (#[trigger] out[j]).request by {
            assert(moved(i) != moved(j));
            assert(out[i] == old_steps[moved(i)]);
            assert(out[j] == old_steps[moved(j)]);
        }
        assert forall |i: int| 0 <= i < out.len() implies
            work.live@.contains((#[trigger] out[i]).request.node) by {
            if i == best { assert(out[i] == old_steps[at as int]); }
            else if i == at { assert(out[i] == old_steps[best as int]); }
            else { assert(out[i] == old_steps[i]); }
        }
        assert forall |i: int, j: int| 0 <= i <= at && i < j < out.len()
            implies (#[trigger] out[i]).rank <= (#[trigger] out[j]).rank by {
            let before_j = if j == best { at as int } else if j == at { best as int } else { j };
            assert(out[j] == old_steps[before_j]);
            if i < at {
                assert(out[i] == old_steps[i]);
                assert(i < before_j);
            } else {
                assert(out[i] == old_steps[best as int]);
                assert(at <= before_j);
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
/// Observations made by the production intake and reverse-reader dispatch.
pub(crate) enum Event<I> {
    Viewport(I, Axis),
    Declaration(I, NodeChange),
    Content(I),
    Readers(Request<I>),
}

pub(crate) trait EventModel: Model<Change = NodeChange> {}

#[verifier::opaque]
pub(crate) open spec fn source_reader_calls<I: Copy>(
    inputs: readers::ReaderInputs<I>, wrap: bool, event: Event<I>,
) -> Seq<(I, Axis, Kind)> {
    match event {
        Event::Viewport(root, axis) => readers::filtered_kinds(inputs, root, axis, readers::Filter::Flexible, 3),
        Event::Declaration(node, change) => readers::declaration_requests(inputs, node, change)
            + if wrap { readers::wrap_edit_requests(inputs, node, change) } else { Seq::empty() },
        Event::Content(node) => readers::content_requests(inputs, node),
        Event::Readers(request) => {
            let node = request.node;
            let axis = request.axis();
            let kind = request.kind;
            let ordinary = match kind {
                Kind::EvenShare => readers::share_readers(inputs, node, axis, inputs.links.children[node].len()),
                Kind::Final => readers::final_readers(inputs, node, axis),
                Kind::Flow => Seq::empty(),
                _ => readers::declaration_readers(inputs, node, axis, kind),
            };
            ordinary + if wrap { readers::wrap_readers(inputs, node, axis, kind) } else { Seq::empty() }
        },
    }
}

pub(crate) open spec fn project_reader_calls<I: Copy>(
    inputs: readers::ReaderInputs<I>, wrap: bool, event: Event<I>,
) -> Seq<Request<I>> {
    crate::sizing_tape::projected_requests(source_reader_calls(inputs, wrap, event))
}

pub(crate) open spec fn child_remainder<I>(order: Order<I>, parent: I, cursor: Option<I>) -> nat {
    if let Some(id) = cursor {
        if order.child(parent, id) {
            ((order.interval)(parent).1 - (order.interval)(id).0) as nat
        } else { 0 }
    } else { 0 }
}

#[verifier::opaque]
pub(crate) open spec fn child_suffix<I>(order: Order<I>, parent: I, cursor: Option<I>) -> Seq<I>
    decreases child_remainder(order, parent, cursor),
    when order.ordered()
{
    match cursor {
        Some(id) if order.child(parent, id) =>
            seq![id] + child_suffix(order, parent, (order.sibling)(id)),
        _ => Seq::empty(),
    }
}

proof fn reader_children_live<I>(order: Order<I>, parent: I, cursor: Option<I>)
    requires order.ordered(),
    ensures forall |i: int| 0 <= i < child_suffix(order, parent, cursor).len() ==> {
        let rows = child_suffix(order, parent, cursor);
        &&& order.child(parent, #[trigger] child_suffix(order, parent, cursor)[i])
        &&& (order.sibling)(rows[i]) == if i + 1 < rows.len() { Some(rows[i + 1]) } else { None }
    },
    decreases child_remainder(order, parent, cursor),
{
    reveal(child_suffix);
    if let Some(first) = cursor {
        if order.child(parent, first) {
            let next = (order.sibling)(first);
            reader_children_live(order, parent, next);
            assert forall |i: int| 0 <= i < child_suffix(order, parent, cursor).len()
                implies {
                    let rows = child_suffix(order, parent, cursor);
                    &&& order.child(parent, #[trigger] child_suffix(order, parent, cursor)[i])
                    &&& (order.sibling)(rows[i]) == if i + 1 < rows.len() { Some(rows[i + 1]) } else { None }
                } by {
                let rows = child_suffix(order, parent, cursor);
                let suffix = child_suffix(order, parent, next);
                assert(rows.len() == suffix.len() + 1);
                if i == 0 {
                    assert(rows[0] == first);
                    if let Some(second) = next {
                        assert(order.child(parent, second));
                        assert(rows[1] == suffix[0] && suffix[0] == second);
                    }
                } else {
                    assert(rows[i] == suffix[i - 1]);
                    if i + 1 < rows.len() { assert(rows[i + 1] == suffix[i]); }
                }
            }
        }
    }
}

/// Capture reads the same declarations, finished flags and sibling chain as the native solver.
#[verifier::opaque]
pub(crate) open spec fn capture_reader_inputs<S: Model + ?Sized>(source: &S) -> readers::ReaderInputs<S::Id> {
    let order = source.order();
    let live = source.live();
    readers::ReaderInputs {
        links: readers::Links {
            live,
            parents: Map::new(live, order.parent),
            children: Map::new(live, |node: S::Id| child_suffix(order, node, (order.first)(node))),
        },
        parameters: |node: S::Id| source.layout_params(node),
        declaration: |node: S::Id, axis: Axis, kind: Kind| {
            let flags = source.layout_record(node).flags;
            sizing_requests::resolved_size(source.layout_params(node), axis is Y, kind,
                flags.is_block_item(), flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0)
        },
    }
}

pub(crate) proof fn capture_links_match_records<S: Model + ?Sized>(source: &S)
    requires source.order().ordered(),
        forall |node: S::Id| #[trigger] source.live().contains(node) == (source.order().live)(node),
    ensures ({
        let order = source.order();
        let links = capture_reader_inputs(source).links;
        &&& links.valid()
        &&& forall |node: S::Id| #[trigger] links.live.contains(node) ==> {
            &&& links.parents[node] == (order.parent)(node)
            &&& links.child(node, 0) == (order.first)(node)
            &&& forall |i: int| 0 <= i < links.children[node].len()
                ==> (order.sibling)(#[trigger] links.children[node][i]) == links.child(node, i + 1)
        }
    }),
{
    reveal(capture_reader_inputs);
    reveal(child_suffix);
    let order = source.order();
    let links = capture_reader_inputs(source).links;
    assert forall |node: S::Id| #[trigger] links.live.contains(node) implies {
        &&& links.parents[node] == (order.parent)(node)
        &&& links.child(node, 0) == (order.first)(node)
        &&& forall |i: int| 0 <= i < links.children[node].len()
            ==> (order.sibling)(#[trigger] links.children[node][i]) == links.child(node, i + 1)
        &&& forall |i: int| 0 <= i < links.children[node].len()
            ==> links.live.contains(#[trigger] links.children[node][i])
    } by {
        let first = (order.first)(node);
        assert(links.children[node] == child_suffix(order, node, first));
        if let Some(child) = first {
            assert(order.child(node, child));
            assert(links.children[node].first() == child);
        }
        reader_children_live(order, node, first);
    };
}

pub(crate) open spec fn calls<S: EventModel + ?Sized>(source: &S, event: Event<S::Id>) -> Seq<Request<S::Id>> {
    project_reader_calls(capture_reader_inputs(source), source.wrap_queue(), event)
}

pub(crate) open spec fn settled<S: EventModel + ?Sized>(source: &S, request: Request<S::Id>) -> Option<u16> {
    (capture_ranks(source))(request)
}

pub(crate) open spec fn capture_ranks<S: Model + ?Sized>(source: &S) -> spec_fn(Request<S::Id>) -> Option<u16> {
    |request: Request<S::Id>| if source.live().contains(request.node) {
        rank_word(source.layout_record(request.node), request.axis(), request.kind)
    } else {
        None
    }
}

pub(crate) open spec fn eligible<S: EventModel + ?Sized>(source: &S, wrap: bool, request: Request<S::Id>) -> bool {
    settled(source, request).is_some() && (wrap || !(request.kind is Flow))
}

pub(crate) open spec fn settled_steps<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>,
) -> bool {
    forall |i: int| 0 <= i < steps.len() ==> {
        let step = #[trigger] steps[i];
        &&& settled(source, step.request) == Some(step.rank)
        &&& queueable(step.rank)
        &&& (wrap || !(step.request.kind is Flow))
    }
}

proof fn keep_settled<S: EventModel + ?Sized>(
    source: &S, wrap: bool, before: Seq<Ranked<S::Id>>, after: Seq<Ranked<S::Id>>,
)
    requires settled_steps(source, wrap, before),
        forall |i: int| 0 <= i < after.len() ==> before.contains(#[trigger] after[i]),
    ensures settled_steps(source, wrap, after),
{
    assert forall |i: int| 0 <= i < after.len() implies {
        let step = #[trigger] after[i];
        &&& settled(source, step.request) == Some(step.rank)
        &&& queueable(step.rank)
        &&& (wrap || !(step.request.kind is Flow))
    } by {
        let at = choose |j: int| 0 <= j < before.len() && #[trigger] before[j] == after[i];
        assert(before[at] == after[i]);
    }
}

pub(crate) open spec fn covers_event<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>, event: Event<S::Id>,
) -> bool {
    forall |i: int| 0 <= i < calls(source, event).len() && eligible(source, wrap, #[trigger] calls(source, event)[i])
        ==> scheduled(steps).contains(calls(source, event)[i])
}

pub(crate) open spec fn covers_seeds<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>, root: S::Id, axes: Axes,
    declarations: Seq<(S::Id, NodeChange)>, content: Seq<S::Id>,
) -> bool {
    &&& axes.horizontal ==> covers_event(source, wrap, steps, Event::Viewport(root, crate::declarations::X))
    &&& axes.vertical ==> covers_event(source, wrap, steps, Event::Viewport(root, Y))
    &&& forall |i: int| 0 <= i < declarations.len() ==> {
        let edit = #[trigger] declarations[i];
        covers_event(source, wrap, steps, Event::Declaration(edit.0, edit.1))
    }
    &&& forall |i: int| 0 <= i < content.len()
        ==> covers_event(source, wrap, steps, Event::Content(#[trigger] content[i]))
}

pub(crate) open spec fn covers_readers<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>, count: int,
) -> bool {
    forall |i: int| 0 <= i < count
        ==> covers_event(source, wrap, steps, Event::Readers((#[trigger] steps[i]).request))
}

fn remember_model<I>(work: &Work<I>) -> (saved: Ghost<Work<I>>)
    ensures saved@ == *work,
    no_unwind
{ Ghost(*work) }

proof fn extends_schedule<I>(before: &Work<I>, after: &Work<I>)
    requires after.extends(before)
    ensures scheduled(before.steps@).subset_of(scheduled(after.steps@))
{
    describe_membership(before.steps@);
    describe_membership(after.steps@);
    assert forall |request: Request<I>| #[trigger] scheduled(before.steps@).contains(request)
        implies scheduled(after.steps@).contains(request) by {
        let i = choose |i: int| 0 <= i < before.steps.len()
            && (#[trigger] before.steps@[i]).request == request;
        assert(after.steps@[i] == before.steps@[i]);
    }
}

proof fn keeps_seeds<S: EventModel + ?Sized>(
    source: &S, before: Seq<Ranked<S::Id>>, after: Seq<Ranked<S::Id>>, wrap: bool,
    root: S::Id, axes: Axes, declarations: Seq<(S::Id, NodeChange)>, content: Seq<S::Id>,
)
    requires covers_seeds(source, wrap, before, root, axes, declarations, content),
        scheduled(before).subset_of(scheduled(after)),
    ensures covers_seeds(source, wrap, after, root, axes, declarations, content),
{
    assert forall |i: int| 0 <= i < declarations.len()
        implies covers_event(source, wrap, after, Event::Declaration((#[trigger] declarations[i]).0, declarations[i].1)) by {
        let edit = declarations[i];
        assert(covers_event(source, wrap, before, Event::Declaration(edit.0, edit.1)));
    }
    assert forall |i: int| 0 <= i < content.len()
        implies covers_event(source, wrap, after, Event::Content(#[trigger] content[i])) by {
        assert(covers_event(source, wrap, before, Event::Content(content[i])));
    }
}

proof fn keeps_readers<S: EventModel + ?Sized>(
    source: &S, before: Seq<Ranked<S::Id>>, after: Seq<Ranked<S::Id>>, wrap: bool, count: int,
)
    requires covers_readers(source, wrap, before, count),
        scheduled(before).subset_of(scheduled(after)),
        forall |i: int| 0 <= i < count ==> #[trigger] after[i] == before[i],
    ensures covers_readers(source, wrap, after, count),
{
    assert forall |i: int| 0 <= i < count
        implies covers_event(source, wrap, after, Event::Readers((#[trigger] after[i]).request)) by {
        assert(covers_event(source, wrap, before, Event::Readers(before[i].request)));
    }
}

}
#[cfg(not(verus_keep_ghost))]
pub(crate) trait EventModel: Model<Change = NodeChange> {}

/// Discover precisely the rank saved in a settled node record.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(work).safe(), old(work).live@.contains(node),
    ensures final(work).extends(old(work)), ({
        let request = sizing_requests::target(node, axis is Y, kind);
        let before = old(work).steps@;
        let after = final(work).steps@;
        match rank_word(*record, axis, kind) {
            None => *final(work) == *old(work),
            Some(rank) => {
                &&& after == before || after == before.push(Ranked { rank, request })
                &&& (!(kind is Flow) || old(work).wrap) && final(work).admitted
                    ==> request_at(after, request, after.len() as int)
            },
        }
    }),
    no_unwind
))]
pub(crate) fn discover_from_record<I: Copy, E: Equal<I>, M: FallibleVecMemory>(
    work: &mut Work<I>, node: I, axis: Axis, kind: Kind, record: &NodeLayoutData,
) {
    if let Some(rank) = settled_rank(record, axis, kind) {
        work.discover::<E, M>(node, axis, kind, rank);
    }
}

/// Capture a registered declaration using the same ordered reader kernels
/// as the ordinary queue. The read-only tape cannot alter its Wrap mode.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.valid(), old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded()
            + source_reader_calls(old(source).inputs(), wrap, Event::Declaration(node, change)),
    no_unwind
))]
pub(crate) fn dispatch_declaration<S: readers::Access + ?Sized>(
    source: &mut S, node: S::Id, change: NodeChange, wrap: bool,
) {
    readers::edited(source, node, change);
    if wrap { readers::wrap_edit(source, node, change); }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(source_reader_calls); }
}

/// Compute the exact ordinary and Wrap suffixes from the same immutable
/// declarations and links that the ranked request will use.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.valid(), old(source).inputs().links.live.contains(request.node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded()
            + source_reader_calls(old(source).inputs(), wrap, Event::Readers(request)),
    no_unwind
))]
pub(crate) fn dispatch_readers<S: readers::Access + ?Sized>(
    source: &mut S, request: Request<S::Id>, wrap: bool,
) {
    let axis = request.axis();
    readers::notify(source, request.node, axis, request.kind);
    if wrap { readers::wrap_notify(source, request.node, axis, request.kind); }
    #[cfg(verus_keep_ghost)]
    proof! { reveal(source_reader_calls); }
}

/// Bind registration and reverse-reader callbacks to an isolated schedule.
/// The adapter reads live declarations, links, and settled rank words.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Events: EventModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(work).safe(), old(work).live@ == self.live(),
            old(work).wrap == self.wrap_queue(),
            settled_steps(self, old(work).wrap, old(work).steps@), self.live().contains(root),
        ensures final(work).extends(old(work)), settled_steps(self, old(work).wrap, final(work).steps@),
            final(work).admitted ==> covers_event(self, old(work).wrap, final(work).steps@, Event::Viewport(root, axis)),
        no_unwind
    ))]
    fn viewport(&self, work: &mut Work<Self::Id>, root: Self::Id, axis: Axis);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(work).safe(), old(work).live@ == self.live(),
            old(work).wrap == self.wrap_queue(),
            settled_steps(self, old(work).wrap, old(work).steps@), self.live().contains(node),
        ensures final(work).extends(old(work)), settled_steps(self, old(work).wrap, final(work).steps@),
            final(work).admitted ==> covers_event(self, old(work).wrap, final(work).steps@, Event::Declaration(node, change)),
        no_unwind
    ))]
    fn declaration(&self, work: &mut Work<Self::Id>, node: Self::Id, change: NodeChange);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(work).safe(), old(work).live@ == self.live(),
            old(work).wrap == self.wrap_queue(),
            settled_steps(self, old(work).wrap, old(work).steps@), self.live().contains(node),
        ensures final(work).extends(old(work)), settled_steps(self, old(work).wrap, final(work).steps@),
            final(work).admitted ==> covers_event(self, old(work).wrap, final(work).steps@, Event::Content(node)),
        no_unwind
    ))]
    fn content(&self, work: &mut Work<Self::Id>, node: Self::Id);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(work).safe(), old(work).live@ == self.live(),
            old(work).wrap == self.wrap_queue(),
            settled_steps(self, old(work).wrap, old(work).steps@), self.live().contains(step.request.node),
        ensures final(work).extends(old(work)), settled_steps(self, old(work).wrap, final(work).steps@),
            final(work).admitted ==> covers_event(self, old(work).wrap, final(work).steps@, Event::Readers(step.request)),
        no_unwind
    ))]
    fn readers(&self, work: &mut Work<Self::Id>, step: Ranked<Self::Id>);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(complete =>
    requires old(steps).len() == 0, source.live().contains(root), wrap == source.wrap_queue(),
        forall |i: int| 0 <= i < edits.declarations.len()
            ==> source.live().contains((#[trigger] edits.declarations@[i]).0),
        forall |i: int| 0 <= i < edits.content.len() ==> source.live().contains(#[trigger] edits.content@[i]),
    ensures final(steps).len() <= tape::CAPACITY, live_steps(source.live(), final(steps)@),
        settled_steps(source, wrap, final(steps)@),
        complete ==> ordered_prefix(final(steps)@, final(steps).len() as int)
            && covers_seeds(source, wrap, final(steps)@, root, axes, edits.declarations@, edits.content@)
            && covers_readers(source, wrap, final(steps)@, final(steps).len() as int),
        unique_requests(final(steps)@),
        owners(final(steps)@).len() <= owner_limit,
    no_unwind
))]
pub(crate) fn capture<S: Events + ?Sized, M: VecMemory>(
    source: &S, root: S::Id, axes: Axes, edits: &Changes<S::Id, NodeChange>,
    owner_limit: u32, wrap: bool, steps: &mut Vec<Ranked<S::Id>>,
) -> bool {
    let mut work = Work {
        steps: M::take(steps), owners: 0, owner_limit, lower_rank: 0, admitted: true, wrap,
        #[cfg(verus_keep_ghost)]
        live: plan_domain(source),
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        describe_membership(work.steps@);
        assert(owners(work.steps@) =~= Set::<S::Id>::empty());
        assert(unique_requests(work.steps@));
    }
    if axes.horizontal { source.viewport(&mut work, root, crate::declarations::X); }
    #[cfg(verus_keep_ghost)]
    let after_x = remember_model(&work);
    if axes.vertical { source.viewport(&mut work, root, Y); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(work.extends(&after_x@));
        extends_schedule(&after_x@, &work);
        if work.admitted && axes.horizontal {
            assert(covers_event(source, wrap, after_x@.steps@, Event::Viewport(root, crate::declarations::X)));
        }
        assert(edits.declarations@.take(0) =~= Seq::<(S::Id, NodeChange)>::empty());
    }
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= edits.declarations.len(), work.safe(), work.live@ == source.live(), work.wrap == wrap, wrap == source.wrap_queue(), work.owner_limit == owner_limit,
            settled_steps(source, wrap, work.steps@),
            work.admitted ==> covers_seeds(source, wrap, work.steps@, root, axes,
                edits.declarations@.take(i as int), Seq::empty()),
            forall |j: int| 0 <= j < edits.declarations.len()
                ==> source.live().contains((#[trigger] edits.declarations@[j]).0),
        decreases edits.declarations.len() - i,
    ))]
    while i < edits.declarations.len() && work.admitted {
        let (node, change) = edits.declarations[i];
        #[cfg(verus_keep_ghost)]
        let previous = remember_model(&work);
        source.declaration(&mut work, node, change);
        #[cfg(verus_keep_ghost)]
        proof! {
            if work.admitted {
                extends_schedule(&previous@, &work);
                let earlier = edits.declarations@.take(i as int);
                let until = edits.declarations@.take(i as int + 1);
                keeps_seeds(source, previous@.steps@, work.steps@, wrap, root, axes, earlier, Seq::empty());
                assert(until =~= earlier.push((node, change)));
                assert forall |j: int| 0 <= j < until.len()
                    implies covers_event(source, wrap, work.steps@,
                        Event::Declaration((#[trigger] until[j]).0, until[j].1)) by {
                    if j < i { assert(until[j] == earlier[j]); }
                    else { assert(until[j] == (node, change)); }
                }
                assert(covers_seeds(source, wrap, work.steps@, root, axes, until, Seq::empty()));
            }
        }
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if work.admitted {
            assert(i == edits.declarations.len());
            assert(edits.declarations@.take(i as int) =~= edits.declarations@);
        }
        assert(edits.content@.take(0) =~= Seq::<S::Id>::empty());
    }
    i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= edits.content.len(), work.safe(), work.live@ == source.live(), work.wrap == wrap, wrap == source.wrap_queue(), work.owner_limit == owner_limit,
            settled_steps(source, wrap, work.steps@),
            work.admitted ==> covers_seeds(source, wrap, work.steps@, root, axes,
                edits.declarations@, edits.content@.take(i as int)),
            forall |j: int| 0 <= j < edits.content.len() ==> source.live().contains(#[trigger] edits.content@[j]),
        decreases edits.content.len() - i,
    ))]
    while i < edits.content.len() && work.admitted {
        let node = edits.content[i];
        #[cfg(verus_keep_ghost)]
        let previous = remember_model(&work);
        source.content(&mut work, node);
        #[cfg(verus_keep_ghost)]
        proof! {
            if work.admitted {
                extends_schedule(&previous@, &work);
                let earlier = edits.content@.take(i as int);
                let until = edits.content@.take(i as int + 1);
                keeps_seeds(source, previous@.steps@, work.steps@, wrap, root, axes, edits.declarations@, earlier);
                assert(until =~= earlier.push(node));
                assert forall |j: int| 0 <= j < until.len()
                    implies covers_event(source, wrap, work.steps@, Event::Content(#[trigger] until[j])) by {
                    if j < i { assert(until[j] == earlier[j]); }
                    else { assert(until[j] == node); }
                }
                assert(covers_seeds(source, wrap, work.steps@, root, axes, edits.declarations@, until));
            }
        }
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if work.admitted {
            assert(i == edits.content.len());
            assert(edits.content@.take(i as int) =~= edits.content@);
        }
    }
    i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= work.steps.len(), work.safe(), work.live@ == source.live(), work.wrap == wrap, wrap == source.wrap_queue(), work.owner_limit == owner_limit,
            settled_steps(source, wrap, work.steps@),
            ordered_prefix(work.steps@, i as int), steps.len() == 0,
            work.admitted ==> covers_seeds(source, wrap, work.steps@, root, axes, edits.declarations@, edits.content@)
                && covers_readers(source, wrap, work.steps@, i as int),
        decreases tape::CAPACITY - i,
    ))]
    while i < work.steps.len() && work.admitted {
        #[cfg(verus_keep_ghost)]
        let before_rank = remember_model(&work);
        next_by_rank(&mut work, i);
        #[cfg(verus_keep_ghost)]
        proof! { keep_settled(source, wrap, before_rank@.steps@, work.steps@); }
        let step = work.steps[i];
        #[cfg(verus_keep_ghost)]
        let prefix = remember_model(&work);
        source.readers(&mut work, step);
        #[cfg(verus_keep_ghost)]
        proof! {
            let selected = prefix@.steps@;
            assert forall |a: int, b: int| 0 <= a <= i && a < b < work.steps.len()
                implies (#[trigger] work.steps@[a]).rank <= (#[trigger] work.steps@[b]).rank by {
                assert(work.steps@[a] == selected[a]);
                if b < selected.len() {
                    assert(work.steps@[b] == selected[b]);
                } else {
                    assert(work.lower_rank == selected[i as int].rank);
                    assert(a == i || selected[a].rank <= selected[i as int].rank);
                }
            }
            if work.admitted {
                extends_schedule(&prefix@, &work);
                let prior = before_rank@.steps@;
                keeps_seeds(source, prior, work.steps@, wrap, root, axes, edits.declarations@, edits.content@);
                assert forall |j: int| 0 <= j < i implies #[trigger] work.steps@[j] == prior[j] by {
                    assert(work.steps@[j] == selected[j]);
                }
                keeps_readers(source, prior, work.steps@, wrap, i as int);
                assert(work.steps@[i as int] == step);
                assert(covers_readers(source, wrap, work.steps@, i as int + 1));
            }
        }
        i += 1;
    }
    let complete = work.admitted;
    *steps = work.steps;
    complete
}

#[cfg(verus_keep_ghost)]
verus! {
fn plan_domain<S: EventModel + ?Sized>(source: &S) -> (domain: Ghost<Set<S::Id>>)
    ensures domain@ == source.live(),
    no_unwind
{ Ghost(source.live()) }
}
