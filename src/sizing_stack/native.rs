//! The synchronous, allocation-free sizing path and its bounded spill.
#![allow(unexpected_cfgs)]

use super::{sizing_requests, Request, RequestAccess, RequestModel, RequestSource};
use core::marker::PhantomData;
#[cfg(not(verus_keep_ghost))]
use super::super::sizing_finish::StoredSize;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel, dependencies::sizing_finish::StoredSize};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use sizing_requests::RequestView;

#[cfg(not(verus_keep_ghost))]
pub(crate) trait NativeModel {
    type Id: Copy + Eq;
    type Opened;
    type View: RequestSource<Id = Self::Id> + ?Sized;
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) trait NativeModel {
    type Id: Copy + Eq;
    type Opened;
    type View: RequestSource<Id = Self::Id> + ?Sized;
    spec fn topology(&self) -> sizing_requests::Topology<Self::Id>;
    spec fn packed_phase(&self, slot: Request<Self::Id>) -> u32;
    spec fn packed_value(&self, slot: Request<Self::Id>) -> f32;
    spec fn opened_request(opened: Self::Opened) -> Request<Self::Id>;
}

pub(crate) open spec fn ready<W: NativeModel + ?Sized>(work: &W) -> ISet<Request<W::Id>> {
    ISet::new(|slot: Request<W::Id>| work.packed_phase(slot) == kernel::SOLVED
        || work.packed_phase(slot) == kernel::IN_PROGRESS)
}

fn ready_start<W: NativeModel>(work: &W) -> (set: Ghost<ISet<Request<W::Id>>>)
    ensures set@ == ready(work),
    no_unwind
{ Ghost(ready(work)) }

pub(crate) open spec fn inputs_available<W: NativeModel + ?Sized>(work: &W, slot: Request<W::Id>) -> bool {
    let inputs = sizing_requests::inputs(work.topology(), slot);
    forall |i: int| 0 <= i < inputs.len() ==> ready(work).contains(#[trigger] inputs[i])
}

pub(crate) open spec fn ordered<I: Copy>(topology: sizing_requests::Topology<I>) -> bool {
    forall |slot: Request<I>| #[trigger] sizing_requests::ordered_children(topology, slot)
}

pub(crate) type VisitEvidence<I> = (bool, Request<I>, ISet<Request<I>>);

pub(crate) open spec fn native_targets_live<I>(trace: Seq<VisitEvidence<I>>, nodes: Set<I>) -> bool {
    forall |i: int| 0 <= i < trace.len() ==> live_visit(#[trigger] trace[i], nodes)
}

pub(crate) open spec fn live_visit<I>(visit: VisitEvidence<I>, nodes: Set<I>) -> bool {
    visit.0 && nodes.contains(visit.1.node)
}

proof fn native_emissions_live<I: Copy>(topology: sizing_requests::Topology<I>, slot: Request<I>, nodes: Set<I>, initial: ISet<Request<I>>)
    requires sizing_requests::live::closed(topology, nodes), nodes.contains(slot.node),
    ensures native_targets_live(sizing_requests::inputs(topology, slot).map_values(
        |dependency: Request<I>| (true, dependency, initial)), nodes),
{
    sizing_requests::live::inputs_stay_live(topology, nodes, slot);
    let inputs = sizing_requests::inputs(topology, slot);
    let emitted = inputs.map_values(|dependency: Request<I>| (true, dependency, initial));
    assert forall |i: int| 0 <= i < emitted.len() implies live_visit(#[trigger] emitted[i], nodes) by {
        assert(emitted[i] == (true, inputs[i], initial));
        assert(nodes.contains(inputs[i].node));
    }
}

fn empty_trace<I>() -> (trace: Ghost<Seq<VisitEvidence<I>>>)
    ensures trace@ == Seq::<VisitEvidence<I>>::empty(),
    no_unwind
{
    Ghost(Seq::empty())
}

fn append_trace<I>(trace: Ghost<Seq<VisitEvidence<I>>>, present: bool, slot: Request<I>, initial: Ghost<ISet<Request<I>>>)
    -> (next: Ghost<Seq<VisitEvidence<I>>>)
    ensures next@ == trace@.push((present, slot, initial@)),
    no_unwind
{
    Ghost(trace@.push((present, slot, initial@)))
}

} // verus!

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait NativeAccess: NativeModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(source =>
        ensures source.topology() == self.topology(),
        no_unwind
    ))]
    fn view(&self) -> &Self::View;

    #[cfg_attr(verus_keep_ghost, verus_spec(start =>
        ensures final(self).topology() == old(self).topology(),
            ready(old(self)).subset_of(ready(final(self))),
            match start {
                None => ready(old(self)).contains(slot) && final(self).packed_phase(slot) == old(self).packed_phase(slot),
                Some((opened, _)) => Self::opened_request(opened) == slot
                    && !ready(old(self)).contains(slot) && final(self).packed_phase(slot) == kernel::IN_PROGRESS,
            },
        no_unwind
    ))]
    fn start(&mut self, slot: Request<Self::Id>) -> Option<(Self::Opened, bool)>;

    #[cfg_attr(verus_keep_ghost, verus_spec(stored =>
        requires inputs_available(old(self), Self::opened_request(opened)),
        ensures final(self).topology() == old(self).topology(),
            ready(old(self)).subset_of(ready(final(self))),
            stored.slot == Self::opened_request(opened), final(self).packed_phase(stored.slot) == kernel::SOLVED,
            stored.value == final(self).packed_value(stored.slot),
        no_unwind
    ))]
    fn finish(&mut self, opened: Self::Opened, check: bool) -> StoredSize<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).packed_phase(Self::opened_request(opened)) == kernel::IN_PROGRESS,
        ensures final(self).topology() == old(self).topology(),
            ready(old(self)).subset_of(ready(final(self))),
            final(self).packed_phase(Self::opened_request(opened)) == kernel::SOLVED,
        no_unwind
    ))]
    fn spill(&mut self, opened: Self::Opened, check: bool);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
trait Continuation<W: NativeAccess> {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires ordered(old(work).topology()),
        ensures final(work).topology() == old(work).topology(),
            ready(old(work)).subset_of(ready(final(work))), ready(final(work)).contains(slot),
            final(work).packed_phase(slot) == if old(work).packed_phase(slot) == kernel::IN_PROGRESS {
                kernel::IN_PROGRESS
            } else { kernel::SOLVED },
        no_unwind
    ))]
    fn visit(work: &mut W, slot: Request<W::Id>);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct NativeRequests<'a, W: NativeAccess, Next: Continuation<W>> {
    work: &'a mut W,
    next: PhantomData<Next>,
    #[cfg(verus_keep_ghost)]
    trace: Ghost<Seq<VisitEvidence<W::Id>>>,
    #[cfg(verus_keep_ghost)]
    initial: Ghost<ISet<Request<W::Id>>>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<'a, W: NativeAccess, Next: Continuation<W>> NativeRequests<'a, W, Next> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        &&& ordered(self.work.topology())
        &&& self.initial@.subset_of(ready(self.work))
        &&& forall |i: int| 0 <= i < self.trace@.len()
            ==> ready(self.work).contains((#[trigger] self.trace@[i]).1)
    }
}

impl<W: NativeAccess, Next: Continuation<W>> RequestModel for NativeRequests<'_, W, Next> {
    type Id = W::Id;
    type Source = W::View;
    type Event = VisitEvidence<W::Id>;
    type Context = W;

    // Request dispatch returns the borrow to the original work frame.
    #[verifier::prophetic]
    closed spec fn context(&self) -> Self::Context { *final(self.work) }

    closed spec fn topology(&self) -> sizing_requests::Topology<W::Id> { self.work.topology() }

    closed spec fn projection(&self) -> spec_fn(Request<W::Id>) -> Self::Event {
        let initial = self.initial@;
        |slot: Request<W::Id>| (true, slot, initial)
    }

    closed spec fn requests(&self) -> Seq<Self::Event> { self.trace@ }
}
}

#[cfg(not(verus_keep_ghost))]
impl<W: NativeAccess, Next: Continuation<W>> RequestModel for NativeRequests<'_, W, Next> {
    type Id = W::Id;
    type Source = W::View;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<W: NativeAccess, Next: Continuation<W>> RequestAccess for NativeRequests<'_, W, Next> {
    #[inline(always)]
    fn source(&self) -> &Self::Source { self.work.view() }

    #[inline(always)]
    fn emit(&mut self, slot: Request<W::Id>) {
        #[cfg(verus_keep_ghost)]
        proof! { use_type_invariant(&*self); }
        #[cfg(verus_keep_ghost)]
        let prior = ready_start(self.work);
        Next::visit(self.work, slot);
        #[cfg(verus_keep_ghost)]
        {
            let old_trace = self.trace;
            self.trace = append_trace(self.trace, true, slot, self.initial);
            proof! {
                assert(self.initial@.subset_of(prior@));
                assert(self.initial@.subset_of(ready(self.work)));
                assert forall |i: int| 0 <= i < self.trace@.len()
                    implies ready(self.work).contains((#[trigger] self.trace@[i]).1) by {
                        if i < old_trace@.len() {
                            assert(self.trace@[i] == old_trace@[i]);
                            assert(prior@.contains(old_trace@[i].1));
                        } else {
                            assert(self.trace@[i] == (true, slot, self.initial@));
                        }
                    };
            }
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Spill;

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<W: NativeAccess> Continuation<W> for Spill {
    fn visit(work: &mut W, slot: Request<W::Id>) {
        if let Some((opened, check)) = work.start(slot) {
            work.spill(opened, check);
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Step<Next>(PhantomData<Next>);

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<W: NativeAccess, Next: Continuation<W>> Continuation<W> for Step<Next> {
    fn visit(work: &mut W, slot: Request<W::Id>) {
        let Some((opened, check)) = work.start(slot) else { return; };
        #[cfg(verus_keep_ghost)]
        let initial = ready_start(work);
        let pending = NativeRequests {
            work: &mut *work,
            next: PhantomData::<Next>,
            #[cfg(verus_keep_ghost)]
            trace: empty_trace(),
            #[cfg(verus_keep_ghost)]
            initial,
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(pending.context() == *final(pending.work)); }
        let visited = sizing_requests::request_inputs(pending, slot);
        #[cfg(verus_keep_ghost)]
        proof! {
            use_type_invariant(&visited);
            let project = visited.projection();
            assert(project(slot) == (true, slot, initial@));
            let topology = visited.topology();
            let exact = sizing_requests::inputs(topology, slot).map_values(|dependency: Request<W::Id>| (true, dependency, initial@));
            assert(visited.requests() =~= exact);
            assert(visited.initial@ == initial@);
            assert(inputs_available(visited.work, slot)) by {
                let inputs = sizing_requests::inputs(visited.work.topology(), slot);
                assert forall |i: int| 0 <= i < inputs.len() implies ready(visited.work).contains(#[trigger] inputs[i]) by {
                    assert(visited.requests()[i] == (true, inputs[i], initial@));
                }
            }
            assert forall |live: Set<W::Id>| sizing_requests::live::closed(topology, live) && live.contains(slot.node)
                implies #[trigger] native_targets_live(visited.requests(), live) by {
                native_emissions_live(topology, slot, live, initial@);
            }
        }
        let _stored = visited.work.finish(opened, check);
    }
}

type Four<Next> = Step<Step<Step<Step<Next>>>>;
type Eight<Next> = Four<Four<Next>>;

// Unoptimized builds retain larger temporary frames during the descent.
#[cfg(debug_assertions)]
type Configured = Eight<Spill>;
#[cfg(not(debug_assertions))]
type Configured = Eight<Eight<Eight<Spill>>>;

/// Stream dependencies synchronously through a finite chain of native visits.
/// Every level dispatches to its strictly shorter continuation.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires ordered(work.topology()),
    ensures result.topology() == work.topology(),
        ready(&work).subset_of(ready(&result)), ready(&result).contains(slot),
        result.packed_phase(slot) == if work.packed_phase(slot) == kernel::IN_PROGRESS {
            kernel::IN_PROGRESS
        } else { kernel::SOLVED },
    no_unwind
))]
pub(crate) fn drive<W: NativeAccess>(mut work: W, slot: Request<W::Id>) -> W {
    Configured::visit(&mut work, slot);
    work
}

#[cfg(test)]
pub(crate) fn drive_spill<W: NativeAccess>(mut work: W, slot: Request<W::Id>) -> W {
    Spill::visit(&mut work, slot);
    work
}
