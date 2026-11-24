//! The synchronous, allocation-free sizing path and its bounded spill.
#![allow(unexpected_cfgs)]

use super::{sizing_requests, Request, RequestAccess, RequestModel, RequestSource};
use core::marker::PhantomData;
use sizing_requests::{FlowMode, RequestView};
#[cfg(not(verus_keep_ghost))]
use super::super::sizing_finish::StoredSize;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel, dependencies::sizing_finish::StoredSize};
#[cfg(not(verus_keep_ghost))]
use super::super::dependency_rules::Form;
#[cfg(verus_keep_ghost)]
use crate::dependencies::rules::Form;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

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

pub(crate) open spec fn empty<I>() -> sizing_requests::Topology<I> {
    sizing_requests::Topology {
        form: |_: Request<I>| None,
        stack_parent: |_: Request<I>| None,
        parent: |_: I| None,
        parent_flow: |_: Request<I>, _: I| false,
        parent_other: |_: Request<I>, _: I| false,
        intrinsic_flow: |_: Request<I>| false,
        intrinsic_other: |_: Request<I>| false,
        children: |_: I| Seq::empty(),
        flow_mode: |_: I| FlowMode::Other,
        block_children: |_: I| Seq::empty(),
    }
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
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires ordered(work.topology()),
        ensures result.topology() == work.topology(),
            ready(&work).subset_of(ready(&result)), ready(&result).contains(slot),
            result.packed_phase(slot) == if work.packed_phase(slot) == kernel::IN_PROGRESS {
                kernel::IN_PROGRESS
            } else { kernel::SOLVED },
        no_unwind
    ))]
    fn visit(work: W, slot: Request<W::Id>) -> W;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct ActiveSource<W: NativeAccess> {
    work: Option<W>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct NativeRequests<W: NativeAccess, Next: Continuation<W>> {
    active: ActiveSource<W>,
    next: PhantomData<Next>,
    #[cfg(verus_keep_ghost)]
    trace: Ghost<Seq<VisitEvidence<W::Id>>>,
    #[cfg(verus_keep_ghost)]
    initial: Ghost<ISet<Request<W::Id>>>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<W: NativeAccess, Next: Continuation<W>> NativeRequests<W, Next> {
    #[verifier::type_invariant]
    spec fn valid(&self) -> bool {
        match &self.active.work {
            Some(active) => {
                &&& ordered(active.topology())
                &&& self.initial@.subset_of(ready(active))
                &&& forall |i: int| 0 <= i < self.trace@.len() && (#[trigger] self.trace@[i]).0
                    ==> ready(active).contains(self.trace@[i].1)
            },
            None => true,
        }
    }

}

impl<W: NativeAccess> RequestView for ActiveSource<W> {
    type Id = W::Id;

    closed spec fn topology(&self) -> sizing_requests::Topology<W::Id> {
        match &self.work {
            Some(active) => active.topology(),
            None => empty(),
        }
    }
}

impl<W: NativeAccess, Next: Continuation<W>> RequestModel for NativeRequests<W, Next> {
    type Id = W::Id;
    type Source = ActiveSource<W>;
    type Event = VisitEvidence<W::Id>;

    closed spec fn topology(&self) -> sizing_requests::Topology<W::Id> { self.active.topology() }

    closed spec fn projection(&self) -> spec_fn(Request<W::Id>) -> Self::Event {
        let present = self.active.work.is_some();
        let initial = self.initial@;
        |slot: Request<W::Id>| (present, slot, initial)
    }

    closed spec fn requests(&self) -> Seq<Self::Event> { self.trace@ }
}
}

#[cfg(not(verus_keep_ghost))]
impl<W: NativeAccess> RequestView for ActiveSource<W> {
    type Id = W::Id;
}

#[cfg(not(verus_keep_ghost))]
impl<W: NativeAccess, Next: Continuation<W>> RequestModel for NativeRequests<W, Next> {
    type Id = W::Id;
    type Source = ActiveSource<W>;
}

impl<W: NativeAccess> ActiveSource<W> {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(view =>
        ensures view.is_some() == self.work.is_some(),
            view.is_some() ==> view.unwrap().topology() == self.topology(),
        no_unwind
    ))]
    fn view(&self) -> Option<&W::View> {
        match &self.work {
            Some(active) => Some(active.view()),
            None => None,
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<W: NativeAccess> RequestSource for ActiveSource<W> {
    #[inline(always)]
    fn form(&self, slot: Request<W::Id>) -> Option<Form> {
        match self.view() { Some(view) => view.form(slot), None => None }
    }

    #[inline(always)]
    fn final_declarations(&self, slot: Request<W::Id>) -> (bool, bool, bool) {
        match self.view() { Some(view) => view.final_declarations(slot), None => (false, false, false) }
    }

    #[inline(always)]
    fn stack_parent(&self, slot: Request<W::Id>) -> Option<W::Id> {
        match self.view() { Some(view) => view.stack_parent(slot), None => None }
    }

    #[inline(always)]
    fn parent(&self, node: W::Id) -> Option<W::Id> {
        match self.view() { Some(view) => view.parent(node), None => None }
    }

    #[inline(always)]
    fn parent_uses_flow(&self, slot: Request<W::Id>, parent: W::Id) -> bool {
        match self.view() { Some(view) => view.parent_uses_flow(slot, parent), None => false }
    }

    #[inline(always)]
    fn parent_uses_other_axis(&self, slot: Request<W::Id>, parent: W::Id) -> bool {
        match self.view() { Some(view) => view.parent_uses_other_axis(slot, parent), None => false }
    }

    #[inline(always)]
    fn intrinsic_uses_flow(&self, slot: Request<W::Id>) -> bool {
        match self.view() { Some(view) => view.intrinsic_uses_flow(slot), None => false }
    }

    #[inline(always)]
    fn intrinsic_uses_other_axis(&self, slot: Request<W::Id>) -> bool {
        match self.view() { Some(view) => view.intrinsic_uses_other_axis(slot), None => false }
    }

    #[inline(always)]
    fn first_child(&self, node: W::Id) -> Option<W::Id> {
        match self.view() { Some(view) => view.first_child(node), None => None }
    }

    #[inline(always)]
    fn child(&self, parent: W::Id, child: W::Id) -> (Option<W::Id>, bool) {
        match self.view() { Some(view) => view.child(parent, child), None => (None, false) }
    }

    #[inline(always)]
    fn flow_mode(&self, parent: W::Id) -> FlowMode {
        match self.view() { Some(view) => view.flow_mode(parent), None => FlowMode::Other }
    }

    #[inline(always)]
    fn block_child(&self, parent: W::Id, child: W::Id) -> (Option<W::Id>, bool, bool) {
        match self.view() { Some(view) => view.block_child(parent, child), None => (None, false, false) }
    }

    #[inline(always)]
    fn wrap_child(&self, parent: W::Id, main: bool, child: W::Id) -> (Option<W::Id>, bool) {
        match self.view() { Some(view) => view.wrap_child(parent, main, child), None => (None, false) }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<W: NativeAccess, Next: Continuation<W>> RequestAccess for NativeRequests<W, Next> {
    #[inline(always)]
    fn source(&self) -> &Self::Source { &self.active }

    #[inline(always)]
    fn emit(&mut self, slot: Request<W::Id>) {
        #[cfg(verus_keep_ghost)]
        proof! { use_type_invariant(&*self); }
        let active = self.active.work.take();
        #[cfg(verus_keep_ghost)]
        let present = active.is_some();
        if let Some(active) = active {
            #[cfg(verus_keep_ghost)]
            let prior = ready_start(&active);
            let visited = Next::visit(active, slot);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(self.initial@.subset_of(prior@));
                assert(self.initial@.subset_of(ready(&visited)));
                assert forall |i: int| 0 <= i < self.trace@.len() && (#[trigger] self.trace@[i]).0
                    implies ready(&visited).contains(self.trace@[i].1) by {
                    assert(prior@.contains(self.trace@[i].1));
                }
            }
            self.active.work = Some(visited);
        }
        #[cfg(verus_keep_ghost)]
        {
            let old_trace = self.trace;
            self.trace = append_trace(self.trace, present, slot, self.initial);
            proof! {
                if let Some(visited) = &self.active.work {
                    assert forall |i: int| 0 <= i < self.trace@.len() && (#[trigger] self.trace@[i]).0
                        implies ready(visited).contains(self.trace@[i].1) by {
                        if i < old_trace@.len() {
                            assert(self.trace@[i] == old_trace@[i]);
                            assert(ready(visited).contains(old_trace@[i].1));
                        } else {
                            assert(self.trace@[i] == (present, slot, self.initial@));
                        }
                    }
                }
            }
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Spill;

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<W: NativeAccess> Continuation<W> for Spill {
    fn visit(mut work: W, slot: Request<W::Id>) -> W {
        if let Some((opened, check)) = work.start(slot) {
            work.spill(opened, check);
        }
        work
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Step<Next>(PhantomData<Next>);

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<W: NativeAccess, Next: Continuation<W>> Continuation<W> for Step<Next> {
    fn visit(mut work: W, slot: Request<W::Id>) -> W {
        let Some((opened, check)) = work.start(slot) else { return work; };
        #[cfg(verus_keep_ghost)]
        let initial = ready_start(&work);
        let pending = NativeRequests {
            active: ActiveSource { work: Some(work) },
            next: PhantomData::<Next>,
            #[cfg(verus_keep_ghost)]
            trace: empty_trace(),
            #[cfg(verus_keep_ghost)]
            initial,
        };
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
            if let Some(active) = &visited.active.work {
                assert(inputs_available(active, slot)) by {
                    let inputs = sizing_requests::inputs(active.topology(), slot);
                    assert forall |i: int| 0 <= i < inputs.len() implies ready(active).contains(#[trigger] inputs[i]) by {
                        assert(visited.requests()[i] == (true, inputs[i], initial@));
                    }
                }
            }
            assert forall |live: Set<W::Id>| sizing_requests::live::closed(topology, live) && live.contains(slot.node)
                implies #[trigger] native_targets_live(visited.requests(), live) by {
                native_emissions_live(topology, slot, live, initial@);
            }
        }
        // The projection records that all requests returned the active solver.
        let Some(mut work) = visited.active.work else { unreachable!() };
        let _stored = work.finish(opened, check);
        work
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
pub(crate) fn drive<W: NativeAccess>(work: W, slot: Request<W::Id>) -> W {
    Configured::visit(work, slot)
}

#[cfg(test)]
pub(crate) fn drive_spill<W: NativeAccess>(work: W, slot: Request<W::Id>) -> W {
    Spill::visit(work, slot)
}
