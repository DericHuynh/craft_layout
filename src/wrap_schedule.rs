//! Ordered inputs to a stack or wrap share and to a wrapping line extent.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub enum Producer { Share, Cross }

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Request<I> {
    ParentMainFinal,
    ParentShare,
    MainFinal(I),
    MainDeclaration(I, usize),
    CrossDeclaration(I, usize),
}

#[cfg(verus_keep_ghost)]
verus! {
pub trait Model {
    type Id: Copy + Eq;
    spec fn children(&self) -> Seq<Child<Self::Id>>;
    type Event;
    type Scope;
    #[verifier::prophetic]
    spec fn scope(&self) -> Self::Scope;
    spec fn project(&self) -> spec_fn(Request<Self::Id>) -> Self::Event;
    spec fn requests(&self) -> Seq<Self::Event>;
}
}

#[cfg(not(verus_keep_ghost))]
pub trait Model {
    type Id: Copy + Eq;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait FlowRequestSchedule: Model {
    #[cfg_attr(verus_keep_ghost, verus_spec(first => ensures first == child_at(self.children(),0), no_unwind))]
    fn first(&self) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(row =>
        requires member(self.children(),child),
        ensures row==(child_at(self.children(),index(self.children(),child)+1),
            current(self.children(),child).in_flow),
        no_unwind
    ))]
    fn row(&self, child: Self::Id) -> (Option<Self::Id>, bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(fill =>
        requires member(self.children(),child),
        ensures fill==current(self.children(),child).has_fill,
        no_unwind
    ))]
    fn fills(&self, child: Self::Id) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(needed =>
        requires member(self.children(),child), i<3,
        ensures needed==selected(current(self.children(),child),producer)[i as int],
        no_unwind
    ))]
    fn declaration(&self, child: Self::Id, producer: Producer, i:usize) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires valid_request(request),
        ensures final(self).children()==old(self).children(),
            final(self).scope()==old(self).scope(), final(self).project()==old(self).project(),
            final(self).requests()==old(self).requests().push((old(self).project())(request)),
        no_unwind
    ))]
    fn request(&mut self, request: Request<Self::Id>);
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires member(old(walk).children(),child),
    ensures final(walk).children()==old(walk).children(),
        final(walk).scope()==old(walk).scope(), final(walk).project()==old(walk).project(),
        final(walk).requests()==old(walk).requests()+declarations(child,producer,
            &selected(current(old(walk).children(),child),producer),3).map_values(old(walk).project()),
    no_unwind
))]
fn request_declarations<S: FlowRequestSchedule>(walk:&mut S, child:S::Id, producer:Producer) {
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i<=3, walk.children()==old(walk).children(), member(walk.children(),child),
            walk.scope()==old(walk).scope(), walk.project()==old(walk).project(),
            walk.requests()==old(walk).requests()+declarations(child,producer,
                &selected(current(walk.children(),child),producer),i as nat).map_values(walk.project()),
        decreases 3-i,
    ))]
    while i<3 {
        if walk.declaration(child,producer,i) {
            walk.request(match producer {
                Producer::Share => Request::MainDeclaration(child,i),
                Producer::Cross => Request::CrossDeclaration(child,i),
            });
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let flags = &selected(current(walk.children(),child),producer);
            extend_declarations(Seq::empty(),child,producer,flags,i as nat);
            assert(walk.requests() =~= old(walk).requests()
                + declarations(child,producer,flags,i as nat + 1).map_values(walk.project()));
        }
        i += 1;
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires distinct(old(walk).children()),
    ensures final(walk).children()==old(walk).children(),
        final(walk).scope()==old(walk).scope(), final(walk).project()==old(walk).project(),
        final(walk).requests()==old(walk).requests() + seq![(old(walk).project())(own(producer))]
            + child_requests(old(walk).children(),producer,old(walk).children().len()).map_values(old(walk).project()),
    no_unwind
))]
pub fn request_flow_inputs<S: FlowRequestSchedule>(walk: &mut S, producer:Producer) {
    #[cfg(verus_keep_ghost)]
    let mut consumed=wrap_lines::start_scan();
    walk.request(match producer { Producer::Share => Request::ParentMainFinal, Producer::Cross => Request::ParentShare });
    let mut next=walk.first();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant walk.children()==old(walk).children(), distinct(walk.children()),
            walk.scope()==old(walk).scope(), walk.project()==old(walk).project(),
            consumed@<=walk.children().len(), next==child_at(walk.children(),consumed@),
            walk.requests()==old(walk).requests()+seq![(walk.project())(own(producer))]
                +child_requests(walk.children(),producer,consumed@).map_values(walk.project()),
        ensures consumed@==walk.children().len(),
        decreases walk.children().len()-consumed@,
    ))]
    while let Some(child)=next {
        #[cfg(verus_keep_ghost)]
        proof! { locate(walk.children(),consumed@,child); }
        let (following,in_flow)=walk.row(child);
        next=following;
        if in_flow {
            match producer {
                Producer::Cross => {
                    walk.request(Request::MainFinal(child));
                    request_declarations(walk,child,producer);
                }
                Producer::Share if walk.fills(child) => request_declarations(walk,child,producer),
                Producer::Share => walk.request(Request::MainFinal(child)),
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            extend_children(Seq::empty(),walk.children(),producer,consumed@);
            assert(walk.requests() =~= old(walk).requests() + seq![(walk.project())(own(producer))]
                + child_requests(walk.children(),producer,consumed@ + 1).map_values(walk.project()));
        }
        #[cfg(verus_keep_ghost)]
        { consumed=wrap_lines::advance(consumed); }
    }
}
