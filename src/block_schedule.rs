// Block sizing declares its vertical context and measures each eligible child
// before consuming the child's optional exported margin summary.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns auto_content_height(intrinsic,flex,parent_auto), no_unwind))]
pub fn auto_content_height(intrinsic: bool, flex: bool, parent_auto: bool) -> bool {
    intrinsic || (parent_auto && flex)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns inline_auto(horizontal,regular,block_item), no_unwind))]
pub fn inline_auto(horizontal: bool, regular: bool, block_item: bool) -> bool {
    horizontal && regular && block_item
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns flex_uses_content_height(vertical,flex,parent_auto), no_unwind))]
pub fn flex_uses_content_height(vertical: bool, flex: bool, parent_auto: bool) -> bool {
    vertical && flex && parent_auto
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns in_flow_parent(block_children,free), no_unwind))]
pub fn in_flow_parent(block_children: Option<bool>, free: bool) -> Option<bool> {
    if free { None } else { block_children }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Request<I> {
    Height(I),
    Margins(I),
}

#[cfg(verus_keep_ghost)]
verus! {
pub trait ScheduleModel {
    type Id: Copy + Eq;

    // The sibling list is unchanged during a traversal. Descendant measurement
    // writes sizes and side-state, but it cannot change layout declarations.
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
pub trait ScheduleModel {
    type Id: Copy + Eq;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait BlockSchedule: ScheduleModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(next => ensures next == child_at(self.children(),0), no_unwind))]
    fn first_child(&self) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(row =>
        requires unique(self.children()), id_index(self.children(),id) < self.children().len(),
            child_at(self.children(),id_index(self.children(),id)) == Some(id),
        ensures row == (
            child_at(self.children(),id_index(self.children(),id)+1),
            self.children()[id_index(self.children(),id) as int].in_flow,
            self.children()[id_index(self.children(),id) as int].block,
        ),
        no_unwind
    ))]
    fn read_child(&self, id: Self::Id) -> (Option<Self::Id>, bool, bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).children() == old(self).children(),
            final(self).scope() == old(self).scope(), final(self).project() == old(self).project(),
            final(self).requests() == old(self).requests().push((old(self).project())(request)),
        no_unwind
    ))]
    fn request(&mut self, request: Request<Self::Id>);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires unique(old(solver).children()),
    ensures final(solver).children() == old(solver).children(),
        final(solver).scope() == old(solver).scope(), final(solver).project() == old(solver).project(),
        final(solver).requests() == old(solver).requests()
            + block_inputs(old(solver).children(),old(solver).children().len()).map_values(old(solver).project()),
    no_unwind
))]
pub fn request_block_inputs<S: BlockSchedule>(solver: &mut S) {
    let mut next = solver.first_child();
    #[cfg(verus_keep_ghost)]
    let mut seen = begin_scan();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            solver.children() == old(solver).children(), unique(solver.children()),
            solver.scope() == old(solver).scope(), solver.project() == old(solver).project(),
            seen@ <= solver.children().len(), next == child_at(solver.children(),seen@),
            solver.requests() == old(solver).requests() + block_inputs(solver.children(),seen@).map_values(solver.project()),
        ensures seen@ == solver.children().len(),
        decreases solver.children().len() - seen@,
    ))]
    while let Some(child) = next {
        #[cfg(verus_keep_ghost)]
        proof! { locate(solver.children(),seen@,child); }
        let (following, in_flow, block) = solver.read_child(child);
        next = following;
        if in_flow {
            solver.request(Request::Height(child));
            if block {
                solver.request(Request::Margins(child));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            append_child(Seq::empty(),solver.children(),seen@);
            assert(solver.requests() =~= old(solver).requests()
                + block_inputs(solver.children(),seen@ + 1).map_values(solver.project()));
        }
        #[cfg(verus_keep_ghost)]
        {
            seen = step_scan(seen);
        }
    }
}
