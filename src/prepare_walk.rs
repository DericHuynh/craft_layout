//! Iterative postorder preparation with a stack of suspended parents.
#![allow(unexpected_cfgs)]

use crate::work_stack::WorkStack;
use crate::vec_memory::VecMemory;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
#[derive(Clone, Copy)]
pub(crate) enum State<F, R> {
    Children(F),
    Done(R),
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum ChildStep<C, F> {
    Prepared,
    Descend(C, F),
    End,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait Model {
    type Child: Copy;
    type Frame: Copy;
    type Summary: Copy;
    type Context: ?Sized;
    type Topology;

    /// Three units for each node covered by the unvisited child suffix.
    /// Whole branches prepared by a fast path also consume their units.
    spec fn remaining(frame: Self::Frame) -> nat;
    spec fn admissible(context: &Self::Context) -> (spec_fn(Self::Frame) -> bool, spec_fn(Self::Child) -> bool);
    spec fn topology(&self, context: &Self::Context) -> Self::Topology;
    spec fn valid(&self, context: &Self::Context) -> bool;

    /// Relate a driver's output to the active frame and suspended parents.
    spec fn coherent(&self, context: &Self::Context, active: Option<Self::Frame>,
        suspended: Seq<(Self::Frame, Self::Child)>) -> bool;
}

pub(crate) open spec fn allowed<D: Model>(context: &D::Context, state: State<D::Frame, D::Summary>) -> bool {
    match state {
        State::Children(frame) => (D::admissible(context).0)(frame),
        State::Done(_) => true,
    }
}

pub(crate) open spec fn eligible_pair<D: Model + ?Sized>(context: &D::Context, pair: (D::Frame, D::Child)) -> bool {
    (D::admissible(context).0)(pair.0) && (D::admissible(context).1)(pair.1)
}

pub(crate) open spec fn eligible_stack<D: Model>(context: &D::Context, pending: Seq<(D::Frame, D::Child)>) -> bool {
    forall |i: int| 0 <= i < pending.len() ==> eligible_pair::<D>(context, #[trigger] pending[i])
}

pub(crate) open spec fn active_frame<D: Model>(state: State<D::Frame, D::Summary>) -> Option<D::Frame> {
    match state { State::Children(frame) => Some(frame), State::Done(_) => None }
}

fn saved_frontier<D: Model, const N: usize>(stack: &WorkStack<(D::Frame, D::Child), N>)
    -> (frontier: Ghost<Seq<(D::Frame, D::Child)>>)
    ensures frontier@ == stack.items(),
    no_unwind
{
    Ghost(stack.items())
}

pub(crate) open spec fn active_cost<D: Model>(state: State<D::Frame, D::Summary>) -> nat {
    match state {
        State::Children(frame) => D::remaining(frame) + 2,
        State::Done(_) => 1,
    }
}

/// In a stable preorder, advancing past the selected child consumes its
/// entire subtree. A descended frame keeps only that child's descendants.
pub proof fn preorder_child_budget(begin: nat, child_end: nat, parent_end: nat)
    requires begin < child_end <= parent_end,
    ensures
        3 * (parent_end - child_end) < 3 * (parent_end - begin),
        3 * (parent_end - child_end) + 3 * (child_end - begin - 1) + 2
            < 3 * (parent_end - begin),
{}

/// After consuming a sibling, either the next one starts beyond its subtree
/// or the suffix is empty. Descending keeps only the remaining descendants.
pub proof fn suffix_and_descendant_budget(
    begin: nat, end: nat, parent_end: nat, resume: nat, first_child: nat,
)
    requires begin < end <= resume <= parent_end, begin < first_child <= end,
    ensures 3 * (parent_end - resume) + 3 * (end - first_child) + 2 < 3 * (parent_end - begin),
{}

spec fn suspended_cost<D: Model>(frames: Seq<(D::Frame, D::Child)>) -> nat
    decreases frames.len(),
{
    if frames.len() == 0 { 0 }
    else { suspended_cost::<D>(frames.drop_last()) + D::remaining(frames.last().0) + 2 }
}

fn saved_cost<D: Model, const N: usize>(
    stack: &WorkStack<(D::Frame, D::Child), N>, state: State<D::Frame, D::Summary>,
) -> (saved: Ghost<(Seq<(D::Frame, D::Child)>, nat)>)
    ensures saved@ == (stack.items(), active_cost::<D>(state)),
    no_unwind
{
    Ghost((stack.items(), active_cost::<D>(state)))
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait Model {
    type Child: Copy;
    type Frame: Copy;
    type Summary: Copy;
    type Context: ?Sized;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Driver: Model {
    #[cfg_attr(verus_keep_ghost, verus_spec(step =>
        requires old(self).valid(old(context)), (Self::admissible(old(context)).0)(*old(frame)),
            old(self).coherent(old(context), Some(*old(frame)), suspended@),
        ensures Self::admissible(final(context)) == Self::admissible(old(context)),
            final(self).topology(final(context)) == old(self).topology(old(context)),
            final(self).valid(final(context)),
            (Self::admissible(final(context)).0)(*final(frame)),
            match step {
            ChildStep::Prepared =>
                Self::remaining(*final(frame)) < Self::remaining(*old(frame)),
            ChildStep::Descend(_, branch) =>
                Self::remaining(*final(frame)) + Self::remaining(branch) + 2
                    < Self::remaining(*old(frame)),
            ChildStep::End => Self::remaining(*final(frame)) == 0,
        },
        match step {
            ChildStep::Descend(child, branch) => (Self::admissible(final(context)).1)(child) && (Self::admissible(final(context)).0)(branch)
                && final(self).coherent(final(context), Some(branch), suspended@.push((*final(frame), child))),
            _ => final(self).coherent(final(context), Some(*final(frame)), suspended@),
        },
        no_unwind
    ))]
    fn advance(&mut self, context: &mut Self::Context, frame: &mut Self::Frame,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>)
        -> ChildStep<Self::Child, Self::Frame>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).valid(old(context)), eligible_pair::<Self>(old(context), (*old(parent), child)),
            old(self).coherent(old(context), None, suspended@.push((*old(parent), child))),
        ensures Self::remaining(*final(parent)) == Self::remaining(*old(parent)),
            final(self).valid(final(context)),
            Self::admissible(final(context)) == Self::admissible(old(context)),
            final(self).topology(final(context)) == old(self).topology(old(context)),
            (Self::admissible(final(context)).0)(*final(parent)),
            final(self).coherent(final(context), Some(*final(parent)), suspended@),
        no_unwind
    ))]
    fn include(&mut self, context: &mut Self::Context, parent: &mut Self::Frame, child: Self::Child, summary: Self::Summary,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).valid(old(context)), (Self::admissible(old(context)).0)(frame),
            Self::remaining(frame) == 0,
            old(self).coherent(old(context), Some(frame), suspended@),
        ensures Self::admissible(final(context)) == Self::admissible(old(context)),
            final(self).topology(final(context)) == old(self).topology(old(context)),
            final(self).valid(final(context)), final(self).coherent(final(context), None, suspended@),
        no_unwind
    ))]
    fn finish(&mut self, context: &mut Self::Context, frame: Self::Frame,
        #[cfg(verus_keep_ghost)] suspended: Ghost<Seq<(Self::Frame, Self::Child)>>) -> Self::Summary;
}

/// Continue each suspended parent with its child's finished summary. Deeper
/// walks can grow storage through the Copy allocation primitive.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(stack).valid(), old(stack).items().len() == 0, old(stack).uses_inline_only(),
        allowed::<D>(old(context), start), old(driver).valid(old(context)),
        old(driver).coherent(old(context), active_frame::<D>(start), old(stack).items()),
    ensures final(stack).valid(), final(stack).items().len() == 0,
        D::admissible(final(context)) == D::admissible(old(context)),
        final(driver).topology(final(context)) == old(driver).topology(old(context)), final(driver).valid(final(context)),
        final(driver).coherent(final(context), None, final(stack).items()),
    no_unwind
))]
pub(crate) fn run<D: Driver, const N: usize, M: VecMemory>(
    driver: &mut D,
    context: &mut D::Context,
    start: State<D::Frame, D::Summary>,
    stack: &mut WorkStack<(D::Frame, D::Child), N>,
) -> D::Summary {
    let mut state = start;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stack.valid(),
            active_cost::<D>(state) + suspended_cost::<D>(stack.items()) <= active_cost::<D>(start),
            stack.initialized_capacity() >= old(stack).initialized_capacity(),
            D::admissible(context) == D::admissible(old(context)),
            driver.topology(context) == old(driver).topology(old(context)),
            allowed::<D>(context, state), eligible_stack::<D>(context, stack.items()), driver.valid(context),
            driver.coherent(context, active_frame::<D>(state), stack.items()),
        decreases active_cost::<D>(state) + suspended_cost::<D>(stack.items()),
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        let saved = saved_cost::<D, N>(stack, state);
        state = match state {
            State::Children(mut frame) => {
                // Consecutive leaf preparations update the same frame in place.
                #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
                #[cfg_attr(verus_keep_ghost, verifier::allow_complex_invariants)]
                #[cfg_attr(verus_keep_ghost, verus_spec(
                    invariant_except_break stack.items() == saved@.0,
                        stack.valid(), eligible_stack::<D>(context, stack.items()),
                        stack.initialized_capacity() >= old(stack).initialized_capacity(),
                        D::admissible(context) == D::admissible(old(context)),
                        driver.topology(context) == old(driver).topology(old(context)), driver.valid(context),
                        (D::admissible(context).0)(frame), D::remaining(frame) + 2 <= saved@.1,
                        driver.coherent(context, Some(frame), stack.items()),
                    decreases D::remaining(frame),
                ))]
                loop {
                    #[cfg(verus_keep_ghost)]
                    let suspended = saved_frontier::<D, N>(stack);
                    match driver.advance(context, &mut frame, #[cfg(verus_keep_ghost)] suspended) {
                        ChildStep::Prepared => {}
                        ChildStep::Descend(child, branch) => {
                            stack.push::<M>((frame, child));
                            #[cfg(verus_keep_ghost)]
                            proof! {
                                assert(stack.items().drop_last() =~= saved@.0);
                                assert forall |i: int| 0 <= i < stack.items().len()
                                    implies eligible_pair::<D>(context, #[trigger] stack.items()[i]) by {
                                    if i < saved@.0.len() {
                                        assert(stack.items()[i] == saved@.0[i]);
                                    }
                                }
                            }
                            break State::Children(branch);
                        }
                        ChildStep::End => {
                            break State::Done(driver.finish(context, frame, #[cfg(verus_keep_ghost)] suspended));
                        }
                    }
                }
            }
            State::Done(summary) => {
                let Some((mut parent, child)) = stack.pop() else {
                    #[cfg(verus_keep_ghost)]
                    proof! { assert(stack.items() =~= saved@.0); }
                    return summary;
                };
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert((parent, child) == saved@.0[saved@.0.len() - 1]);
                    assert(stack.items().push((parent, child)) =~= saved@.0);
                    assert forall |i: int| 0 <= i < stack.items().len()
                        implies eligible_pair::<D>(context, #[trigger] stack.items()[i]) by {
                        assert(stack.items()[i] == saved@.0[i]);
                    }
                }
                #[cfg(verus_keep_ghost)]
                let suspended = saved_frontier::<D, N>(stack);
                driver.include(context, &mut parent, child, summary, #[cfg(verus_keep_ghost)] suspended);
                State::Children(parent)
            }
        };
    }
}
