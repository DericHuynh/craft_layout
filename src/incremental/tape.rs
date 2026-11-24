//! Bounded recording and replay of a stable numeric dependency schedule.
#![allow(unexpected_cfgs)]

use crate::vec_memory::{FallibleVecMemory, VecMemory, try_append};
use super::intake::Changes;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const CAPACITY: usize = 1024;
#[cfg_attr(verus_keep_ghost, verus_verify)]
const EDIT_LIMIT: usize = 8;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const MIN_STEPS: usize = 64;

#[derive(Clone, Copy, Debug, Default)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct Axes {
    pub horizontal: bool,
    pub vertical: bool,
}

impl Axes {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.any(), no_unwind))]
    pub(crate) fn any(self) -> bool { self.horizontal || self.vertical }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.covers(requested), no_unwind))]
    pub(crate) fn covers(self, requested: Self) -> bool {
        (!requested.horizontal || self.horizontal) && (!requested.vertical || self.vertical)
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out.covers(self), out.covers(other), no_unwind))]
    pub(crate) fn union(self, other: Self) -> Self {
        Self { horizontal: self.horizontal || other.horizontal, vertical: self.vertical || other.vertical }
    }
}

/// Native equality for a node identity and its copyable registration mask.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait EditEquality<I: Copy, C: Copy> {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (left == right), no_unwind))]
    fn same_id(left: I, right: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (left == right), no_unwind))]
    fn same_change(left: C, right: C) -> bool;
}

#[derive(Clone, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct Tape<I, C, S> {
    pub axes: Axes,
    pub(crate) declarations: Vec<(I, C)>,
    pub(crate) content: Vec<I>,
    pub steps: Vec<S>,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) struct TapeView<I, C, S> {
    pub axes: Axes,
    pub declarations: Seq<(I, C)>,
    pub content: Seq<I>,
    pub steps: Seq<S>,
}

impl<I, C, S> Tape<I, C, S> {
    pub(crate) open spec fn view(&self) -> TapeView<I, C, S> {
        TapeView { axes: self.axes, declarations: self.declarations@, content: self.content@, steps: self.steps@ }
    }
}
}

#[cfg(not(verus_keep_ghost))]
impl<I, C, S> Tape<I, C, S> {
    pub(crate) const fn new() -> Self {
        Self {
            axes: Axes { horizontal: false, vertical: false },
            declarations: Vec::new(),
            content: Vec::new(),
            steps: Vec::new(),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<I: Copy, C: Copy, S: Copy> Tape<I, C, S> {

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).steps.len() == 0,
        final(self).declarations.len() == 0, final(self).content.len() == 0, !final(self).axes.any(), no_unwind))]
    pub(crate) fn invalidate<M: VecMemory>(&mut self) {
        self.axes = Axes { horizontal: false, vertical: false };
        M::clear(&mut self.steps);
        M::clear(&mut self.declarations);
        M::clear(&mut self.content);
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(equal => ensures equal ==
        (self.declarations@ == edits.declarations@ && self.content@ == edits.content@), no_unwind))]
    pub(crate) fn same_edits<E: EditEquality<I, C>>(&self, edits: &Changes<I, C>) -> bool {
        if self.declarations.len() != edits.declarations.len() || self.content.len() != edits.content.len() {
            return false;
        }
        let mut i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= self.declarations.len(), self.declarations.len() == edits.declarations.len(),
                forall |j: int| 0 <= j < i ==> self.declarations@[j] == edits.declarations@[j],
            decreases self.declarations.len() - i,
        ))]
        while i < self.declarations.len() {
            let (left_node, left_change) = self.declarations[i];
            let (right_node, right_change) = edits.declarations[i];
            if !E::same_id(left_node, right_node) || !E::same_change(left_change, right_change) {
                #[cfg(verus_keep_ghost)]
                proof! { assert(self.declarations@[i as int] != edits.declarations@[i as int]); }
                return false;
            }
            i += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(self.declarations@ =~= edits.declarations@); }
        i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= self.content.len(), self.content.len() == edits.content.len(),
                self.declarations@ == edits.declarations@,
                forall |j: int| 0 <= j < i ==> self.content@[j] == edits.content@[j],
            decreases self.content.len() - i,
        ))]
        while i < self.content.len() {
            if !E::same_id(self.content[i], edits.content[i]) {
                #[cfg(verus_keep_ghost)]
                proof! { assert(self.content@[i as int] != edits.content@[i as int]); }
                return false;
            }
            i += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(self.content@ =~= edits.content@); }
        true
    }

    /// A copied key accompanies a schedule only after successful discovery.
    /// Allocation failure leaves an empty schedule.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(copied =>
        ensures final(self).steps.len() == 0, !final(self).axes.any(),
            copied ==> final(self).declarations@ == edits.declarations@
                && final(self).content@ == edits.content@,
        no_unwind))]
    pub(crate) fn copy_key<M: VecMemory + FallibleVecMemory>(&mut self, edits: &Changes<I, C>) -> bool {
        self.invalidate::<M>();
        if edits.declarations.len() > EDIT_LIMIT || edits.content.len() > EDIT_LIMIT {
            return false;
        }
        let mut i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= edits.declarations.len(), self.declarations@ == edits.declarations@.take(i as int),
                self.steps.len() == 0, !self.axes.any(), self.content.len() == 0,
            decreases edits.declarations.len() - i,
        ))]
        while i < edits.declarations.len() {
            if !try_append::<_, M>(&mut self.declarations, edits.declarations[i]) { return false; }
            i += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(self.declarations@ =~= edits.declarations@); }
        i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= edits.content.len(), self.content@ == edits.content@.take(i as int),
                self.steps.len() == 0, !self.axes.any(), self.declarations@ == edits.declarations@,
            decreases edits.content.len() - i,
        ))]
        while i < edits.content.len() {
            if !try_append::<_, M>(&mut self.content, edits.content[i]) { return false; }
            i += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(self.content@ =~= edits.content@); }
        true
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(ok =>
    ensures final(steps)@ == if ok { old(steps)@.push(step) } else { old(steps)@ },
        ok ==> final(steps).len() <= CAPACITY,
    no_unwind))]
pub(crate) fn record<S: Copy, M: FallibleVecMemory>(steps: &mut Vec<S>, step: S) -> bool {
    steps.len() < CAPACITY && try_append::<_, M>(steps, step)
}
