//! A small LIFO for suspended traversals. Only deep walks allocate.
#![allow(unexpected_cfgs)]

use crate::vec_memory::VecMemory;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Inline<T, const N: usize> {
    slots: [Option<T>; N],
    len: usize,
}

impl<T: Copy, const N: usize> Inline<T, N> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(overflow =>
        requires old(self).len <= N,
        ensures final(self).len <= N,
            old(self).len < N ==> overflow.is_none()
                && final(self).len == old(self).len + 1
                && final(self).slots@ == old(self).slots@.update(old(self).len as int, Some(item)),
            old(self).len == N ==> overflow == Some(item) && *final(self) == *old(self),
        no_unwind
    ))]
    fn push(&mut self, item: T) -> Option<T> {
        if self.len == N {
            return Some(item);
        }
        let index = self.len;
        self.slots[index] = Some(item);
        self.len = index + 1;
        None
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires old(self).len <= N,
        ensures final(self).len <= N, final(self).slots == old(self).slots,
            old(self).len == 0 ==> out.is_none() && final(self).len == 0,
            old(self).len > 0 ==> final(self).len + 1 == old(self).len
                && out == old(self).slots@[final(self).len as int],
        no_unwind
    ))]
    fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        self.slots[self.len]
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct WorkStack<T, const N: usize> {
    inline: Inline<T, N>,
    spill: Vec<T>,
    // Popped entries remain initialized and can be reused without growing the vector.
    spill_len: usize,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<T, const N: usize> WorkStack<T, N> {
    pub(crate) closed spec fn valid(self) -> bool {
        &&& self.inline.len <= N
        &&& self.spill_len <= self.spill.len()
        &&& self.spill_len > 0 ==> self.inline.len == N
        &&& forall|i: int| 0 <= i < self.inline.len ==> (#[trigger] self.inline.slots@[i]).is_some()
    }

    pub(crate) closed spec fn items(self) -> Seq<T> {
        Seq::new(self.inline.len as nat, |i: int| self.inline.slots@[i].unwrap())
            + self.spill@.take(self.spill_len as int)
    }

    pub(crate) closed spec fn can_push_inline(self) -> bool {
        self.inline.len < N
    }

    pub(crate) closed spec fn uses_inline_only(self) -> bool {
        self.spill_len == 0
    }

    pub(crate) closed spec fn can_push_without_growing(self) -> bool {
        self.can_push_inline() || self.spill_len < self.spill.len()
    }

    pub(crate) closed spec fn initialized_capacity(self) -> nat {
        N as nat + self.spill@.len()
    }

    pub(crate) proof fn fits_inline(self)
        requires self.valid(), self.items().len() < N,
        ensures self.can_push_inline(), self.can_push_without_growing(),
    {}

    pub(crate) proof fn fits_initialized(self)
        requires self.valid(), self.items().len() < self.initialized_capacity(),
        ensures self.can_push_without_growing(),
    {}
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.valid(), out.items() == Seq::<T>::empty(), out.uses_inline_only(),
        out.initialized_capacity() == N + spill@.len(),
    no_unwind
))]
pub(crate) fn work_stack<T: Copy, const N: usize, M: VecMemory>(spill: Vec<T>) -> WorkStack<T, N> {
    let out = WorkStack { inline: Inline { slots: M::empty_slots(), len: 0 }, spill, spill_len: 0 };
    #[cfg(verus_keep_ghost)]
    proof! { assert(out.items() =~= Seq::<T>::empty()); }
    out
}

impl<T: Copy, const N: usize> WorkStack<T, N> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).valid(),
        ensures final(self).valid(), final(self).items() == old(self).items().push(item),
            final(self).initialized_capacity() >= old(self).initialized_capacity(),
            old(self).can_push_inline() ==> final(self).uses_inline_only(),
        no_unwind
    ))]
    pub(crate) fn push<M: VecMemory>(&mut self, item: T) {
        if let Some(overflow) = self.inline.push(item) {
            let index = self.spill_len;
            if index < self.spill.len() {
                self.spill[index] = overflow;
            } else {
                M::append(&mut self.spill, overflow);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(index < self.spill@.len());
                assert(self.spill@.len() == self.spill.len());
            }
            self.spill_len = index + 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(self.spill@.take(self.spill_len as int)
                    =~= old(self).spill@.take(old(self).spill_len as int).push(item));
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |i: int| 0 <= i < self.inline.len implies (#[trigger] self.inline.slots@[i]).is_some() by {
                if i < old(self).inline.len { assert(old(self).inline.slots@[i].is_some()); }
            }
            assert(self.items() =~= old(self).items().push(item));
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires old(self).valid(),
        ensures final(self).valid(),
            final(self).initialized_capacity() == old(self).initialized_capacity(),
            old(self).uses_inline_only() ==> final(self).uses_inline_only(),
            old(self).items().len() == 0 ==> out.is_none() && final(self).items().len() == 0,
            old(self).items().len() > 0 ==> out == Some(old(self).items().last())
                && final(self).items() == old(self).items().drop_last(),
        no_unwind
    ))]
    pub(crate) fn pop(&mut self) -> Option<T> {
        let out = if self.spill_len == 0 {
            self.inline.pop()
        } else {
            self.spill_len -= 1;
            Some(self.spill[self.spill_len])
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |i: int| 0 <= i < self.inline.len implies (#[trigger] self.inline.slots@[i]).is_some() by {
                assert(old(self).inline.slots@[i].is_some());
            }
            if old(self).items().len() != 0 {
                if old(self).spill_len == 0 {
                    assert(old(self).inline.slots@[self.inline.len as int].is_some());
                } else {
                    assert(self.spill@.take(self.spill_len as int)
                        =~= old(self).spill@.take(old(self).spill_len as int).drop_last());
                }
                assert(self.items() =~= old(self).items().drop_last());
            }
        }
        out
    }

    // Return initialized storage so the next walk can reuse it without growth.
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(spill =>
        ensures self.initialized_capacity() == N + spill@.len(),
        no_unwind
    ))]
    pub(crate) fn into_spill(self) -> Vec<T> {
        self.spill
    }
}

// Sizing reverses the newly queued dependencies in one contiguous spill.
impl<T: Copy> WorkStack<T, 0> {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(len =>
        requires self.valid(),
        ensures len == self.items().len(),
        no_unwind
    ))]
    pub(crate) fn live_len(&self) -> usize { self.spill_len }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).valid(), start <= old(self).items().len(),
        ensures final(self).valid(), final(self).initialized_capacity() == old(self).initialized_capacity(),
            final(self).items().len() == old(self).items().len(),
            forall |i: int| 0 <= i < start ==> #[trigger] final(self).items()[i] == old(self).items()[i],
            forall |i: int| start <= i < old(self).items().len() ==>
                #[trigger] final(self).items()[i] == old(self).items()[start + old(self).items().len() - i - 1],
        no_unwind
    ))]
    #[allow(clippy::manual_swap)]
    pub(crate) fn reverse_from(&mut self, start: usize) {
        let end = self.spill_len;
        let mut left = start;
        let mut right = end;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant start <= left <= right <= end, end == self.spill_len, end == old(self).items().len(),
                self.valid(), self.initialized_capacity() == old(self).initialized_capacity(),
                left - start == end - right,
                forall |i:int| 0 <= i < end && (i < start || left <= i < right) ==>
                    #[trigger] self.spill@[i] == old(self).items()[i],
                forall |i:int| start <= i < left || right <= i < end ==>
                    #[trigger] self.spill@[i] == old(self).items()[start + end - i - 1],
            decreases right - left,
        ))]
        while right - left > 1 {
            right -= 1;
            let item = self.spill[left];
            self.spill[left] = self.spill[right];
            self.spill[right] = item;
            left += 1;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |i: int| start <= i < end implies
                #[trigger] self.items()[i] == old(self).items()[start + end - i - 1] by {
                if left <= i < right {
                    assert(i == left && right == left + 1 && i == start + end - i - 1);
                }
            }
        }
    }
}
