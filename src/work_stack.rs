//! A small LIFO for suspended traversals. Only deep walks allocate.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Inline<T, const N: usize> {
    slots: [Option<T>; N],
    len: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out.len == 0))]
fn empty_inline<T: Copy, const N: usize>() -> Inline<T, N> {
    Inline { slots: [None; N], len: 0 }
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
}

#[cfg(verus_keep_ghost)]
verus! {
impl<T, const N: usize> WorkStack<T, N> {
    pub(crate) closed spec fn valid(self) -> bool {
        &&& self.inline.len <= N
        &&& self.spill.len() > 0 ==> self.inline.len == N
        &&& forall|i: int| 0 <= i < self.inline.len ==> (#[trigger] self.inline.slots@[i]).is_some()
    }

    pub(crate) closed spec fn items(self) -> Seq<T> {
        Seq::new(self.inline.len as nat, |i: int| self.inline.slots@[i].unwrap()) + self.spill@
    }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out.valid(), out.items() == Seq::<T>::empty()))]
pub(crate) fn work_stack<T: Copy, const N: usize>(mut spill: Vec<T>) -> WorkStack<T, N> {
    spill.clear();
    let out = WorkStack { inline: empty_inline(), spill };
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
    ))]
    pub(crate) fn push(&mut self, item: T) {
        if let Some(overflow) = self.inline.push(item) {
            self.spill.push(overflow);
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
            old(self).items().len() == 0 ==> out.is_none() && final(self).items().len() == 0,
            old(self).items().len() > 0 ==> out == Some(old(self).items().last())
                && final(self).items() == old(self).items().drop_last(),
    ))]
    pub(crate) fn pop(&mut self) -> Option<T> {
        let out = match self.spill.pop() {
            Some(item) => Some(item),
            None => self.inline.pop(),
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |i: int| 0 <= i < self.inline.len implies (#[trigger] self.inline.slots@[i]).is_some() by {
                assert(old(self).inline.slots@[i].is_some());
            }
            if old(self).items().len() != 0 {
                if old(self).spill.len() == 0 {
                    assert(old(self).inline.slots@[self.inline.len as int].is_some());
                }
                assert(self.items() =~= old(self).items().drop_last());
            }
        }
        out
    }

    pub(crate) fn into_spill(self) -> Vec<T> { self.spill }
}
