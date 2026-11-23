//! Ranked LIFO lists sharing an allocation and a free list. Links are one-based.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use super::{at_rank, BucketCount, physical, did_push, did_pop,rank};

/// Reserve a bucket for `level`. The logical head at every absolute rank stays
/// unchanged when unused buckets are inserted before or after the current span.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(idx =>
    requires old(heads).len() + *old(base) as int <= BucketCount(),
    ensures idx < final(heads).len(), idx + *final(base) as int == level as int,
        *final(base) as int + final(heads).len() <= BucketCount(),
        forall|r:int| #[trigger] at_rank(final(heads)@,*final(base),r) == at_rank(old(heads)@,*old(base),r),
        old(heads).len() != 0 && level >= *old(base) ==> *final(base) == *old(base),
))]
pub(crate) fn bucket_for(heads: &mut Vec<usize>, base: &mut u16, level: u16) -> usize {
    if heads.is_empty() {
        *base = level;
    } else if level < *base {
        let missing = usize::from(*base - level);
        let extra = missing.max(heads.len()).min(usize::from(*base));
        let old_len = heads.len();
        heads.resize(old_len + extra, 0);
        heads.copy_within(0..old_len, extra);
        let mut i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= extra, heads.len() == extra + old_len, old_len == old(heads).len(),
                extra <= *old(base) as int,
                forall|j:int| 0 <= j < i ==> #[trigger] heads[j] == 0,
                forall|j:int| 0 <= j < old_len ==> #[trigger] heads[j+extra] == old(heads)[j],
            decreases extra - i,
        ))]
        while i < extra {
            heads[i] = 0;
            i += 1;
        }
        *base -= extra as u16;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|r:int| #[trigger] at_rank(heads@,*base,r) == at_rank(old(heads)@,*old(base),r) by {
                if *old(base) <= r < *old(base) as int + old_len {
                    assert(*base as int == *old(base) as int - extra);
                    assert(heads[(r-*old(base))+extra] == old(heads)[r-*old(base)]);
                    assert(heads[r-*base] == old(heads)[r-*old(base)]);
                }
            }
        }
    }
    let index = usize::from(level - *base);
    if heads.len() <= index {
        grow_heads(heads, index + 1, *base);
    }
    index
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(heads).len() <= len,
    ensures final(heads).len() == len,
        forall|r:int| #[trigger] at_rank(final(heads)@,_base,r) == at_rank(old(heads)@,_base,r),
))]
fn grow_heads(heads: &mut Vec<usize>, len: usize, _base: u16) {
    heads.resize(len, 0);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|r:int| #[trigger] at_rank(heads@,_base,r) == at_rank(old(heads)@,_base,r) by {
            if _base <= r < _base as int + len && r - _base >= old(heads).len() {
                assert(heads[r - _base] == 0);
            }
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires *old(free) <= old(entries).len(),
    ensures ({
        let prev = old(entries)@;
        let link = *old(free);
        let value = (slot,*old(head));
        &&& final(entries)@ == (if link == 0 { prev.push(value) } else { prev.update(link-1,value) })
        &&& *final(head) == (if link == 0 { prev.len() as int+1 } else {link as int})
        &&& *final(free) == (if link == 0 {0usize} else {prev[link-1].1})
    }),
))]
pub(crate) fn link<T>(entries: &mut Vec<(T, usize)>, free: &mut usize, head: &mut usize, slot: T) {
    let entry = (slot, *head);
    if *free == 0 {
        entries.push(entry);
        *head = entries.len();
    } else {
        *head = *free;
        let index = *free - 1;
        *free = entries[index].1;
        entries[index] = entry;
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(slot =>
    requires 0 < *old(head) <= old(entries).len(),
    ensures ({
        let prev = old(entries)@;
        let link = *old(head);
        &&& slot == prev[link-1].0
        &&& *final(head) == prev[link-1].1
        &&& *final(free) == link
        &&& final(entries)@ == prev.update(link-1,(slot,*old(free)))
    }),
    no_unwind
))]
pub(crate) fn unlink<T: Copy>(entries: &mut [(T, usize)], free: &mut usize, head: &mut usize) -> T {
    let link = *head;
    let (slot, next) = &mut entries[link - 1];
    *head = *next;
    *next = *free;
    *free = link;
    *slot
}

/// Select the lowest occupied dependency bucket from the current cursor.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(found =>
    requires start <= heads.len(),
    ensures start <= found <= heads.len(),
        found < heads.len() ==> heads[found as int] != 0,
        forall|i: int| start <= i < found ==> #[trigger] heads[i] == 0,
    no_unwind
))]
pub fn first_nonempty(heads: &[usize], start: usize) -> usize {
    let mut index = start;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= index <= heads.len(),
            forall|i: int| start <= i < index ==> #[trigger] heads[i] == 0,
        decreases heads.len() - index,
    ))]
    while index < heads.len() && heads[index] == 0 {
        index += 1;
    }
    index
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug)]
#[cfg_attr(not(verus_keep_ghost), derive(Clone))]
pub struct WorkQueue<T> {
    pub heads: Vec<usize>,
    pub entries: Vec<(T, usize)>,
    pub free: usize,
    pub cursor: usize,
    pub first_level: u16,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(q =>
    ensures q.heads.len()==0, q.entries.len()==0, q.free==0, q.cursor==0, q.first_level==0,
))]
const fn empty_queue<T>() -> WorkQueue<T> {
    WorkQueue { heads: Vec::new(), entries: Vec::new(), free: 0, cursor: 0, first_level: 0 }
}

impl<T> WorkQueue<T> {
    pub(crate) const fn new() -> Self { empty_queue() }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires physical(old(self)), old(self).cursor==0 || old(self).first_level as int + old(self).cursor <= level,
        ensures did_push(old(self),final(self),level,slot),
    ))]
    pub(crate) fn push(&mut self, level: u16, slot: T) {
        debug_assert!(self.heads.is_empty() || level >= self.first_level || self.cursor == 0);
        let index = bucket_for(&mut self.heads, &mut self.first_level, level);
        debug_assert!(index >= self.cursor);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|r:int| #[trigger] rank(old(self),r) == at_rank(self.heads@,self.first_level,r) by {
                assert(at_rank(self.heads@,self.first_level,r)==at_rank(old(self).heads@,old(self).first_level,r));
            }
            assert(at_rank(self.heads@,self.first_level,level as int) == rank(old(self),level as int));
            assert(self.heads[index as int] == rank(old(self),level as int));
        }
        link(&mut self.entries, &mut self.free, &mut self.heads[index], slot);
        #[cfg(verus_keep_ghost)]
        proof! {
            let e=if old(self).free==0 {old(self).entries.len() as int+1} else {old(self).free as int};
            assert forall|pos:int| #[trigger] rank(self,pos) ==
                (if pos==level as int {e} else {rank(old(self),pos) as int}) by {
                if self.first_level <= pos < self.first_level as int + self.heads.len() && pos != level as int {
                    assert(self.heads[pos-self.first_level] == rank(old(self),pos));
                }
            }
            assert forall|pos:int| pos < self.first_level as int + self.cursor implies #[trigger] rank(self,pos)==0 by {
                if self.cursor==0 { } else { assert(self.first_level==old(self).first_level); }
            }
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(value =>
        requires physical(old(self)),
        ensures did_pop(old(self),final(self),value),
    ))]
    pub(crate) fn pop(&mut self) -> Option<T> where T: Copy {
        self.cursor = first_nonempty(&self.heads, self.cursor);
        if self.cursor == self.heads.len() {
            self.clear();
            return None;
        }
        Some(unlink(&mut self.entries, &mut self.free, &mut self.heads[self.cursor]))
    }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).heads.len()==0, final(self).entries.len()==0, final(self).free==0, final(self).cursor==0,
    ))]
    pub(crate) fn clear(&mut self) {
        self.heads.clear();
        self.entries.clear();
        self.free = 0;
        self.cursor = 0;
    }
}
