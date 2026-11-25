//! Ranked LIFO lists sharing an allocation and a free list. Links are one-based.
#![allow(unexpected_cfgs)]
use crate::vec_memory::{CapacityMemory, VecMemory, append_bounded, max_copy_capacity};
#[cfg(verus_keep_ghost)]
use crate::vec_memory::capacity_limit;
#[cfg(not(verus_keep_ghost))]
use crate::vec_memory::RustVec;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use super::{
    at_rank, BucketCount, did_pop, did_push, empty_queue_is_represented, no_entries, physical,
    pop_removes_lowest, push_preserves_membership, rank, represented, well_formed,
};

/// At most 65,536 machine words hold the rank buckets. Enlarging the range
/// initializes the new bucket heads to zero. Copying bucket words has no
/// allocation and accepts overlapping ranges.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait ZeroedQueueMemory: VecMemory + CapacityMemory {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(items).len() <= len <= BucketCount(),
        ensures final(items).len() == len,
            forall |i: int| 0 <= i < old(items).len() ==> #[trigger] final(items)[i] == old(items)[i],
            forall |i: int| old(items).len() <= i < len ==> #[trigger] final(items)[i] == 0,
        no_unwind
    ))]
    fn resize_zeros(items: &mut Vec<usize>, len: usize);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires source_len + destination <= old(items).len(),
        ensures final(items).len() == old(items).len(),
            forall |i: int| 0 <= i < source_len ==> #[trigger] final(items)[destination + i] == old(items)[i],
        no_unwind
    ))]
    fn copy_prefix(items: &mut Vec<usize>, source_len: usize, destination: usize);
}

#[cfg(not(verus_keep_ghost))]
impl ZeroedQueueMemory for RustVec {
    #[inline(always)]
    fn resize_zeros(items: &mut Vec<usize>, len: usize) { items.resize(len, 0); }

    #[inline(always)]
    fn copy_prefix(items: &mut Vec<usize>, source_len: usize, destination: usize) {
        items.copy_within(0..source_len, destination);
    }
}

#[cfg(verus_keep_ghost)]
verus! {
fn head_words(heads: &Vec<usize>) -> (words: Ghost<Seq<usize>>)
    ensures words@ == heads@,
    no_unwind
{
    Ghost(heads@)
}
}

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
    no_unwind
))]
pub(crate) fn bucket_for<M: ZeroedQueueMemory>(heads: &mut Vec<usize>, base: &mut u16, level: u16) -> usize {
    if heads.is_empty() {
        *base = level;
    } else if level < *base {
        let old_len = heads.len();
        let missing = (*base - level) as usize;
        let wanted = if old_len > missing { old_len } else { missing };
        let extra = if wanted > *base as usize { *base as usize } else { wanted };
        M::resize_zeros(heads, old_len + extra);
        #[cfg(verus_keep_ghost)]
        let expanded = head_words(heads);
        M::copy_prefix(heads, old_len, extra);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |j: int| 0 <= j < old_len implies
                #[trigger] heads[j + extra] == old(heads)[j] by {
                assert(heads[extra + j] == expanded@[j]);
                assert(expanded@[j] == old(heads)[j]);
            }
        }
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
    let index = (level - *base) as usize;
    if heads.len() <= index {
        grow_heads::<M>(heads, index + 1, *base);
    }
    index
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(heads).len() <= len <= BucketCount(),
    ensures final(heads).len() == len,
        forall|r:int| #[trigger] at_rank(final(heads)@,_base,r) == at_rank(old(heads)@,_base,r),
    no_unwind
))]
fn grow_heads<M: ZeroedQueueMemory>(heads: &mut Vec<usize>, len: usize, _base: u16) {
    M::resize_zeros(heads, len);
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
        *old(free) == 0 ==> old(entries).len() < capacity_limit::<(T, usize)>(),
    ensures ({
        let prev = old(entries)@;
        let link = *old(free);
        let value = (slot,*old(head));
        &&& final(entries)@ == (if link == 0 { prev.push(value) } else { prev.update(link-1,value) })
        &&& *final(head) == (if link == 0 { prev.len() as int+1 } else {link as int})
        &&& *final(free) == (if link == 0 {0usize} else {prev[link-1].1})
    }),
    no_unwind
))]
pub(crate) fn link<T: Copy, M: CapacityMemory>(entries: &mut Vec<(T, usize)>, free: &mut usize, head: &mut usize, slot: T) {
    let entry = (slot, *head);
    if *free == 0 {
        append_bounded::<_, M>(entries, entry);
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
    pub started: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(q =>
    ensures q.heads.len()==0, q.entries.len()==0, q.free==0, q.cursor==0, q.first_level==0, !q.started,
        well_formed(&q),
))]
const fn empty_queue<T>() -> WorkQueue<T> {
    let result = WorkQueue { heads: Vec::new(), entries: Vec::new(), free: 0, cursor: 0, first_level: 0, started: false };
    #[cfg(verus_keep_ghost)]
    proof! {
        empty_queue_is_represented(&result);
        assert(represented(&result, no_entries()));
    }
    result
}

impl<T> WorkQueue<T> {
    pub(crate) const fn new() -> Self { empty_queue() }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(accepted =>
        requires well_formed(old(self)),
        ensures accepted == ((!old(self).started || old(self).first_level as int + old(self).cursor <= level)
                && (old(self).free != 0 || old(self).entries.len() < capacity_limit::<(T, usize)>())),
            accepted ==> did_push(old(self),final(self),level,slot),
            !accepted ==> *final(self) == *old(self),
            well_formed(final(self)),
        no_unwind
    ))]
    pub(crate) fn try_push_with<M: ZeroedQueueMemory>(&mut self, level: u16, slot: T) -> bool where T: Copy {
        // The first pop can leave the cursor at zero. After that pop the
        // current bucket is a lower bound, even when its last slot was taken.
        if self.started && (level < self.first_level || ((level - self.first_level) as usize) < self.cursor) {
            return false;
        }
        if self.free == 0 && self.entries.len() >= max_copy_capacity::<(T, usize)>() {
            return false;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let witness = choose |w: super::Chains| #[trigger] represented(old(self), w);
            assert(physical(old(self)));
        }
        let index = bucket_for::<M>(&mut self.heads, &mut self.first_level, level);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall|r:int| #[trigger] rank(old(self),r) == at_rank(self.heads@,self.first_level,r) by {
                assert(at_rank(self.heads@,self.first_level,r)==at_rank(old(self).heads@,old(self).first_level,r));
            }
            assert(at_rank(self.heads@,self.first_level,level as int) == rank(old(self),level as int));
            assert(self.heads[index as int] == rank(old(self),level as int));
        }
        link::<_, M>(&mut self.entries, &mut self.free, &mut self.heads[index], slot);
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
            let prior = choose |w: super::Chains| #[trigger] represented(old(self), w);
            push_preserves_membership(old(self), self, level, slot, prior);
        }
        true
    }

    #[cfg(not(verus_keep_ghost))]
    #[inline]
    pub(crate) fn try_push(&mut self, level: u16, slot: T) -> bool where T: Copy {
        self.try_push_with::<RustVec>(level, slot)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(value =>
        requires well_formed(old(self)),
        ensures well_formed(final(self)),
            if let Some((rank, slot)) = value {
                rank == final(self).first_level as int + final(self).cursor
                    && did_pop(old(self), final(self), Some(slot))
            } else { did_pop(old(self), final(self), None) },
        no_unwind
    ))]
    pub(crate) fn pop_with<M: VecMemory>(&mut self) -> Option<(u16, T)> where T: Copy {
        #[cfg(verus_keep_ghost)]
        proof! {
            let witness = choose |w: super::Chains| #[trigger] represented(old(self), w);
            assert(physical(old(self)));
        }
        self.cursor = first_nonempty(self.heads.as_slice(), self.cursor);
        if self.cursor == self.heads.len() {
            self.clear_with::<M>();
            return None;
        }
        self.started = true;
        let rank = (self.first_level as usize + self.cursor) as u16;
        let slot = unlink(self.entries.as_mut_slice(), &mut self.free, &mut self.heads[self.cursor]);
        #[cfg(verus_keep_ghost)]
        proof! {
            let prior = choose |w: super::Chains| #[trigger] represented(old(self), w);
            pop_removes_lowest(old(self), self, Some(slot), prior);
        }
        Some((rank, slot))
    }

    #[cfg(not(verus_keep_ghost))]
    #[cfg(test)]
    pub(crate) fn pop(&mut self) -> Option<(u16, T)> where T: Copy {
        self.pop_with::<RustVec>()
    }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).heads.len()==0, final(self).entries.len()==0, final(self).free==0,
            final(self).cursor==0, !final(self).started, well_formed(final(self)),
        no_unwind
    ))]
    pub(crate) fn clear_with<M: VecMemory>(&mut self) where T: Copy {
        M::clear(&mut self.heads);
        M::clear(&mut self.entries);
        self.free = 0;
        self.cursor = 0;
        self.started = false;
        #[cfg(verus_keep_ghost)]
        proof! {
            empty_queue_is_represented(self);
            assert(represented(self, no_entries()));
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub(crate) fn clear(&mut self) where T: Copy {
        self.clear_with::<RustVec>();
    }
}
