//! Memoize exact wrapped text heights for an owned tree's live identities.
#![allow(unexpected_cfgs)]

use crate::vec_memory::{FallibleVecMemory, VecMemory, try_append};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
const BUCKETS: usize = 256;

#[derive(Clone, Copy, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Height {
    width: u32,
    bits: u32,
}

#[derive(Clone, Copy, Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Bucket {
    owner: u64,
    epoch: u32,
    first: Option<Height>,
    second: Option<Height>,
    third: Option<Height>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
const EMPTY: Bucket = Bucket { owner: 0, epoch: 0, first: None, second: None, third: None };

#[derive(Debug)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Cache {
    epoch: u32,
    rows: Vec<Bucket>,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) type Expected = spec_fn(u64, u32) -> u32;

pub(crate) trait HeightModel {
    spec fn expected(&self) -> Expected;
}

fn measurement_input<H: HeightModel>(callback: &H) -> (expected: Ghost<Expected>)
    ensures expected@ == callback.expected(),
    no_unwind
{ Ghost(callback.expected()) }

spec fn matching_width(entry: Option<Height>, width: u32) -> Option<u32> {
    if entry.is_some() && entry.unwrap().width == width { Some(entry.unwrap().bits) } else { None }
}

spec fn expected_height(owner: u64, height: Option<Height>, expected: Expected) -> bool {
    height.is_some() ==> height.unwrap().bits == expected(owner, height.unwrap().width)
}

spec fn safe_row(bucket: Bucket, expected: Expected) -> bool {
    expected_height(bucket.owner, bucket.first, expected)
    && expected_height(bucket.owner, bucket.second, expected)
    && expected_height(bucket.owner, bucket.third, expected)
}

impl Cache {
    pub(crate) closed spec fn cached_height(&self, owner: u64, width: u32) -> Option<u32> {
        let at = owner as int % BUCKETS as int;
        if at >= self.rows.len() {
            None
        } else {
            let row = self.rows@[at];
            if row.owner != owner || row.epoch != self.epoch {
                None
            } else if matching_width(row.first, width).is_some() {
                matching_width(row.first, width)
            } else if matching_width(row.second, width).is_some() {
                matching_width(row.second, width)
            } else {
                matching_width(row.third, width)
            }
        }
    }

    pub(crate) closed spec fn storage_valid(&self) -> bool {
        &&& self.rows.len() <= BUCKETS
        &&& forall |i: int| 0 <= i < self.rows.len() ==> (#[trigger] self.rows@[i]).epoch <= self.epoch
    }

    pub(crate) closed spec fn valid(&self, expected: Expected) -> bool {
        &&& self.storage_valid()
        &&& forall |i: int| 0 <= i < self.rows.len() ==> {
            let row = #[trigger] self.rows@[i];
            row.epoch != self.epoch || row.owner as int % BUCKETS as int == i && safe_row(row, expected)
            || row.first.is_none() && row.second.is_none() && row.third.is_none()
        }
    }
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait HeightModel {}
#[cfg(not(verus_keep_ghost))]
impl<T> HeightModel for T {}

/// The owner's callback gives the same height for the live incarnation and width.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait MeasureHeight: HeightModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(bits =>
        ensures final(self).expected() == old(self).expected(),
            bits == old(self).expected()(owner, width),
        no_unwind
    ))]
    fn measure_height(&mut self, owner: u64, width: u32) -> u32;
}

#[cfg(not(verus_keep_ghost))]
impl<F: FnMut(u64, u32) -> u32> MeasureHeight for F {
    #[inline(always)]
    fn measure_height(&mut self, owner: u64, width: u32) -> u32 { self(owner, width) }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result < BUCKETS, result == owner as int % BUCKETS as int,
    no_unwind
))]
fn index(owner: u64) -> usize { (owner % BUCKETS as u64) as usize }

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(answer =>
    ensures answer == matching_width(slot, width),
    no_unwind
))]
fn check(slot: Option<Height>, width: u32) -> Option<u32> {
    match slot { Some(height) if height.width == width => Some(height.bits), _ => None }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Cache {
    #[cfg_attr(verus_keep_ghost, verus_spec(cache =>
        ensures forall |expected: Expected| cache.valid(expected),
        no_unwind
    ))]
    pub(crate) fn new<M: VecMemory>() -> Self {
        Self { epoch: 0, rows: M::empty() }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(answer =>
        requires self.valid(expected@),
        ensures answer == self.cached_height(owner, width),
            answer.is_some() ==> answer.unwrap() == expected@(owner, width),
        no_unwind
    ))]
    pub(crate) fn height(
        &self, owner: u64, width: u32,
        #[cfg(verus_keep_ghost)] expected: Ghost<Expected>,
    ) -> Option<u32> {
        let at = index(owner);
        if at >= self.rows.len() { return None; }
        let row = &self.rows[at];
        if row.owner != owner || row.epoch != self.epoch { return None; }
        if let Some(bits) = check(row.first, width) { return Some(bits); }
        if let Some(bits) = check(row.second, width) { return Some(bits); }
        check(row.third, width)
    }

    /// Use either the exact saved word or a fresh reading of the same input.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(bits =>
        requires old(self).valid(old(callback).expected()),
        ensures final(self).valid(final(callback).expected()),
            final(callback).expected() == old(callback).expected(),
            bits == old(callback).expected()(owner, width),
            old(self).cached_height(owner, width).is_some() ==>
                *final(self) == *old(self) && *final(callback) == *old(callback),
        no_unwind
    ))]
    pub(crate) fn query<M: FallibleVecMemory, H: MeasureHeight>(
        &mut self, owner: u64, width: u32, callback: &mut H,
    ) -> u32 {
        #[cfg(verus_keep_ghost)]
        let expected = measurement_input(callback);
        if let Some(bits) = self.height(owner, width, #[cfg(verus_keep_ghost)] expected) {
            return bits;
        }
        let bits = callback.measure_height(owner, width);
        self.remember::<M>(owner, width, bits, #[cfg(verus_keep_ghost)] expected);
        bits
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).valid(expected@), bits == expected@(owner, width),
        ensures final(self).valid(expected@),
        no_unwind
    ))]
    pub(crate) fn remember<M: FallibleVecMemory>(
        &mut self, owner: u64, width: u32, bits: u32,
        #[cfg(verus_keep_ghost)] expected: Ghost<Expected>,
    ) {
        let at = index(owner);
        if at >= self.rows.len() {
            let additional = BUCKETS - self.rows.len();
            if !M::try_reserve(&mut self.rows, additional) { return; }
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant self.valid(expected@),
                decreases BUCKETS - self.rows.len(),
            ))]
            while self.rows.len() < BUCKETS {
                if !try_append::<_, M>(&mut self.rows, EMPTY) { return; }
            }
        }
        let mut row = self.rows[at];
        if row.owner != owner || row.epoch != self.epoch {
            row = EMPTY;
            row.owner = owner;
            row.epoch = self.epoch;
        }
        row.third = row.second;
        row.second = row.first;
        row.first = Some(Height { width, bits });
        self.rows[at] = row;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).valid(before@),
            forall |id: u64, width: u32| id != owner ==> (#[trigger] before@(id, width)) == after@(id, width),
        ensures final(self).valid(after@),
        no_unwind
    ))]
    pub(crate) fn invalidate_node(
        &mut self, owner: u64,
        #[cfg(verus_keep_ghost)] before: Ghost<Expected>,
        #[cfg(verus_keep_ghost)] after: Ghost<Expected>,
    ) {
        let at = index(owner);
        if at < self.rows.len() && self.rows[at].owner == owner && self.rows[at].epoch == self.epoch {
            self.rows[at] = EMPTY;
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).storage_valid(),
        ensures forall |expected: Expected| final(self).valid(expected),
        no_unwind
    ))]
    pub(crate) fn clear<M: VecMemory>(&mut self) {
        if self.epoch == u32::MAX {
            M::clear(&mut self.rows);
            self.epoch = 0;
        } else {
            self.epoch += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vec_memory::RustVec;

    #[test]
    fn invalidation_does_not_revive_old_entries_when_the_epoch_wraps() {
        let mut cache = Cache::new::<RustVec>();
        cache.remember::<RustVec>(7, 17, 23);
        cache.epoch = u32::MAX;
        cache.remember::<RustVec>(8, 19, 29);
        assert_eq!(cache.height(8, 19), Some(29));
        cache.clear::<RustVec>();
        assert_eq!(cache.height(7, 17), None);
        assert_eq!(cache.height(8, 19), None);
        cache.remember::<RustVec>(7, 17, 31);
        assert_eq!(cache.height(7, 17), Some(31));
    }
}
