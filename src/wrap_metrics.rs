//! A wrap child stores its line's Fill share and cross extent independently.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::prepare_frame::FrameFloat;
#[cfg(verus_keep_ghost)]
use crate::prepare_frame::FrameWords;

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Metric {
    Share,
    Cross,
}

impl Metric {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.word(), no_unwind))]
    pub fn word(self) -> usize {
        match self { Self::Share => 0, Self::Cross => 1 }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const INITIAL_WORDS: [u32; 2] = [0, 0];

/// A dependency can return to a consumer before the wrap producer finishes.
/// The provisional metric for that channel is zero.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns ready_metric(producer_solved, metric), no_unwind))]
pub fn ready_metric(producer_solved: bool, metric: Metric) -> Option<Metric> {
    if producer_solved { Some(metric) } else { None }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(word => ensures word == words[metric.word() as int], no_unwind))]
pub fn read_metric(words: &[u32; 2], metric: Metric) -> u32 {
    words[metric.word()]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(words)[metric.word() as int] == bits,
        final(words)[1 - metric.word() as int] == old(words)[1 - metric.word() as int],
    no_unwind
))]
pub fn store_metric(words: &mut [u32; 2], metric: Metric, bits: u32) {
    words[metric.word()] = bits;
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(flags =>
    ensures flags == old | mask, flags & mask == mask, flags & !mask == old & !mask,
    no_unwind
))]
pub fn mark_start(old: u32, mask: u32) -> u32 {
    let flags = old | mask;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(((old | mask) & mask) == mask && ((old | mask) & !mask) == (old & !mask)) by(bit_vector);
    }
    flags
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(marked => ensures marked == (flags & mask != 0), no_unwind))]
pub fn is_start(flags: u32, mask: u32) -> bool {
    flags & mask != 0
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(flags) == *old(flags) & !mask,
        final(words)[0] == 0, final(words)[1] == 0,
    no_unwind
))]
pub(crate) fn clear_parent_line(flags: &mut u32, mask: u32, words: &mut [u32; 2]) {
    *flags &= !mask;
    *words = INITIAL_WORDS;
}

#[cfg(verus_keep_ghost)]
verus! {
pub trait CacheModel {
    type Id: Copy + Eq;
    spec fn run(&self) -> Seq<(Self::Id, bool)>;
    spec fn stop(&self) -> Option<Self::Id>;
    spec fn cache(&self) -> Map<Self::Id, (u32, u32)>;
    #[verifier::prophetic]
    spec fn returned_cache(&self) -> Map<Self::Id, (u32, u32)>;
}
}

#[cfg(not(verus_keep_ghost))]
pub trait CacheModel {
    type Id: Copy + Eq;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait LineCache: CacheModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (next == stop), no_unwind))]
    fn same_cursor(&self, next: Option<Self::Id>, stop: Option<Self::Id>) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(step =>
        requires member(self.run(), self.stop(), id),
        ensures step == (cursor(self.run(),self.stop(),index(self.run(),self.stop(),id) + 1),
            self.run()[index(self.run(),self.stop(),id)].1),
        no_unwind
    ))]
    fn row(&self, id: Self::Id) -> (Option<Self::Id>, bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).cache().contains_key(id),
        ensures final(self).run() == old(self).run(), final(self).stop() == old(self).stop(),
            final(self).cache() == old(self).cache().insert(id, replace_word(old(self).cache()[id], metric, bits)),
            final(self).returned_cache() == old(self).returned_cache(),
        no_unwind
    ))]
    fn set_line_bits(&mut self, id: Self::Id, metric: Metric, bits: u32);
}

/// A line's ordered record borrow ends once its selected word is written.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait LineRecordAccess: LineCache {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures self.returned_cache() == self.cache(),
        no_unwind
    ))]
    fn finish(self);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires distinct(old(cache).run(),stop), old(cache).stop() == stop,
        next == cursor(old(cache).run(),stop,0),
        forall |i:int| 0 <= i < old(cache).run().len() ==>
            old(cache).cache().contains_key((#[trigger] old(cache).run()[i]).0),
    ensures final(cache).cache() == stamp(old(cache).run(),old(cache).run().len(),old(cache).cache(),metric,bits),
        final(cache).returned_cache() == old(cache).returned_cache(),
    no_unwind
))]
pub(crate) fn publish_metrics<S: LineCache + ?Sized>(
    cache: &mut S,
    mut next: Option<S::Id>,
    stop: Option<S::Id>,
    metric: Metric,
    bits: u32,
) {
    #[cfg(verus_keep_ghost)]
    let mut consumed = wrap_lines::start_scan();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            cache.run() == old(cache).run(), cache.stop() == stop, distinct(cache.run(),stop),
            cache.returned_cache() == old(cache).returned_cache(),
            consumed@ <= cache.run().len(),
            next == cursor(cache.run(),stop,consumed@ as int),
            cache.cache() == stamp(cache.run(),consumed@,old(cache).cache(),metric,bits),
            forall |i:int| 0 <= i < cache.run().len() ==>
                cache.cache().contains_key((#[trigger] cache.run()[i]).0)
                && old(cache).cache().contains_key(cache.run()[i].0),
        ensures next == stop,
        decreases cache.run().len() - consumed@,
    ))]
    while let (Some(id), false) = (next, cache.same_cursor(next, stop)) {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(consumed@ < cache.run().len());
            locate(cache.run(),stop,consumed@,id);
        }
        let (following, in_flow) = cache.row(id);
        if in_flow {
            cache.set_line_bits(id, metric, bits);
        }
        next = following;
        #[cfg(verus_keep_ghost)]
        { consumed = wrap_lines::advance(consumed); }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(next == stop);
        assert(cursor(cache.run(), stop, cache.run().len() as int) == stop);
        assert(consumed@ == cache.run().len());
    }
}

/// Convert the line extent once, then publish the exact binary32 word on
/// the planned sibling run in its own channel.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires distinct(old(cache).run(), stop), old(cache).stop() == stop,
        first == cursor(old(cache).run(), stop, 0),
        forall |i: int| 0 <= i < old(cache).run().len() ==>
            old(cache).cache().contains_key((#[trigger] old(cache).run()[i]).0),
    ensures final(cache).cache() == stamp(old(cache).run(), old(cache).run().len(),
        old(cache).cache(), metric, F::word(value)),
        final(cache).returned_cache() == old(cache).returned_cache(),
    no_unwind
))]
pub(crate) fn publish_line<S: LineCache + ?Sized, F: FrameFloat>(
    cache: &mut S, first: Option<S::Id>, stop: Option<S::Id>, metric: Metric, value: f32,
) {
    publish_metrics(cache, first, stop, metric, F::bits(value));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pending_wrap_metrics_hide_stale_nonfinite_bits() {
        let mut words = INITIAL_WORDS;
        let nan = 0x7fc0_1234;
        let infinity = f32::NEG_INFINITY.to_bits();
        store_metric(&mut words, Metric::Share, nan);
        store_metric(&mut words, Metric::Cross, infinity);

        for (metric, bits) in [(Metric::Share, nan), (Metric::Cross, infinity)] {
            let read = |producer_solved| {
                ready_metric(producer_solved, metric).map_or(0.0, |ready| {
                    f32::from_bits(read_metric(&words, ready))
                })
            };
            assert_eq!(read(false).to_bits(), 0.0_f32.to_bits());
            assert_eq!(read(true).to_bits(), bits);
        }
    }
}
