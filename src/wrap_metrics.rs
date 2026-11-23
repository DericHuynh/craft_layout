//! A wrap child stores its line's Fill share and cross extent independently.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Metric {
    Share,
    Cross,
}

impl Metric {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.word()))]
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
#[cfg_attr(verus_keep_ghost, verus_spec(returns ready_metric(producer_solved, metric)))]
pub fn ready_metric(producer_solved: bool, metric: Metric) -> Option<Metric> {
    if producer_solved { Some(metric) } else { None }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(word => ensures word == words[metric.word() as int]))]
pub fn read_metric(words: &[u32; 2], metric: Metric) -> u32 {
    words[metric.word()]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(words)[metric.word() as int] == bits,
        final(words)[1 - metric.word() as int] == old(words)[1 - metric.word() as int],
))]
pub fn store_metric(words: &mut [u32; 2], metric: Metric, bits: u32) {
    words[metric.word()] = bits;
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(flags =>
    requires mask != 0,
    ensures flags & mask != 0, flags & !mask == old & !mask,
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
#[cfg_attr(verus_keep_ghost, verus_spec(marked => ensures marked == (flags & mask != 0)))]
pub fn is_start(flags: u32, mask: u32) -> bool {
    flags & mask != 0
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(flags) == *old(flags) & !mask,
        final(words)[0] == 0, final(words)[1] == 0,
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
}
}

#[cfg(not(verus_keep_ghost))]
pub trait CacheModel {
    type Id: Copy + Eq;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait LineCache: CacheModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (next == stop)))]
    fn same_cursor(&self, next: Option<Self::Id>, stop: Option<Self::Id>) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(step =>
        requires member(self.run(), self.stop(), id),
        ensures step == (cursor(self.run(),self.stop(),index(self.run(),self.stop(),id) + 1),
            self.run()[index(self.run(),self.stop(),id)].1),
    ))]
    fn row(&self, id: Self::Id) -> (Option<Self::Id>, bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).cache().contains_key(id),
        ensures final(self).run() == old(self).run(), final(self).stop() == old(self).stop(),
            final(self).cache() == old(self).cache().insert(id, replace_word(old(self).cache()[id], metric, bits)),
    ))]
    fn set_line_bits(&mut self, id: Self::Id, metric: Metric, bits: u32);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires distinct(old(cache).run(),stop), old(cache).stop() == stop,
        next == cursor(old(cache).run(),stop,0),
        forall |i:int| 0 <= i < old(cache).run().len() ==>
            old(cache).cache().contains_key((#[trigger] old(cache).run()[i]).0),
    ensures final(cache).cache() == stamp(old(cache).run(),old(cache).run().len(),old(cache).cache(),metric,bits),
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
            consumed@ <= cache.run().len(),
            next == cursor(cache.run(),stop,consumed@ as int),
            cache.cache() == stamp(cache.run(),consumed@,old(cache).cache(),metric,bits),
            forall |i:int| 0 <= i < cache.run().len() ==>
                cache.cache().contains_key((#[trigger] cache.run()[i]).0)
                && old(cache).cache().contains_key(cache.run()[i].0),
        decreases cache.run().len() - consumed@,
    ))]
    while !cache.same_cursor(next, stop) {
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(consumed@ < cache.run().len());
            assert(next == Some(cache.run()[consumed@ as int].0));
        }
        let id = next.unwrap();
        #[cfg(verus_keep_ghost)]
        proof! { locate(cache.run(),stop,consumed@,id); }
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
