// Shared by the layout solver and its Verus grid proof.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use super::{bit, runs_of, extend_runs};

/// Bit counts are the scanner's only target primitives. The native instance
/// uses the total Rust integer intrinsics, which count all 64 zeros for zero.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) trait ZeroCounts {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out as int == vstd::std_specs::bits::u64_leading_zeros(word),
        no_unwind
    ))]
    fn leading(word: u64) -> u32;

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == vstd::std_specs::bits::u64_trailing_zeros(word),
        no_unwind
    ))]
    fn trailing(word: u64) -> u32;
}

#[cfg(not(verus_keep_ghost))]
pub(super) struct IntrinsicZeroCounts;

#[cfg(not(verus_keep_ghost))]
impl ZeroCounts for IntrinsicZeroCounts {
    #[inline(always)]
    fn leading(word: u64) -> u32 { word.leading_zeros() }

    #[inline(always)]
    fn trailing(word: u64) -> u32 { word.trailing_zeros() }
}

/// Bit i of the result marks a run of `span` open cells starting at i.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= span <= 64,
    ensures runs_of(result, open, span as int),
    no_unwind
))]
pub fn open_grid_starts(open: u64, span: u32) -> u64 {
    let mut runs = open;
    let mut length = 1u32;
    #[cfg(verus_keep_ghost)]
    proof! { assert(runs_of(open, open, 1)); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= length <= span <= 64, runs_of(runs, open, length as int),
        decreases 64 - length,
    ))]
    while length * 2 <= span {
        #[cfg(verus_keep_ghost)]
        proof! { extend_runs(open, runs, length, length); }
        runs &= runs >> length;
        length *= 2;
    }
    #[cfg(verus_keep_ghost)]
    proof! { extend_runs(open, runs, length, (span - length) as u32); }
    runs & (runs >> (span - length))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires start < 64, end < 64,
    ensures forall |i: u32| i < 64 ==> #[trigger] bit(result, i as int) == (start <= i <= end),
    no_unwind
))]
pub fn word_range(start: u32, end: u32) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |i:u32| i<64 implies
            #[trigger] bit((u64::MAX << start) & (u64::MAX >> (63 - end) as u32), i as int)
                == (start <= i <= end) by {
            assert(((((u64::MAX << start) & (u64::MAX >> 63u32.wrapping_sub(end))) >> i) & 1) != 0
                == (start <= i && i <= end)) by(bit_vector) requires i < 64, start < 64, end < 64;
        }
    }
    (u64::MAX << start) & (u64::MAX >> (63 - end))
}

/// First free position after the highest colliding bit, or 64 at the word end.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires collisions != 0, collisions & occupied == collisions,
    ensures
        super::collision_run(occupied, collisions, next),
    no_unwind
))]
pub fn after_collision<C: ZeroCounts>(occupied: u64, collisions: u64) -> u32 {
    let last = 63 - C::leading(collisions);
    let free = !occupied & (u64::MAX << last);
    let next = C::trailing(free);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bit(collisions,last as int));
        assert(bit(occupied,last as int)) by {
            assert((collisions & occupied) == collisions && ((collisions >> last) & 1) != 0
                ==> ((occupied >> last) & 1) != 0) by(bit_vector);
        }
        assert forall |j:u32| j < 64 implies #[trigger] bit(free,j as int)
            == (!bit(occupied,j as int) && j >= last) by {
            assert(((((!occupied & (u64::MAX << last)) >> j) & 1) != 0)
                == (((occupied >> j) & 1 == 0) && j >= last)) by(bit_vector)
                    requires last < 64, j < 64;
        }
        if next <= last {
            assert(bit(free,next as int));
        }
        assert forall |j:u32| last <= j < next implies #[trigger] bit(occupied,j as int) by {
            assert(j < 64);
            assert(!bit(free,j as int));
            assert(!bit(occupied,j as int) ==> bit(free,j as int));
        }
    }
    next
}

/// Compute the first open start in a row after combining its spanned occupancy words.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires pos < 64, 1 <= span <= 64,
    ensures pos <= next <= 64,
        next < 64 ==> super::open_range(!blocked, next as int, span as int),
        forall |i:int| pos <= i < next ==> !#[trigger] super::open_range(!blocked, i, span as int),
    no_unwind
))]
pub fn first_word_start<C: ZeroCounts>(blocked: u64, pos: u32, span: u32) -> u32 {
    let runs = open_grid_starts(!blocked, span);
    let starts = runs & (u64::MAX << pos);
    let next = C::trailing(starts);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |j:u32| j < 64 implies #[trigger] bit(starts,j as int)
            == (j >= pos && bit(runs,j as int)) by {
            assert(((((runs & (u64::MAX << pos)) >> j) & 1) != 0)
                == (j >= pos && (((runs >> j) & 1) != 0))) by(bit_vector)
                    requires pos < 64, j < 64;
        }
        if next < 64 { assert(bit(starts, next as int)); }
        assert forall |i:int| pos <= i < next implies
            !#[trigger] super::open_range(!blocked, i, span as int) by {
            let j = i as u32;
            assert(!bit(starts, j as int));
            assert(!bit(runs, j as int));
        }
    }
    next
}

/// Find the first start in two rows with the same span. Interleaving the
/// independent word operations gives the compiler two lanes to vectorize.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires 1 <= span <= 64,
    ensures super::first_word_run(open.0, next.0, span),
        super::first_word_run(open.1, next.1, span),
    no_unwind
))]
pub fn first_pair_starts<C: ZeroCounts>(open: (u64, u64), span: u32) -> (u32, u32) {
    let (mut left, mut right) = open;
    let mut length = 1u32;
    #[cfg(verus_keep_ghost)]
    proof! { assert(runs_of(left, open.0, 1)); assert(runs_of(right, open.1, 1)); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1 <= length <= span <= 64,
            runs_of(left, open.0, length as int), runs_of(right, open.1, length as int),
        decreases 64 - length,
    ))]
    while length * 2 <= span {
        #[cfg(verus_keep_ghost)]
        proof! { extend_runs(open.0, left, length, length); extend_runs(open.1, right, length, length); }
        left &= left >> length;
        right &= right >> length;
        length *= 2;
    }
    let remainder = span - length;
    #[cfg(verus_keep_ghost)]
    proof! { extend_runs(open.0, left, length, remainder); extend_runs(open.1, right, length, remainder); }
    left &= left >> remainder;
    right &= right >> remainder;
    let next = (C::trailing(left), C::trailing(right));
    #[cfg(verus_keep_ghost)]
    proof! {
        if next.0 < 64 { assert(bit(left, next.0 as int)); }
        if next.1 < 64 { assert(bit(right, next.1 as int)); }
        assert forall |i:int| 0 <= i < next.0 implies !#[trigger] super::open_range(open.0, i, span as int) by {
            let j = i as u32;
            assert(!bit(left, j as int));
        }
        assert forall |i:int| 0 <= i < next.1 implies !#[trigger] super::open_range(open.1, i, span as int) by {
            let j = i as u32;
            assert(!bit(right, j as int));
        }
    }
    next
}

/// Combine a row with the cells occupied by a span (or by another spanned row).
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures forall |j:u32| j < 64 ==> #[trigger] bit(result,j as int)
        == (bit(word,j as int) || bit(mask,j as int)),
    no_unwind
))]
pub fn union(word: u64, mask: u64) -> u64 {
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |j:u32| j < 64 implies #[trigger] bit(word | mask,j as int)
            == (bit(word,j as int) || bit(mask,j as int)) by {
            assert(((((word | mask) >> j) & 1) != 0)
                == ((((word >> j) & 1) != 0) || (((mask >> j) & 1) != 0))) by(bit_vector);
        }
    }
    word | mask
}

/// Find a colliding word in this spanned row and the first column in that
/// word after its occupied run. Check later words first to skip more starts.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires first <= last < row.len(),
    ensures match result {
        None => forall |i:int| first <= i <= last ==> #[trigger] super::overlap(
            row@[i], i, first as int, last as int, start_mask, end_mask) == 0,
        Some((word, next)) => first <= word <= last && super::collision_run(row@[word as int],
            super::overlap(row@[word as int], word as int, first as int, last as int, start_mask, end_mask), next),
    },
    no_unwind
))]
pub fn probe_row<C: ZeroCounts>(row: &[u64], first: usize, last: usize, start_mask: u64, end_mask: u64) -> Option<(usize, u32)> {
    let first_bits = if first == last {
        row[first] & start_mask & end_mask
    } else {
        let end_bits = row[last] & end_mask;
        if end_bits != 0 {
            #[cfg(verus_keep_ghost)]
            proof! { let v=row[last as int]; assert(((v & end_mask) & v) == (v & end_mask)) by(bit_vector); }
            return Some((last, after_collision::<C>(row[last], end_bits)));
        }
        let mut word = last;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant first < word <= last < row.len(),
                forall |i:int| word <= i <= last ==> #[trigger] super::overlap(
                    row@[i],i,first as int,last as int,start_mask,end_mask) == 0,
            decreases word - first,
        ))]
        while word - first > 1 {
            word -= 1;
            let bits = row[word];
            if bits != 0 {
                #[cfg(verus_keep_ghost)]
                proof! { assert((bits & bits) == bits) by(bit_vector); }
                return Some((word, after_collision::<C>(bits, bits)));
            }
        }
        row[first] & start_mask
    };
    if first_bits != 0 {
        #[cfg(verus_keep_ghost)]
        proof! {
            let occupied = row[first as int];
            assert((occupied & start_mask & end_mask) & occupied == (occupied & start_mask & end_mask)) by(bit_vector);
            assert((occupied & start_mask) & occupied == (occupied & start_mask)) by(bit_vector);
        }
        Some((first, after_collision::<C>(row[first], first_bits)))
    } else {
        None
    }
}

/// Mark all cells of the span on one packed row.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires first <= last < old(row).len(),
    ensures final(row)@.len() == old(row)@.len(),
        forall |i:int| 0 <= i < final(row)@.len() ==> #[trigger] final(row)@[i] ==
            (old(row)@[i] | super::mark_mask(i,first as int,last as int,start_mask,end_mask)),
    no_unwind
))]
pub fn occupy_row(row: &mut [u64], first: usize, last: usize, start_mask: u64, end_mask: u64) {
    #[cfg(verus_keep_ghost)]
    proof! { super::or_identities(); }
    if first == last {
        row[first] |= start_mask & end_mask;
    } else {
        row[first] |= start_mask;
        let mut i = first + 1;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant first < i <= last < row.len(), row@.len() == old(row)@.len(),
                forall |v:u64| (#[trigger] (v | 0u64)) == v,
                forall |v:u64| (#[trigger] (v | u64::MAX)) == u64::MAX,
                forall |j:int| 0 <= j < row.len() ==> #[trigger] row@[j] ==
                    (if j < i { old(row)@[j] | super::mark_mask(j,first as int,last as int,start_mask,end_mask) }
                        else { old(row)@[j] }),
            decreases last-i,
        ))]
        while i < last {
            row[i] = u64::MAX;
            i += 1;
        }
        row[last] |= end_mask;
    }
}
