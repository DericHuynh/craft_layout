//! Arithmetic at text word boundaries after the native classifier supplies a mask.
#![allow(unexpected_cfgs)]

use super::LineWidths;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn lane_is_set(mask: u32, lane: u32) -> bool {
        (mask >> lane) & 1u32 != 0
    }

    pub(crate) open spec fn lanes_inside(mask: u32, first: usize, end: usize) -> bool {
        forall |lane: u32| lane < 32 && #[trigger] lane_is_set(mask, lane)
            ==> first <= lane < end
    }
}

/// Integer bit counts supplied by Rust. The verifier models the three
/// primitive results where the native implementation uses std's operations.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait BitLanes {
    #[cfg_attr(verus_keep_ghost, verus_spec(lane =>
        requires mask != 0,
        ensures lane < 32, lane_is_set(mask, lane),
            mask & (1u32 << lane).wrapping_sub(1) == 0,
        no_unwind
    ))]
    fn first(mask: u32) -> u32;

    #[cfg_attr(verus_keep_ghost, verus_spec(lane =>
        requires mask != 0,
        ensures lane < 32, lane_is_set(mask, lane),
            forall |i: u32| lane < i < 32 ==> !#[trigger] lane_is_set(mask, i),
        no_unwind
    ))]
    fn last(mask: u32) -> u32;

    #[cfg_attr(verus_keep_ghost, verus_spec(count =>
        ensures count <= 32, (count == 0) == (mask == 0),
        no_unwind
    ))]
    fn count(mask: u32) -> u32;
}

#[cfg(all(target_arch = "x86_64", not(verus_keep_ghost)))]
pub(crate) struct NativeBitLanes;

#[cfg(all(target_arch = "x86_64", not(verus_keep_ghost)))]
impl BitLanes for NativeBitLanes {
    #[inline(always)]
    fn first(mask: u32) -> u32 { mask.trailing_zeros() }

    #[inline(always)]
    fn last(mask: u32) -> u32 { 31 ^ mask.leading_zeros() }

    #[inline(always)]
    fn count(mask: u32) -> u32 { mask.count_ones() }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait WordWidths {
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn width(&mut self, width: usize);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl WordWidths for LineWidths {
    #[inline(always)]
    fn width(&mut self, width: usize) {
        self.add_word(width);
    }
}

/// Remove the first marked lane, retaining only lanes strictly after it.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(lane =>
    requires *old(mask) != 0,
    ensures lane < 32, lane_is_set(*old(mask), lane), *final(mask) < *old(mask),
        forall |i: u32| i < 32 && #[trigger] lane_is_set(*final(mask), i)
            ==> lane < i && lane_is_set(*old(mask), i),
    no_unwind
))]
pub(crate) fn pop_lane<B: BitLanes>(mask: &mut u32) -> u32 {
    let before = *mask;
    let lane = B::first(before);
    let after = before & (before - 1);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(after < before) by(bit_vector) requires before != 0, after == before & before.wrapping_sub(1);
        assert forall |i: u32| i < 32 && #[trigger] lane_is_set(after, i)
            implies lane < i && lane_is_set(before, i) by {
            assert((after >> i) & 1 != 0 ==> lane < i && (before >> i) & 1 != 0) by(bit_vector)
                requires lane < 32, i < 32, after == before & before.wrapping_sub(1),
                    (before >> lane) & 1 != 0,
                    before & (1u32 << lane).wrapping_sub(1) == 0;
        }
    }
    *mask = after;
    lane
}

/// Pop a lane from the SSE mask without losing the position bound.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(lane =>
    requires *old(mask) != 0,
    ensures lane < 16, *final(mask) < *old(mask),
        lane_is_set(*old(mask) as u32, lane),
    no_unwind
))]
pub(crate) fn pop_lane16<B: BitLanes>(mask: &mut u16) -> u32 {
    let mut wide = *mask as u32;
    #[cfg(verus_keep_ghost)]
    let before = wide;
    let lane = pop_lane::<B>(&mut wide);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(lane < 16) by(bit_vector) requires before <= 65535u32, lane < 32, (before >> lane) & 1 != 0;
    }
    *mask = wide as u16;
    lane
}

/// Count the marked lanes strictly before a boundary in an SSE window.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(count =>
    requires lane < 16,
    ensures count <= 32,
    no_unwind
))]
pub(crate) fn prefix_count16<B: BitLanes>(mask: u16, lane: u32) -> usize {
    let boundary = 1u32 << lane;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(boundary != 0) by(bit_vector) requires lane < 16, boundary == 1u32 << lane;
    }
    B::count(mask as u32 & (boundary - 1)) as usize
}

/// Move the new bytes of an overlapping SSE load into its low lanes.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires 1 <= count <= 16,
    ensures out == mask >> ((16 - count) as usize),
    no_unwind
))]
pub(crate) fn tail_mask16(mask: u16, count: usize) -> u16 {
    mask >> (16 - count)
}

/// Move the new bytes of an overlapping AVX2 load into its low lanes.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires 1 <= count <= 32,
    ensures out == mask >> ((32 - count) as usize), lanes_inside(out, 0, count),
    no_unwind
))]
pub(crate) fn tail_mask32(mask: u32, count: usize) -> u32 {
    let out = mask >> (32 - count);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |i: u32| i < 32 && #[trigger] lane_is_set(out, i)
            implies i < count by {
            assert((out >> i) & 1 != 0 ==> i < count) by(bit_vector)
                requires i < 32, 1 <= count <= 32, out == mask >> ((32 - count) as usize);
        }
    }
    out
}

/// Keep only active tail lanes without shifting their byte offsets.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires 1 <= count <= 32,
    ensures out == u32::MAX << ((32 - count) as usize),
    no_unwind
))]
pub(crate) fn active_tail32(count: usize) -> u32 {
    u32::MAX << (32 - count)
}

/// A verbatim line has no leading or adjacent spaces. Carry the latest lane
/// into the next window so adjacency is tested there as well.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires 1 <= count <= 32,
    ensures out == if spaces & ((spaces << 1) | previous) != 0 {
        None
    } else {
        Some(spaces >> ((count - 1) as usize))
    },
    no_unwind
))]
pub(crate) fn single_space_end(spaces: u32, previous: u32, count: usize) -> Option<u32> {
    if spaces & ((spaces << 1) | previous) != 0 {
        return None;
    }
    Some(spaces >> (count - 1))
}

/// Emit the text run that has no closing boundary in its final window.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn finish_word<W: WordWidths>(words: &mut W, previous_space: u32, start: usize, end: usize) {
    if previous_space == 0 {
        if let Some(width) = end.checked_sub(start) {
            words.width(width);
        }
    }
}

/// Emit widths in lane order. An initial closing boundary belongs to a word
/// whose opening can be in an earlier vector.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires base + count <= usize::MAX, *old(start) <= base, lanes_inside(boundaries, 0, count),
    ensures *final(start) <= base + count,
    no_unwind
))]
pub(crate) fn emit_boundary_words<B: BitLanes, W: WordWidths>(
    mut boundaries: u32, in_word: bool, base: usize, count: usize, start: &mut usize, words: &mut W,
) {
    let _ = count;
    #[cfg(verus_keep_ghost)]
    let mut floor = 0usize;
    if boundaries != 0 && in_word {
        #[cfg(verus_keep_ghost)]
        let before = boundaries;
        let lane = pop_lane::<B>(&mut boundaries);
        #[cfg(verus_keep_ghost)]
        proof! { assert(lane_is_set(before, lane)); }
        #[cfg(verus_keep_ghost)]
        { floor = lane as usize + 1; }
        words.width(base + lane as usize - *start);
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant floor <= count, *start <= base + floor, base + count <= usize::MAX,
            lanes_inside(boundaries, floor, count),
        decreases boundaries,
    ))]
    while boundaries != 0 {
        #[cfg(verus_keep_ghost)]
        let before = boundaries;
        let lane = pop_lane::<B>(&mut boundaries);
        #[cfg(verus_keep_ghost)]
        proof! { assert(lane_is_set(before, lane)); }
        *start = base + lane as usize;
        #[cfg(verus_keep_ghost)]
        { floor = lane as usize + 1; }
        if boundaries != 0 {
            #[cfg(verus_keep_ghost)]
            let before = boundaries;
            let closing = pop_lane::<B>(&mut boundaries);
            #[cfg(verus_keep_ghost)]
            proof! { assert(lane_is_set(before, closing)); }
            #[cfg(verus_keep_ghost)]
            { floor = closing as usize + 1; }
            words.width(base + closing as usize - *start);
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct WrappedWords {
    pub(crate) previous_space: u32,
    pub(crate) word_start: usize,
    pub(crate) lines: LineWidths,
}

impl WrappedWords {
    /// Append a block of logical characters. Only active lanes participate,
    /// and an empty block leaves the partly read word untouched.
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires count <= 32, base + count <= usize::MAX,
            old(self).previous_space <= 1, old(self).word_start <= base,
            lanes_inside(spaces, 0, count),
        ensures final(self).previous_space <= 1, final(self).word_start <= base + count,
        no_unwind
    ))]
    pub(crate) fn block<B: BitLanes>(&mut self, spaces: u32, count: usize, base: usize) {
        if count == 0 { return; }
        let previous = (spaces << 1) | self.previous_space;
        let ends = spaces & !previous;
        let last_is_space = (spaces >> (count - 1)) & 1;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(last_is_space <= 1) by(bit_vector)
                requires last_is_space == (spaces >> ((count - 1) as usize)) & 1;
            assert forall |i: u32| i < 32 && #[trigger] lane_is_set(ends, i)
                implies lane_is_set(spaces, i) by {
                assert((ends >> i) & 1 != 0 ==> (spaces >> i) & 1 != 0) by(bit_vector)
                    requires ends == spaces & !previous, i < 32;
            }
        }
        // A prefix that fits as a whole can be appended without visiting each
        // completed word. One separator is charged per completed word.
        if ends != 0 {
            #[cfg(verus_keep_ghost)]
            proof! { assert(spaces != 0) by(bit_vector) requires ends == spaces & !previous, ends != 0; }
            let last_end = B::last(ends);
            let one_past = 1u32 << last_end;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(one_past != 0) by(bit_vector) requires last_end < 32, one_past == 1u32 << last_end;
            }
            let letters = (one_past - 1) & !spaces;
            let carry = if self.previous_space == 0 { base - self.word_start } else { 0 };
            if self.lines.append_batch(B::count(letters), carry, B::count(ends)) {
                self.previous_space = last_is_space;
                let last_space = B::last(spaces);
                #[cfg(verus_keep_ghost)]
                proof! { assert(lane_is_set(spaces, last_space)); }
                self.word_start = base + (last_space as usize + 1);
                return;
            }
        }

        let valid = u32::MAX >> (32 - count);
        let boundaries = (spaces ^ previous) & valid;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |i: u32| i < 32 && #[trigger] lane_is_set(boundaries, i)
                implies i < count by {
                assert((boundaries >> i) & 1 != 0 ==> (i as usize) < count) by(bit_vector)
                    requires i < 32, 1 <= count <= 32,
                        boundaries == (spaces ^ previous) & valid,
                        valid == u32::MAX >> ((32 - count) as usize);
            }
        }
        emit_boundary_words::<B, _>(boundaries, self.previous_space == 0, base, count, &mut self.word_start, &mut self.lines);
        self.previous_space = last_is_space;
    }
}
