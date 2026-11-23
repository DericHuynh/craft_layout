//! Tail partition for 32 input bytes followed by two UTF-8 lookahead bytes.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const LANES: usize = 32;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const WINDOW: usize = 34;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const MIN_PADDED: usize = 12;

/// An SSE2 window has no overlap before the tail. A partial tail loads the
/// last full window and uses only the lanes after the current cursor.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(window =>
    ensures match window {
        None => cursor >= len || len < 16,
        Some((start,count)) => cursor < len && len >= 16
            && 1 <= count <= 16 && start + 16 <= len
            && start + (16 - count) == cursor
            && count == vstd::math::min(16, len - cursor),
    },
    no_unwind
))]
pub(crate) fn window16(len: usize, cursor: usize) -> Option<(usize, usize)> {
    if cursor >= len { return None; }
    let remaining = len - cursor;
    if remaining >= 16 {
        Some((cursor, 16))
    } else if len >= 16 {
        Some((len - 16, remaining))
    } else {
        None
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(mask =>
    requires 1 <= count <= 16,
    ensures mask == u16::MAX >> ((16 - count) as usize),
    no_unwind
))]
pub(crate) fn low_lanes16(count: usize) -> u16 {
    u16::MAX >> (16 - count)
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn two_byte_space(first: u8, second: u8) -> bool {
        first == 0xc2 && (second == 0x85 || second == 0xa0)
    }

    pub open spec fn three_byte_space(first: u8, second: u8, third: u8) -> bool {
        (first == 0xe1 && second == 0x9a && third == 0x80)
        || (first == 0xe2 && second == 0x80
            && (0x80 <= third <= 0x8a || third == 0xa8 || third == 0xa9 || third == 0xaf))
        || (first == 0xe2 && second == 0x81 && third == 0x9f)
        || (first == 0xe3 && second == 0x80 && third == 0x80)
    }
}

/// Recognize a non-ASCII separator at a candidate leading byte. The input may
/// end anywhere, including partway through a UTF-8 sequence.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(width =>
    ensures width == (
        if at + 2 <= bytes.len() && two_byte_space(bytes@[at as int],bytes@[at + 1]) { 2u32 }
        else if at + 3 <= bytes.len() && three_byte_space(bytes@[at as int],bytes@[at + 1],bytes@[at + 2]) { 3u32 }
        else { 0u32 }
    ), width > 0 ==> at + width <= bytes.len(), width <= 3,
    no_unwind
))]
#[allow(clippy::manual_range_contains)]
pub(crate) fn unicode_separator_width(bytes: &[u8], at: usize) -> u32 {
    if at >= bytes.len() || bytes.len() - at < 2 { return 0; }
    let rest = bytes.split_at(at).1;
    let first = rest[0];
    let second = rest[1];
    if first == 0xc2 {
        if second == 0x85 || second == 0xa0 { 2 } else { 0 }
    } else if rest.len() < 3 {
        0
    } else {
        let third = rest[2];
        if (first == 0xe1 && second == 0x9a && third == 0x80)
            || (first == 0xe2 && second == 0x80
                && ((0x80 <= third && third <= 0x8a) || third == 0xa8 || third == 0xa9 || third == 0xaf))
            || (first == 0xe2 && second == 0x81 && third == 0x9f)
            || (first == 0xe3 && second == 0x80 && third == 0x80)
        {
            3
        } else {
            0
        }
    }
}

/// The full windows advance by 32 bytes and must have two following bytes.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(tail => ensures
    tail.0 == (if bytes.len() < 2 { 0int } else { bytes.len() - 2 }) / LANES as int * LANES as int,
    tail.0 <= bytes.len(), bytes.len() - tail.0 < WINDOW,
    tail.1@ == bytes@.subrange(tail.0 as int, bytes.len() as int),
    no_unwind
))]
pub(crate) fn mixed_tail(bytes: &[u8]) -> (usize, &[u8]) {
    let available = bytes.len().saturating_sub(2);
    let start = (available / LANES) * LANES;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(available == (available / LANES) * LANES + available % LANES);
    }
    (start, bytes.split_at(start).1)
}

/// Keep two lookahead bytes where present, without assigning them active lanes.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires MIN_PADDED <= bytes.len() < WINDOW,
    ensures out.0 == (if bytes.len() < LANES { bytes.len() } else { LANES }),
        1 <= out.0 <= LANES,
        out.1 == u32::MAX >> ((LANES - out.0) as usize),
        final(padded)@.subrange(0, bytes.len() as int) == bytes@,
        forall |i: int| bytes.len() <= i < WINDOW ==> #[trigger] final(padded)[i] == old(padded)[i],
    no_unwind
))]
pub(crate) fn pad_mixed_tail(bytes: &[u8], padded: &mut [u8; WINDOW]) -> (usize, u32) {
    let count = if bytes.len() < LANES { bytes.len() } else { LANES };
    let (dest, _) = padded.split_at_mut(bytes.len());
    // Equal-length, non-overlapping slices let the compiler lower this to a copy.
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= bytes.len(), dest.len() == bytes.len(),
            forall |j: int| 0 <= j < i ==> #[trigger] dest[j] == bytes[j],
        decreases bytes.len() - i,
    ))]
    while i < bytes.len() {
        dest[i] = bytes[i];
        i += 1;
    }
    let valid = u32::MAX >> (LANES - count);
    (count, valid)
}
