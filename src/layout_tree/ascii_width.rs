use super::{ascii_space, text_scan::whitespace_bytes};
use std::arch::x86_64::*;

mod avx2;

const WIDTH: usize = 16;

#[inline(always)]
pub(super) fn width(bytes: &[u8]) -> Option<usize> {
    if let Some(last) = bytes.last_chunk::<32>() && is_x86_feature_detected!("avx2") {
        // SAFETY: The detector checks both CPU support and saved vector state.
        return unsafe { avx2::normalized_width(bytes, last) };
    }
    if let Some(last) = bytes.last_chunk::<WIDTH>() {
        return normalized_width(bytes, last);
    }
    if bytes.len() >= 4 {
        return short_width(bytes);
    }

    let mut count = 0;
    let mut previous_space = true;
    for &byte in bytes {
        if !byte.is_ascii() { return None; }
        let white = ascii_space(byte);
        if !white { count += 1 + usize::from(previous_space); }
        previous_space = white;
    }
    Some(count.saturating_sub(1))
}

// A short label is packed as its first and last 4 or 8 bytes. Keep the
// prefix and the portion of the last chunk that extends past it.
const fn short_window_masks() -> [[u8; WIDTH]; WIDTH] {
    let mut masks = [[0; WIDTH]; WIDTH];
    let mut len = 4;
    while len < WIDTH {
        let half = if len >= 8 { 8 } else { 4 };
        let first_new = 3 * half - len;
        let mut lane = 0;
        while lane < 2 * half {
            if lane < half || lane >= first_new { masks[len][lane] = 255; }
            lane += 1;
        }
        len += 1;
    }
    masks
}

static SHORT_WINDOW_MASKS: [[u8; WIDTH]; WIDTH] = short_window_masks();

/// Count a label between four and fifteen bytes in a single vector.
#[inline]
fn short_width(bytes: &[u8]) -> Option<usize> {
    // SAFETY: SSE2 is part of the x86-64 baseline. Short loads are expressed
    // as checked array references. The mask row always supplies 16 bytes.
    unsafe {
        let input = if let Some(first) = bytes.first_chunk::<8>() {
            let low = i64::from_ne_bytes(*first);
            let high = i64::from_ne_bytes(*bytes.last_chunk().unwrap());
            _mm_set_epi64x(high, low)
        } else {
            let low = u64::from(u32::from_ne_bytes(*bytes.first_chunk().unwrap()));
            let high = u64::from(u32::from_ne_bytes(*bytes.last_chunk().unwrap()));
            _mm_cvtsi64_si128(((high << 32) | low) as i64)
        };
        // Overlap is harmless for validation and the unused lanes are zero.
        if _mm_movemask_epi8(input) != 0 { return None; }
        let white = whitespace_bytes(input);
        let previous = _mm_or_si128(_mm_slli_si128::<1>(white), _mm_cvtsi32_si128(255));
        let valid = _mm_loadu_si128(SHORT_WINDOW_MASKS[bytes.len()].as_ptr().cast());
        let zero = _mm_setzero_si128();
        let counts = _mm_sub_epi8(zero, _mm_and_si128(negative_width(white, previous), valid));
        let sums = _mm_sad_epu8(counts, zero);
        let count = _mm_add_epi64(sums, _mm_srli_si128::<8>(sums));
        Some(_mm_cvtsi128_si32(_mm_subs_epu16(count, _mm_cvtsi32_si128(1))) as usize)
    }
}

/// Count whitespace preceded by whitespace. A virtual space before byte zero
/// includes all leading spaces in that count. Subtract it and a trailing
/// separator from the input length to get the normalized width.
fn normalized_width(bytes: &[u8], last: &[u8; WIDTH]) -> Option<usize> {
    // Leave the final window to the same masked operation at every length.
    let (blocks, tail) = bytes[..bytes.len() - 1].as_chunks::<WIDTH>();
    let final_lanes = tail.len() + 1;
    // SAFETY: SSE2 is part of the x86-64 baseline. Every unaligned load reads
    // exactly one complete WIDTH-byte array.
    unsafe {
        let zero = _mm_setzero_si128();
        let mut sums = zero;
        // Treat the byte preceding the input as whitespace.
        let mut carry = _mm_cvtsi32_si128(255);
        // Each byte slot accumulates at most one per block.
        for group in blocks.chunks(255) {
            let mut counts = zero;
            for block in group {
                let data = _mm_loadu_si128(block.as_ptr().cast());
                if _mm_movemask_epi8(data) != 0 { return None; }
                let white = whitespace_bytes(data);
                let previous = _mm_or_si128(_mm_slli_si128::<1>(white), carry);
                carry = _mm_srli_si128::<15>(white);
                counts = _mm_sub_epi8(counts, _mm_and_si128(white, previous));
            }
            sums = _mm_add_epi64(sums, _mm_sad_epu8(counts, zero));
        }
        let data = _mm_loadu_si128(last.as_ptr().cast());
        if _mm_movemask_epi8(data) != 0 { return None; }
        let white = whitespace_bytes(data);
        // The carry matters for lane zero only when the entire window is new.
        // An overlapping window masks out that lane and other duplicate bytes.
        let previous = _mm_or_si128(_mm_slli_si128::<1>(white), carry);
        let lanes = _mm_setr_epi8(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15);
        let new_lanes = _mm_cmpgt_epi8(lanes, _mm_set1_epi8(WIDTH as i8 - 1 - final_lanes as i8));
        let paired = _mm_and_si128(white, previous);
        let counts = _mm_sub_epi8(zero, _mm_and_si128(paired, new_lanes));
        sums = _mm_add_epi64(sums, _mm_sad_epu8(counts, zero));
        Some(finish_width(bytes.len(), sums, _mm_srli_si128::<15>(white)))
    }
}

#[inline]
fn finish_width(len: usize, sums: __m128i, last_white: __m128i) -> usize {
    // SAFETY: SSE2 is part of the x86-64 baseline.
    unsafe {
        let count = _mm_add_epi64(sums, _mm_srli_si128::<8>(sums));
        let trailing = _mm_and_si128(last_white, _mm_cvtsi32_si128(1));
        let removed = _mm_add_epi64(count, trailing);
        let width = _mm_sub_epi64(_mm_cvtsi64_si128(len as i64), removed);
        // Only all-whitespace labels underflow. Their normalized width is zero.
        let underflow = _mm_srai_epi32::<31>(_mm_shuffle_epi32::<0x55>(width));
        _mm_cvtsi128_si64(_mm_andnot_si128(underflow, width)) as usize
    }
}

#[inline]
fn negative_width(white: __m128i, previous: __m128i) -> __m128i {
    // SAFETY: SSE2 is part of the x86-64 baseline.
    unsafe {
        // Each text byte contributes one, with an extra one at word starts.
        // Subtract byte values 0xff or 0xfe to add one or two respectively.
        _mm_andnot_si128(white, _mm_add_epi8(previous, _mm_set1_epi8(-1)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counts_words_across_full_overlapping_and_accumulator_boundaries() {
        let text = b"\tABC\r \x0b12\x0cN\n   xyz\0".repeat(230);
        for start in 0..16 {
            for end in (start + 16..start + 96).chain(start + 4064..start + 4128) {
                let bytes = &text[start..end];
                let expected = std::str::from_utf8(bytes).unwrap().split_whitespace()
                    .map(str::len).reduce(|a, b| a + 1 + b).unwrap_or(0);
                assert_eq!(normalized_width(bytes, bytes.last_chunk().unwrap()), Some(expected), "{start}..{end}");
            }
        }
        for byte in *b" A" {
            let bytes = [byte; 4097];
            let expected = if byte == b' ' { 0 } else { bytes.len() };
            assert_eq!(normalized_width(&bytes, bytes.last_chunk().unwrap()), Some(expected));
        }
    }

    #[test]
    fn short_registers_keep_only_input_bytes_and_real_word_starts() {
        for len in 4..16 {
            let mut bytes = [b'A'; 16];
            for pattern in 0..1u16 << len {
                for (index, byte) in bytes[..len].iter_mut().enumerate() {
                    *byte = if pattern >> index & 1 != 0 { b'\t' } else { b'A' };
                }
                let text = std::str::from_utf8(&bytes[..len]).unwrap();
                let expected = text.split_whitespace().map(str::len)
                    .reduce(|a, b| a + 1 + b).unwrap_or(0);
                assert_eq!(short_width(text.as_bytes()), Some(expected), "{len}, mask {pattern}");
            }
        }
    }

    #[test]
    fn fused_validation_rejects_non_ascii_in_every_lane_and_tail() {
        let mut bytes = [b'A'; 4129];
        for len in [1, 3, 4, 7, 8, 15, 16, 17, 31, 32, 33, 63, 64, 65, 128, 129, bytes.len()] {
            for offset in 0..len {
                bytes[offset] = if offset % 2 == 0 { 0x80 } else { 0xff };
                assert_eq!(width(&bytes[..len]), None, "length {len}, invalid byte {offset}");
                bytes[offset] = b'A';
            }
        }
    }
}
