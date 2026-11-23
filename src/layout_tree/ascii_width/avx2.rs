use super::super::text_scan::whitespace_avx2 as whitespace;
use std::arch::x86_64::*;

const WIDTH: usize = 32;

/// Count normalized width while checking that every byte is ASCII.
///
/// The caller supplies the last complete window of `bytes`.
///
/// # Safety
/// AVX2 must be available on the current CPU.
#[target_feature(enable = "avx2")]
pub(super) unsafe fn normalized_width(bytes: &[u8], last: &[u8; WIDTH]) -> Option<usize> {
    let (blocks, tail) = bytes.as_chunks::<WIDTH>();
    let zero = _mm256_setzero_si256();
    let mut sums = zero;
    // The virtual byte before the string is whitespace, so this also removes
    // leading whitespace. The last whitespace run needs its own correction.
    let mut previous_white = _mm256_set1_epi8(-1);
    for group in blocks.chunks(u8::MAX as usize) {
        let mut counts = zero;
        for block in group {
            // SAFETY: The array supplies a full unaligned vector load.
            let input = unsafe { _mm256_loadu_si256(block.as_ptr().cast()) };
            if _mm256_movemask_epi8(input) != 0 {
                return None;
            }
            let white = whitespace(input);
            let previous = preceding_bytes(white, previous_white);
            counts = _mm256_sub_epi8(counts, _mm256_and_si256(white, previous));
            previous_white = white;
        }
        sums = _mm256_add_epi64(sums, _mm256_sad_epu8(counts, zero));
    }
    if !tail.is_empty() {
        // SAFETY: The last window is also a full vector.
        let input = unsafe { _mm256_loadu_si256(last.as_ptr().cast()) };
        if _mm256_movemask_epi8(input) != 0 {
            return None;
        }
        let white = whitespace(input);
        let previous = preceding_bytes(white, zero);
        let lanes = _mm256_setr_epi8(
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
            16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
        );
        // Each new lane has its predecessor inside this overlapping window.
        let new_lanes = _mm256_cmpgt_epi8(lanes, _mm256_set1_epi8((WIDTH - 1 - tail.len()) as i8));
        let pairs = _mm256_and_si256(_mm256_and_si256(white, previous), new_lanes);
        sums = _mm256_add_epi64(sums, _mm256_sad_epu8(_mm256_sub_epi8(zero, pairs), zero));
        previous_white = white;
    }
    let halves = _mm_add_epi64(_mm256_castsi256_si128(sums), _mm256_extracti128_si256::<1>(sums));
    let trailing_white = _mm_srli_si128::<15>(_mm256_extracti128_si256::<1>(previous_white));
    Some(super::finish_width(bytes.len(), halves, trailing_white))
}

#[inline]
#[target_feature(enable = "avx2")]
fn preceding_bytes(white: __m256i, previous_white: __m256i) -> __m256i {
    // PALIGNR shifts each 128-bit lane separately. Put the appropriate
    // previous lane alongside each half to carry across both boundaries.
    let preceding_lanes = _mm256_permute2x128_si256::<0x21>(previous_white, white);
    _mm256_alignr_epi8::<15>(white, preceding_lanes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn width_and_ascii_status_match_across_vector_boundaries() {
        if !is_x86_feature_detected!("avx2") {
            return;
        }
        for byte in 0..=127 {
            let input = [byte; WIDTH];
            let text = std::str::from_utf8(&input).unwrap();
            let width = text.split_whitespace().next().map_or(0, str::len);
            assert_eq!(unsafe { normalized_width(&input, &input) }, Some(width));
        }
        let pattern = b"\tABC\r \x0b12\x0cN\n   xyz\0".repeat(500);
        for start in 0..WIDTH {
            for len in (WIDTH..4 * WIDTH).chain(8_140..8_175) {
                let input = &pattern[start..start + len];
                let expected = std::str::from_utf8(input).unwrap().split_whitespace()
                    .map(str::len).reduce(|left, right| left + 1 + right).unwrap_or(0);
                assert_eq!(unsafe { normalized_width(input, input.last_chunk().unwrap()) }, Some(expected));
            }
        }
        for content in *b" A" {
            let input = [content; 8_161];
            let width = if content == b' ' { 0 } else { input.len() };
            assert_eq!(unsafe { normalized_width(&input, input.last_chunk().unwrap()) }, Some(width));
        }
        for len in [63, 64, 65, 8_159, 8_160, 8_161] {
            let mut input = vec![b'A'; len];
            for offset in [0, 15, 16, 31, 32, len - 2, len - 1] {
                input[offset] = 0x80;
                assert_eq!(unsafe { normalized_width(&input, input.last_chunk().unwrap()) }, None);
                input[offset] = b'A';
            }
        }
    }
}
