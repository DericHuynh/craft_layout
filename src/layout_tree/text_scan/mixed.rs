use super::{LineWidths, WrappedWords, Xy, whitespace_avx2};
use super::windows::{LANES, MIN_PADDED, WINDOW, mixed_tail, pad_mixed_tail};
use std::arch::x86_64::*;

/// Measures logical character widths across ASCII and UTF-8.
///
/// # Safety
/// The CPU and operating system must support AVX2, POPCNT, and BMI2.
#[target_feature(enable = "avx2,popcnt,bmi2")]
pub(in crate::layout_tree) unsafe fn measure_mixed_avx2(text: &str, lines: LineWidths) -> Xy<f32> {
    let mut scan = WrappedWords::new(lines);
    let mut base = 0;
    let bytes = text.as_bytes();
    // A whitespace code point takes at most three bytes. Reserve two bytes
    // after each SIMD window so the last lane can inspect its UTF-8 followers.
    let mut rest = bytes;
    while let Some(block) = rest.first_chunk::<WINDOW>() {
        base += count_mixed_block(block, u32::MAX, &mut scan, base);
        rest = rest.split_at(LANES).1;
    }
    let (mut tail, bytes_left) = mixed_tail(bytes);
    if bytes_left.len() >= MIN_PADDED {
        // Count at most one more vector here. The copied follower bytes permit
        // classification at the far edge and padding carries no character width.
        let mut padded = [0; WINDOW];
        let (count, valid) = pad_mixed_tail(bytes_left, &mut padded);
        base += count_mixed_block(&padded, valid, &mut scan, base);
        tail += count;
    }
    // A previously counted lead may have continuation bytes in the scalar tail.
    while !text.is_char_boundary(tail) {
        tail += 1;
    }
    base = scan.chars(&text[tail..], base);
    scan.finish(base)
}

#[inline]
#[target_feature(enable = "avx2,popcnt,bmi2")]
fn count_mixed_block(block: &[u8; WINDOW], valid: u32, scan: &mut WrappedWords, base: usize) -> usize {
    // SAFETY: The array supplies a full unaligned vector load.
    let input = unsafe { _mm256_loadu_si256(block.as_ptr().cast()) };
    let ascii_white = whitespace_avx2(input);
    let (white, count) = if (_mm256_movemask_epi8(input) as u32 & valid) == 0 {
        (_mm256_movemask_epi8(ascii_white) as u32 & valid, valid.count_ones() as usize)
    } else {
        let continuation = _mm256_cmpgt_epi8(_mm256_set1_epi8(-64), input);
        // Each code point is represented by its first byte, even when its
        // continuation bytes extend into the following block.
        let starts = !(_mm256_movemask_epi8(continuation) as u32) & valid;
        let unicode_white = unicode_whitespace_leads(block, input);
        let white = _mm256_movemask_epi8(_mm256_or_si256(ascii_white, unicode_white)) as u32;
        (_pext_u32(white, starts), starts.count_ones() as usize)
    };
    scan.block(white, count, base);
    count
}

#[inline]
#[target_feature(enable = "avx2")]
fn unicode_whitespace_leads(block: &[u8; WINDOW], input: __m256i) -> __m256i {
    #[inline]
    #[target_feature(enable = "avx2")]
    fn byte_eq(input: __m256i, byte: u8) -> __m256i {
        _mm256_cmpeq_epi8(input, _mm256_set1_epi8(byte as i8))
    }
    let c2 = byte_eq(input, 0xc2);
    let e1 = byte_eq(input, 0xe1);
    let e2 = byte_eq(input, 0xe2);
    let e3 = byte_eq(input, 0xe3);
    let possible = _mm256_or_si256(_mm256_or_si256(c2, e1), _mm256_or_si256(e2, e3));
    if _mm256_movemask_epi8(possible) == 0 {
        return possible;
    }
    // SAFETY: The 34-byte array supplies a full vector after either offset.
    let second = unsafe { _mm256_loadu_si256(block[1..].as_ptr().cast()) };
    let third = unsafe { _mm256_loadu_si256(block[2..].as_ptr().cast()) };
    let second80 = byte_eq(second, 0x80);
    let third80 = byte_eq(third, 0x80);

    // U+0085 and U+00A0, U+1680, and U+3000.
    let c2 = _mm256_and_si256(c2, _mm256_or_si256(byte_eq(second, 0x85), byte_eq(second, 0xa0)));
    let e1 = _mm256_and_si256(e1, _mm256_and_si256(byte_eq(second, 0x9a), third80));
    let e3 = _mm256_and_si256(e3, _mm256_and_si256(second80, third80));

    // U+2000–U+200A, U+2028, U+2029 and U+202F (E2 80 xx), then U+205F.
    let low = _mm256_cmpgt_epi8(_mm256_set1_epi8(0x8bu8 as i8), third);
    let a8_a9 = byte_eq(_mm256_and_si256(third, _mm256_set1_epi8(-2)), 0xa8);
    let row80 = _mm256_and_si256(second80, _mm256_or_si256(low, _mm256_or_si256(a8_a9, byte_eq(third, 0xaf))));
    let row81 = _mm256_and_si256(byte_eq(second, 0x81), byte_eq(third, 0x9f));
    let e2 = _mm256_and_si256(e2, _mm256_or_si256(row80, row81));

    _mm256_or_si256(_mm256_or_si256(c2, e1), _mm256_or_si256(e2, e3))
}

impl WrappedWords {
    #[inline]
    fn chars(&mut self, text: &str, mut base: usize) -> usize {
        for c in text.chars() {
            let white = u32::from(c.is_whitespace());
            if self.previous_space != white {
                if white == 0 {
                    self.word_start = base;
                } else {
                    self.lines.add_word(base - self.word_start);
                }
            }
            self.previous_space = white;
            base += 1;
        }
        base
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unicode_space_leads_match_rust_at_vector_boundaries() {
        if !is_x86_feature_detected!("avx2") {
            return;
        }

        let check = |c: char, lane: usize, expected: u32| {
            let mut window = [b'x'; 35];
            c.encode_utf8(&mut window[lane..]);
            let block = window.first_chunk::<34>().unwrap();
            // SAFETY: AVX2 was detected and the array supplies a full vector.
            let mask = unsafe {
                let input = _mm256_loadu_si256(block.as_ptr().cast());
                _mm256_movemask_epi8(unicode_whitespace_leads(block, input)) as u32
            };
            assert_eq!(mask, expected, "character {c:?} in lane {lane}");
        };

        for code in 0..=0x10ffff {
            let Some(c) = char::from_u32(code) else { continue };
            if !c.is_ascii() && c.is_whitespace() {
                for lane in 0..32 {
                    check(c, lane, 1 << lane);
                }
            } else {
                check(c, (code % 32) as usize, 0);
            }
        }
    }
}
