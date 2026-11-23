use std::ops::Range;

use super::ascii_space;
#[cfg(target_arch = "x86_64")]
use super::{LineWidths, Xy};
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

#[cfg(target_arch = "x86_64")]
mod mixed;
#[cfg(target_arch = "x86_64")]
#[path = "text_windows.rs"]
pub(super) mod windows;
#[cfg(target_arch = "x86_64")]
pub(super) use mixed::measure_mixed_avx2;

#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub(super) fn next_window16(bytes: &[u8], cursor: usize) -> Option<(&[u8; 16], usize)> {
    let (start, count) = windows::window16(bytes.len(), cursor)?;
    Some((bytes.get(start..)?.first_chunk()?, count))
}

/// Yields byte ranges of non-whitespace runs. The input is known to be ASCII.
pub(super) struct AsciiWords<'text> {
    bytes: &'text [u8],
    cursor: usize,
    #[cfg(target_arch = "x86_64")]
    transitions: u16,
    #[cfg(target_arch = "x86_64")]
    block_start: usize,
    #[cfg(target_arch = "x86_64")]
    previous_space: u16,
}

impl<'text> AsciiWords<'text> {
    pub(super) fn new(bytes: &'text [u8]) -> Self {
        Self {
            bytes,
            cursor: 0,
            #[cfg(target_arch = "x86_64")]
            transitions: 0,
            #[cfg(target_arch = "x86_64")]
            block_start: 0,
            #[cfg(target_arch = "x86_64")]
            previous_space: 1,
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[inline]
    fn boundary(&mut self) -> usize {
        while self.transitions == 0 {
            let Some((block, count)) = next_window16(self.bytes, self.cursor) else {
                // The input end is both a word's optional final boundary and
                // the sentinel indicating that no further word starts.
                return self.bytes.len();
            };
            self.block_start = self.cursor;
            let spaces = whitespace_mask(block) >> (16 - count);
            self.transitions = spaces ^ ((spaces << 1) | self.previous_space);
            self.transitions &= windows::low_lanes16(count);
            self.previous_space = spaces >> (count - 1);
            self.cursor += count;
        }
        let offset = self.transitions.trailing_zeros() as usize;
        self.transitions &= self.transitions - 1;
        self.block_start + offset
    }
}

impl Iterator for AsciiWords<'_> {
    type Item = Range<usize>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        #[cfg(target_arch = "x86_64")]
        if self.bytes.len() >= 16 {
            let start = self.boundary();
            return (start < self.bytes.len()).then(|| start..self.boundary());
        }

        let remaining = &self.bytes[self.cursor..];
        let start = remaining.iter().position(|&byte| !ascii_space(byte))?;
        let word = &remaining[start..];
        let end = word.iter().position(|&byte| ascii_space(byte)).unwrap_or(word.len());
        let range = (self.cursor + start)..(self.cursor + start + end);
        self.cursor = range.end;
        Some(range)
    }
}

// Measurements consume every word. Scan each block once and pass its complete
// word lengths directly to the wrapping calculation.
#[cfg(target_arch = "x86_64")]
pub(super) fn for_each_ascii_word_width(bytes: &[u8], last: &[u8; 16], mut word: impl FnMut(usize)) {
    let (blocks, tail) = bytes.as_chunks::<16>();
    let mut previous_space = 1u16;
    let mut word_start = 0;
    for (block_index, block) in blocks.iter().enumerate() {
        let base = block_index * 16;
        let spaces = whitespace_mask(block);
        emit_words(spaces ^ ((spaces << 1) | previous_space), previous_space, base, &mut word_start, &mut word);
        previous_space = spaces >> 15;
    }
    if !tail.is_empty() {
        // The last window overlaps bytes already visited. Shift them out.
        let spaces = whitespace_mask(last) >> (16 - tail.len());
        let boundaries = (spaces ^ ((spaces << 1) | previous_space)) & (u16::MAX >> (16 - tail.len()));
        emit_words(boundaries, previous_space, blocks.len() * 16, &mut word_start, &mut word);
        previous_space = spaces >> (tail.len() - 1);
    }
    if previous_space == 0 {
        word(bytes.len() - word_start);
    }
}

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn emit_words(mut boundaries: u16, previous_space: u16, base: usize, word_start: &mut usize, mut word: impl FnMut(usize)) {
    if boundaries != 0 && previous_space == 0 {
        // The first boundary closes a word that started in an earlier block.
        let end = base + boundaries.trailing_zeros() as usize;
        boundaries &= boundaries - 1;
        word(end - *word_start);
    }
    while boundaries != 0 {
        *word_start = base + boundaries.trailing_zeros() as usize;
        boundaries &= boundaries - 1;
        if boundaries != 0 {
            let end = base + boundaries.trailing_zeros() as usize;
            boundaries &= boundaries - 1;
            word(end - *word_start);
        }
    }
}

#[cfg(target_arch = "x86_64")]
struct WrappedWords {
    previous_space: u32,
    word_start: usize,
    lines: LineWidths,
}

#[cfg(target_arch = "x86_64")]
impl WrappedWords {
    fn new(lines: LineWidths) -> Self {
        Self { previous_space: 1, word_start: 0, lines }
    }

    #[inline(always)]
    fn block(&mut self, spaces: u32, count: usize, base: usize) {
        let previous = (spaces << 1) | self.previous_space;
        let ends = spaces & !previous;
        // Count letters up to the last completed word and one separator per
        // word, except before the first word of a line. If this whole prefix
        // fits, its individual words cannot cause a line break.
        if ends != 0 {
            let last_end = 31 - ends.leading_zeros();
            let letters = ((1u32 << last_end) - 1) & !spaces;
            let carry = if self.previous_space == 0 { base - self.word_start } else { 0 };
            let first_line = usize::from(self.lines.current == 0);
            let joined = self.lines.current + letters.count_ones() as usize + carry
                + ends.count_ones() as usize - first_line;
            if joined <= self.lines.max {
                self.lines.count += first_line;
                self.lines.current = joined;
                self.lines.longest = self.lines.longest.max(joined);
                self.previous_space = spaces >> (count - 1);
                // The only unfinished word, if any, follows the last space.
                self.word_start = base + (32 - spaces.leading_zeros()) as usize;
                return;
            }
        }

        let boundaries = (spaces ^ previous) & (u32::MAX >> (32 - count));
        self.emit_words(boundaries, base);
        self.previous_space = spaces >> (count - 1);
    }

    #[inline(always)]
    fn emit_words(&mut self, mut boundaries: u32, base: usize) {
        if boundaries != 0 && self.previous_space == 0 {
            let end = base + boundaries.trailing_zeros() as usize;
            boundaries &= boundaries - 1;
            self.lines.add_word(end - self.word_start);
        }
        while boundaries != 0 {
            self.word_start = base + boundaries.trailing_zeros() as usize;
            boundaries &= boundaries - 1;
            if boundaries != 0 {
                let end = base + boundaries.trailing_zeros() as usize;
                boundaries &= boundaries - 1;
                self.lines.add_word(end - self.word_start);
            }
        }
    }

    #[inline]
    fn finish(mut self, len: usize) -> Xy<f32> {
        if self.previous_space == 0 {
            self.lines.add_word(len - self.word_start);
        }
        self.lines.size()
    }
}

#[cfg(target_arch = "x86_64")]
/// Measures wrapping for input already known to be ASCII.
///
/// # Safety
/// The current CPU must support AVX2 and POPCNT. The two arrays must be the
/// first and last 16 bytes of `bytes`.
#[target_feature(enable = "avx2,popcnt")]
pub(super) unsafe fn measure_wrapped_avx2(
    bytes: &[u8], first: &[u8; 16], last16: &[u8; 16], lines: LineWidths,
) -> Xy<f32> {
    let mut scan = WrappedWords::new(lines);
    let Some(last) = bytes.last_chunk::<32>() else {
        // SAFETY: Each array supplies a full 16-byte load.
        let window = unsafe {
            let first = _mm_loadu_si128(first.as_ptr().cast());
            let last = _mm_loadu_si128(last16.as_ptr().cast());
            _mm256_inserti128_si256::<1>(_mm256_castsi128_si256(first), last)
        };
        let raw = _mm256_movemask_epi8(whitespace_avx2(window)) as u32;
        // Keep the low lane and move only new bytes from the high lane after it.
        let low_lane = u32::from(u16::MAX);
        let spaces = (raw & low_lane) | ((raw >> (32 - bytes.len())) & !low_lane);
        scan.block(spaces, bytes.len(), 0);
        return scan.finish(bytes.len());
    };
    // Reserve the last byte so there is always a final window to consume.
    let (blocks, tail) = bytes[..bytes.len() - 1].as_chunks::<32>();
    for (index, block) in blocks.iter().enumerate() {
        scan.block(whitespace_mask_avx2(block), 32, index * 32);
    }
    let count = tail.len() + 1;
    scan.block(whitespace_mask_avx2(last) >> (32 - count), count, blocks.len() * 32);
    scan.finish(bytes.len())
}

#[cfg(target_arch = "x86_64")]
#[inline]
#[target_feature(enable = "avx2")]
fn whitespace_mask_avx2(block: &[u8; 32]) -> u32 {
    // SAFETY: The array supplies a full vector load.
    let input = unsafe { _mm256_loadu_si256(block.as_ptr().cast()) };
    _mm256_movemask_epi8(whitespace_avx2(input)) as u32
}

#[cfg(target_arch = "x86_64")]
#[inline]
#[target_feature(enable = "avx2")]
pub(super) fn whitespace_avx2(input: __m256i) -> __m256i {
    // The whitespace bytes have distinct low nibbles. Verify the entire
    // ASCII byte after the shuffle, using 0x80 as an out-of-range entry.
    let lookup = _mm256_setr_epi8(
        b' ' as i8, -128, -128, -128, -128, -128, -128, -128,
        -128, 9, 10, 11, 12, 13, -128, -128,
        b' ' as i8, -128, -128, -128, -128, -128, -128, -128,
        -128, 9, 10, 11, 12, 13, -128, -128,
    );
    _mm256_cmpeq_epi8(input, _mm256_shuffle_epi8(lookup, input))
}

#[cfg(target_arch = "x86_64")]
#[inline]
fn whitespace_mask(bytes: &[u8; 16]) -> u16 {
    use std::arch::x86_64::*;
    // SSE2 is available on x86-64 and the array supplies a full 16-byte load.
    unsafe { _mm_movemask_epi8(whitespace_bytes(_mm_loadu_si128(bytes.as_ptr().cast()))) as u16 }
}

#[cfg(target_arch = "x86_64")]
#[inline]
pub(super) fn whitespace_bytes(bytes: std::arch::x86_64::__m128i) -> std::arch::x86_64::__m128i {
    use std::arch::x86_64::*;
    // SSE2 is available on x86-64. Bias unsigned differences into signed
    // order so only 9 through 13 map to -128 through -124.
    unsafe {
        let biased = _mm_sub_epi8(bytes, _mm_set1_epi8(-119));
        let controls = _mm_cmpgt_epi8(_mm_set1_epi8(-123), biased);
        let spaces = _mm_cmpeq_epi8(bytes, _mm_set1_epi8(b' ' as i8));
        _mm_or_si128(controls, spaces)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn unicode_separator_bytes_match_rust_for_every_scalar() {
        let mut buffer = [0; 4];
        for scalar in (128..=char::MAX as u32).filter_map(char::from_u32) {
            let bytes = scalar.encode_utf8(&mut buffer).as_bytes();
            let expected = if scalar.is_whitespace() { bytes.len() as u32 } else { 0 };
            assert_eq!(windows::unicode_separator_width(bytes, 0), expected, "{scalar:?}");
            if expected != 0 {
                for shorter in 0..bytes.len() {
                    assert_eq!(windows::unicode_separator_width(&bytes[..shorter], 0), 0, "{scalar:?}");
                }
            }
        }
    }

    #[test]
    fn word_spans_match_unicode_ascii_whitespace() {
        // Include every ASCII byte immediately before and after a block boundary.
        for byte in 0..=127 {
            let mut bytes = *b"\t multiple spaces \x0b a_long_word_without_a_gap  \r\n end  ";
            bytes[15] = byte;
            bytes[16] = byte;
            bytes[31] = byte;
            bytes[32] = byte;
            for end in 0..=bytes.len() {
                let text = std::str::from_utf8(&bytes[..end]).unwrap();
                let actual = AsciiWords::new(text.as_bytes()).map(|word| &text[word]);
                assert!(actual.eq(text.split_whitespace()), "byte {byte}, length {end}");
                #[cfg(target_arch = "x86_64")]
                if let Some(last) = text.as_bytes().last_chunk::<16>() {
                    let mut expected = text.split_whitespace().map(str::len);
                    for_each_ascii_word_width(text.as_bytes(), last, |actual| {
                        assert_eq!(Some(actual), expected.next(), "byte {byte}, length {end}");
                    });
                    assert_eq!(expected.next(), None);
                }
            }
        }
    }
}
