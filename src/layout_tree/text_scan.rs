use std::ops::Range;

#[cfg(target_arch = "x86_64")]
use super::{LineWidths, Xy};
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::*;

#[cfg(target_arch = "x86_64")]
mod mixed;
#[path = "text_windows.rs"]
#[cfg_attr(not(target_arch = "x86_64"), allow(dead_code))]
pub(super) mod windows;
use windows::ascii_space;
#[cfg(target_arch = "x86_64")]
use windows::boundaries::{WordWidths, WrappedWords, emit_boundary_words, finish_word, pop_lane16, tail_mask16, tail_mask32};
#[cfg(target_arch = "x86_64")]
use windows::native::{load_avx, load_sse2};
#[cfg(target_arch = "x86_64")]
pub(super) use mixed::measure_mixed_avx2;
#[cfg(target_arch = "x86_64")]
pub(super) use windows::boundaries::NativeBitLanes;
#[cfg(target_arch = "x86_64")]
pub(super) use windows::text_avx2_supported;

#[cfg(target_arch = "x86_64")]
#[inline(always)]
pub(super) fn next_window16<'text>(bytes: &'text [u8], cursor: &mut usize) -> Option<(&'text [u8; 16], usize, usize)> {
    let (block, start, count) = windows::take_window16(bytes, cursor)?;
    Some((block.first_chunk()?, start, count))
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
            let Some((block, start, count)) = next_window16(self.bytes, &mut self.cursor) else {
                // The input end is both a word's optional final boundary and
                // the sentinel indicating that no further word starts.
                return self.bytes.len();
            };
            self.block_start = start;
            let spaces = tail_mask16(whitespace_mask(block), count);
            let (_, previous, transitions) = windows::transitions16(spaces as u32, self.previous_space, count);
            self.previous_space = previous;
            self.transitions = transitions;
        }
        let offset = pop_lane16::<NativeBitLanes>(&mut self.transitions);
        self.block_start.saturating_add(offset as usize)
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

        let remaining = self.bytes.get(self.cursor..)?;
        let start = remaining.iter().position(|&byte| !ascii_space(byte))?;
        let word = remaining.get(start..)?;
        let end = word.iter().position(|&byte| ascii_space(byte)).unwrap_or(word.len());
        let start = self.cursor.checked_add(start)?;
        let range = start..start.checked_add(end)?;
        self.cursor = range.end;
        Some(range)
    }
}

// Measurements consume every word. Scan each block once and pass its complete
// word lengths directly to the wrapping calculation.
#[cfg(target_arch = "x86_64")]
pub(super) fn for_each_ascii_word_width<W: WordWidths>(bytes: &[u8], last: &[u8; 16], words: &mut W) {
    let (prefix, tail) = windows::partition_windows::<16>(bytes, false);
    let mut rest = prefix;
    let mut previous_space = 1u16;
    let mut word_start = 0;
    while let Some((block, base)) = windows::take_full_window::<16>(&mut rest, prefix.len()) {
        let Some(block) = block.first_chunk::<16>() else { return; };
        let spaces = whitespace_mask(block);
        let boundaries = spaces ^ ((spaces << 1) | previous_space);
        emit_boundary_words::<NativeBitLanes, _>(boundaries as u32, previous_space == 0, base, 16, &mut word_start, words);
        previous_space = spaces >> 15;
    }
    if !tail.is_empty() {
        // The last window overlaps bytes already visited. Shift them out.
        let spaces = tail_mask16(whitespace_mask(last), tail.len());
        let (_, previous, boundaries) = windows::transitions16(spaces as u32, previous_space, tail.len());
        emit_boundary_words::<NativeBitLanes, _>(boundaries as u32, previous_space == 0, prefix.len(), tail.len(), &mut word_start, words);
        previous_space = previous;
    }
    finish_word(words, u32::from(previous_space), word_start, bytes.len());
}

#[cfg(target_arch = "x86_64")]
impl WrappedWords {
    fn new(lines: LineWidths) -> Self {
        Self { previous_space: 1, word_start: 0, lines }
    }

    #[inline]
    fn finish(mut self, len: usize) -> Xy<f32> {
        finish_word(&mut self.lines, self.previous_space, self.word_start, len);
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
        let first = load_sse2(first);
        let last = load_sse2(last16);
        let window = _mm256_inserti128_si256::<1>(_mm256_castsi128_si256(first), last);
        let raw = _mm256_movemask_epi8(whitespace_avx2(window)) as u32;
        // Keep the low lane and move only new bytes from the high lane after it.
        let low_lane = u32::from(u16::MAX);
        let spaces = (raw & low_lane) | (tail_mask32(raw, bytes.len()) & !low_lane);
        scan.block::<NativeBitLanes>(spaces, bytes.len(), 0);
        return scan.finish(bytes.len());
    };
    // Reserve the last byte so there is always a final window to consume.
    let (prefix, tail) = windows::partition_windows::<32>(bytes, true);
    let mut rest = prefix;
    while let Some((block, base)) = windows::take_full_window::<32>(&mut rest, prefix.len()) {
        let Some(block) = block.first_chunk::<32>() else { return scan.finish(base); };
        scan.block::<NativeBitLanes>(whitespace_mask_avx2(block), 32, base);
    }
    let count = tail.len();
    scan.block::<NativeBitLanes>(tail_mask32(whitespace_mask_avx2(last), count), count, prefix.len());
    scan.finish(bytes.len())
}

#[cfg(target_arch = "x86_64")]
#[inline]
#[target_feature(enable = "avx2")]
fn whitespace_mask_avx2(block: &[u8; 32]) -> u32 {
    let input = load_avx(block);
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
    // SAFETY: SSE2 is available on x86-64.
    unsafe { _mm_movemask_epi8(whitespace_bytes(load_sse2(bytes))) as u16 }
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
    struct CheckWidths<W>(W);

    #[cfg(target_arch = "x86_64")]
    impl<W: FnMut(usize)> WordWidths for CheckWidths<W> {
        fn width(&mut self, width: usize) { (self.0)(width); }
    }

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
                    for_each_ascii_word_width(text.as_bytes(), last, &mut CheckWidths(|actual| {
                        assert_eq!(Some(actual), expected.next(), "byte {byte}, length {end}");
                    }));
                    assert_eq!(expected.next(), None);
                }
            }
        }
    }
}
