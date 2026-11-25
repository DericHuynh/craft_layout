use super::super::text_scan::{NativeBitLanes, next_window16};
use super::super::text_scan::windows::boundaries::{BitLanes, pop_lane16, prefix_count16, tail_mask16};
use super::super::text_scan::windows::native::load_sse2;
use super::super::text_scan::windows::{separator_lanes, span_width, transitions16, unicode_separator_width};
use std::ops::Range;

// Classify ASCII with SSE2 and decode only UTF-8 leads in mixed windows.
pub(super) struct MixedWords<'a, const WIDTHS: bool> {
    text: &'a str,
    cursor: usize,
    block_start: usize,
    carried_space: u32,
    previous_space: u16,
    transitions: u16,
    continuation: u16,
    preceding_continuations: usize,
}

impl<'a, const WIDTHS: bool> MixedWords<'a, WIDTHS> {
    pub(super) fn new(text: &'a str) -> Option<Self> {
        if text.len() < 16 { return None; }
        Some(Self {
            text,
            cursor: 0,
            block_start: 0,
            carried_space: 0,
            previous_space: 1,
            transitions: 0,
            continuation: 0,
            preceding_continuations: 0,
        })
    }

    #[inline]
    fn boundary(&mut self) -> (usize, usize) {
        while self.transitions == 0 {
            if WIDTHS && self.continuation != 0 {
                let count = NativeBitLanes::count(u32::from(self.continuation)) as usize;
                self.preceding_continuations = self.preceding_continuations.saturating_add(count);
            }
            self.continuation = 0;
            let Some((block, start, count)) = next_window16(self.text.as_bytes(), &mut self.cursor) else {
                return (self.text.len(), self.preceding_continuations);
            };
            self.block_start = start;
            self.fill_window(block, count);
        }
        let at = pop_lane16::<NativeBitLanes>(&mut self.transitions);
        let skipped = if WIDTHS && self.continuation != 0 {
            prefix_count16::<NativeBitLanes>(self.continuation, at)
        } else {
            0
        };
        (self.block_start.saturating_add(at as usize), self.preceding_continuations.saturating_add(skipped))
    }

    #[inline]
    fn fill_window(&mut self, block: &[u8; 16], count: usize) {
        use std::arch::x86_64::*;
        use super::super::text_scan::whitespace_bytes;

        let bytes = self.text.as_bytes();
        // SAFETY: SSE2 is available on x86-64 and the array covers the load.
        let (ascii, continuations, possible_spaces) = unsafe {
            let value = load_sse2(block);
            let ascii = tail_mask16(_mm_movemask_epi8(whitespace_bytes(value)) as u16, count);
            let high = tail_mask16(_mm_movemask_epi8(value) as u16, count);
            if high == 0 {
                (ascii, 0, 0)
            } else {
                let continuations = tail_mask16(_mm_movemask_epi8(_mm_cmpgt_epi8(_mm_set1_epi8(-64), value)) as u16, count);
                // Non-ASCII whitespace starts with C2 or E1–E3, so other leads
                // can contribute to the width without being decoded.
                let two_bytes = _mm_cmpeq_epi8(value, _mm_set1_epi8(0xc2_u8 as i8));
                let biased = _mm_sub_epi8(value, _mm_set1_epi8(0x61));
                let three_bytes = _mm_cmpgt_epi8(_mm_set1_epi8(-125), biased);
                let possible_spaces = tail_mask16(_mm_movemask_epi8(_mm_or_si128(two_bytes, three_bytes)) as u16, count);
                (ascii, continuations, possible_spaces)
            }
        };
        // Mark every byte of a Unicode separator, including any that spill
        // into the next window. Transitions therefore stay at UTF-8 boundaries.
        let mut spaces = u32::from(ascii) | self.carried_space;
        let mut leading = possible_spaces;
        while leading != 0 {
            let at = pop_lane16::<NativeBitLanes>(&mut leading);
            let width = unicode_separator_width(bytes, self.block_start.saturating_add(at as usize));
            if width != 0 {
                spaces |= separator_lanes(at, width);
            }
        }
        (self.carried_space, self.previous_space, self.transitions) = transitions16(spaces, self.previous_space, count);
        self.continuation = continuations;
    }
}

impl<const WIDTHS: bool> Iterator for MixedWords<'_, WIDTHS> {
    type Item = (Range<usize>, usize);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (start, skipped_before) = self.boundary();
        if start == self.text.len() { return None; }
        let (end, skipped_after) = self.boundary();
        Some((start..end, span_width(start, end, skipped_before, skipped_after)?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mixed_words_keep_spans_and_widths_across_windows() {
        let input = "  <a>  beta & long_identifier17\t next_word\n  and final text";
        let whitespace = (128..=0x10ffff).filter_map(char::from_u32).filter(|ch| ch.is_whitespace());
        for character in whitespace.chain(['β', '猫', '🦀', '\u{200b}', '\u{feff}']) {
            for index in 0..=input.len() {
                let mut text = input.to_owned();
                text.insert(index, character);
                let expected = text.split_whitespace().map(|word| (word, word.chars().count()));
                let actual = MixedWords::<true>::new(&text).unwrap().map(|(span, width)| (&text[span], width));
                assert!(actual.eq(expected), "{character:?} at {index}");
                let expected = text.split_whitespace();
                let actual = MixedWords::<false>::new(&text).unwrap().map(|(span, _)| &text[span]);
                assert!(actual.eq(expected), "{character:?} at {index}");
            }
        }
    }
}
