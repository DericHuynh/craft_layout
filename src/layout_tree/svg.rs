use super::*;
use super::text_scan::AsciiWords;
use super::text_scan::windows::{SVG_NUMBER_CACHE_BITS, next_svg_escape, separated_by_space, svg_color_bytes, svg_color_suffix, svg_number_index};
use arrayvec::ArrayString;
use std::fmt::{self, Write};
use std::ops::Range;

#[path = "svg_number_format.rs"]
mod number_format;
use number_format::{SVG_NUMBER_CAPACITY, write_svg_number};

#[path = "svg_control.rs"]
mod controller;
use controller::{WordSpan, next_line, paint_nodes};

#[cfg(target_arch = "x86_64")]
#[path = "svg_words.rs"]
mod svg_words;
#[cfg(target_arch = "x86_64")]
use svg_words::MixedWords;
#[cfg(target_arch = "x86_64")]
use super::text_scan::{NativeBitLanes, text_avx2_supported};
#[cfg(target_arch = "x86_64")]
use super::text_scan::windows::boundaries::{active_tail32, pop_lane, single_space_end, tail_mask16, tail_mask32};
#[cfg(target_arch = "x86_64")]
use super::text_scan::windows::native::{load_avx, load_sse2};
#[cfg(target_arch = "x86_64")]
use super::text_scan::windows::{TextAvx2, partition_windows, take_full_window, unicode_separator_width};

impl<T> LayoutTree<T> {
    fn write_svg_inner(&self, svg: &mut (impl Write + ?Sized), text: impl Fn(&T) -> &str) -> fmt::Result {
        let mut numbers = SvgNumbers::new();
        let window = self.layout_data.window_size;
        writeln!(svg, "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"{}\" height=\"{}\" font-family=\"monospace\" font-size=\"7.5\">", window.x, window.y)?;
        writeln!(svg, "<rect width=\"100%\" height=\"100%\" fill=\"#faf8f5\"/>")?;
        paint_nodes(self.root, self.nodes.len(), fmt::Error, &mut |i| {
            let node = self.nodes.get(i).ok_or(fmt::Error)?;
            let next = self.next_in_subtree(self.root, i, !node.params.disabled);
            if !node.has_published_rect() {
                return Ok(next);
            }
            let color = node_color(i);
            let color = color.as_str();
            let rect = node.rect;
            let size = node.params.size;

            numbers.write_fields(svg, [
                ("<rect x=\"", rect.x[0]), ("\" y=\"", rect.y[0]),
                ("\" width=\"", rect.x[1] - rect.x[0]), ("\" height=\"", rect.y[1] - rect.y[0]),
            ])?;
            writeln!(svg, "\" fill=\"{color}\" fill-opacity=\"0.06\" stroke=\"{color}\"/>")?;
            if node.params.text != TextContent::None && let Some(context) = self.context(node) {
                let [left, right] = node.params.padding.x;
                let wraps = node.params.text == TextContent::Wrapping && !matches!(node.params.size.x, Size::AspectRatio(_));
                let wrap_width = wraps.then(|| (node.layout.size().x - left - right).max(0.0));
                let mut n = 0usize;
                for line in wrapped_lines(text(context), wrap_width) {
                    let y = rect.y[0] + node.params.padding.y[0] + (n as f32 + 0.75) * LINE_HEIGHT;
                    let length = line.width_in_chars as f32 * CHAR_WIDTH;
                    numbers.write_fields(svg, [
                        ("<text x=\"", rect.x[0] + left), ("\" y=\"", y),
                        ("\" font-size=\"", FONT_SIZE), ("\" textLength=\"", length),
                    ])?;
                    svg.write_str("\" lengthAdjust=\"spacingAndGlyphs\" fill=\"#222\">")?;
                    line.write_text(svg)?;
                    writeln!(svg, "</text>")?;
                    n = n.saturating_add(1);
                }
            }
            numbers.write_fields(svg, [("<text x=\"", rect.x[0] + 2.25), ("\" y=\"", rect.y[0] + 9.0)])?;
            write!(svg, "\" fill=\"{color}\">")?;
            numbers.write_size(svg, size.x)?;
            svg.write_str(" × ")?;
            numbers.write_size(svg, size.y)?;
            svg.write_str("</text>\n")?;
            Ok(next)
        })?;
        writeln!(svg, "</svg>")
    }

    fn svg_string(&self, text: impl Fn(&T) -> &str) -> String {
        // Each visible node emits a rectangle and its size label. Use the measured count
        // only while it is current; a structural change may have hidden a whole subtree.
        let visible = if self.layout_data.pending_full_solve.is_none() {
            self.layout_data.n_nodes_solved as usize
        } else {
            0
        };
        let mut svg = SvgString(String::new());
        // About 240 bytes of markup per node plus the header. A failed estimate
        // leaves the String free to grow as individual tags are written.
        let _ = svg.0.try_reserve_exact(visible.saturating_mul(240).saturating_add(256));
        if self.write_svg_inner(&mut svg, text).is_err() {
            svg.0.clear();
            let _ = svg.write_str("<svg xmlns=\"http://www.w3.org/2000/svg\"/>\n");
        }
        svg.0
    }

    /// Writes the published layout rectangles to a caller-provided buffer or formatter.
    pub fn write_svg(&self, svg: &mut (impl Write + ?Sized)) -> fmt::Result {
        self.write_svg_inner(svg, |_| "")
    }

    /// Draws an SVG image representing the layout rectangles from the last `solve_layout()`.
    pub fn to_svg(&self) -> String {
        self.svg_string(|_| "")
    }
}

struct SvgString(String);

impl Write for SvgString {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        // Reserve before appending so output size or allocation failure is a write error.
        self.0.try_reserve(text.len()).map_err(|_| fmt::Error)?;
        self.0.push_str(text);
        Ok(())
    }
}

impl<T: AsRef<str>> LayoutTree<T> {
    /// Writes the published layout rectangles and their text to a caller-provided buffer or formatter.
    pub fn write_svg_with_text(&self, svg: &mut (impl Write + ?Sized)) -> fmt::Result {
        self.write_svg_inner(svg, |text| text.as_ref())
    }

    /// Draws an SVG image representing the layout from the last `solve_layout()`.
    ///
    /// The text will only have the correct dimensions if [`measure_monospace_text()`] is used as the measurement function.
    pub fn to_svg_with_text(&self) -> String {
        self.svg_string(|text| text.as_ref())
    }
}

/// Each line borrows its original UTF-8 span. Its width counts one space between words.
struct WrappedLine<'text> {
    source: &'text str,
    width_in_chars: usize,
    single_spaces: bool,
    ascii: bool,
    #[cfg(target_arch = "x86_64")]
    mixed: bool,
    verbatim: bool,
}

impl WrappedLine<'_> {
    fn write_text(&self, svg: &mut (impl Write + ?Sized)) -> fmt::Result {
        if self.verbatim {
            return svg.write_str(self.source);
        }
        if self.single_spaces {
            return write_escaped(svg, self.source);
        }
        #[cfg(target_arch = "x86_64")]
        if self.mixed && let Some(words) = MixedWords::<false>::new(self.source) {
            return write_words(svg, self.source, words.map(|(span, _)| span));
        }
        if self.ascii {
            write_words(svg, self.source, AsciiWords::new(self.source.as_bytes()))
        } else {
            let mut words = self.source.split_whitespace();
            if let Some(first) = words.next() { write_escaped(svg, first)?; }
            for word in words {
                svg.write_char(' ')?;
                write_escaped(svg, word)?;
            }
            Ok(())
        }
    }
}

fn word_span(source: &str, word: &str) -> Option<Range<usize>> {
    let start = word.as_ptr().addr().checked_sub(source.as_ptr().addr())?;
    let end = start.checked_add(word.len())?;
    (end <= source.len()).then_some(start..end)
}

fn write_words(
    svg: &mut (impl Write + ?Sized), source: &str, mut words: impl Iterator<Item = Range<usize>>,
) -> fmt::Result {
    let Some(first) = words.next() else { return Ok(()) };
    let (mut start, mut end) = (first.start, first.end);
    for word in words {
        // Keep one borrowed span across separators that already need no edits.
        if !separated_by_space(source.as_bytes(), end, word.start) {
            write_escaped(svg, source.get(start..end).ok_or(fmt::Error)?)?;
            svg.write_char(' ')?;
            start = word.start;
        }
        end = word.end;
    }
    write_escaped(svg, source.get(start..end).ok_or(fmt::Error)?)
}

fn wrapped_lines(text: &str, wrap_width: Option<f32>) -> impl Iterator<Item = WrappedLine<'_>> {
    let max = max_line_chars(wrap_width);
    #[cfg(target_arch = "x86_64")]
    let plain = if text.len() >= 32 && text.len() <= max {
        let trimmed = text.trim_matches(' ');
        plain_line(trimmed).map(|(chars, needs_escaping)| (trimmed, chars, needs_escaping))
    } else {
        None
    };
    #[cfg(not(target_arch = "x86_64"))]
    let plain: Option<(&str, usize, bool)> = None;
    let ascii = plain.is_none() && text.is_ascii();
    #[cfg(target_arch = "x86_64")]
    let (mut mixed_words, unicode_text) = if !ascii && plain.is_none() && text.len() >= 128 {
        // Dense Unicode separators favor the scalar splitter. ASCII indentation
        // has no effect on the sample.
        let separators = text.chars().take(8)
            .filter(|ch| !ch.is_ascii() && ch.is_whitespace()).count();
        if separators >= 4 {
            (None, text.trim())
        } else {
            (MixedWords::<true>::new(text), text)
        }
    } else {
        (None, text)
    };
    #[cfg(target_arch = "x86_64")]
    let mixed = mixed_words.is_some();
    #[cfg(not(target_arch = "x86_64"))]
    let unicode_text = text;
    let mut ascii_words = AsciiWords::new(text.as_bytes());
    let mut unicode_words = unicode_text.split_whitespace();
    let mut words = move || {
        #[cfg(target_arch = "x86_64")]
        if let Some(words) = &mut mixed_words {
            let (span, width) = words.next()?;
            return Some(WordSpan { start: span.start, end: span.end, width });
        }
        if ascii {
            let word = ascii_words.next()?;
            let width = word.end.saturating_sub(word.start);
            Some(WordSpan { start: word.start, end: word.end, width })
        } else {
            let word = unicode_words.next()?;
            let span = word_span(text, word)?;
            Some(WordSpan { start: span.start, end: span.end, width: word.chars().count() })
        }
    };
    let mut pending = None;
    let mut after = 0;
    let mut yielded = false;
    std::iter::from_fn(move || {
        if let Some((source, chars, needs_escaping)) = plain {
            if std::mem::replace(&mut yielded, true) { return None; }
            return Some(WrappedLine {
                source,
                width_in_chars: chars,
                single_spaces: true,
                ascii: false,
                #[cfg(target_arch = "x86_64")]
                mixed: false,
                verbatim: !needs_escaping,
            });
        }
        let (line, single_spaces) = next_line(text.as_bytes(), max, after, &mut words, &mut pending)?;
        after = line.end;
        Some(WrappedLine {
            source: text.get(line.start..line.end)?,
            width_in_chars: line.width,
            single_spaces,
            ascii,
            #[cfg(target_arch = "x86_64")]
            mixed,
            verbatim: false,
        })
    })
}

/// For ASCII text that needs no wrapping or whitespace normalization, detect
/// whether it can be emitted directly or still needs entity escaping.
#[cfg(target_arch = "x86_64")]
fn plain_ascii_line(bytes: &[u8]) -> Option<bool> {
    use std::arch::x86_64::*;

    let last = bytes.last_chunk::<16>()?;
    if last[15] == b' ' { return None; }
    let (prefix, tail) = partition_windows::<16>(bytes, false);
    let mut rest = prefix;
    // SAFETY: SSE2 is available on x86-64, and every load uses a complete array.
    unsafe {
        let space = _mm_set1_epi8(b' ' as i8);
        let amp = _mm_set1_epi8(b'&' as i8);
        let lt = _mm_set1_epi8(b'<' as i8);
        let bias = _mm_set1_epi8((b'\t' ^ 0x80) as i8);
        let control_limit = _mm_set1_epi8(i8::MIN + (b'\r' - b'\t' + 1) as i8);
        let mut specials = _mm_setzero_si128();
        let mut previous_space = 1u32;
        let mut scan = |block: &[u8; 16], count: usize| {
            let value = load_sse2(block);
            // The signed bias identifies the ASCII whitespace controls 9–13.
            let controls = _mm_cmpgt_epi8(control_limit, _mm_sub_epi8(value, bias));
            if _mm_movemask_epi8(_mm_or_si128(value, controls)) != 0 { return None; }
            let spaces = tail_mask16(_mm_movemask_epi8(_mm_cmpeq_epi8(value, space)) as u16, count);
            previous_space = single_space_end(u32::from(spaces), previous_space, count)?;
            specials = _mm_or_si128(specials, _mm_or_si128(_mm_cmpeq_epi8(value, amp), _mm_cmpeq_epi8(value, lt)));
            Some(())
        };
        while let Some((block, _)) = take_full_window::<16>(&mut rest, prefix.len()) {
            scan(block.first_chunk()?, 16)?;
        }
        // Only the space transitions must exclude any overlap with the preceding block.
        if !tail.is_empty() { scan(last, tail.len())?; }
        Some(_mm_movemask_epi8(specials) != 0)
    }
}

#[cfg(target_arch = "x86_64")]
fn plain_line(text: &str) -> Option<(usize, bool)> {
    if text.len() >= 96 && text_avx2_supported(TextAvx2::AsciiOrSvg) {
        // SAFETY: The feature detector checks both the CPU and operating system.
        return unsafe { plain_line_avx2(text) };
    }
    if !text.as_bytes().first()?.is_ascii() {
        return None;
    }
    plain_ascii_line(text.as_bytes()).map(|needs_escaping| (text.len(), needs_escaping))
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn plain_line_avx2(text: &str) -> Option<(usize, bool)> {
    use std::arch::x86_64::*;

    const WIDTH: usize = 32;
    let bytes = text.as_bytes();
    let last = bytes.last_chunk::<WIDTH>()?;
    if last[WIDTH - 1] == b' ' {
        return None;
    }
    let (prefix, tail) = partition_windows::<WIDTH>(bytes, false);
    let mut rest = prefix;
    let space = _mm256_set1_epi8(b' ' as i8);
    let amp = _mm256_set1_epi8(b'&' as i8);
    let lt = _mm256_set1_epi8(b'<' as i8);
    let bias = _mm256_set1_epi8((b'\t' ^ 0x80) as i8);
    let control_limit = _mm256_set1_epi8(i8::MIN + (b'\r' - b'\t' + 1) as i8);
    let mut specials = _mm256_setzero_si256();
    let mut previous_space = 1u32;
    let mut width_in_chars = text.len();
    let mut scan = |block: &[u8; WIDTH], count: usize, base: usize| {
        let value = load_avx(block);
        let controls = _mm256_cmpgt_epi8(control_limit, _mm256_sub_epi8(value, bias));
        let exceptional = _mm256_movemask_epi8(_mm256_or_si256(value, controls)) as u32;
        if exceptional != 0 {
            let high = _mm256_movemask_epi8(value) as u32;
            if exceptional != high {
                return None;
            }
            let remaining_lanes = active_tail32(count);
            let continuation = _mm256_movemask_epi8(_mm256_cmpgt_epi8(_mm256_set1_epi8(-64), value)) as u32;
            width_in_chars = width_in_chars.checked_sub((continuation & remaining_lanes).count_ones() as usize)?;
            // Non-ASCII Unicode whitespace starts with C2 or E1–E3. Decode
            // only those candidates and count all UTF-8 continuation bytes.
            let two_bytes = _mm256_cmpeq_epi8(value, _mm256_set1_epi8(0xc2_u8 as i8));
            let biased = _mm256_sub_epi8(value, _mm256_set1_epi8(0x61));
            let three_bytes = _mm256_cmpgt_epi8(_mm256_set1_epi8(-125), biased);
            let possible_spaces = _mm256_movemask_epi8(_mm256_or_si256(two_bytes, three_bytes)) as u32 & remaining_lanes;
            if possible_spaces != 0 && contains_unicode_whitespace(bytes, base, possible_spaces) { return None; }
        }
        let spaces = tail_mask32(_mm256_movemask_epi8(_mm256_cmpeq_epi8(value, space)) as u32, count);
        previous_space = single_space_end(spaces, previous_space, count)?;
        let entities = _mm256_or_si256(_mm256_cmpeq_epi8(value, amp), _mm256_cmpeq_epi8(value, lt));
        specials = _mm256_or_si256(specials, entities);
        Some(())
    };
    while let Some((block, base)) = take_full_window::<WIDTH>(&mut rest, prefix.len()) {
        scan(block.first_chunk()?, WIDTH, base)?;
    }
    // Only new lanes participate in the space transitions and Unicode decoding for an overlapping tail.
    if !tail.is_empty() {
        scan(last, tail.len(), bytes.len().checked_sub(WIDTH)?)?;
    }
    Some((width_in_chars, _mm256_movemask_epi8(specials) != 0))
}

#[cfg(target_arch = "x86_64")]
#[inline(never)]
fn contains_unicode_whitespace(bytes: &[u8], base: usize, mut leading: u32) -> bool {
    while leading != 0 {
        let offset = pop_lane::<NativeBitLanes>(&mut leading);
        if unicode_separator_width(bytes, base.saturating_add(offset as usize)) != 0 {
            return true;
        }
    }
    false
}

fn write_escaped(svg: &mut (impl Write + ?Sized), text: &str) -> fmt::Result {
    let mut start = 0;
    while let Some(index) = next_svg_escape(text.as_bytes(), start) {
        let prefix = text.get(start..index).ok_or(fmt::Error)?;
        let entity = match text.as_bytes().get(index) {
            Some(b'&') => "&amp;",
            Some(b'<') => "&lt;",
            _ => return Err(fmt::Error),
        };
        svg.write_str(prefix)?;
        svg.write_str(entity)?;
        start = index.checked_add(1).ok_or(fmt::Error)?;
    }
    svg.write_str(text.get(start..).ok_or(fmt::Error)?)
}

fn node_color(i: NodeKey) -> SvgColor {
    use slotmap::Key;
    let mut hash = i.data().as_ffi().wrapping_add(0x9e37_79b9_7f4a_7c15);
    hash = (hash ^ (hash >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    hash = (hash ^ (hash >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    hash ^= hash >> 31;
    SvgColor::from_hash(hash)
}

struct SvgColor {
    bytes: [u8; 18],
    start: usize,
}

impl SvgColor {
    #[inline]
    fn from_hash(hash: u64) -> Self {
        let (bytes, start) = svg_color_bytes(hash);
        Self { bytes, start }
    }

    fn as_str(&self) -> &str {
        let suffix = svg_color_suffix(&self.bytes, self.start);
        // SAFETY: svg_color_bytes establishes the suffix's verified ASCII precondition.
        unsafe { std::str::from_utf8_unchecked(suffix) }
    }
}

// Coordinates, line lengths and dimensions recur across tags. Cache their exact Display
// spellings for this render. Using the bits as keys keeps -0.0 distinct from +0.0.
struct SvgNumbers([(u32, ArrayString<SVG_NUMBER_CAPACITY>); 1 << SVG_NUMBER_CACHE_BITS]);

impl SvgNumbers {
    fn new() -> Self {
        Self([(0, ArrayString::new()); 1 << SVG_NUMBER_CACHE_BITS])
    }

    fn number(&mut self, value: f32) -> Option<&str> {
        let bits = value.to_bits();
        let (key, text) = self.0.get_mut(svg_number_index(bits))?;
        if *key != bits || text.is_empty() {
            text.clear();
            if write_svg_number(text, value).is_err() {
                text.clear();
                return None;
            }
            *key = bits;
        }
        Some(text.as_str())
    }

    fn write_number(&mut self, svg: &mut (impl Write + ?Sized), value: f32) -> fmt::Result {
        if let Some(text) = self.number(value) {
            svg.write_str(text)
        } else {
            write_svg_number(svg, value)
        }
    }

    fn write_fields<const N: usize>(&mut self, svg: &mut (impl Write + ?Sized), fields: [(&str, f32); N]) -> fmt::Result {
        for (prefix, value) in fields {
            svg.write_str(prefix)?;
            self.write_number(svg, value)?;
        }
        Ok(())
    }

    fn write_size(&mut self, svg: &mut (impl Write + ?Sized), size: Size) -> fmt::Result {
        let (value, suffix) = match size {
            Size::Fill => return svg.write_str("fill"),
            Size::FitContent => return svg.write_str("fit"),
            Size::Auto => return svg.write_str("auto"),
            Size::Pixels(value) => (value, "px"),
            Size::Frac(value) => (value, "fr"),
            Size::AspectRatio(value) => {
                svg.write_str("ratio ")?;
                (value, "")
            }
        };
        self.write_number(svg, (value * 100.0).round() / 100.0)?;
        svg.write_str(suffix)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn plain_unicode_lines_keep_width_and_reject_whitespace() {
        if !is_x86_feature_detected!("avx2") {
            return;
        }
        let whitespace = (128..=0x10ffff).filter_map(char::from_u32).filter(|ch| ch.is_whitespace());
        for character in whitespace.chain(['α', '字', '🦀', '\u{00a1}', '\u{1681}', '\u{200b}', '\u{3001}']) {
            for position in [0, 15, 16, 30, 31, 32, 33, 95, 96, 126, 127, 128, 129] {
                let mut text = "a".repeat(129);
                text.insert(position, character);
                text.push_str("&<");
                let expected = (!character.is_whitespace()).then_some((text.chars().count(), true));
                assert_eq!(plain_line(&text), expected, "{character:?} at {position}");
            }
        }
    }

    #[test]
    fn svg_colors_match_the_decimal_display() {
        for i in 0..4_096u64 {
            let hash = i.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let hue = hash % 360;
            let saturation = 45 + (hash >> 16) % 25;
            let lightness = 32 + (hash >> 32) % 14;
            assert_eq!(
                SvgColor::from_hash(hash).as_str(),
                format!("hsl({hue}, {saturation}%, {lightness}%)"),
            );
        }
    }

    #[test]
    fn svg_number_cache_preserves_display_across_evictions() {
        let mut numbers = SvgNumbers::new();
        for exponent in 0..=255u32 {
            for fraction in [0, 1, 0x0012_3456, 0x007f_ffff] {
                for sign in [0, 1 << 31] {
                    let value = f32::from_bits(sign | exponent << 23 | fraction);
                    let expected = value.to_string();
                    assert_eq!(numbers.number(value), Some(expected.as_str()));
                    assert_eq!(numbers.number(value), Some(expected.as_str()));
                }
            }
        }
    }

    #[test]
    fn svg_propagates_a_stream_failure() {
        struct LimitedWriter(usize);
        impl fmt::Write for LimitedWriter {
            fn write_str(&mut self, text: &str) -> fmt::Result {
                self.0 = self.0.checked_sub(text.len()).ok_or(fmt::Error)?;
                Ok(())
            }
        }
        let tree = LayoutTree::<&str>::new();
        let len = tree.to_svg_with_text().len();
        for limit in [0, len / 2, len - 1] {
            assert!(tree.write_svg_with_text(&mut LimitedWriter(limit)).is_err());
        }
        assert!(tree.write_svg_with_text(&mut LimitedWriter(len)).is_ok());
    }

    #[test]
    fn borrowed_lines_and_ascii_measurement_agree_across_chunk_boundaries() {
        let id = LayoutTree::<()>::new().root();
        // Include every ASCII byte, in particular vertical tab and the non-whitespace controls.
        let input: String = (0..=127u8).chain((0..=127u8).rev()).map(char::from).collect();
        for end in 0..=input.len() {
            let mut text = &input[..end];
            for width in [None, Some(0.0), Some(12.0 * CHAR_WIDTH)] {
                let expected = measure_word_widths(text.split_whitespace().map(str::len), width);
                let measured = measure_monospace_text(id.clone(), Some(&mut text), width);
                assert_eq!(expected, measured);
                let lines = wrapped_lines(text, width);
                let mut count = 0;
                let mut longest = 0;
                for line in lines {
                    let normalized = line.source.split_whitespace().collect::<Vec<_>>().join(" ");
                    assert_eq!(normalized.len(), line.width_in_chars);
                    count += 1;
                    longest = longest.max(line.width_in_chars);
                }
                assert_eq!(measured, Xy::new(longest as f32 * CHAR_WIDTH, count as f32 * LINE_HEIGHT));
            }
        }
    }

    #[test]
    fn ascii_svg_lines_match_the_unicode_splitter_across_vector_boundaries() {
        let text = "  &first\tword\x0b<second> \nword \r\x0clast&\t<end>  longword_without_spaces  ";
        for end in 0..=text.len() {
            let input = &text[..end];
            for float_width in [None, Some(0.0), Some(8.0 * CHAR_WIDTH), Some(15.0 * CHAR_WIDTH)] {
                let max = max_line_chars(float_width);
                let mut reference = vec![String::new()];
                let mut width = 0;
                for word in input.split_whitespace() {
                    if width != 0 && width + 1 + word.len() > max {
                        reference.push(String::new());
                        width = 0;
                    }
                    let line = reference.last_mut().unwrap();
                    if width != 0 {
                        line.push(' ');
                        width += 1;
                    }
                    width += word.len();
                    line.push_str(&word.replace('&', "&amp;").replace('<', "&lt;"));
                }
                reference.retain(|line| !line.is_empty());
                let actual: Vec<_> = wrapped_lines(input, float_width).map(|line| {
                    let mut output = String::new();
                    line.write_text(&mut output).unwrap();
                    output
                }).collect();
                assert_eq!(actual, reference);
            }
        }
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn ascii_line_scan_handles_space_and_entity_masks_across_blocks() {
        for len in [16, 17, 31, 32, 33, 47, 48, 49, 95, 96, 97, 111, 112, 127, 128, 129] {
            let mut bytes = [b'a'; 129];
            for index in 0..len {
                for byte in [b' ', b'\t', b'\n', b'\x0b', b'\x0c', b'\r', b'&', b'<', 0, 0x7f, 0x80, 0xff] {
                    bytes[index] = byte;
                    let expected = match byte {
                        b' ' if index == 0 || index == len - 1 => None,
                        b'\t'..=b'\r' | 0x80..=0xff => None,
                        b'&' | b'<' => Some(true),
                        _ => Some(false),
                    };
                    assert_eq!(plain_ascii_line(&bytes[..len]), expected, "{len}: {index} {byte}");
                }
                bytes[index] = b'a';
            }
            for index in 0..len - 1 {
                bytes[index..=index + 1].fill(b' ');
                assert_eq!(plain_ascii_line(&bytes[..len]), None, "{len}: {index}");
                bytes[index..=index + 1].fill(b'a');
            }
        }
    }

    #[test]
    fn one_line_svg_preserves_text_after_trimming_and_escaping() {
        for text in [
            " a normalized ASCII line with an ordinary trailing space ",
            " an escaped & label with a < character around the vector boundary ",
            " another normal line until an accent is encountered here: λ ",
            " a regular label until a mixed\x0b separator is encountered ",
            "                                ",
        ] {
            let expected = text.split_whitespace().collect::<Vec<_>>().join(" ");
            let expected = expected.replace('&', "&amp;").replace('<', "&lt;");
            let mut lines = wrapped_lines(text, Some((text.len() as f32 + 1.0) * CHAR_WIDTH));
            let mut actual = String::new();
            if let Some(line) = lines.next() {
                line.write_text(&mut actual).unwrap();
            }
            assert_eq!(actual, expected);
            assert!(lines.next().is_none());
        }
    }

    #[test]
    fn svg_lines_preserve_normalized_text_and_xml_entities() {
        let text = "\u{a0}λ< \t &猫\u{200a}dog\u{b} x&<  ";
        for (width, expected) in [
            (None, "λ&lt; &amp;猫 dog x&amp;&lt;\n"),
            (Some(5.0 * CHAR_WIDTH), "λ&lt; &amp;猫\ndog\nx&amp;&lt;\n"),
            (Some(0.0), "λ&lt;\n&amp;猫\ndog\nx&amp;&lt;\n"),
        ] {
            let mut svg = String::new();
            for line in wrapped_lines(text, width) {
                line.write_text(&mut svg).unwrap();
                svg.push('\n');
            }
            assert_eq!(svg, expected);
        }
    }

    #[test]
    fn svg_streams_normalized_and_escaped_borrowed_text_in_paint_order() {
        let text = String::from("  λ&<  \t 猫\u{2003}longword  ");
        let mut tree = LayoutTree::new();
        let params = LayoutParams {
            text: TextContent::Wrapping,
            size: Xy::new(Size::Pixels(5.0 * CHAR_WIDTH), Size::FitContent),
            ..LayoutParams::DEFAULT
        };
        let root = tree.root();
        tree.add_node_with_context(&root, params, "painted last").unwrap();
        tree.add_node_with_context(&root, params, text.as_str()).unwrap();
        tree.add_node_with_context(&root, LayoutParams { disabled: true, ..params }, "hidden").unwrap();
        tree.solve_layout_with_measure(Xy::new_symm(120.0), measure_monospace_text);
        tree.add_node_with_context(&root, params, "unplaced").unwrap();
        let mut svg = String::from("prefix");
        tree.write_svg_with_text(&mut svg).unwrap();
        assert_eq!(&svg["prefix".len()..], tree.to_svg_with_text());
        let short = svg.find(">λ&amp;&lt; 猫</text>").unwrap();
        let long = svg.find(">longword</text>").unwrap();
        let last = svg.find(">painted</text>").unwrap();
        assert!(short < long && long < last);
        assert!(!svg.contains("hidden"));
        assert!(!svg.contains("unplaced"));
    }

}
