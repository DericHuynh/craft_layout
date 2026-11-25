//! Text widths, SIMD window arithmetic, and bounds used to render SVG text.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(any(target_arch = "x86_64", verus_keep_ghost))]
#[path = "text_boundaries.rs"]
pub(crate) mod boundaries;

#[cfg(all(target_arch = "x86_64", not(verus_keep_ghost)))]
#[path = "text_native.rs"]
pub(crate) mod native;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const LANES: usize = 32;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const WINDOW: usize = 34;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const MIN_PADDED: usize = 12;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub(crate) enum TextAvx2 {
    AsciiOrSvg,
    AsciiWrap,
    UnicodeWrap,
}

/// Permission to enter AVX2 code depends on the instructions that entry uses.
/// The reports are the CPU and operating-system checks returned by std.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(allowed =>
    ensures allowed == (avx2 && match entry {
        TextAvx2::AsciiOrSvg => true,
        TextAvx2::AsciiWrap => popcnt,
        TextAvx2::UnicodeWrap => popcnt && bmi2,
    }),
    no_unwind
))]
pub(crate) fn permits_text_avx2(entry: TextAvx2, avx2: bool, popcnt: bool, bmi2: bool) -> bool {
    avx2 && match entry {
        TextAvx2::AsciiOrSvg => true,
        TextAvx2::AsciiWrap => popcnt,
        TextAvx2::UnicodeWrap => popcnt && bmi2,
    }
}

#[cfg(all(target_arch = "x86_64", not(verus_keep_ghost)))]
#[inline(always)]
pub(crate) fn text_avx2_supported(entry: TextAvx2) -> bool {
    let avx2 = std::arch::is_x86_feature_detected!("avx2")
        && std::arch::is_x86_feature_detected!("avx");
    let popcnt = avx2 && !matches!(entry, TextAvx2::AsciiOrSvg)
        && std::arch::is_x86_feature_detected!("popcnt");
    let bmi2 = popcnt && matches!(entry, TextAvx2::UnicodeWrap)
        && std::arch::is_x86_feature_detected!("bmi2");
    permits_text_avx2(entry, avx2, popcnt, bmi2)
}

/// Partition the usable prefix into full blocks. Scans that always finish
/// with an overlapping window reserve the last input byte for that window.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires WIDTH > 0,
    ensures out.0.len() % WIDTH == 0, out.0.len() + out.1.len() == bytes.len(),
        out.0@ + out.1@ == bytes@,
        reserve_last && bytes.len() > 0 ==> 1 <= out.1.len() <= WIDTH,
        !reserve_last ==> out.1.len() < WIDTH,
    no_unwind
))]
pub(crate) fn partition_windows<const WIDTH: usize>(bytes: &[u8], reserve_last: bool) -> (&[u8], &[u8]) {
    let used = if reserve_last { bytes.len().saturating_sub(1) } else { bytes.len() };
    let blocks = used / WIDTH;
    #[cfg(verus_keep_ghost)]
    proof! {
        use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_fundamental_div_mod_converse, lemma_mod_pos_bound};
        let used_bytes = used as int;
        let step = WIDTH as int;
        let full_bytes = (blocks as int) * step;
        lemma_fundamental_div_mod(used_bytes, step);
        vstd::arithmetic::mul::lemma_mul_is_commutative(step, blocks as int);
        lemma_mod_pos_bound(used_bytes, step);
        assert(used_bytes == full_bytes + used_bytes % step);
        lemma_fundamental_div_mod_converse(full_bytes, step, blocks as int, 0);
    }
    bytes.split_at(blocks * WIDTH)
}

/// Borrow the next complete native load and its starting byte in the prefix.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires WIDTH > 0, old(rest).len() <= total,
    ensures final(rest).len() <= total,
        match out {
            Some((block, base)) => block.len() == WIDTH
                && base + old(rest).len() == total
                && base + WIDTH + final(rest).len() == total
                && block@ + final(rest)@ == old(rest)@,
            None => final(rest)@ == old(rest)@ && old(rest).len() < WIDTH,
        },
    no_unwind
))]
pub(crate) fn take_full_window<'text, const WIDTH: usize>(
    rest: &mut &'text [u8], total: usize,
) -> Option<(&'text [u8], usize)> {
    if rest.len() < WIDTH { return None; }
    let base = total - rest.len();
    let (block, next) = rest.split_at(WIDTH);
    *rest = next;
    Some((block, base))
}

/// The width of two adjacent words after normalizing the separator to one space.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns joined_width(current, next), no_unwind))]
pub(crate) fn joined_width(current: usize, next: usize) -> usize {
    current.saturating_add(1).saturating_add(next)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct LineWidths {
    pub count: usize,
    pub longest: usize,
    pub current: usize,
    pub max: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.count == 0, out.longest == 0, out.current == 0, out.max == max,
    no_unwind
))]
pub(crate) fn line_widths(max: usize) -> LineWidths {
    LineWidths { count: 0, longest: 0, current: 0, max }
}

impl LineWidths {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).max == old(self).max,
            final(self).longest == vstd::math::max(old(self).longest as int, final(self).current as int),
            if old(self).current == 0 || joined_width(old(self).current, width) > old(self).max {
                final(self).current == width
                    && final(self).count == vstd::math::min(usize::MAX as int, old(self).count + 1)
            } else {
                final(self).current == joined_width(old(self).current, width)
                    && final(self).count == old(self).count
            },
        no_unwind
    ))]
    pub(crate) fn add_word(&mut self, width: usize) {
        let joined = joined_width(self.current, width);
        if self.current == 0 || joined > self.max {
            self.count = self.count.saturating_add(1);
            self.current = width;
        } else {
            self.current = joined;
        }
        self.longest = if self.longest < self.current { self.current } else { self.longest };
    }

    /// The vector scan can append all completed words together when they fit.
    /// It receives counts for at most one 32-lane vector and a carried word.
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(fits =>
        requires letters <= 32, 1 <= words <= 32,
        ensures final(self).max == old(self).max,
            fits ==> {
                let first = if old(self).current == 0 { 1int } else { 0 };
                &&& final(self).current == vstd::math::min(usize::MAX as int,
                    old(self).current + carry + letters + words - first)
                &&& final(self).count == vstd::math::min(usize::MAX as int, old(self).count + first)
                &&& final(self).longest == vstd::math::max(old(self).longest as int, final(self).current as int)
            },
            !fits ==> final(self).count == old(self).count && final(self).current == old(self).current
                && final(self).longest == old(self).longest,
        no_unwind
    ))]
    pub(crate) fn append_batch(&mut self, letters: u32, carry: usize, words: u32) -> bool {
        let first = if self.current == 0 { 1 } else { 0 };
        let added = (letters + words - first) as usize;
        let joined = self.current.saturating_add(carry).saturating_add(added);
        if joined > self.max {
            return false;
        }
        self.count = self.count.saturating_add(first as usize);
        self.current = joined;
        self.longest = if self.longest < joined { joined } else { self.longest };
        true
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns ascii_space(byte), no_unwind))]
pub(crate) fn ascii_space(byte: u8) -> bool {
    // Unicode White_Space includes vertical tab alongside the ASCII controls.
    byte == b' ' || b'\t' <= byte && byte <= b'\r'
}

/// Reduce at most one portable block of adjacent ASCII pairs.
#[cfg(any(not(target_arch = "x86_64"), verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires preceding.len() <= 64, following.len() <= 64,
    ensures out.1 <= out.0 <= following.len(), out.0 <= preceding.len(),
    no_unwind
))]
pub(crate) fn count_ascii_pairs(preceding: &[u8], following: &[u8]) -> (u8, u8) {
    let mut len = preceding.len();
    if following.len() < len { len = following.len(); }
    let mut chars = 0;
    let mut words = 0;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant words <= chars <= index <= len, len <= preceding.len(), len <= following.len(),
            len <= 64,
        decreases len - index,
    ))]
    while index < len {
        let is_text = !ascii_space(following[index]);
        chars += is_text as u8;
        words += (ascii_space(preceding[index]) && is_text) as u8;
        index += 1;
    }
    (chars, words)
}

/// The very short x86 path needs neither a vector load nor a UTF-8 scan.
#[cfg(any(target_arch = "x86_64", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires bytes.len() <= 3,
    ensures out.is_some() ==> out.unwrap() <= 2 * bytes.len(),
    no_unwind
))]
pub(crate) fn short_ascii_width(bytes: &[u8]) -> Option<usize> {
    let mut count = 0;
    let mut previous_space = true;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant count <= 2 * index, index <= bytes.len() <= 3,
        decreases bytes.len() - index,
    ))]
    while index < bytes.len() {
        let byte = bytes[index];
        if byte > 127 { return None; }
        let white = ascii_space(byte);
        if !white { count += 1 + previous_space as usize; }
        previous_space = white;
        index += 1;
    }
    Some(count.saturating_sub(1))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns is_continuation(byte), no_unwind))]
pub(crate) fn is_continuation(byte: u8) -> bool {
    0x80 <= byte && byte < 0xc0
}

/// Count one column per non-separator scalar. All UTF-8 continuation bytes
/// are skipped, since classification and width are both assigned to the lead.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.max == lines.max,
    no_unwind
))]
pub(crate) fn scan_scalar_words<const ASCII: bool>(bytes: &[u8], mut lines: LineWidths) -> LineWidths {
    let mut cursor = 0;
    let mut width = 0;
    #[cfg(verus_keep_ghost)]
    let max = lines.max;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant width <= cursor <= bytes.len(), lines.max == max,
        decreases bytes.len() - cursor,
    ))]
    while cursor < bytes.len() {
        let lead = bytes[cursor];
        if ASCII || !is_continuation(lead) {
            if ascii_space(lead) || (!ASCII && lead >= 0xc2 && unicode_separator_width(bytes, cursor) != 0) {
                if width != 0 {
                    lines.add_word(width);
                    width = 0;
                }
            } else {
                width += 1;
            }
        }
        cursor += 1;
    }
    if width != 0 { lines.add_word(width); }
    lines
}

/// Move from a byte position to its next UTF-8 character boundary. On a
/// string the end of the byte slice is itself a boundary.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires start <= bytes.len(),
    ensures start <= out <= bytes.len(),
        out < bytes.len() ==> !is_continuation(bytes@[out as int]),
        forall |i: int| start <= i < out ==> is_continuation(#[trigger] bytes@[i]),
    no_unwind
))]
pub(crate) fn next_char_boundary(bytes: &[u8], start: usize) -> usize {
    let mut cursor = start;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= cursor <= bytes.len(),
            forall |i: int| start <= i < cursor ==> is_continuation(#[trigger] bytes@[i]),
        decreases bytes.len() - cursor,
    ))]
    while cursor < bytes.len() && is_continuation(bytes[cursor]) {
        #[cfg(verus_keep_ghost)]
        proof! { assert(is_continuation(bytes@[cursor as int])); }
        cursor += 1;
    }
    cursor
}

/// Whether two byte spans are separated by exactly one space.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (end < bytes.len() && next == end + 1 && bytes@[end as int] == b' '),
    no_unwind
))]
pub(crate) fn separated_by_space(bytes: &[u8], end: usize, next: usize) -> bool {
    end < bytes.len() && next == end + 1 && bytes[end] == b' '
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns svg_escape_byte(byte), no_unwind))]
pub(crate) fn svg_escape_byte(byte: u8) -> bool {
    byte == b'&' || byte == b'<'
}

/// Subtracting one per byte sets a high bit if a zero byte is present.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures forall |lane: u64| lane < 8 && out == 0 ==> #[trigger] ((word >> (8u64 * lane)) as u8) != 0,
    no_unwind
))]
fn zero_byte_high_bits(word: u64) -> u64 {
    let out = word.wrapping_sub(0x0101_0101_0101_0101) & !word & 0x8080_8080_8080_8080;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |lane: u64| lane < 8 && out == 0 implies #[trigger] ((word >> (8u64 * lane)) as u8) != 0 by {
            assert(lane < 8 && out == 0 ==> ((word >> (8u64 * lane)) as u8) != 0) by(bit_vector)
                requires out == word.wrapping_sub(0x0101_0101_0101_0101u64) & !word & 0x8080_8080_8080_8080u64;
        }
    }
    out
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires at + 8 <= bytes.len(),
    ensures !out ==> forall |i: int| at <= i < at + 8 ==> !svg_escape_byte(#[trigger] bytes@[i]),
    no_unwind
))]
fn escape_in_eight(bytes: &[u8], at: usize) -> bool {
    // Pack in little-endian order using byte loads. This also works when the
    // source is unaligned, without adding an unsafe read.
    let block = bytes.split_at(at).1.split_at(8).0;
    let [b0, b1, b2, b3, b4, b5, b6, b7] = [block[0], block[1], block[2], block[3], block[4], block[5], block[6], block[7]];
    let word = (b0 as u64) | ((b1 as u64) << 8) | ((b2 as u64) << 16) | ((b3 as u64) << 24)
        | ((b4 as u64) << 32) | ((b5 as u64) << 40) | ((b6 as u64) << 48) | ((b7 as u64) << 56);
    let ampersand = word ^ 0x2626_2626_2626_2626;
    let less = word ^ 0x3c3c_3c3c_3c3c_3c3c;
    let ampersands = zero_byte_high_bits(ampersand);
    let lesses = zero_byte_high_bits(less);
    let out = (ampersands | lesses) != 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        if !out {
            assert(ampersands == 0 && lesses == 0) by(bit_vector) requires (ampersands | lesses) == 0;
            assert forall |i: int| at <= i < at + 8 implies !svg_escape_byte(#[trigger] bytes@[i]) by {
                let lane = (i - at) as u64;
                let byte = bytes@[i];
                assert(lane < 8);
                assert(lane == 0 && byte == b0 || lane == 1 && byte == b1 || lane == 2 && byte == b2 || lane == 3 && byte == b3
                    || lane == 4 && byte == b4 || lane == 5 && byte == b5 || lane == 6 && byte == b6 || lane == 7 && byte == b7);
                assert(((ampersand >> (8u64 * lane)) as u8) != 0);
                assert(((less >> (8u64 * lane)) as u8) != 0);
                assert(byte != b'&' && byte != b'<') by(bit_vector)
                    requires lane == 0 && byte == b0 || lane == 1 && byte == b1 || lane == 2 && byte == b2 || lane == 3 && byte == b3
                        || lane == 4 && byte == b4 || lane == 5 && byte == b5 || lane == 6 && byte == b6 || lane == 7 && byte == b7,
                        word == (b0 as u64) | ((b1 as u64) << 8) | ((b2 as u64) << 16) | ((b3 as u64) << 24)
                            | ((b4 as u64) << 32) | ((b5 as u64) << 40) | ((b6 as u64) << 48) | ((b7 as u64) << 56),
                        ampersand == word ^ 0x2626_2626_2626_2626u64,
                        less == word ^ 0x3c3c_3c3c_3c3c_3c3cu64,
                        ((ampersand >> (8u64 * lane)) as u8) != 0,
                        ((less >> (8u64 * lane)) as u8) != 0;
            }
        }
    }
    out
}

/// Find the next byte requiring an SVG entity. These ASCII bytes cannot be
/// part of a multibyte UTF-8 scalar.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires start <= bytes.len(),
    ensures match out {
        Some(found) => start <= found < bytes.len() && svg_escape_byte(bytes@[found as int])
            && forall |i: int| start <= i < found ==> !svg_escape_byte(#[trigger] bytes@[i]),
        None => forall |i: int| start <= i < bytes.len() ==> !svg_escape_byte(#[trigger] bytes@[i]),
    },
    no_unwind
))]
pub(crate) fn next_svg_escape(bytes: &[u8], start: usize) -> Option<usize> {
    let mut at = start;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= at <= bytes.len(),
            forall |i: int| start <= i < at ==> !svg_escape_byte(#[trigger] bytes@[i]),
        decreases bytes.len() - at,
    ))]
    while bytes.len() - at >= 8 {
        if escape_in_eight(bytes, at) { break; }
        at += 8;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= at <= bytes.len(),
            forall |i: int| start <= i < at ==> !svg_escape_byte(#[trigger] bytes@[i]),
        decreases bytes.len() - at,
    ))]
    while at < bytes.len() {
        if svg_escape_byte(bytes[at]) { return Some(at); }
        at += 1;
    }
    None
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const SVG_NUMBER_CACHE_BITS: u32 = 6;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(index =>
    ensures index < 64,
    no_unwind
))]
pub(crate) fn svg_number_index(bits: u32) -> usize {
    let hash = (bits ^ (bits >> 13)).wrapping_mul(0x9e37_79b9);
    let index = hash >> (u32::BITS - SVG_NUMBER_CACHE_BITS);
    #[cfg(verus_keep_ghost)]
    proof! { assert((hash >> 26u32) < 64u32) by(bit_vector); }
    index as usize
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(pair =>
    requires value < 100,
    ensures pair@[0] == b'0' + value / 10, pair@[1] == b'0' + value % 10,
        b'0' <= pair@[0] <= b'9', b'0' <= pair@[1] <= b'9',
    no_unwind
))]
fn decimal_pair(value: u8) -> [u8; 2] {
    [b'0' + value / 10, b'0' + value % 10]
}

/// The suffix at `start` is an ASCII HSL color with no leading hue zeros.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.1 <= 2,
        forall |j: int| 0 <= j < 18 ==> #[trigger] out.0@[j] <= 0x7f,
    no_unwind
))]
pub(crate) fn svg_color_bytes(hash: u64) -> ([u8; 18], usize) {
    let hue = (hash % 360) as u16;
    let saturation = (45 + (hash >> 16) % 25) as u8;
    let lightness = (32 + (hash >> 32) % 14) as u8;
    let mut bytes = [b'h', b's', b'l', b'(', b'0', b'0', b'0', b',', b' ', b'0', b'0', b'%', b',', b' ', b'0', b'0', b'%', b')'];
    bytes[4] = b'0' + (hue / 100) as u8;
    let hue_digits = decimal_pair((hue % 100) as u8);
    bytes[5] = hue_digits[0];
    bytes[6] = hue_digits[1];
    let saturation_digits = decimal_pair(saturation);
    bytes[9] = saturation_digits[0];
    bytes[10] = saturation_digits[1];
    let lightness_digits = decimal_pair(lightness);
    bytes[14] = lightness_digits[0];
    bytes[15] = lightness_digits[1];

    // Copy the prefix backwards, allowing the two ranges to overlap.
    let start = if hue < 10 { 2 } else if hue < 100 { 1 } else { 0 };
    let mut left = 4;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= 2, left <= 4,
            forall |j: int| 0 <= j < 18 ==> #[trigger] bytes@[j] <= 0x7f,
        decreases left,
    ))]
    while left != 0 {
        left -= 1;
        bytes[start + left] = bytes[left];
    }
    (bytes, start)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires start <= bytes.len(),
        forall |j: int| 0 <= j < bytes.len() ==> #[trigger] bytes@[j] <= 0x7f,
    ensures out@ == bytes@.subrange(start as int, bytes.len() as int),
        forall |j: int| 0 <= j < out.len() ==> #[trigger] out@[j] <= 0x7f,
    no_unwind
))]
pub(crate) fn svg_color_suffix(bytes: &[u8], start: usize) -> &[u8] {
    bytes.split_at(start).1
}

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

/// Advance the logical cursor and borrow the complete load, which can
/// overlap bytes already consumed when a partial window ends the input.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures match out {
        None => *final(cursor) == *old(cursor) && (*old(cursor) >= bytes.len() || bytes.len() < 16),
        Some((block, base, count)) => base == *old(cursor)
            && base + count == *final(cursor) <= bytes.len()
            && 1 <= count <= 16 && block.len() == 16,
    },
    no_unwind
))]
pub(crate) fn take_window16<'text>(bytes: &'text [u8], cursor: &mut usize) -> Option<(&'text [u8], usize, usize)> {
    let base = *cursor;
    let Some((start, count)) = window16(bytes.len(), base) else { return None; };
    let block = bytes.split_at(start).1.split_at(16).0;
    *cursor += count;
    Some((block, base, count))
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

/// Finish the SSE2 window after classifying ASCII and any Unicode separators.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires 1 <= count <= 16,
    ensures out.0 == spaces >> count, out.1 <= 1,
        out.2 as u32 <= ((1u32 << count) - 1) as u32,
    no_unwind
))]
pub(crate) fn transitions16(spaces: u32, previous_space: u16, count: usize) -> (u32, u16, u16) {
    let current = spaces as u16;
    let valid = low_lanes16(count);
    let transitions = (current ^ ((current << 1) | previous_space)) & valid;
    let previous = (current >> (count - 1)) & 1;
    let carried = spaces >> count;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(previous <= 1) by(bit_vector) requires previous == (current >> ((count - 1) as usize)) & 1;
        assert(transitions as u32 <= (1u32 << count) - 1u32) by(bit_vector)
            requires 1 <= count <= 16,
                valid == u16::MAX >> ((16 - count) as usize),
                transitions == (current ^ ((current << 1) | previous_space)) & valid;
    }
    (carried, previous, transitions)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(mask =>
    requires lane < 16, width <= 3,
    ensures mask == (((1u32 << width) - 1) as u32) << lane,
    no_unwind
))]
pub(crate) fn separator_lanes(lane: u32, width: u32) -> u32 {
    let end = 1u32 << width;
    #[cfg(verus_keep_ghost)]
    proof! { assert(end >= 1) by(bit_vector) requires width <= 3, end == 1u32 << width; }
    (end - 1) << lane
}

/// A UTF-8 line counts bytes minus the continuation bytes in that interval.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(width =>
    ensures width == if start <= end && skipped_before <= skipped_after
            && skipped_after - skipped_before <= end - start {
        Some((end - start - (skipped_after - skipped_before)) as usize)
    } else { None },
    no_unwind
))]
pub(crate) fn span_width(start: usize, end: usize, skipped_before: usize, skipped_after: usize) -> Option<usize> {
    let bytes = end.checked_sub(start)?;
    let continuations = skipped_after.checked_sub(skipped_before)?;
    bytes.checked_sub(continuations)
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

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns active_mixed_lanes(bytes), no_unwind))]
pub(crate) fn active_mixed_lanes(bytes: usize) -> usize {
    if bytes < LANES { bytes } else { LANES }
}

/// Keep two lookahead bytes where present, without assigning them active lanes.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires MIN_PADDED <= bytes.len() < WINDOW,
    ensures out.0 == active_mixed_lanes(bytes.len()),
        1 <= out.0 <= LANES,
        out.1 == u32::MAX >> ((LANES - out.0) as usize),
        final(padded)@.subrange(0, bytes.len() as int) == bytes@,
        forall |i: int| bytes.len() <= i < WINDOW ==> #[trigger] final(padded)[i] == old(padded)[i],
    no_unwind
))]
pub(crate) fn pad_mixed_tail(bytes: &[u8], padded: &mut [u8; WINDOW]) -> (usize, u32) {
    let count = active_mixed_lanes(bytes.len());
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

/// The native classifier counts only leading bytes in the active lanes.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait MixedBlockWidth {
    #[cfg_attr(verus_keep_ghost, verus_spec(width =>
        requires block.len() == WINDOW,
        ensures width <= LANES,
        no_unwind
    ))]
    fn measure_block(&mut self, block: &[u8], base: usize) -> usize;

    #[cfg_attr(verus_keep_ghost, verus_spec(width =>
        requires MIN_PADDED <= tail.len() < WINDOW,
        ensures width <= active_mixed_lanes(tail.len()),
        no_unwind
    ))]
    fn measure_tail(&mut self, tail: &[u8], base: usize) -> usize;
}

/// Full windows leave two lookahead bytes. A padded window consumes only its
/// valid lanes, then the cursor advances past any continuations to the first
/// scalar the caller still needs to measure.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.0 + out.1.len() <= bytes.len(), out.1.len() < WINDOW,
        out.1@ == bytes@.subrange(bytes.len() - out.1.len(), bytes.len() as int),
        out.1.len() > 0 ==> !is_continuation(out.1@[0]),
    no_unwind
))]
pub(crate) fn scan_mixed_windows<'text, M: MixedBlockWidth>(bytes: &'text [u8], measure: &mut M) -> (usize, &'text [u8]) {
    let mut rest = bytes;
    let mut offset = 0;
    let mut width = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant width <= offset <= bytes.len(), offset + rest.len() == bytes.len(),
            rest@ == bytes@.subrange(offset as int, bytes.len() as int),
        decreases rest.len(),
    ))]
    while rest.len() >= WINDOW {
        let block = rest.split_at(WINDOW).0;
        width += measure.measure_block(block, width);
        rest = rest.split_at(LANES).1;
        offset += LANES;
        #[cfg(verus_keep_ghost)]
        proof! { assert(rest@ =~= bytes@.subrange(offset as int, bytes.len() as int)); }
    }
    if rest.len() >= MIN_PADDED {
        width += measure.measure_tail(rest, width);
        offset += active_mixed_lanes(rest.len());
    }
    let start = next_char_boundary(bytes, offset);
    (width, bytes.split_at(start).1)
}

/// Continue the last possibly open SIMD word in the remaining scalar bytes.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(end =>
    requires base + tail.len() <= usize::MAX,
    ensures base <= end <= base + tail.len(),
    no_unwind
))]
pub(crate) fn append_character_tail(
    tail: &[u8], base: usize, lines: &mut LineWidths, start: &mut usize, previous_space: &mut u32,
) -> usize {
    let mut end = base;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= tail.len(), base <= end <= base + i, base + tail.len() <= usize::MAX,
        decreases tail.len() - i,
    ))]
    while i < tail.len() {
        let lead = tail[i];
        if !is_continuation(lead) {
            let space = if ascii_space(lead) || (lead >= 0xc2 && unicode_separator_width(tail, i) != 0) {
                1
            } else {
                0
            };
            if *previous_space != space {
                if space == 0 {
                    *start = end;
                } else {
                    lines.add_word(end.saturating_sub(*start));
                }
            }
            *previous_space = space;
            #[cfg(verus_keep_ghost)]
            proof! { assert(end <= base + i < base + tail.len() <= usize::MAX); }
            end += 1;
        }
        i += 1;
    }
    end
}

/// An unaligned vector reads exactly 32 bytes beginning at this offset.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires bytes.len() == WINDOW, offset <= 2,
    ensures out.len() == LANES, out@ == bytes@.subrange(offset as int, offset + LANES),
    no_unwind
))]
pub(crate) fn lookahead_vector(bytes: &[u8], offset: usize) -> &[u8] {
    bytes.split_at(offset).1.split_at(LANES).0
}
