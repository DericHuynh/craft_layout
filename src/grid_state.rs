//! Grid side state read by sizing and placement.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Read the in-flow item's spans in search height/width order.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns assignment_item(disabled, free, x, y, vertical), no_unwind))]
pub(crate) fn assignment_item(disabled: bool, free: bool, x: u16, y: u16, vertical: bool) -> Option<(u16, u16)> {
    if disabled || free { None } else if vertical { Some((x, y)) } else { Some((y, x)) }
}

/// Decode the cell coordinates and track counts in their physical axis order.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns physical_pair(main, cross, vertical), no_unwind))]
pub fn physical_pair<T: Copy>(main: T, cross: T, vertical: bool) -> [T; 2] {
    if vertical { [cross, main] } else { [main, cross] }
}

/// A width grid owns its track state on the main-axis Final slot.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns writes_width_grid(final_slot, main_axis), no_unwind))]
pub fn writes_width_grid(final_slot: bool, main_axis: bool) -> bool {
    final_slot && main_axis
}

/// Compare the published track words, including the width used by the search.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns count_changed(old, new), no_unwind))]
pub fn count_changed(old: (u32, u32), new: (u32, u32)) -> bool {
    old.0 != new.0 || old.1 != new.1
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum AssignmentPath { Sequential, OneRow, Search }

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns assignment_path(columns, children, spans), no_unwind))]
pub fn assignment_path(columns: usize, children: usize, spans: bool) -> AssignmentPath {
    if !spans { AssignmentPath::Sequential }
    // The cached child count is saturated at u32::MAX. It can bound the
    // width of a single row only while it represents the exact count.
    else if children < u32::MAX as usize && columns / u16::MAX as usize >= children { AssignmentPath::OneRow }
    else { AssignmentPath::Search }
}

// Beyond this bound the bitmap can cost hundreds of megabytes for just a few
// rectangles. Allow a spare row for the packed search's cursor arithmetic.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const MAX_PACKED_WORDS: usize = (512 * 1024 * 1024) / 8;

/// The number of aligned occupancy words needed for a row.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(stride =>
    ensures columns <= stride * 64, stride * 64 < columns + 64,
        (columns == 0) == (stride == 0),
    no_unwind
))]
pub fn row_stride(columns: usize) -> usize {
    let words = columns / 64;
    if columns % 64 == 0 { words } else { words + 1 }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(words =>
    ensures words == vstd::math::min(MAX_PACKED_WORDS as int, (isize::MAX as int) / 8),
    no_unwind
))]
const fn max_packed_words() -> usize {
    let capacity = isize::MAX as usize / 8;
    if MAX_PACKED_WORDS < capacity { MAX_PACKED_WORDS } else { capacity }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(rows =>
    requires stride > 0,
    ensures rows <= MAX_PACKED_WORDS,
        rows > 0 ==> (rows + 1) * stride <= MAX_PACKED_WORDS
            && (rows + 1) * stride <= (isize::MAX as int) / 8,
    no_unwind
))]
pub fn packed_row_budget(stride: usize) -> u64 {
    let max_words = max_packed_words();
    let rows = max_words / stride;
    #[cfg(verus_keep_ghost)]
    proof! {
        let words = max_words as int;
        let step = stride as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(words, step);
        vstd::arithmetic::mul::lemma_mul_is_commutative(step, rows as int);
        assert(words == (rows as int) * step + words % step);
        assert(0 <= words % step);
    }
    if rows > 0 { (rows - 1) as u64 } else { 0 }
}

/// The shape and capacity checked before any packed placement.
#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct PackedShape {
    pub columns: usize,
    pub stride: usize,
    pub row_budget: u64,
}

#[cfg(verus_keep_ghost)]
verus! {
    impl PackedShape {
        pub(crate) open spec fn valid(self) -> bool {
            &&& 0 < self.columns <= self.stride * 64
            &&& self.stride > 0
            &&& self.row_budget <= MAX_PACKED_WORDS
            &&& self.row_budget > 0 ==> (self.row_budget + 1) * self.stride <= MAX_PACKED_WORDS
                && (self.row_budget + 1) * self.stride <= (isize::MAX as int) / 8
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(shape =>
    requires columns > 0,
    ensures shape.columns == columns, shape.valid(),
    no_unwind
))]
pub(crate) fn packed_shape(columns: usize) -> PackedShape {
    let stride = row_stride(columns);
    PackedShape { columns, stride, row_budget: packed_row_budget(stride) }
}

/// The cached population can skip the span scan only if every child could
/// use its maximum height and still stay within the budget.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(fits =>
    requires budget <= MAX_PACKED_WORDS,
    ensures fits == (children * (u16::MAX as int) <= budget), fits ==> children < u32::MAX,
    no_unwind
))]
pub fn worst_height_fits(children: u32, budget: u64) -> bool {
    children as u64 * u16::MAX as u64 <= budget
}

/// One step of the exact scan. A zero declared span uses one row.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires height <= budget <= MAX_PACKED_WORDS,
    ensures out == {
        let next = height + if span == 0 { 1int } else { span as int };
        if next <= budget { Some(next as u64) } else { None }
    },
    no_unwind
))]
pub fn charge_height(height: u64, span: u16, budget: u64) -> Option<u64> {
    let span = if span == 0 { 1 } else { span };
    let next = height + span as u64;
    if next <= budget { Some(next) } else { None }
}

/// Backfill's initial reservation is a hint based on the number of in-flow
/// children. Skip it if its word count would exceed the packed-grid budget.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(words =>
    requires columns > 0,
    ensures
        words <= MAX_PACKED_WORDS, words * 8 <= isize::MAX,
        words == {
            let rows = if children == 0 { 0int } else { 1 + (children as int - 1) / (columns as int) };
            let requested = rows * stride;
            if requested <= MAX_PACKED_WORDS && requested * 8 <= isize::MAX { requested } else { 0int }
        },
    no_unwind
))]
pub(crate) fn backfill_reserve_words(children: usize, columns: usize, stride: usize) -> usize {
    if children == 0 { return 0; }
    let rows = 1 + (children - 1) / columns;
    let Some(words) = rows.checked_mul(stride) else { return 0; };
    if words <= max_packed_words() { words } else { 0 }
}

/// Grow geometrically while keeping every requested capacity within the packed budget.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(capacity =>
    requires current < needed <= MAX_PACKED_WORDS, needed <= (isize::MAX as int) / 8,
    ensures needed <= capacity <= MAX_PACKED_WORDS, capacity <= (isize::MAX as int) / 8,
    no_unwind
))]
pub(crate) fn packed_growth_words(current: usize, needed: usize) -> usize {
    let maximum = max_packed_words();
    let grown = if current <= maximum / 2 { current * 2 } else { maximum };
    let grown = if grown < 4 { 4 } else { grown };
    if grown < needed { needed } else { grown }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == {
        let width = vstd::math::max(w as int, 1);
        let height = vstd::math::max(h as int, 1);
        if pos + width <= columns {
            Some(((pos + width) as usize, vstd::math::max(rows as int, height) as usize))
        } else {
            None
        }
    },
    no_unwind
))]
pub fn extend_one_row(pos: usize, rows: usize, w: u16, h: u16, columns: usize) -> Option<(usize, usize)> {
    let width = if w == 0 { 1 } else { w as usize };
    let height = if h == 0 { 1 } else { h as usize };
    if width > columns.saturating_sub(pos) {
        None
    } else {
        Some((pos + width, if rows < height { height } else { rows }))
    }
}

/// Publish both track counts in the grid's otherwise-unused slots.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires x<old(slots).len(), y<old(slots).len(), x!=y,
    ensures final(slots).len()==old(slots).len(), final(slots)[x as int]==lines.0,
        final(slots)[y as int]==lines.1,
        forall |i:int| 0<=i<old(slots).len() && i!=x && i!=y
            ==> #[trigger] final(slots)[i]==old(slots)[i],
    no_unwind
))]
pub fn publish_tracks<T: Copy>(slots: &mut [T], x: usize, y: usize, lines: (T, T)) {
    slots[x] = lines.0;
    slots[y] = lines.1;
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(lines =>
    requires x<slots.len(), y<slots.len(),
    ensures lines==(slots[x as int],slots[y as int]),
    no_unwind
))]
pub fn published_tracks<T: Copy, const N: usize>(slots: &[T; N], x: usize, y: usize) -> (T, T) {
    (slots[x], slots[y])
}

/// Placement decodes the incoming grid cell's physical coordinates.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(cell => ensures cell==(words[0],words[1]), no_unwind))]
pub fn published_cell(words: [u32; 2]) -> (u32, u32) {
    (words[0], words[1])
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct WidthKey {
    pub(crate) tracks: f32,
    pub(crate) columns: usize,
}

/// Binary32 rounding and clamping shared by the grid assignment and preview.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait WidthRounding {
    #[cfg_attr(verus_keep_ghost, verus_spec(key => ensures key.columns > 0, no_unwind))]
    fn floor_columns(quotient: f32) -> WidthKey;
}

#[cfg(not(verus_keep_ghost))]
pub(crate) struct RustWidthRounding;

#[cfg(not(verus_keep_ghost))]
impl WidthRounding for RustWidthRounding {
    #[inline(always)]
    fn floor_columns(quotient: f32) -> WidthKey {
        let tracks = quotient.floor().max(1.0).min(usize::MAX as f32);
        WidthKey { tracks, columns: tracks as usize }
    }
}

/// The rounded value is both the display track count and the key for the
/// integer-width search. A zero step has one track and never allocates an
/// unbounded board. The upper clamp follows Rust's saturating integer cast.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(key => ensures key.columns > 0, no_unwind))]
pub(crate) fn width_key<M: WidthRounding>(inner: f32, width: f32, gap: f32) -> WidthKey {
    let step = width + gap;
    if step == 0.0 {
        WidthKey { tracks: 1.0, columns: 1 }
    } else {
        M::floor_columns((inner + gap) / step)
    }
}

/// The numeric queue can carry a completed assignment across an exact key match.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns reuse_width_cells(retained, key), no_unwind))]
pub fn reuse_width_cells(retained: Option<u32>, key: u32) -> bool {
    match retained { Some(previous) => previous == key, None => false }
}

/// A regional solve of an in-flow grid item reuses the enclosing assignment.
/// Creating fresh slot data must preserve the cell assigned by that parent.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns preserve_parent_cell(in_flow, grid_parent, cell), no_unwind))]
pub fn preserve_parent_cell(in_flow: bool, grid_parent: bool, cell: [u32; 2]) -> Option<[u32; 2]> {
    if in_flow && grid_parent { Some(cell) } else { None }
}
