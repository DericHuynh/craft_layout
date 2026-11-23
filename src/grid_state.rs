//! Grid side state read by sizing and placement.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Decode the cell coordinates and track counts in their physical axis order.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns physical_pair(main, cross, vertical)))]
pub fn physical_pair<T: Copy>(main: T, cross: T, vertical: bool) -> [T; 2] {
    if vertical { [cross, main] } else { [main, cross] }
}

/// A width grid owns its track state on the main-axis Final slot.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns writes_width_grid(final_slot, main_axis)))]
pub fn writes_width_grid(final_slot: bool, main_axis: bool) -> bool {
    final_slot && main_axis
}

/// Compare the published track words, including the width used by the search.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns count_changed(old, new)))]
pub fn count_changed(old: (u32, u32), new: (u32, u32)) -> bool {
    old.0 != new.0 || old.1 != new.1
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum AssignmentPath { Sequential, OneRow, Search }

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns assignment_path(columns, children, spans)))]
pub fn assignment_path(columns: usize, children: usize, spans: bool) -> AssignmentPath {
    if !spans { AssignmentPath::Sequential }
    else if columns / u16::MAX as usize >= children { AssignmentPath::OneRow }
    else { AssignmentPath::Search }
}

// Beyond this bound the bitmap can cost hundreds of megabytes for just a few
// rectangles. Allow a spare row for the packed search's cursor arithmetic.
#[cfg_attr(verus_keep_ghost, verus_verify)]
const MAX_PACKED_WORDS: usize = (512 * 1024 * 1024) / 8;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(rows =>
    requires stride > 0,
    ensures rows > 0 ==> (rows + 1) * stride <= (isize::MAX as int) / 8,
    no_unwind
))]
pub fn packed_row_budget(stride: usize) -> u64 {
    let capacity = isize::MAX as usize / 8;
    let max_words = if MAX_PACKED_WORDS < capacity { MAX_PACKED_WORDS } else { capacity };
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

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires pos+w <= usize::MAX,
    ensures result.0==pos+w, result.1==vstd::math::max(rows as int,h as int),
))]
pub fn extend_one_row(pos: usize, rows: usize, w: usize, h: usize) -> (usize, usize) {
    (pos+w, rows.max(h))
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
))]
pub fn published_tracks<T: Copy>(slots: &[T], x: usize, y: usize) -> (T, T) {
    (slots[x], slots[y])
}

/// Placement decodes the incoming grid cell's physical coordinates.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(cell => ensures cell==(words[0],words[1])))]
pub fn published_cell(words: [u32; 2]) -> (u32, u32) {
    (words[0], words[1])
}

/// The rounded value is both the display track count and the key for the
/// integer-width search. A zero step has one track and never allocates an
/// unbounded board. The upper clamp follows Rust's saturating integer cast.
#[cfg(not(verus_keep_ghost))]
#[inline]
pub fn width_key(inner: f32, width: f32, gap: f32) -> f32 {
    let step = width + gap;
    if step == 0.0 { 1.0 } else { ((inner + gap) / step).floor().max(1.0).min(usize::MAX as f32) }
}

/// A regional solve of an in-flow grid item reuses the enclosing assignment.
/// Creating fresh slot data must preserve the cell assigned by that parent.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns preserve_parent_cell(in_flow, grid_parent, cell)))]
pub fn preserve_parent_cell(in_flow: bool, grid_parent: bool, cell: [u32; 2]) -> Option<[u32; 2]> {
    if in_flow && grid_parent { Some(cell) } else { None }
}
