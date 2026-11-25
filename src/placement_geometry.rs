//! One-axis geometry for placement. The host supplies already read declarations
//! and measured values, while arithmetic keeps the published operation order.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use crate::stack_line::{between_gaps, evenly_spaced_gaps};
#[cfg(not(verus_keep_ghost))]
use crate::place::stack_line::{between_gaps, evenly_spaced_gaps};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::prepare_frame::FrameFloat;

#[derive(Debug, Clone, Copy, PartialEq)]
/// The "origin" of a layout node inside its own rectangle.
///
/// For example, an element with `Size::Pixels(10.0)` and `Pos::Pixels(0.0)` on an axis will be placed at `[0.0, 10.0]`, `[-5.0, 5.0]` or `[-10.0, 0.0]` if its `Anchor` is `Start`, `Center` or `End` respectively.
///
/// Has no effect in a stack's main axis, or with the edge and center alignment positions.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Anchor {
    /// The left or top edge of the element's rectangle.
    Start,
    /// The center of the element's rectangle.
    Center,
    /// The right or bottom edge of the element's rectangle.
    End,
    /// Any fraction, with `0.0` corresponding to the left or top edge and `1.0` corresponding to the right or bottom edge.
    Frac(f32),
}

#[derive(Debug, Clone, Copy, PartialEq)]
/// The position of a layout node in the space of its parent.
///
/// If the node is a child of a stack, its `Pos` value on the stack's main axis is ignored, as the stack positions the child according to its own logic.
///
/// In a grid, the `Pos` value controls how the node is placed within the space of a grid cell.
/// In normal block flow, margins and the containing block determine in-flow positions.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Pos {
    /// The left or top side of the parent.
    Start,
    /// The center of the parent.
    Center,
    /// The right or bottom side of the parent.
    End,
    /// A fixed number of pixels starting from the left or top side of the parent.
    Pixels(f32),
    /// A fraction of the parent's size starting from its left or top side.
    Frac(f32),
    /// Anchor at a fraction of the parent's inner extent plus a logical pixel offset.
    /// Both components are measured from the same origin, including when that origin is flipped.
    /// For example, `Offset { fraction: 1.0, pixels: -8.0 }` places the anchor eight pixels
    /// before the far edge as the parent resizes.
    Offset {
        /// Fraction of the available range along this axis.
        fraction: f32,
        /// Additional distance from the origin, in logical pixels.
        pixels: f32,
    },
}

/// What to do if a freely placed node would extend past the edges of the window. It has no effect on the children of a `Stack` or a `Grid`, unless they are `free_placement`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum WindowOverflow {
    /// Leave the node where it is, even if it extends past the window edge.
    #[default]
    Ignore,
    /// Push the node back inside the window.
    Clamp,
    /// Keep the requested placement if it fits on this axis. On overflow, try the
    /// opposite side of the anchor, as a context menu would. When neither side
    /// fits, clamp the originally requested placement into the window. If the
    /// node is as large as the window or larger, place its near edge at zero.
    Flip,
}

/// The way that a stack's children are arranged along its main axis.
#[derive(Debug, Clone, Copy, Hash, PartialEq)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Arrange {
    /// The children are arranged close together at the start of the stack.
    Start,
    /// The children are arranged close together at the end of the stack.
    End,
    /// The children are arranged close together in the center of the stack.
    Center,
    /// The free space is divided equally between the children, with no space at the edges.
    SpaceBetween,
    /// Each child gets an equal amount of free space on both sides, so the space at the edges is half the space between the children.
    SpaceAround,
    /// The free space is divided equally between the children and the edges.
    SpaceEvenly,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait FloatClassification {
    spec fn finite_word(value: f32) -> bool;
    spec fn maximum(left: f32, right: f32) -> f32;
    spec fn minimum(left: f32, right: f32) -> f32;
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait FloatClassification {}

#[cfg(not(verus_keep_ghost))]
impl<T> FloatClassification for T {}

/// Only the Rust float intrinsics sit outside the arithmetic kernel. Keeping
/// these calls preserves Rust's handling of NaNs and tied signed zeros.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FloatBounds: FloatClassification {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == Self::maximum(left, right), no_unwind))]
    fn max(left: f32, right: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == Self::minimum(left, right), no_unwind))]
    fn min(left: f32, right: f32) -> f32;
}

#[cfg(not(verus_keep_ghost))]
pub(crate) struct RustFloat;

#[cfg(not(verus_keep_ghost))]
impl FloatBounds for RustFloat {
    #[inline(always)]
    fn max(left: f32, right: f32) -> f32 { left.max(right) }

    #[inline(always)]
    fn min(left: f32, right: f32) -> f32 { left.min(right) }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn padded_range<F: FrameFloat>(edges: [f32; 2], padding: [f32; 2]) -> [f32; 2] {
    let [start, end] = edges;
    let [pad_start, pad_end] = padding;
    [F::sum(start, pad_start), F::difference(end, pad_end)]
}

pub(crate) open spec fn centered<F: FrameFloat>(start: f32, end: f32, size: f32) -> [f32; 2] {
    let center = F::quotient(F::sum(start, end), 2.0f32);
    let half = F::quotient(size, 2.0f32);
    [F::difference(center, half), F::sum(center, half)]
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns padded_range::<F>(edges, padding), no_unwind))]
pub(crate) fn inner_range<F: FrameFloat>(edges: [f32; 2], padding: [f32; 2]) -> [f32; 2] {
    let [start, end] = edges;
    let [pad_start, pad_end] = padding;
    [F::add(start, pad_start), F::subtract(end, pad_end)]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns centered::<F>(start, end, size), no_unwind))]
pub(crate) fn centered_range<F: FrameFloat>(start: f32, end: f32, size: f32) -> [f32; 2] {
    let center = F::divide(F::add(start, end), 2.0);
    let half = F::divide(size, 2.0);
    [F::subtract(center, half), F::add(center, half)]
}

/// Restart a stack or wrap line at the chosen alignment.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures arrange is Start ==> result == (start, spacing),
    no_unwind
))]
pub(crate) fn line_start_and_gap<F: FloatBounds>(arrange: Arrange, [start, end]: [f32; 2], total: f32, n: u32, spacing: f32) -> (f32, f32) {
    let free = F::max((end - start) - total, 0.0);
    match arrange {
        Arrange::Start => (start, spacing),
        Arrange::End => (end - total, spacing),
        Arrange::Center => ((start + end) / 2.0 - total / 2.0, spacing),
        Arrange::SpaceBetween => {
            let extra = if n > 1 { free / between_gaps(n) as f32 } else { 0.0 };
            (start, spacing + extra)
        }
        Arrange::SpaceAround => {
            let extra = if n > 0 { free / n as f32 } else { 0.0 };
            (start + extra / 2.0, spacing + extra)
        }
        Arrange::SpaceEvenly => {
            let extra = if n > 0 { free / evenly_spaced_gaps(n) as f32 } else { 0.0 };
            (start + extra, spacing + extra)
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn anchored<F: FrameFloat>(reference: f32, anchor: Anchor, flipped: bool, size: f32) -> [f32; 2] {
    let offset = F::product(anchor_fraction(anchor), size);
    if !flipped {
        let low = F::difference(reference, offset);
        [low, F::sum(low, size)]
    } else {
        let high = F::sum(reference, offset);
        [F::difference(high, size), high]
    }
}

pub(crate) open spec fn positioned<F: FrameFloat>(range: [f32; 2], position: Pos, anchor: Anchor,
    flipped: bool, size: f32,
) -> [f32; 2] {
    let [inner_start, inner_end] = range;
    let origin = if !flipped { inner_start } else { inner_end };
    let far = if !flipped { inner_end } else { inner_start };
    match position {
        Pos::Start => if !flipped { [origin, F::sum(origin, size)] } else { [F::difference(origin, size), origin] },
        Pos::End => if !flipped { [F::difference(far, size), far] } else { [far, F::sum(far, size)] },
        Pos::Pixels(pixels) => anchored::<F>(if !flipped { F::sum(origin, pixels) }
            else { F::difference(origin, pixels) }, anchor, flipped, size),
        Pos::Frac(frac) => {
            let offset = F::product(frac, F::difference(inner_end, inner_start));
            anchored::<F>(if !flipped { F::sum(origin, offset) }
                else { F::difference(origin, offset) }, anchor, flipped, size)
        },
        Pos::Offset { fraction, pixels } => {
            let offset = F::sum(F::product(fraction, F::difference(inner_end, inner_start)), pixels);
            anchored::<F>(if !flipped { F::sum(origin, offset) }
                else { F::difference(origin, offset) }, anchor, flipped, size)
        },
        Pos::Center => centered::<F>(inner_start, inner_end, size),
    }
}

pub(crate) open spec fn strict<F: FrameFloat>(left: f32, right: f32) -> bool {
    F::at_most(left, right) && !F::number_eq(left, right)
}

pub(crate) open spec fn fit_window<F: FrameFloat>(win_high: f32, behavior: WindowOverflow,
    flipped: bool, anchor: Anchor, rect: [f32; 2],
) -> [f32; 2] {
    let win_low = 0.0f32;
    let [lo, hi] = rect;
    let size = F::difference(hi, lo);
    if F::at_most(F::difference(win_high, win_low), size) {
        [win_low, F::sum(win_low, size)]
    } else {
        let [lo, hi] = if behavior is Flip {
            let offset = F::product(anchor_fraction(anchor), size);
            let a = if !flipped { F::sum(lo, offset) } else { F::difference(hi, offset) };
            let twice = F::product(2.0f32, a);
            let low = F::difference(twice, hi);
            let high = F::difference(twice, lo);
            if strict::<F>(win_high, hi) && F::at_most(win_low, low)
                || strict::<F>(lo, win_low) && F::at_most(high, win_high)
            { [low, high] } else { rect }
        } else { rect };
        let size = F::difference(hi, lo);
        let (lo, hi) = if strict::<F>(win_high, hi) { (F::difference(win_high, size), win_high) }
            else { (lo, hi) };
        if strict::<F>(lo, win_low) { [win_low, F::sum(win_low, size)] } else { [lo, hi] }
    }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns anchor_fraction(anchor), no_unwind))]
pub(crate) fn anchor_fraction(anchor: Anchor) -> f32 {
    match anchor {
        Anchor::Start => 0.0,
        Anchor::Center => 0.5,
        Anchor::End => 1.0,
        Anchor::Frac(f) => f,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns anchored::<F>(reference, anchor, flipped, child_size), no_unwind))]
fn position_at<F: FrameFloat>(reference: f32, anchor: Anchor, flipped: bool, child_size: f32) -> [f32; 2] {
    let offset = F::multiply(anchor_fraction(anchor), child_size);
    if !flipped {
        let low = F::subtract(reference, offset);
        [low, F::add(low, child_size)]
    } else {
        let high = F::add(reference, offset);
        [F::subtract(high, child_size), high]
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns positioned::<F>(range, position, anchor, flipped, child_size), no_unwind))]
pub(crate) fn resolve_position<F: FrameFloat>(range: [f32; 2], position: Pos, anchor: Anchor,
    flipped: bool, child_size: f32,
) -> [f32; 2] {
    let [inner_start, inner_end] = range;
    let origin_edge = if !flipped { inner_start } else { inner_end };
    let far_edge = if !flipped { inner_end } else { inner_start };
    match position {
        Pos::Start => {
            if !flipped { [origin_edge, F::add(origin_edge, child_size)] }
            else { [F::subtract(origin_edge, child_size), origin_edge] }
        }
        Pos::End => {
            if !flipped { [F::subtract(far_edge, child_size), far_edge] }
            else { [far_edge, F::add(far_edge, child_size)] }
        }
        Pos::Pixels(pixels) => {
            let reference = if !flipped { F::add(origin_edge, pixels) } else { F::subtract(origin_edge, pixels) };
            position_at::<F>(reference, anchor, flipped, child_size)
        }
        Pos::Frac(frac) => {
            let static_pos = F::multiply(frac, F::subtract(inner_end, inner_start));
            let reference = if !flipped { F::add(origin_edge, static_pos) } else { F::subtract(origin_edge, static_pos) };
            position_at::<F>(reference, anchor, flipped, child_size)
        }
        Pos::Offset { fraction, pixels } => {
            let offset = F::add(F::multiply(fraction, F::subtract(inner_end, inner_start)), pixels);
            let reference = if !flipped { F::add(origin_edge, offset) } else { F::subtract(origin_edge, offset) };
            position_at::<F>(reference, anchor, flipped, child_size)
        }
        Pos::Center => centered_range::<F>(inner_start, inner_end, child_size),
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns fit_window::<F>(win_high, behavior, flipped, anchor, rect), no_unwind))]
pub(crate) fn window_overflow<F: FrameFloat>(win_high: f32, behavior: WindowOverflow, flipped: bool,
    anchor: Anchor, rect: [f32; 2],
) -> [f32; 2] {
    let win_low = 0.0;
    let [lo, hi] = rect;
    let size = F::subtract(hi, lo);

    if F::less_or_equal(F::subtract(win_high, win_low), size) {
        return [win_low, F::add(win_low, size)];
    }

    let mut out = rect;
    if let WindowOverflow::Flip = behavior {
        // Mirror about the fixed point on the node, such as the cursor.
        let offset = F::multiply(anchor_fraction(anchor), size);
        let a = if !flipped { F::add(lo, offset) } else { F::subtract(hi, offset) };
        let twice = F::multiply(2.0, a);
        let reflected = [F::subtract(twice, hi), F::subtract(twice, lo)];
        let should_reflect = F::less_than(win_high, hi) && F::less_or_equal(win_low, reflected[0])
            || F::less_than(lo, win_low) && F::less_or_equal(reflected[1], win_high);
        if should_reflect {
            out = reflected;
        }
    }

    // Clamp, including when a flip would still overflow.
    let [mut lo, mut hi] = out;
    let size = F::subtract(hi, lo);
    if F::less_than(win_high, hi) {
        hi = win_high;
        lo = F::subtract(hi, size);
    }
    if F::less_than(lo, win_low) {
        lo = win_low;
        hi = F::add(lo, size);
    }
    [lo, hi]
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn block_inline_edges<F: FloatBounds>([left, right]: [f32; 2], size: f32, [left_margin, right_margin]: [f32; 2],
    [left_auto, right_auto]: [bool; 2], flipped: bool,
) -> [f32; 2] {
    let spare = F::max(right - left - size - left_margin - right_margin, 0.0);
    let auto_count = left_auto as usize + right_auto as usize;
    let (margin, auto) = if flipped { (right_margin, right_auto) } else { (left_margin, left_auto) };
    #[cfg(verus_keep_ghost)]
    proof! { assert(auto ==> 0 < auto_count <= 2); }
    let leading = if auto { spare / auto_count as f32 } else { margin };
    if flipped {
        let end = right - leading;
        [end - size, end]
    } else {
        let start = left + leading;
        [start, start + size]
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn grid_track_size<F: FloatBounds>(size: f32, [pad_start, pad_end]: [f32; 2], spacing: f32, n: f32) -> f32 {
    F::max((size - pad_start - pad_end - spacing * (n - 1.0)) / F::max(n, 1.0), 0.0)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn grid_cell_edges<F: FloatBounds>([start, end]: [f32; 2], [pad_start, pad_end]: [f32; 2],
    flipped: bool, index: f32, cell: f32, spacing: f32, span: u16, lines: f32,
) -> [f32; 2] {
    let span = if span == 0 { 1 } else { span };
    let span = F::min(span as f32, F::max(lines, 1.0));
    let offset = index * (cell + spacing);
    let length = span * cell + (span - 1.0) * spacing;
    if !flipped {
        let start = start + pad_start + offset;
        [start, start + length]
    } else {
        let end = end - pad_end - offset;
        [end - length, end]
    }
}

#[cfg(any(not(target_arch = "x86_64"), test, verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn grid_start_edges(origin: f32, step: f32, cell: f32, size: f32) -> [f32; 2] {
    let start = (origin + cell * step) + 0.0;
    [start, start + size]
}
