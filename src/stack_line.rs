//! Cursor and edge operations for an in-flow stack or wrap item.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
pub trait ScalarModel: Copy {
    spec fn sum(left: Self, right: Self) -> Self;
    spec fn difference(left: Self, right: Self) -> Self;
    spec fn zero(value: Self) -> bool;
}
}

#[cfg(not(verus_keep_ghost))]
pub trait ScalarModel: Copy {}
#[cfg(not(verus_keep_ghost))]
impl ScalarModel for f32 {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Scalar: ScalarModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::sum(self, other)))]
    fn add(self, other: Self) -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::difference(self, other)))]
    fn sub(self, other: Self) -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::zero(self)))]
    fn is_zero(self) -> bool;
}

#[cfg(not(verus_keep_ghost))]
impl Scalar for f32 {
    #[inline(always)]
    fn add(self, other: Self) -> Self { self + other }
    #[inline(always)]
    fn sub(self, other: Self) -> Self { self - other }
    #[inline(always)]
    fn is_zero(self) -> bool { self == 0.0 }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns adjusted(size, margin)))]
pub fn with_margin<F: Scalar>(size: F, margin: F) -> F {
    if margin.is_zero() { size } else { size.add(margin) }
}

/// Full placement and resumption from a preceding unrounded edge must round
/// the trailing margin and gap into the item's advance before adding its start.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns advance(start, size, trailing, gap)))]
pub fn after_item<F: Scalar>(start: F, size: F, trailing: F, gap: F) -> F {
    start.add(with_margin(size, trailing).add(gap))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(edges =>
    ensures (edges, *final(cursor)) == full_step(*old(cursor), flipped, range, size, margin, gap),
))]
pub fn place<F: Scalar>(cursor: &mut F, flipped: bool, range: [F; 2], size: F, margin: [F; 2], gap: F) -> [F; 2] {
    let (leading, trailing) = if flipped { (margin[1], margin[0]) } else { (margin[0], margin[1]) };
    let position = with_margin(*cursor, leading);
    *cursor = after_item(position, size, trailing, gap);
    if flipped {
        let end = range[0].add(range[1]).sub(position);
        [end.sub(size), end]
    } else {
        [position, position.add(size)]
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(edges =>
    ensures (edges, *final(cursor)) == start_step(*old(cursor), cross_start, horizontal, size, gap),
))]
pub fn place_start<F: Scalar>(cursor: &mut F, cross_start: F, horizontal: bool, size: [F; 2], gap: F) -> [[F; 2]; 2] {
    let (x, y, main_size) = if horizontal { (*cursor, cross_start, size[0]) } else { (cross_start, *cursor, size[1]) };
    *cursor = (*cursor).add(main_size.add(gap));
    [[x, x.add(size[0])], [y, y.add(size[1])]]
}

/// There is one more space than there are in-flow children. A line of
/// u32::MAX children still has a nonzero divisor.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == count + 1, no_unwind))]
pub fn evenly_spaced_gaps(count: u32) -> u64 { count as u64 + 1 }
