// Both full Fill solvers and the cached stack tail use these budget operations.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub fn charge(space: f32, cost: f32) -> f32 {
    space - cost
}

/// A fully consumed budget has a canonical positive-zero representation.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub fn nonnegative(space: f32) -> f32 {
    if space > 0.0 { space } else { 0.0 }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub fn after_gaps(inner: f32, gaps: f32) -> f32 {
    nonnegative(charge(inner, gaps))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub fn share(budget: f32, frozen: f32, weight: f32) -> f32 {
    if weight > 0.0 { (budget - frozen) / weight } else { 0.0 }
}

/// The caller checks that no bound may freeze a Fill child.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub fn exhausted(inner: f32, gaps: f32, without_gaps: f32) -> bool {
    gaps >= inner || without_gaps <= 0.0
}
