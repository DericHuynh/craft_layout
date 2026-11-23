// Both full Fill solvers and the cached stack tail use these budget operations.
#[inline(always)]
pub fn charge(space: f32, cost: f32) -> f32 {
    space - cost
}

/// A fully consumed budget has a canonical positive-zero representation.
#[inline(always)]
pub fn nonnegative(space: f32) -> f32 {
    if space > 0.0 { space } else { 0.0 }
}

#[inline(always)]
pub fn after_gaps(inner: f32, gaps: f32) -> f32 {
    nonnegative(charge(inner, gaps))
}

#[inline(always)]
pub fn share(budget: f32, frozen: f32, weight: f32) -> f32 {
    if weight > 0.0 { (budget - frozen) / weight } else { 0.0 }
}

/// The caller checks that no bound may freeze a Fill child.
#[cfg(feature = "incremental")]
#[inline(always)]
pub fn exhausted(inner: f32, gaps: f32, without_gaps: f32) -> bool {
    gaps >= inner || without_gaps <= 0.0
}
