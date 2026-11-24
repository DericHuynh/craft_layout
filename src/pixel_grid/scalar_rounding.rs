//! Arithmetic shared by the native scalar rounding paths and the verifier.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Scale {
    pub(super) factor: f64,
    pub(super) inverse: f64,
    #[cfg(target_arch = "x86_64")]
    pub(super) factor_f32: f32,
    #[cfg(target_arch = "x86_64")]
    pub(super) inverse_f32: f32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Scale {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn new(scale: f32) -> Self {
        let (factor, inverse) = scale_factors(scale);
        Self {
            factor,
            inverse,
            #[cfg(target_arch = "x86_64")]
            factor_f32: scale,
            #[cfg(target_arch = "x86_64")]
            inverse_f32: inverse as f32,
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn prepare_scale(scale: f32, bits: u32) -> (Scale, bool, bool) {
    (Scale::new(scale), scale == 1.0, supports_packed_power_of_two(bits))
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FloatRound {
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn abs(value: f64) -> f64;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn copy_sign(value: f64, sign: f64) -> f64;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn round(value: f64) -> f64;
}

#[cfg(not(verus_keep_ghost))]
pub(crate) struct RustRound;

#[cfg(not(verus_keep_ghost))]
impl FloatRound for RustRound {
    #[inline(always)]
    fn abs(value: f64) -> f64 { value.abs() }

    #[inline(always)]
    fn copy_sign(value: f64, sign: f64) -> f64 { value.copysign(sign) }

    #[inline(always)]
    fn round(value: f64) -> f64 { value.round() }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn scale_factors(scale: f32) -> (f64, f64) {
    let factor = scale as f64;
    (factor, 1.0 / factor)
}

/// Both the factor and reciprocal must be normal binary32 powers of two.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(compatible =>
    ensures compatible == (0x0080_0000u32 <= bits <= 0x7e80_0000u32 && bits & 0x007f_ffffu32 == 0),
    no_unwind
))]
pub(crate) fn supports_packed_power_of_two(bits: u32) -> bool {
    bits >= 0x0080_0000 && bits <= 0x7e80_0000 && bits & 0x007f_ffff == 0
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn snap_edge<F: FloatRound>(edge: f32, factor: f64, inverse: f64, baseline_sse2: bool) -> f32 {
    let scaled = edge as f64 * factor;
    let rounded = if baseline_sse2 {
        // Baseline SSE2 has no packed round instruction. The product of two f32s has
        // at most 48 significant bits, so at 2^47 and above it is already integral.
        let magnitude = F::abs(scaled);
        const INTEGRAL_LIMIT: f64 = 140_737_488_355_328.0; // 2^47
        const UNIT_SPACING: f64 = 4_503_599_627_370_496.0; // 2^52
        const BIAS: f64 = 1.000_000_000_000_000_2; // 1 + 2^-52
        // Below that limit, adding 2^52 rounds to the nearest integer. Bias upwards
        // by at most two f64 ULPs so half-integers round away from zero. The five
        // spare significand bits ensure this cannot round a non-tie across a boundary.
        let biased = magnitude * BIAS;
        let nearest = (biased + UNIT_SPACING) - UNIT_SPACING;
        let rounded = if magnitude < INTEGRAL_LIMIT { nearest } else { magnitude };
        F::copy_sign(rounded, scaled)
    } else {
        F::round(scaled)
    };
    // Binary32 inputs leave enough distance from each binary32 rounding
    // boundary for the binary64 reciprocal and multiply errors.
    (rounded * inverse) as f32
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn snap_rect<F: FloatRound>([left, right, top, bottom]: [f32; 4], scale: Scale, baseline_sse2: bool) -> [f32; 4] {
    [
        snap_edge::<F>(left, scale.factor, scale.inverse, baseline_sse2),
        snap_edge::<F>(right, scale.factor, scale.inverse, baseline_sse2),
        snap_edge::<F>(top, scale.factor, scale.inverse, baseline_sse2),
        snap_edge::<F>(bottom, scale.factor, scale.inverse, baseline_sse2),
    ]
}
