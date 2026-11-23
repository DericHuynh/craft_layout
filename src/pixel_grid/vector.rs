use core::arch::x86_64::*;
use core::mem::transmute;

#[inline]
fn round_pair(scaled: __m128d) -> __m128d {
    // SSE2 is available on every x86-64 target. A product of two binary32
    // values has at most 48 significant bits; the scalar kernel uses the
    // same bias and integer-spacing constants for this range.
    unsafe {
        let sign_mask = _mm_set1_pd(-0.0);
        let magnitude = _mm_andnot_pd(sign_mask, scaled);
        let biased = _mm_mul_pd(magnitude, _mm_set1_pd(1.0 + f64::EPSILON));
        let spacing = _mm_set1_pd((1_u64 << 52) as f64);
        let nearest = _mm_sub_pd(_mm_add_pd(biased, spacing), spacing);
        let small = _mm_cmplt_pd(magnitude, _mm_set1_pd((1_u64 << 47) as f64));
        let rounded = _mm_or_pd(_mm_and_pd(small, nearest), _mm_andnot_pd(small, magnitude));
        _mm_or_pd(rounded, _mm_and_pd(scaled, sign_mask))
    }
}

#[inline]
#[target_feature(enable = "sse2")]
pub(super) fn sse2_scaled(edges: [f32; 4], scale: super::Scale) -> [f32; 4] {
    let input = unsafe { transmute::<[f32; 4], __m128>(edges) };
    let factor = _mm_set1_pd(scale.factor);
    let inverse = _mm_set1_pd(scale.inverse);
    let lo = _mm_mul_pd(_mm_cvtps_pd(input), factor);
    let hi = _mm_mul_pd(_mm_cvtps_pd(_mm_movehl_ps(input, input)), factor);
    let lo = _mm_cvtpd_ps(_mm_mul_pd(round_pair(lo), inverse));
    let hi = _mm_cvtpd_ps(_mm_mul_pd(round_pair(hi), inverse));
    unsafe { transmute::<__m128, [f32; 4]>(_mm_movelh_ps(lo, hi)) }
}

#[inline]
#[target_feature(enable = "sse2")]
pub(super) fn sse2_unit(edges: [f32; 4], _scale: super::Scale) -> [f32; 4] {
    let input = unsafe { transmute::<[f32; 4], __m128>(edges) };
    let (rounded, small) = round_ps(input);
    #[cfg(target_feature = "sse4.1")]
    let output = {
        let _ = small;
        rounded
    };
    #[cfg(not(target_feature = "sse4.1"))]
    let output = keep_large(input, rounded, small);
    unsafe { transmute::<__m128, [f32; 4]>(output) }
}

#[inline]
#[target_feature(enable = "sse2")]
pub(super) fn sse2_power_of_two(edges: [f32; 4], scale: super::Scale) -> [f32; 4] {
    let input = unsafe { transmute::<[f32; 4], __m128>(edges) };
    let scaled = _mm_mul_ps(input, _mm_set1_ps(scale.factor_f32));
    let (rounded, small) = round_ps(scaled);
    let snapped = _mm_mul_ps(rounded, _mm_set1_ps(scale.inverse_f32));
    // Above the cutoff the scaled edge was already integral, even if the
    // binary32 product overflowed. Publish the original unscaled edge there.
    unsafe { transmute::<__m128, [f32; 4]>(keep_large(input, snapped, small)) }
}

#[inline]
#[target_feature(enable = "sse2")]
fn keep_large(input: __m128, rounded: __m128, small: __m128) -> __m128 {
    _mm_or_ps(_mm_and_ps(small, rounded), _mm_andnot_ps(small, input))
}

#[inline]
#[target_feature(enable = "sse2")]
fn round_ps(input: __m128) -> (__m128, __m128) {
    let sign_mask = _mm_set1_ps(-0.0);
    let magnitude = _mm_andnot_ps(sign_mask, input);
    let small = _mm_cmplt_ps(magnitude, _mm_set1_ps((1_u32 << 23) as f32));
    // Add the binary32 predecessor of 0.5. The sum with 0.5 rounds to
    // 1.0, while the sum with the preceding input stays below 1.0.
    let bias = _mm_set1_ps(f32::from_bits(0x3eff_ffff));
    #[cfg(target_feature = "sse4.1")]
    let rounded = {
        // Packed floating-point truncation keeps signed zero and integral
        // inputs, including magnitudes at or above 2^23, without a blend.
        let half = _mm_or_ps(_mm_and_ps(input, sign_mask), bias);
        // SAFETY: This build enables SSE4.1 for the entire binary.
        unsafe { _mm_round_ps::<_MM_FROUND_TO_ZERO>(_mm_add_ps(input, half)) }
    };
    #[cfg(not(target_feature = "sse4.1"))]
    let rounded = {
        let nearest = _mm_cvtepi32_ps(_mm_cvttps_epi32(_mm_add_ps(magnitude, bias)));
        _mm_or_ps(nearest, _mm_and_ps(input, sign_mask))
    };
    (rounded, small)
}

#[inline(always)]
pub(super) unsafe fn avx2(edges: [f32; 4], scale: super::Scale) -> [f32; 4] {
    let input = unsafe { transmute::<[f32; 4], __m128>(edges) };
    let factor_and_inverse = unsafe { transmute::<[f64; 2], __m128d>([scale.factor, scale.inverse]) };
    let output = unsafe { avx2_registers(input, factor_and_inverse) };
    unsafe { transmute::<__m128, [f32; 4]>(output) }
}

// Keep the packed lanes and both scale values in registers across the target-feature boundary.
// The private caller and callee are always compiled together by Rust.
#[inline]
#[allow(improper_ctypes_definitions)]
#[target_feature(enable = "avx2")]
unsafe extern "C" fn avx2_registers(input: __m128, factor_and_inverse: __m128d) -> __m128 {
    let scale = _mm256_broadcastsd_pd(factor_and_inverse);
    let inverse = _mm256_broadcastsd_pd(_mm_unpackhi_pd(factor_and_inverse, factor_and_inverse));
    avx2_wide(input, scale, inverse)
}

#[target_feature(enable = "avx2")]
pub(super) unsafe fn avx2_many(rects: &mut [[f32; 4]], scale: super::Scale) {
    let factor = _mm256_set1_pd(scale.factor);
    let inverse = _mm256_set1_pd(scale.inverse);
    for rect in rects {
        let input = unsafe { transmute::<[f32; 4], __m128>(*rect) };
        let output = avx2_wide(input, factor, inverse);
        *rect = unsafe { transmute::<__m128, [f32; 4]>(output) };
    }
}

#[inline]
#[target_feature(enable = "avx2")]
fn avx2_wide(input: __m128, scale: __m256d, inverse: __m256d) -> __m128 {
    let scaled = _mm256_mul_pd(_mm256_cvtps_pd(input), scale);
    let sign = _mm256_and_pd(scaled, _mm256_set1_pd(-0.0));
    let half = _mm256_or_pd(sign, _mm256_set1_pd(0.5));
    // The product has at most 48 significant bits. Adding a signed half
    // and truncating rounds ties away and retains the sign of zero.
    let rounded = _mm256_round_pd::<{ _MM_FROUND_TO_ZERO }>(_mm256_add_pd(scaled, half));
    _mm256_cvtpd_ps(_mm256_mul_pd(rounded, inverse))
}

#[cfg(any(test, all(target_feature = "avx2", target_feature = "fma")))]
#[inline(always)]
pub(super) unsafe fn avx2_fma(edges: [f32; 4], scale: super::Scale) -> [f32; 4] {
    let input = unsafe { transmute::<[f32; 4], __m128>(edges) };
    let output = unsafe { avx2_fma_registers(input, scale.factor, scale.inverse) };
    unsafe { transmute::<__m128, [f32; 4]>(output) }
}

#[cfg(any(test, all(target_feature = "avx2", target_feature = "fma")))]
#[inline]
#[allow(improper_ctypes_definitions)]
#[target_feature(enable = "avx2,fma")]
unsafe extern "C" fn avx2_fma_registers(input: __m128, scale: f64, inverse: f64) -> __m128 {
    let edges = _mm256_cvtps_pd(input);
    // A positive scale preserves each edge's sign. The product of two f32s
    // is exact in f64, so fusing the signed half gives the same rounded sum.
    let sign = _mm256_and_pd(edges, _mm256_set1_pd(-0.0));
    let half = _mm256_or_pd(sign, _mm256_set1_pd(0.5));
    let biased = _mm256_fmadd_pd(edges, _mm256_set1_pd(scale), half);
    let rounded = _mm256_round_pd::<{ _MM_FROUND_TO_ZERO }>(biased);
    _mm256_cvtpd_ps(_mm256_mul_pd(rounded, _mm256_set1_pd(inverse)))
}

#[cfg(keru_avx512)]
#[inline(always)]
pub(super) unsafe fn avx512(edges: [f32; 4], scale: super::Scale) -> [f32; 4] {
    let input = unsafe { transmute::<[f32; 4], __m128>(edges) };
    let output = unsafe { avx512_registers(input, scale.factor, scale.inverse) };
    unsafe { transmute::<__m128, [f32; 4]>(output) }
}

#[cfg(keru_avx512)]
#[inline]
#[clippy::msrv = "1.89"]
#[allow(improper_ctypes_definitions)]
#[target_feature(enable = "avx512f")]
unsafe extern "C" fn avx512_registers(input: __m128, scale: f64, inverse: f64) -> __m128 {
    // The upper four lanes are unused. Initialize them without reading past
    // the rectangle, and publish only the lower four results.
    let input = _mm256_insertf128_ps::<1>(_mm256_castps128_ps256(input), _mm_setzero_ps());
    let result = avx512_wide(input, _mm512_set1_pd(scale), _mm512_set1_pd(inverse));
    _mm256_castps256_ps128(result)
}

#[cfg(keru_avx512)]
#[inline]
#[clippy::msrv = "1.89"]
#[target_feature(enable = "avx512f")]
pub(super) unsafe fn avx512_many(rects: &mut [[f32; 4]], scale: super::Scale) {
    let factor = _mm512_set1_pd(scale.factor);
    let inverse = _mm512_set1_pd(scale.inverse);
    let (pairs, tail) = rects.as_chunks_mut::<2>();
    for pair in pairs {
        // The eight lanes belong to two consecutive, complete rectangles.
        let input = unsafe { transmute::<[[f32; 4]; 2], __m256>(*pair) };
        let output = avx512_wide(input, factor, inverse);
        *pair = unsafe { transmute::<__m256, [[f32; 4]; 2]>(output) };
    }
    if let [rect] = tail {
        *rect = unsafe { avx512(*rect, scale) };
    }
}

#[cfg(keru_avx512)]
#[inline]
#[clippy::msrv = "1.89"]
#[target_feature(enable = "avx512f")]
fn avx512_wide(input: __m256, scale: __m512d, inverse: __m512d) -> __m256 {
    let scaled = _mm512_mul_pd(_mm512_cvtps_pd(input), scale);
    let bits = _mm512_castpd_si512(scaled);
    let sign_mask = _mm512_set1_epi64(i64::MIN);
    let half = _mm512_castsi512_pd(_mm512_or_si512(
        _mm512_and_si512(bits, sign_mask), _mm512_set1_epi64(0.5_f64.to_bits() as i64),
    ));
    let rounded = _mm512_roundscale_pd::<{ _MM_FROUND_TO_ZERO }>(
        _mm512_add_pd(scaled, half),
    );
    _mm512_cvtpd_ps(_mm512_mul_pd(rounded, inverse))
}
