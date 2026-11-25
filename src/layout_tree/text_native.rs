//! The typed unaligned reads used by the native text classifiers.

use std::arch::x86_64::{__m128i, __m256i, _mm_loadu_si128, _mm256_loadu_si256, _pext_u32};

#[inline(always)]
pub(crate) fn load_sse2(bytes: &[u8; 16]) -> __m128i {
    // SAFETY: x86-64 provides SSE2 and the array supplies 16 initialized bytes.
    unsafe { _mm_loadu_si128(bytes.as_ptr().cast()) }
}

/// # Safety
/// AVX must be enabled on the executing CPU and operating system.
#[inline]
#[target_feature(enable = "avx")]
pub(crate) fn load_avx(bytes: &[u8; 32]) -> __m256i {
    // SAFETY: This function enables AVX. The array supplies 32 initialized bytes.
    unsafe { _mm256_loadu_si256(bytes.as_ptr().cast()) }
}

/// Pack the marked bits into the low lanes selected by `positions`.
#[inline]
#[target_feature(enable = "bmi2")]
pub(crate) fn pack_lanes(mask: u32, positions: u32) -> u32 {
    _pext_u32(mask, positions)
}
