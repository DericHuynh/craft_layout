#[path = "pixel_grid/dispatch.rs"]
mod dispatch;
#[cfg(target_arch = "x86_64")]
#[path = "pixel_grid/vector.rs"]
mod vector;

#[derive(Clone, Copy)]
pub(crate) struct Scale {
    factor: f64,
    inverse: f64,
    #[cfg(target_arch = "x86_64")]
    factor_f32: f32,
    #[cfg(target_arch = "x86_64")]
    inverse_f32: f32,
}

impl Scale {
    #[inline]
    pub(crate) fn new(scale: f32) -> Self {
        let factor = f64::from(scale);
        let inverse = 1.0 / factor;
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

// Require both the factor and reciprocal to be normal binary32 powers of two.
fn supports_packed_power_of_two(scale: f32) -> bool {
    let bits = scale.to_bits();
    (0x0080_0000..=0x7e80_0000).contains(&bits) && bits & 0x007f_ffff == 0
}

/// The factor, inverse, and backend prepared once for this placement pass.
pub(crate) struct Snapper {
    scale: Scale,
    selected: dispatch::Selected,
}

impl Snapper {
    pub(crate) fn new(scale: f32) -> Self {
        Self {
            scale: Scale::new(scale),
            selected: dispatch::Selected::detect(scale == 1.0, supports_packed_power_of_two(scale)),
        }
    }

    #[inline]
    pub(crate) fn snap(&self, edges: [f32; 4]) -> [f32; 4] {
        self.selected.snap(edges, self.scale)
    }

    #[inline]
    pub(crate) fn prefers_batch(&self) -> bool {
        self.selected.prefers_batch()
    }

    #[inline]
    pub(crate) fn snap_many(&self, rects: &mut [[f32; 4]]) {
        self.selected.snap_many(rects, self.scale);
    }
}

#[inline]
fn scalar(edges: [f32; 4], scale: Scale) -> [f32; 4] {
    edges.map(|edge| snap_edge(edge, scale))
}

#[inline]
pub(crate) fn snap_edge(edge: f32, scale: Scale) -> f32 {
    let scaled = f64::from(edge) * scale.factor;
    let rounded = if cfg!(all(target_arch = "x86_64", not(target_feature = "sse4.1"))) {
        // Baseline SSE2 has no packed round instruction. The product of two f32s has
        // at most 48 significant bits, so at 2^47 and above it is already integral.
        let magnitude = scaled.abs();
        const INTEGRAL_LIMIT: f64 = (1_u64 << 47) as f64;
        const UNIT_SPACING: f64 = (1_u64 << 52) as f64;
        // Below that limit, adding 2^52 rounds to the nearest integer. Bias upwards
        // by at most two f64 ULPs so half-integers round away from zero. The five
        // spare significand bits ensure this cannot round a non-tie across a boundary.
        let biased = magnitude * (1.0 + f64::EPSILON);
        let nearest = (biased + UNIT_SPACING) - UNIT_SPACING;
        let rounded = if magnitude < INTEGRAL_LIMIT { nearest } else { magnitude };
        rounded.copysign(scaled)
    } else {
        scaled.round()
    };
    // Binary32 inputs leave enough distance from each binary32 rounding
    // boundary for the binary64 reciprocal and multiply errors.
    (rounded * scale.inverse) as f32
}

#[cfg(test)]
mod tests {
    use super::{Scale, dispatch::{Backend, Features, Selected, select_for_build}, supports_packed_power_of_two};
    use rand::{Rng, SeedableRng};

    #[test]
    fn avx2_uses_unit_kernel_and_requires_separate_fma_support() {
        let mut features = Features { avx512f: false, avx2: true, fma: false, sse2: true };
        assert_eq!(select_for_build(features, true, false, true, true, true), Backend::Sse2Unit);
        assert_eq!(select_for_build(features, true, false, true, false, true), Backend::Sse2PowerOfTwo);
        assert_eq!(select_for_build(features, true, false, true, false, false), Backend::Avx2);
        features.fma = true;
        assert_eq!(select_for_build(features, true, false, true, true, true), Backend::Sse2Unit);
        assert_eq!(select_for_build(features, true, false, true, false, false), Backend::Avx2Fma);
        assert_eq!(select_for_build(features, true, false, false, false, false), Backend::Avx2);
        features.avx2 = false;
        assert_eq!(select_for_build(features, true, false, true, false, false), Backend::Sse2);
        assert_eq!(select_for_build(features, false, false, true, false, true), Backend::Scalar);
    }

    #[test]
    fn packed_power_of_two_requires_a_normal_reciprocal() {
        for scale in [f32::MIN_POSITIVE, 0.5, 1.0, 2.0, f32::from_bits(0x7e80_0000)] {
            assert!(supports_packed_power_of_two(scale));
        }
        for scale in [0.0, -2.0, 1.25, f32::from_bits(0x0040_0000), f32::from_bits(0x7f00_0000), f32::INFINITY] {
            assert!(!supports_packed_power_of_two(scale));
        }
    }

    #[test]
    fn batches_match_individual_rectangles_in_order() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x08c1_21c0);
        let cases: &[(Backend, &[f32])] = &[
            (Backend::Scalar, &[0.75, 1.0, 1.25, f32::MAX]),
            (Backend::Sse2Unit, &[1.0]),
            (Backend::Sse2PowerOfTwo, &[f32::MIN_POSITIVE, 0.5, 2.0, 4.0]),
            (Backend::Sse2, &[0.75, 1.0, 1.25, f32::MAX]),
            (Backend::Avx2, &[f32::from_bits(1), 0.75, 1.25, f32::MAX]),
            (Backend::Avx2Fma, &[f32::from_bits(1), 0.75, 1.25, f32::MAX]),
            (Backend::Avx512, &[f32::from_bits(1), 0.75, 1.25, f32::MAX]),
        ];
        for &(backend, scales) in cases {
            let Some(selected) = Selected::for_test(backend) else { continue };
            for &scale in scales {
                let params = Scale::new(scale);
                let mut edges = [[0.0; 4]; 17];
                edges[0] = [0.0, -0.0, f32::INFINITY, f32::NEG_INFINITY];
                edges[1] = [0.5, -0.5, f32::NAN, f32::MAX];
                for rect in &mut edges[2..] {
                    *rect = std::array::from_fn(|_| f32::from_bits(rng.random()));
                }
                for len in 0..=edges.len() {
                    let mut batch = edges;
                    selected.snap_many(&mut batch[..len], params);
                    for (index, (input, output)) in edges.into_iter().zip(batch).enumerate() {
                        let expected = if index < len { selected.snap(input, params) } else { input };
                        for (actual, expected) in output.into_iter().zip(expected) {
                            assert!(
                                actual.to_bits() == expected.to_bits() || actual.is_nan() && expected.is_nan(),
                                "{backend:?} {scale} {len} {index}: {actual:?} != {expected:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn usable_backends_match_the_scalar_reference() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(0x0800_2512);
        let backends = [
            Backend::Scalar, Backend::Sse2Unit, Backend::Sse2PowerOfTwo, Backend::Sse2,
            Backend::Avx2, Backend::Avx2Fma, Backend::Avx512,
        ];
        for backend in backends {
            let Some(selected) = Selected::for_test(backend) else { continue };
            let check = |edges: [f32; 4], scale: f32| {
                let expected = edges.map(|edge| {
                    let scale = f64::from(scale);
                    ((f64::from(edge) * scale).round() / scale) as f32
                });
                for (expected, actual) in expected.into_iter().zip(selected.snap(edges, Scale::new(scale))) {
                    if expected.is_nan() {
                        assert!(actual.is_nan(), "{backend:?}");
                    } else {
                        assert_eq!(expected.to_bits(), actual.to_bits(), "{backend:?}, {edges:?}, {scale}");
                    }
                }
            };
            let scales: &[f32] = match backend {
                Backend::Sse2Unit => &[1.0],
                Backend::Sse2PowerOfTwo => &[f32::MIN_POSITIVE, 0.5, 2.0, 4.0, f32::from_bits(0x7e80_0000)],
                _ => &[f32::from_bits(1), 0.75, 1.0, 1.25, 3.0, f32::MAX],
            };
            for &scale in scales {
                check([0.0, -0.0, f32::INFINITY, f32::NEG_INFINITY], scale);
                check([f32::NAN, f32::from_bits(1), f32::MAX, -f32::MAX], scale);
                for pixel in [0.5, 1.5, 2.5, 127.5, 4095.5, 8_388_607.5] {
                    let edge = (pixel / f64::from(scale)) as f32;
                    check([edge.next_down(), edge, edge.next_up(), -edge], scale);
                }
            }
            if !matches!(backend, Backend::Sse2Unit | Backend::Sse2PowerOfTwo) {
                // Each positive edge is just below a half-pixel. Fusing at f32
                // precision can round the biased sum up to the next pixel.
                let a = f32::from_bits(0x3ecc_cccc);
                let b = f32::from_bits(0x4033_3333);
                check([a, -a, b, -b], 1.25);
            }
            for _ in 0..20_000 {
                let edges = std::array::from_fn(|_| f32::from_bits(rng.random()));
                let scale = match backend {
                    Backend::Sse2Unit => 1.0,
                    Backend::Sse2PowerOfTwo => f32::from_bits(rng.random_range(1..=253) << 23),
                    _ => f32::from_bits(rng.random_range(1..=f32::MAX.to_bits())),
                };
                check(edges, scale);
            }
        }
    }
}
