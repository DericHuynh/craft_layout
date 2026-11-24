#[path = "pixel_grid/dispatch.rs"]
mod dispatch;
#[path = "pixel_grid/scalar_rounding.rs"]
mod scalar_rounding;
#[cfg(target_arch = "x86_64")]
#[path = "pixel_grid/vector.rs"]
mod vector;

pub(crate) use scalar_rounding::Scale;

// Require both the factor and reciprocal to be normal binary32 powers of two.
#[cfg(test)]
fn supports_packed_power_of_two(scale: f32) -> bool {
    scalar_rounding::supports_packed_power_of_two(scale.to_bits())
}

/// The factor, inverse, and backend prepared once for this placement pass.
pub(crate) struct Snapper {
    scale: Scale,
    selected: dispatch::Selected,
}

impl Snapper {
    pub(crate) fn new(scale: f32) -> Self {
        let (scale, unit, power_of_two) = scalar_rounding::prepare_scale(scale, scale.to_bits());
        Self { scale, selected: dispatch::Selected::detect(unit, power_of_two) }
    }

    #[inline]
    pub(crate) fn snap(&self, edges: [f32; 4]) -> [f32; 4] {
        self.selected.snap(&NativeRenderer, edges, self.scale)
    }

    #[inline]
    pub(crate) fn prefers_batch(&self) -> bool {
        self.selected.prefers_batch(cfg!(target_feature = "avx2"), cfg!(target_feature = "avx512f"))
    }

    #[inline]
    pub(crate) fn snap_many(&self, rects: &mut [[f32; 4]]) {
        self.selected.snap_many(&NativeRenderer, rects, self.scale);
    }
}

#[inline]
fn scalar(edges: [f32; 4], scale: Scale) -> [f32; 4] {
    scalar_rounding::snap_rect::<scalar_rounding::RustRound>(
        edges, scale, cfg!(all(target_arch = "x86_64", not(target_feature = "sse4.1"))),
    )
}

#[inline]
#[allow(dead_code)] // Compiled directly by the native IEEE rounding proof.
pub(crate) fn snap_edge(edge: f32, scale: Scale) -> f32 {
    scalar_rounding::snap_edge::<scalar_rounding::RustRound>(
        edge, scale.factor, scale.inverse,
        cfg!(all(target_arch = "x86_64", not(target_feature = "sse4.1"))),
    )
}

struct NativeRenderer;

impl dispatch::RendererModel for NativeRenderer {
    type Scale = Scale;
}

macro_rules! native_entry {
    ($entry:ident, $available:meta) => {
        #[inline]
        fn $entry(&self, edges: [f32; 4], scale: Scale) -> [f32; 4] {
            #[cfg($available)]
            {
                // SAFETY: only the checked selector calls this method, after
                // testing the entry's CPU and OS requirements.
                unsafe { vector::$entry(edges, scale) }
            }
            #[cfg(not($available))]
            { scalar(edges, scale) }
        }
    };
}

macro_rules! native_batch {
    ($entry:ident, $available:meta) => {
        #[inline]
        fn $entry(&self, rects: &mut [[f32; 4]], scale: Scale) {
            #[cfg($available)]
            {
                // SAFETY: the batch has the same CPU and OS requirements as
                // the corresponding single-rectangle entry.
                unsafe { vector::$entry(rects, scale) }
            }
            #[cfg(not($available))]
            for rect in rects { *rect = scalar(*rect, scale); }
        }
    };
}

impl dispatch::Renderer for NativeRenderer {
    #[inline]
    fn scalar(&self, edges: [f32; 4], scale: Scale) -> [f32; 4] { scalar(edges, scale) }

    native_entry!(sse2_unit, target_arch = "x86_64");
    native_entry!(sse2_power_of_two, target_arch = "x86_64");
    native_entry!(sse2_scaled, target_arch = "x86_64");
    native_entry!(avx2, target_arch = "x86_64");
    native_entry!(avx2_fma, all(target_arch = "x86_64", any(test, all(target_feature = "avx2", target_feature = "fma"))));
    native_entry!(avx512, all(target_arch = "x86_64", keru_avx512));
    native_batch!(avx2_many, target_arch = "x86_64");
    native_batch!(avx512_many, all(target_arch = "x86_64", keru_avx512));
}

#[cfg(test)]
mod tests {
    use super::{NativeRenderer, Scale, dispatch::{Backend, Features, Selected, select_for_build}, supports_packed_power_of_two};
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
                    selected.snap_many(&NativeRenderer, &mut batch[..len], params);
                    for (index, (input, output)) in edges.into_iter().zip(batch).enumerate() {
                        let expected = if index < len { selected.snap(&NativeRenderer, input, params) } else { input };
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
                for (expected, actual) in expected.into_iter().zip(selected.snap(&NativeRenderer, edges, Scale::new(scale))) {
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
