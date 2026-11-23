//! Select a rounding kernel from the features reported as usable by Rust.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Backend {
    Scalar,
    Sse2Unit,
    Sse2PowerOfTwo,
    Sse2,
    Avx2,
    Avx2Fma,
    Avx512,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub(crate) struct Features {
    pub avx512f: bool,
    pub avx2: bool,
    pub fma: bool,
    pub sse2: bool,
}

// Mask the detector reports with the architecture and the compiled entry set.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns for_build(detected, x86_64, has_avx512_entry, has_fma_entry)))]
pub(crate) fn for_build(detected: Features, x86_64: bool, has_avx512_entry: bool, has_fma_entry: bool) -> Features {
    Features {
        avx512f: x86_64 && has_avx512_entry && detected.avx512f,
        avx2: x86_64 && detected.avx2,
        fma: x86_64 && has_fma_entry && detected.fma,
        sse2: x86_64 && detected.sse2,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl Features {
        pub(crate) open spec fn permits(self, backend: Backend) -> bool {
            match backend {
                Backend::Scalar => true,
                Backend::Sse2Unit | Backend::Sse2PowerOfTwo | Backend::Sse2 => self.sse2,
                Backend::Avx2 => self.avx2,
                Backend::Avx2Fma => self.avx2 && self.fma,
                Backend::Avx512 => self.avx512f && self.avx2,
            }
        }

        pub(crate) open spec fn priority(self, backend: Backend) -> bool {
            &&& (backend is Avx512) == (self.avx512f && self.avx2)
            &&& (backend is Avx2Fma) == (self.avx2 && !self.avx512f && self.fma)
            &&& (backend is Avx2) == (self.avx2 && !self.avx512f && !self.fma)
            &&& (backend is Sse2) == (self.sse2 && !self.avx2)
            &&& (backend is Scalar) == (!self.sse2 && !self.avx2)
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(backend =>
    ensures features.permits(backend), features.priority(backend),
))]
pub(crate) fn select(features: Features) -> Backend {
    if features.avx512f && features.avx2 {
        Backend::Avx512
    } else if features.avx2 && features.fma {
        Backend::Avx2Fma
    } else if features.avx2 {
        Backend::Avx2
    } else if features.sse2 {
        Backend::Sse2
    } else {
        Backend::Scalar
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(backend => ensures
    ({
        let available = for_build(detected, x86_64, has_avx512_entry, has_fma_entry);
        &&& available.permits(backend)
        &&& (backend is Sse2Unit) == (unit_scale && available.sse2)
        &&& (backend is Sse2PowerOfTwo) == (!unit_scale && power_of_two && available.sse2)
        &&& !((unit_scale || power_of_two) && available.sse2) ==> available.priority(backend)
    }),
))]
pub(crate) fn select_for_build(
    detected: Features,
    x86_64: bool,
    has_avx512_entry: bool,
    has_fma_entry: bool,
    unit_scale: bool,
    power_of_two: bool,
) -> Backend {
    let available = for_build(detected, x86_64, has_avx512_entry, has_fma_entry);
    if unit_scale && available.sse2 {
        // Every usable vector backend shares the inlined binary32 path at 1.0.
        Backend::Sse2Unit
    } else if power_of_two && available.sse2 {
        Backend::Sse2PowerOfTwo
    } else {
        select(available)
    }
}

#[cfg(any(test, verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(supported => ensures supported == features.permits(backend)))]
fn supported(features: Features, backend: Backend) -> bool {
    match backend {
        Backend::Scalar => true,
        Backend::Sse2Unit | Backend::Sse2PowerOfTwo | Backend::Sse2 => features.sse2,
        Backend::Avx2 => features.avx2,
        Backend::Avx2Fma => features.avx2 && features.fma,
        Backend::Avx512 => features.avx512f && features.avx2,
    }
}

#[cfg(not(verus_keep_ghost))]
#[inline]
fn detector_reports() -> Features {
    #[cfg(target_arch = "x86_64")]
    {
        #[cfg(keru_avx512)]
        let avx512f = std::is_x86_feature_detected!("avx512f");
        #[cfg(not(keru_avx512))]
        let avx512f = false;
        Features {
            avx512f,
            avx2: std::is_x86_feature_detected!("avx2"),
            fma: cfg!(any(test, all(target_feature = "avx2", target_feature = "fma")))
                && std::is_x86_feature_detected!("fma"),
            sse2: std::is_x86_feature_detected!("sse2"),
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        Features {
            avx512f: false,
            avx2: false,
            fma: false,
            sse2: false,
        }
    }
}

// The verifier and the native entry calls expand this same backend-to-entry
// mapping. Entries which were not compiled fall through to the scalar kernel.
macro_rules! route {
    ($backend:expr, $enter:ident $(, $arg:expr)*) => {
        match $backend {
            Backend::Scalar => $enter!(scalar $(, $arg)*),
            Backend::Sse2Unit => $enter!(sse2_unit, target_arch = "x86_64" $(, $arg)*),
            Backend::Sse2PowerOfTwo => $enter!(sse2_power_of_two, target_arch = "x86_64" $(, $arg)*),
            Backend::Sse2 => $enter!(sse2_scaled, target_arch = "x86_64" $(, $arg)*),
            Backend::Avx2 => $enter!(avx2, target_arch = "x86_64" $(, $arg)*),
            Backend::Avx2Fma => $enter!(avx2_fma, all(target_arch = "x86_64", any(test, all(target_feature = "avx2", target_feature = "fma"))) $(, $arg)*),
            Backend::Avx512 => $enter!(avx512, all(target_arch = "x86_64", keru_avx512) $(, $arg)*),
        }
    };
}

// Keep the hot unit-scale loop separate so the backend switch can be hoisted
// out of loops that snap a sequence of rectangles.
macro_rules! route_prepared {
    ($backend:expr, $unit:expr, $enter:ident $(, $arg:expr)*) => {{
        if $unit {
            route!(Backend::Sse2Unit, $enter $(, $arg)*)
        } else {
            route!($backend, $enter $(, $arg)*)
        }
    }};
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(unit => ensures unit == (backend is Sse2Unit)))]
fn uses_unit_entry(backend: Backend) -> bool {
    matches!(backend, Backend::Sse2Unit)
}

#[cfg(not(verus_keep_ghost))]
macro_rules! enter_native {
    (scalar, $edges:expr, $scale:expr) => {
        super::scalar($edges, $scale)
    };
    ($entry:ident, $available:meta, $edges:expr, $scale:expr) => {{
        #[cfg($available)]
        {
            // SAFETY: Selected can only be constructed from the checked feature
            // set. The entry table identifies which checked feature is used.
            unsafe { super::vector::$entry($edges, $scale) }
        }
        #[cfg(not($available))]
        {
            super::scalar($edges, $scale)
        }
    }};
}

#[cfg(not(verus_keep_ghost))]
macro_rules! enter_batch {
    (avx2, $available:meta, $rects:expr, $scale:expr) => {
        enter_batch!(@wide avx2_many, $available, $rects, $scale)
    };
    (avx512, $available:meta, $rects:expr, $scale:expr) => {
        enter_batch!(@wide avx512_many, $available, $rects, $scale)
    };
    (@wide $entry:ident, $available:meta, $rects:expr, $scale:expr) => {{
        #[cfg($available)]
        {
            // SAFETY: The same checked backend and feature guard admit the
            // single-rectangle entry, and the batch requires the same features.
            unsafe { super::vector::$entry($rects, $scale) }
        }
        #[cfg(not($available))]
        enter_batch!(scalar, $rects, $scale);
    }};
    (scalar, $rects:expr, $scale:expr) => {
        for rect in $rects {
            *rect = super::scalar(*rect, $scale);
        }
    };
    ($entry:ident, $available:meta, $rects:expr, $scale:expr) => {
        for rect in $rects {
            *rect = enter_native!($entry, $available, *rect, $scale);
        }
    };
}

#[cfg(verus_keep_ghost)]
macro_rules! entry_identity {
    (scalar) => {
        Backend::Scalar
    };
    (sse2_unit, $available:meta) => {
        Backend::Sse2Unit
    };
    (sse2_power_of_two, $available:meta) => {
        Backend::Sse2PowerOfTwo
    };
    (sse2_scaled, $available:meta) => {
        Backend::Sse2
    };
    (avx2, $available:meta) => {
        Backend::Avx2
    };
    (avx2_fma, $available:meta) => {
        Backend::Avx2Fma
    };
    (avx512, $available:meta) => {
        Backend::Avx512
    };
}

#[cfg(verus_keep_ghost)]
#[verus_verify]
#[verus_spec(returns backend)]
pub(crate) fn entry_for(backend: Backend) -> Backend {
    route_prepared!(backend, uses_unit_entry(backend), entry_identity)
}

// The only production constructor selects from the actual detected capability
// set. Keeping the backend private prevents callers from fabricating a choice.
#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Copy)]
pub(super) struct Selected {
    backend: Backend,
    unit: bool,
}

#[cfg(not(verus_keep_ghost))]
impl Selected {
    #[inline]
    pub(super) fn detect(unit_scale: bool, power_of_two: bool) -> Self {
        Self::from_backend(select_for_build(
            detector_reports(),
            cfg!(target_arch = "x86_64"),
            // Use the inlined AVX2 entry when only AVX2 is enabled globally.
            cfg!(all(keru_avx512, any(not(target_feature = "avx2"), target_feature = "avx512f"))),
            // FMA is faster when the packed kernel can inline into its caller.
            cfg!(all(target_feature = "avx2", target_feature = "fma")),
            unit_scale,
            power_of_two && !cfg!(target_feature = "avx2"),
        ))
    }

    #[inline]
    pub(super) fn snap(self, edges: [f32; 4], scale: super::Scale) -> [f32; 4] {
        route_prepared!(self.backend, self.unit, enter_native, edges, scale)
    }

    #[inline]
    pub(super) fn prefers_batch(self) -> bool {
        match self.backend {
            Backend::Avx2 => !cfg!(target_feature = "avx2"),
            Backend::Avx512 => !cfg!(target_feature = "avx512f"),
            _ => false,
        }
    }

    #[inline]
    pub(super) fn snap_many(self, rects: &mut [[f32; 4]], scale: super::Scale) {
        route!(self.backend, enter_batch, rects, scale)
    }

    #[inline]
    fn from_backend(backend: Backend) -> Self {
        Self { backend, unit: uses_unit_entry(backend) }
    }

    #[cfg(test)]
    pub(super) fn for_test(backend: Backend) -> Option<Self> {
        let features = for_build(
            detector_reports(),
            cfg!(target_arch = "x86_64"),
            cfg!(keru_avx512),
            true,
        );
        supported(features, backend).then_some(Self::from_backend(backend))
    }
}
