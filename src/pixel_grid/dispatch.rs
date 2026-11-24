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

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub(crate) struct Build {
    pub x86_64: bool,
    pub avx512_compiled: bool,
    pub inlined_avx2: bool,
    pub inlined_avx512: bool,
    pub inlined_fma: bool,
}

impl Build {
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.avx512_entry(), no_unwind))]
    pub(crate) fn avx512_entry(self) -> bool {
        self.avx512_compiled && (!self.inlined_avx2 || self.inlined_avx512)
    }

    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.fma_entry(), no_unwind))]
    pub(crate) fn fma_entry(self) -> bool { self.inlined_avx2 && self.inlined_fma }
}

// Mask the detector reports with the architecture and the compiled entry set.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns for_build(detected, x86_64, has_avx512_entry, has_fma_entry), no_unwind))]
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
    no_unwind
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
    no_unwind
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
#[cfg_attr(verus_keep_ghost, verus_spec(supported => ensures supported == features.permits(backend), no_unwind))]
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
#[cfg_attr(verus_keep_ghost, verus_spec(unit => ensures unit == (backend is Sse2Unit), no_unwind))]
fn uses_unit_entry(backend: Backend) -> bool {
    matches!(backend, Backend::Sse2Unit)
}

macro_rules! enter_renderer {
    (scalar, $renderer:expr, $edges:expr, $scale:expr) => {
        $renderer.scalar($edges, $scale)
    };
    ($entry:ident, $available:meta, $renderer:expr, $edges:expr, $scale:expr) => {
        $renderer.$entry($edges, $scale)
    };
}

macro_rules! enter_batch {
    (avx2, $available:meta, $selected:expr, $renderer:expr, $rects:expr, $scale:expr) => {
        $renderer.avx2_many($rects, $scale)
    };
    (avx512, $available:meta, $selected:expr, $renderer:expr, $rects:expr, $scale:expr) => {
        $renderer.avx512_many($rects, $scale)
    };
    (scalar, $selected:expr, $renderer:expr, $rects:expr, $scale:expr) => {
        enter_batch!(@lanes scalar, $selected, $renderer, $rects, $scale)
    };
    ($entry:ident, $available:meta, $selected:expr, $renderer:expr, $rects:expr, $scale:expr) => {
        enter_batch!(@lanes $entry, $selected, $renderer, $rects, $scale)
    };
    (@lanes $entry:ident, $selected:expr, $renderer:expr, $rects:expr, $scale:expr) => {{
        let mut i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i <= $rects.len(), $rects.len() == old($rects).len(),
                $renderer.features().permits(entry_identity!($entry)),
                rounded_prefix($renderer, entry_identity!($entry), old($rects)@, $rects@, $scale, i as int),
            decreases $rects.len() - i,
        ))]
        while i < $rects.len() {
            let input = $rects[i];
            $rects[i] = $renderer.$entry(input, $scale);
            i += 1;
        }
    }};
}

#[cfg(verus_keep_ghost)]
macro_rules! entry_identity {
    (scalar) => {
        Backend::Scalar
    };
    (sse2_unit $(, $available:meta)?) => {
        Backend::Sse2Unit
    };
    (sse2_power_of_two $(, $available:meta)?) => {
        Backend::Sse2PowerOfTwo
    };
    (sse2_scaled $(, $available:meta)?) => {
        Backend::Sse2
    };
    (avx2 $(, $available:meta)?) => {
        Backend::Avx2
    };
    (avx2_fma $(, $available:meta)?) => {
        Backend::Avx2Fma
    };
    (avx512 $(, $available:meta)?) => {
        Backend::Avx512
    };
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait RendererModel {
    type Scale: Copy;
    spec fn features(&self) -> Features;
    spec fn edge_word(&self, edge: f32) -> u32;
    spec fn snapped_word(&self, backend: Backend, edge: f32, scale: Self::Scale) -> u32;
}

pub(crate) open spec fn lane_results<R: RendererModel + ?Sized>(
    renderer: &R, backend: Backend, input: [f32; 4], output: [f32; 4], scale: R::Scale,
) -> bool {
    forall|lane: int| 0 <= lane < 4 ==> crate::input_words::layout_word(#[trigger] renderer.edge_word(output@[lane]))
        == renderer.snapped_word(backend, input@[lane], scale)
}

pub(crate) open spec fn same_snapped_words<R: RendererModel + ?Sized>(renderer: &R, left: [f32; 4], right: [f32; 4]) -> bool {
    forall|lane: int| 0 <= lane < 4 ==> crate::input_words::layout_word(#[trigger] renderer.edge_word(left@[lane]))
        == crate::input_words::layout_word(renderer.edge_word(right@[lane]))
}

spec fn rounded_prefix<R: RendererModel + ?Sized>(
    renderer: &R, backend: Backend, input: Seq<[f32; 4]>, output: Seq<[f32; 4]>, scale: R::Scale, i: int,
) -> bool {
    &&& forall|j: int| 0 <= j < i ==> lane_results(renderer, backend, input[j], #[trigger] output[j], scale)
    &&& forall|j: int| i <= j < output.len() ==> #[trigger] output[j] == input[j]
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait RendererModel {
    type Scale: Copy;
}

/// Actual scalar and fixed-width hardware entry points. The caller checks the
/// reported CPU features before entering any vector routine.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Renderer: RendererModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(rounded =>
        ensures lane_results(self, Backend::Scalar, edges, rounded, scale), no_unwind
    ))]
    fn scalar(&self, edges: [f32; 4], scale: Self::Scale) -> [f32; 4];

    #[cfg_attr(verus_keep_ghost, verus_spec(rounded =>
        requires self.features().sse2, ensures lane_results(self, Backend::Sse2Unit, edges, rounded, scale), no_unwind
    ))]
    fn sse2_unit(&self, edges: [f32; 4], scale: Self::Scale) -> [f32; 4];

    #[cfg_attr(verus_keep_ghost, verus_spec(rounded =>
        requires self.features().sse2, ensures lane_results(self, Backend::Sse2PowerOfTwo, edges, rounded, scale), no_unwind
    ))]
    fn sse2_power_of_two(&self, edges: [f32; 4], scale: Self::Scale) -> [f32; 4];

    #[cfg_attr(verus_keep_ghost, verus_spec(rounded =>
        requires self.features().sse2, ensures lane_results(self, Backend::Sse2, edges, rounded, scale), no_unwind
    ))]
    fn sse2_scaled(&self, edges: [f32; 4], scale: Self::Scale) -> [f32; 4];

    #[cfg_attr(verus_keep_ghost, verus_spec(rounded =>
        requires self.features().avx2, ensures lane_results(self, Backend::Avx2, edges, rounded, scale), no_unwind
    ))]
    fn avx2(&self, edges: [f32; 4], scale: Self::Scale) -> [f32; 4];

    #[cfg_attr(verus_keep_ghost, verus_spec(rounded =>
        requires self.features().avx2, self.features().fma,
        ensures lane_results(self, Backend::Avx2Fma, edges, rounded, scale), no_unwind
    ))]
    fn avx2_fma(&self, edges: [f32; 4], scale: Self::Scale) -> [f32; 4];

    #[cfg_attr(verus_keep_ghost, verus_spec(rounded =>
        requires self.features().avx512f, self.features().avx2,
        ensures lane_results(self, Backend::Avx512, edges, rounded, scale), no_unwind
    ))]
    fn avx512(&self, edges: [f32; 4], scale: Self::Scale) -> [f32; 4];

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires self.features().avx2, ensures final(rects).len() == old(rects).len(),
            forall|i: int| 0 <= i < old(rects).len() ==> lane_results(self, Backend::Avx2,
                old(rects)@[i], (#[trigger] final(rects)@[i]), scale),
        no_unwind
    ))]
    fn avx2_many(&self, rects: &mut [[f32; 4]], scale: Self::Scale);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires self.features().avx512f, self.features().avx2,
        ensures final(rects).len() == old(rects).len(),
            forall|i: int| 0 <= i < old(rects).len() ==> lane_results(self, Backend::Avx512,
                old(rects)@[i], (#[trigger] final(rects)@[i]), scale),
        no_unwind
    ))]
    fn avx512_many(&self, rects: &mut [[f32; 4]], scale: Self::Scale);
}

// Keeping the backend private prevents callers from fabricating a choice.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub(crate) struct Selected {
    backend: Backend,
    unit: bool,
}

#[cfg(verus_keep_ghost)]
verus! {
impl Selected {
    pub(crate) closed spec fn admitted(self, features: Features) -> bool {
        features.permits(self.backend) && self.unit == (self.backend is Sse2Unit)
    }

    pub(crate) closed spec fn choice(self) -> Backend { self.backend }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl Selected {
    #[cfg(not(verus_keep_ghost))]
    #[inline]
    pub(super) fn detect(unit_scale: bool, power_of_two: bool) -> Self {
        Self::configure(
            detector_reports(),
            Build {
                x86_64: cfg!(target_arch = "x86_64"), avx512_compiled: cfg!(keru_avx512),
                inlined_avx2: cfg!(target_feature = "avx2"), inlined_avx512: cfg!(target_feature = "avx512f"),
                inlined_fma: cfg!(target_feature = "fma"),
            },
            unit_scale,
            power_of_two,
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(selected =>
        ensures selected.admitted(for_build(detected, build.x86_64, build.avx512_entry(), build.fma_entry())),
        no_unwind
    ))]
    #[inline]
    pub(crate) fn configure(detected: Features, build: Build, unit_scale: bool, power_of_two: bool) -> Self {
        // Keep the inlined AVX2 route when there is no inlined wider entry.
        // FMA also saves work only when it can inline into the caller.
        Self::prepare(
            detected, build.x86_64, build.avx512_entry(), build.fma_entry(),
            unit_scale, power_of_two && !build.inlined_avx2,
        )
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(selected =>
        ensures selected.admitted(for_build(detected, x86_64, avx512_entry, fma_entry)),
            ({
                let available = for_build(detected, x86_64, avx512_entry, fma_entry);
                let backend = selected.choice();
                &&& available.permits(backend)
                &&& (backend is Sse2Unit) == (unit_scale && available.sse2)
                &&& (backend is Sse2PowerOfTwo) == (!unit_scale && power_of_two && available.sse2)
                &&& !((unit_scale || power_of_two) && available.sse2) ==> available.priority(backend)
            }),
        no_unwind
    ))]
    #[inline]
    pub(crate) fn prepare(
        detected: Features, x86_64: bool, avx512_entry: bool, fma_entry: bool, unit_scale: bool, power_of_two: bool,
    ) -> Self {
        Self::from_backend(select_for_build(detected, x86_64, avx512_entry, fma_entry, unit_scale, power_of_two))
    }

    #[cfg(verus_keep_ghost)]
    #[verus_spec(entry =>
        requires self.admitted(available),
        ensures entry == self.choice(), available.permits(entry),
        no_unwind
    )]
    pub(crate) fn entry(self, available: Features) -> Backend {
        route_prepared!(self.backend, self.unit, entry_identity)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(rounded =>
        requires self.admitted(renderer.features()),
        ensures lane_results(renderer, self.choice(), edges, rounded, scale), no_unwind
    ))]
    #[inline]
    pub(crate) fn snap<R: Renderer>(self, renderer: &R, edges: [f32; 4], scale: R::Scale) -> [f32; 4] {
        route_prepared!(self.backend, self.unit, enter_renderer, renderer, edges, scale)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    #[inline]
    pub(crate) fn prefers_batch(self, inlined_avx2: bool, inlined_avx512: bool) -> bool {
        match self.backend {
            Backend::Avx2 => !inlined_avx2,
            Backend::Avx512 => !inlined_avx512,
            _ => false,
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires self.admitted(renderer.features()),
        ensures final(rects).len() == old(rects).len(),
            forall|i: int| 0 <= i < old(rects).len() ==> lane_results(renderer, self.choice(),
                old(rects)@[i], (#[trigger] final(rects)@[i]), scale),
        no_unwind
    ))]
    #[inline]
    pub(crate) fn snap_many<R: Renderer>(self, renderer: &R, rects: &mut [[f32; 4]], scale: R::Scale) {
        route!(self.backend, enter_batch, self, renderer, rects, scale)
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(selected =>
        ensures selected.backend == backend, selected.unit == (backend is Sse2Unit),
        no_unwind
    ))]
    #[inline]
    fn from_backend(backend: Backend) -> Self {
        Self { backend, unit: uses_unit_entry(backend) }
    }

    #[cfg(all(test, not(verus_keep_ghost)))]
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
