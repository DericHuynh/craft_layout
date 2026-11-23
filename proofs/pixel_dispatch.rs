//! Source-linked dispatch selection and entry routing for pixel snapping.
use vstd::prelude::*;

#[path = "../src/pixel_grid/dispatch.rs"]
mod dispatch;
use dispatch::{Backend, Features, entry_for, for_build, select_for_build};

verus! {

/// An environment model for the instructions enabled by the Rust codegen
/// attributes, including the platform's saved vector state.
struct Capabilities {
    pub sse2_usable: bool,
    pub sse42: bool,
    pub avx: bool,
    pub avx2: bool,
    pub avx512f: bool,
    pub fma: bool,
    pub f16c: bool,
    pub xmm_ymm_state: bool,
    pub zmm_state: bool,
}

impl Capabilities {
    spec fn avx2_usable(self) -> bool {
        self.sse42 && self.avx && self.avx2 && self.xmm_ymm_state
    }

    spec fn avx512_extension(self) -> bool {
        self.avx512f && self.fma && self.f16c && self.xmm_ymm_state && self.zmm_state
    }

    // Rust's AVX512F detector checks FMA, F16C, and the extended OS state.
    // AVX2 is checked separately because it is implied by the Rust attribute.
    spec fn reports_sound(self, reported: Features) -> bool {
        &&& reported.sse2 ==> self.sse2_usable
        &&& reported.avx2 ==> self.avx2_usable()
        &&& reported.fma ==> self.fma
        &&& reported.avx512f ==> self.avx512_extension()
    }

    spec fn permits(self, entry: Backend) -> bool {
        match entry {
            Backend::Scalar => true,
            Backend::Sse2Unit | Backend::Sse2PowerOfTwo | Backend::Sse2 => self.sse2_usable,
            Backend::Avx2 => self.avx2_usable(),
            Backend::Avx2Fma => self.avx2_usable() && self.fma,
            Backend::Avx512 => self.avx2_usable() && self.avx512_extension(),
        }
    }
}

/// Follow the executable constructor's selection and the exact mapping of
/// variants to calls. The capability premise is the Rust detector contract.
/// Intrinsic implementations and the machine's reports are outside Verus.
fn selected_entry_is_usable(
    reported: Features,
    x86_64: bool,
    has_avx512_entry: bool,
    has_fma_entry: bool,
    unit_scale: bool,
    power_of_two: bool,
    Ghost(hardware): Ghost<Capabilities>,
) -> (entry: Backend)
    requires hardware.reports_sound(reported),
    ensures
        hardware.permits(entry),
        !x86_64 ==> entry is Scalar,
        entry is Sse2 ==> x86_64 && reported.sse2,
        entry is Avx2 ==> x86_64 && reported.avx2 && (!reported.fma || !has_fma_entry),
        entry is Avx2Fma ==> x86_64 && has_fma_entry && reported.avx2 && reported.fma,
        entry is Avx512 ==> x86_64 && has_avx512_entry && reported.avx512f && reported.avx2,
        (entry is Sse2Unit) == (unit_scale && x86_64 && reported.sse2),
        (entry is Sse2PowerOfTwo) == (!unit_scale && power_of_two && x86_64 && reported.sse2),
        !((unit_scale || power_of_two) && x86_64 && reported.sse2) ==>
            for_build(reported, x86_64, has_avx512_entry, has_fma_entry).priority(entry),
{
    let selection = select_for_build(reported, x86_64, has_avx512_entry, has_fma_entry, unit_scale, power_of_two);
    entry_for(selection)
}

}
