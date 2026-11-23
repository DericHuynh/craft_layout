//! Validation of public binary32 inputs before constructing restricted values.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(valid =>
    ensures valid == (word & 0x8000_0000u32 == 0
        && word & 0x7f80_0000u32 != 0x7f80_0000u32 && word != 0),
    no_unwind
))]
pub(crate) const fn positive_finite(word: u32) -> bool {
    let valid = word != 0 && word < 0x7f80_0000;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((word != 0 && word < 0x7f80_0000u32) == (word & 0x8000_0000u32 == 0
            && word & 0x7f80_0000u32 != 0x7f80_0000u32 && word != 0)) by (bit_vector);
    }
    valid
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures match out {
        None => word & 0x7f80_0000u32 == 0x7f80_0000u32,
        Some(bits) => word & 0x7f80_0000u32 != 0x7f80_0000u32
            && bits == (if word & 0x7fff_ffffu32 == 0 { 0u32 } else { word }),
    },
    no_unwind
))]
pub(crate) const fn finite_margin(word: u32) -> Option<u32> {
    let magnitude = word & 0x7fff_ffff;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((word & 0x7fff_ffffu32 >= 0x7f80_0000u32)
            == (word & 0x7f80_0000u32 == 0x7f80_0000u32)) by (bit_vector);
    }
    if magnitude >= 0x7f80_0000 {
        None
    } else if magnitude == 0 {
        Some(0)
    } else {
        Some(word)
    }
}
