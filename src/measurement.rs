//! An opt-in, bit-exact measurement contract for downstream Verus code.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// The dimension a custom content measurement is computing.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Axis {
    /// Horizontal dimension.
    X,
    /// Vertical dimension.
    Y,
}

/// The engine's measurement arguments in exact IEEE 754 binary32 bits.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Request {
    /// Unwrapped text width.
    TextWidth,
    /// Text height with an optional width constraint.
    TextHeight {
        /// Width bits, or `None` for unwrapped text.
        wrap_width: Option<u32>,
    },
    /// Intrinsic content-box measurement.
    Content {
        /// The requested dimension.
        axis: Axis,
        /// Known dimension bits in X, Y order.
        known_dimensions: [Option<u32>; 2],
        /// Explicit maximum bits in X, Y order.
        max_size: [Option<u32>; 2],
    },
}

impl Request {
    /// Compares the full request, preserving the option tags and exact bit words.
    /// Verus exposes this equality when checking a cache lookup.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (*self == *other), no_unwind))]
    pub fn same_input(&self, other: &Self) -> bool {
        match (*self, *other) {
            (Self::TextWidth, Self::TextWidth) => true,
            (Self::TextHeight { wrap_width: a }, Self::TextHeight { wrap_width: b }) => same_word(a, b),
            (
                Self::Content { axis: axis_a, known_dimensions: known_a, max_size: max_a },
                Self::Content { axis: axis_b, known_dimensions: known_b, max_size: max_b },
            ) => matches!((axis_a, axis_b), (Axis::X, Axis::X) | (Axis::Y, Axis::Y))
                && same_dimensions(known_a, known_b) && same_dimensions(max_a, max_b),
            _ => false,
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (a == b), no_unwind))]
fn same_word(a: Option<u32>, b: Option<u32>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a == b,
        (None, None) => true,
        _ => false,
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (a == b), no_unwind))]
fn same_dimensions(a: [Option<u32>; 2], b: [Option<u32>; 2]) -> bool {
    let same = same_word(a[0], b[0]) && same_word(a[1], b[1]);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(same ==> a@ =~= b@);
        assert(same ==> a =~= b);
    }
    same
}

/// Measured dimensions in exact IEEE 754 binary32 bits.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SizeBits {
    /// Width bits.
    pub x: u32,
    /// Height bits.
    pub y: u32,
}

#[cfg(verus_keep_ghost)]
verus! {

/// The logical behavior of a downstream executable measurer.
pub trait Model<N: Copy, C: ?Sized> {
    /// Which states are safe to reuse. A cache-free implementation can return `true`.
    spec fn cache_valid(&self) -> bool;

    /// A pure result computed from the node, immutable content and request.
    /// Mutable measurer state is unavailable to this function.
    spec fn expected(node: N, content: &C, request: Request) -> SizeBits;
}

}

#[cfg(not(verus_keep_ghost))]
#[doc(hidden)]
pub trait Model<N: Copy, C: ?Sized> {}

#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized, N: Copy, C: ?Sized> Model<N, C> for T {}

/// A measurement routine that can be verified against a pure result model.
/// Implementations may update scratch state while preserving cache validity.
/// Include all measurement inputs, such as font data and node content, in `C`.
/// In Verus, measurement must also be proved unable to unwind from a valid cache.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Measurer<N: Copy, C: ?Sized>: Model<N, C> {
    /// Measure the supplied content for this request.
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).cache_valid(),
        ensures final(self).cache_valid(), result == Self::expected(node, content, request),
        no_unwind
    ))]
    fn measure(&mut self, node: N, content: &C, request: Request) -> SizeBits;
}
