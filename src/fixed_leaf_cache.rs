//! Packed declarations and eligibility for reusing an ordinary fixed leaf.
#![allow(unexpected_cfgs)]

#[cfg(not(verus_keep_ghost))]
use crate::structural_changes::StructuralChange;
#[cfg(verus_keep_ghost)]
use crate::structural::kernel::StructuralChange;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const READY: u8 = 1;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const IN_FLOW: u8 = 2;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const SPANS: u8 = 4;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const STACK_START: u8 = 8;

#[cfg_attr(not(verus_keep_ghost), repr(transparent))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Summary(pub(crate) u8);

impl Summary {
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    pub(crate) const EMPTY: Self = Self(0);

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.is_empty(), no_unwind))]
    pub(crate) fn is_empty(self) -> bool {
        self.0 == 0
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.is_ready(), no_unwind))]
    pub(crate) fn is_ready(self) -> bool {
        self.0 & READY != 0
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.in_flow(), no_unwind))]
    pub(crate) fn in_flow(self) -> bool {
        self.0 & IN_FLOW != 0
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.spans(), no_unwind))]
    pub(crate) fn spans(self) -> bool {
        self.0 & SPANS != 0
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.stack_start(), no_unwind))]
    pub(crate) fn stack_start(self) -> bool {
        self.0 & STACK_START != 0
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(summary =>
    ensures summary.describes(free, spans, simple_start),
    no_unwind
))]
pub(crate) fn record(free: bool, spans: bool, simple_start: bool) -> Summary {
    let bits = if free {
        READY
    } else {
        let span_bit = (spans as u8) * SPANS;
        let start_bit = (simple_start as u8) * STACK_START;
        READY | IN_FLOW | span_bit | start_bit
    };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(bits & READY != 0
            && (bits & IN_FLOW != 0) == !free
            && (bits & SPANS != 0) == (!free && spans)
            && (bits & STACK_START != 0) == (!free && simple_start)
            && bits < 16) by(bit_vector)
            requires bits == (if free { READY } else {
                READY | IN_FLOW | (if spans { SPANS } else { 0 })
                    | (if simple_start { STACK_START } else { 0 })
            });
    }
    Summary(bits)
}

/// Eligibility requires exactly four solved slots and only the fixed-leaf marker.
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns registered_flags(marker, solved), no_unwind))]
pub(crate) const fn registered_flags(marker: u32, solved: u32) -> u32 {
    marker | solved | (solved << 2) | (solved << 4) | (solved << 6)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(flags) == (*old(flags) & !fixed_marker), final(summary).is_empty(),
    no_unwind
))]
pub(crate) fn invalidate(flags: &mut u32, fixed_marker: u32, summary: &mut Summary) {
    *flags &= !fixed_marker;
    *summary = Summary::EMPTY;
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(reused =>
    ensures reused == matches_fixed_pixels(flags, fixed, *flow),
        *final(mark) == (if reused { StructuralChange::Clean } else { *old(mark) }),
    no_unwind
))]
pub(crate) fn reuse_registered(
    flags: u32, fixed: u32, flow: &[u32; 2], mark: &mut StructuralChange,
) -> bool {
    let [first, second] = *flow;
    if flags != fixed || first != 0 || second != 0 { return false; }
    if !matches!(*mark, StructuralChange::Clean) {
        *mark = StructuralChange::Clean;
    }
    true
}

#[cfg(verus_keep_ghost)]
verus! {

impl Summary {
    /// Direct facts for one prepared, enabled ordinary leaf.
    pub(crate) open spec fn describes(self, free: bool, spans: bool, simple_start: bool) -> bool {
        &&& self.is_ready()
        &&& self.in_flow() == !free
        &&& self.spans() == (!free && spans)
        &&& self.stack_start() == (!free && simple_start)
        &&& self.0 < 16
    }
}

pub open spec fn matches_fixed_pixels(flags: u32, fixed: u32, flow: [u32; 2]) -> bool {
    flags == fixed && flow[0] == 0 && flow[1] == 0
}

}
