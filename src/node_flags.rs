//! Packed per-node slot phases and layout flags.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, X, Y};
#[cfg(not(verus_keep_ghost))]
use crate::{flow::wrap_metrics, solve::cycle_rules};
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, wrap_metrics::kernel as wrap_metrics};
use cycle_rules::{Kind, N_SLOTS};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(index =>
    ensures index < N_SLOTS, index == cycle_rules::slot_index(axis.index(), kind),
    no_unwind
))]
pub(crate) const fn slot_index(axis: Axis, kind: Kind) -> usize {
    cycle_rules::slot_index(axis.index(), kind)
}

const _: () = { assert!(X as usize == 0 && Y as usize == 1); };

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct NodeFlags(pub(crate) u32);

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl NodeFlags {
    pub(crate) const EMPTY: NodeFlags = NodeFlags(0);

    pub(crate) const FLEX_CHILD_X: u32 = 1 << (2 * N_SLOTS + 2);
    pub(crate) const FLEX_CHILD_Y: u32 = 1 << (2 * N_SLOTS + 3);
    pub(crate) const GRID_SPANS: u32 = 1 << (2 * N_SLOTS + 4);
    pub(crate) const BLOCK_ITEM: u32 = 1 << (2 * N_SLOTS + 5);
    pub(crate) const BLOCK_PARENT_AUTO_HEIGHT: u32 = 1 << (2 * N_SLOTS + 6);
    pub(crate) const BLOCK_CONTAINER: u32 = 1 << (2 * N_SLOTS + 7);
    pub(crate) const WRAP_CONTAINER: u32 = 1 << (2 * N_SLOTS + 8);
    pub(crate) const WRAP_LINE_START: u32 = 1 << (2 * N_SLOTS + 9);
    pub(crate) const DESCENDANTS_NEED_SOLVE: u32 = 1 << (2 * N_SLOTS + 10);
    pub(crate) const FIXED_LEAF: u32 = 1 << (2 * N_SLOTS + 11);

    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.is_block_item(), no_unwind))]
    pub(crate) fn is_block_item(self) -> bool {
        self.0 & Self::BLOCK_ITEM != 0
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(cycle => ensures cycle == (self.0 & (cycle_rules::CYCLE_X | cycle_rules::CYCLE_Y) != 0), no_unwind))]
    pub(crate) fn has_cycle(self) -> bool {
        self.0 & (cycle_rules::CYCLE_X | cycle_rules::CYCLE_Y) != 0
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn has_flow(self) -> bool {
        self.0 & (Self::BLOCK_CONTAINER | Self::WRAP_CONTAINER) != 0
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(block => ensures block == (self.0 & Self::BLOCK_CONTAINER != 0), no_unwind))]
    pub(crate) fn is_block_container(self) -> bool {
        self.0 & Self::BLOCK_CONTAINER != 0
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn starts_wrap_line(self) -> bool {
        wrap_metrics::is_start(self.0, Self::WRAP_LINE_START)
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::flex_child(axis), no_unwind))]
    pub(crate) fn flex_child(axis: Axis) -> u32 {
        match axis {
            X => NodeFlags::FLEX_CHILD_X,
            Y => NodeFlags::FLEX_CHILD_Y,
        }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(state =>
        ensures state == cycle_rules::read_state(self.0, cycle_rules::slot_index(axis.index(), kind) as u32),
        no_unwind
    ))]
    pub(crate) fn check_state(self, axis: Axis, kind: Kind) -> u32 {
        cycle_rules::read_state(self.0, slot_index(axis, kind) as u32)
    }

    #[cfg(any(feature = "incremental", test, verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires state < 4,
        ensures cycle_rules::read_state(final(self).0, cycle_rules::slot_index(axis.index(), kind) as u32) == state,
            forall |other: u32| other < 16 && other != cycle_rules::slot_index(axis.index(), kind) ==>
                #[trigger] cycle_rules::read_state(final(self).0, other) == cycle_rules::read_state(old(self).0, other),
        no_unwind
    ))]
    pub(crate) fn set_state(&mut self, axis: Axis, kind: Kind, state: u32) {
        self.0 = cycle_rules::write_state(self.0, slot_index(axis, kind) as u32, state);
    }
}

const _: () = { assert!(2 * N_SLOTS + 12 <= 32, "The slot states and the flags don't fit in NodeFlags"); };
