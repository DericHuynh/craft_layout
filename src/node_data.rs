//! Initialized per-node state and typed reads of packed sizing slots.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, X, Y, Xy};
use crate::node_flags::{NodeFlags, slot_index};
use crate::prepare_frame::FrameFloat;
#[cfg(verus_keep_ghost)]
use crate::prepare_frame::FrameWords;
#[cfg(not(verus_keep_ghost))]
use crate::{flow::wrap_metrics, margin_storage, solve::{cycle_rules, grid_state}};
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::solve::dependency_rules;
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::{StructuralChange, fixed_leaf_cache, placement_work::PlacementWork};
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, dependencies::rules as dependency_rules, fixed_leaf_cache::runtime as fixed_leaf_cache,
    grid::frame::state as grid_state, margin_storage::kernel as margin_storage, placement::kernel::PlacementWork, structural::kernel::StructuralChange,
    wrap_metrics::kernel as wrap_metrics};
use cycle_rules::{Kind, N_SLOTS};
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use fixed_leaf_cache::Summary as FixedLeafSummary;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(not(verus_keep_ghost))]
pub(crate) const EMPTY_VALUES: [f32; N_SLOTS] = {
    let mut values = [f32::from_bits(cycle_rules::provisional_bits(false)); N_SLOTS];
    values[slot_index(X, Kind::Max)] = f32::from_bits(cycle_rules::provisional_bits(true));
    values[slot_index(Y, Kind::Max)] = f32::from_bits(cycle_rules::provisional_bits(true));
    values
};

#[cfg(any(feature = "incremental", verus_keep_ghost))]
// Use two 32-bit words so the ticket needs only 32-bit alignment.
#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, derive(Debug))]
#[repr(C)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct TopologyTicket {
    low: u32,
    high: u32,
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl TopologyTicket {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(ticket => ensures ticket.value() == value, no_unwind))]
    const fn new(value: u64) -> Self {
        let ticket = Self {
            low: value as u32,
            high: (value >> 32) as u32,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((value as u32) as u64 | (((value >> 32) as u32) as u64) << 32 == value)
                by (bit_vector);
        }
        ticket
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.value(), no_unwind))]
    const fn value(&self) -> u64 {
        (self.low as u64) | ((self.high as u64) << 32)
    }
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
impl core::fmt::Debug for TopologyTicket {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.value(), f)
    }
}

// Zero permanently disables the optimization, so a stale epoch never wraps.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    ensures next == 0 || epoch < next < 0x8000_0000,
        next != 0 <==> 0 < epoch < 0x7fff_ffff,
    no_unwind
))]
pub(crate) fn next_dormant_grid_epoch(epoch: u32) -> u32 {
    if epoch == 0 || epoch >= 0x7fff_ffff { 0 } else { epoch + 1 }
}

/// Per-node data used by the layout solver.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct NodeLayoutData {
    // Traversal reads the flags, placement work, cached style, and Final sizes
    // together. Keep those fields ahead of the dependency levels and ticket.
    /// The state of every slot.
    pub(crate) flags: NodeFlags,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) placement: PlacementWork,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) structural_change: StructuralChange,
    // Prepared from live declarations only for the owned tree. Declaration and
    // inherited visibility changes clear it along with the fixed-pixel marker.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) fixed_leaf_summary: FixedLeafSummary,
    /// Placement inputs produced from the ready slots of a fresh full solve.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) prepared_placement: u8,
    /// The value of every slot. Mapped by `slot_index()`.
    pub(crate) values: [f32; N_SLOTS],
    /// A grid item's two cell coordinates, or a wrap item's line metric.
    pub(crate) parent_flow: [u32; 2],
    /// In-flow child count. A Block stores presence in bit zero and the high
    /// bits of its one-based margin index in the rest of the word.
    pub(crate) n_placed_children: u32,
    /// The dependency level of every slot. Mapped by `slot_index()`.
    ///
    /// The "level" is the longest chain of dependencies of dependencies flowing into a slot. This is used for efficient incremental relayout.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) levels: [u16; N_SLOTS],
    // Identifies this record in a custom adapter's last solved topology.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) topology_index: TopologyTicket,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl NodeLayoutData {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) const DORMANT_GRID: u8 = 8;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.has_dormant_grid(), no_unwind))]
    pub(crate) fn has_dormant_grid(&self) -> bool {
        self.prepared_placement & Self::DORMANT_GRID != 0
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires epoch < 0x8000_0000,
        ensures final(self).has_dormant_grid(),
            final(self).flags == NodeFlags::EMPTY,
            final(self).dormant_grid_epoch() == epoch,
            final(self).dormant_grid_flags(axis) == Some(old(self).flags),
            *final(self) == (NodeLayoutData {
                topology_index: final(self).topology_index, flags: NodeFlags::EMPTY,
                prepared_placement: Self::DORMANT_GRID, ..*old(self)
            }),
        no_unwind
    ))]
    pub(crate) fn park_grid(&mut self, axis: Axis, epoch: u32) {
        // The owned tree does not use custom-adapter topology tickets.
        let a = axis.index() as u64;
        let flags = self.flags.0;
        let ticket = ((epoch as u64) << 33) | (a << 32) | flags as u64;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((ticket >> 33) as u32 == epoch
                && ((ticket >> 32) & 1) == a
                && ticket as u32 == flags) by(bit_vector)
                requires a < 2, epoch < 0x8000_0000,
                    ticket == ((epoch as u64) << 33) | (a << 32) | flags as u64;
        }
        self.topology_index = TopologyTicket::new(ticket);
        self.flags = NodeFlags::EMPTY;
        self.prepared_placement = Self::DORMANT_GRID;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(Self::DORMANT_GRID == 8u8);
            assert(8u8 & 8u8 != 0) by(bit_vector);
            assert(self.has_dormant_grid());
            assert(self.dormant_grid_flags(axis) == Some(NodeFlags(flags)));
        }
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.dormant_grid_epoch(), no_unwind))]
    pub(crate) fn dormant_grid_epoch(&self) -> u32 {
        (self.topology_index() >> 33) as u32
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(restore =>
        ensures restore == (visibility_only && !disabled && can_retain && epoch != 0
            && self.has_dormant_grid() && self.flags.0 == 0 && self.dormant_grid_epoch() == epoch),
            self.dormant_grid_epoch() < epoch ==> !restore,
        no_unwind
    ))]
    pub(crate) fn can_restore_dormant_grid(
        &self, visibility_only: bool, disabled: bool, can_retain: bool, epoch: u32,
    ) -> bool {
        visibility_only && !disabled && epoch != 0 && can_retain && self.has_dormant_grid()
            && self.flags.0 == 0 && self.dormant_grid_epoch() == epoch
    }

    /// The owned arena uses the otherwise unused topology ticket for hidden
    /// descendants. Parked Grid roots use their own packed ticket format.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.hidden_epoch_matches(epoch), no_unwind))]
    pub(crate) fn hidden_epoch_matches(&self, epoch: u32) -> bool {
        epoch != 0 && !self.has_dormant_grid() && self.topology_index() == epoch as u64
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.dormant_grid_flags(axis), no_unwind))]
    pub(crate) fn dormant_grid_flags(&self, axis: Axis) -> Option<NodeFlags> {
        let saved = self.topology_index();
        if !self.has_dormant_grid() || ((saved >> 32) & 1) != axis.index() as u64 { None }
        else { Some(NodeFlags(saved as u32)) }
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures !final(self).has_dormant_grid(),
            final(self).structural_change != StructuralChange::DormantGrid,
            *final(self) == (NodeLayoutData {
                topology_index: final(self).topology_index, prepared_placement: final(self).prepared_placement,
                structural_change: final(self).structural_change, ..*old(self)
            }),
            !old(self).has_dormant_grid() ==> final(self).topology_index() == old(self).topology_index(),
        no_unwind
    ))]
    pub(crate) fn clear_dormant_grid(&mut self) {
        if self.has_dormant_grid() {
            let before = self.prepared_placement;
            self.prepared_placement = before & !Self::DORMANT_GRID;
            #[cfg(verus_keep_ghost)]
            proof! {
                let after = self.prepared_placement;
                assert(after & 8u8 == 0) by(bit_vector) requires after == before & !8u8;
            }
            self.topology_index = TopologyTicket::new(0);
        }
        if matches!(self.structural_change, StructuralChange::DormantGrid) {
            self.structural_change = StructuralChange::Subtree;
        }
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) const PREPARED_WRAP: u8 = 1;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) const PREPARED_WRAP_START: u8 = 16;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) const PREPARED_PAIR: u8 = 2;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) const PREPARED_UNIFORM_LEAVES: u8 = 4;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) const PREPARED_FIT_LEAVES: u8 = 32;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.topology_index(), no_unwind))]
    pub(crate) const fn topology_index(&self) -> u64 {
        self.topology_index.value()
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).topology_index() == ticket,
            *final(self) == (NodeLayoutData { topology_index: final(self).topology_index, ..*old(self) }),
        no_unwind
    ))]
    pub(crate) fn set_topology_index(&mut self, ticket: u64) {
        self.topology_index = TopologyTicket::new(ticket);
    }

    /// Creates a new empty [`NodeLayoutData`].
    #[cfg(not(verus_keep_ghost))]
    pub const fn new() -> Self {
        Self::with_initial_words(EMPTY_VALUES, #[cfg(feature = "incremental")] [0; N_SLOTS])
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(data =>
        ensures data.values == values, data.flags == NodeFlags::EMPTY, data.n_placed_children == 0,
            data.placement == PlacementWork::Clean, data.prepared_placement == 0,
        no_unwind
    ))]
    pub(crate) const fn with_initial_words(
        values: [f32; N_SLOTS],
        #[cfg(any(feature = "incremental", verus_keep_ghost))] levels: [u16; N_SLOTS],
    ) -> Self {
        NodeLayoutData {
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            topology_index: TopologyTicket::new(0),
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            structural_change: StructuralChange::Clean,
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            placement: PlacementWork::Clean,
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            fixed_leaf_summary: FixedLeafSummary::EMPTY,
            values,
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            prepared_placement: 0,
            flags: NodeFlags::EMPTY,
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            levels,
            n_placed_children: 0,
            parent_flow: wrap_metrics::INITIAL_WORDS,
        }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(size =>
        ensures size.x == self.values@[cycle_rules::slot_index(X.index(), Kind::Final) as int],
            size.y == self.values@[cycle_rules::slot_index(Y.index(), Kind::Final) as int],
        no_unwind
    ))]
    pub(crate) fn size(&self) -> Xy<f32> {
        let values = &self.values;
        Xy::new(values[slot_index(X, Kind::Final)], values[slot_index(Y, Kind::Final)])
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(has_children =>
        ensures has_children == if self.flags.0 & NodeFlags::BLOCK_CONTAINER != 0 {
            margin_storage::block_has_children(self.n_placed_children)
        } else { self.n_placed_children != 0 },
        no_unwind
    ))]
    pub(crate) fn has_in_flow_children(&self) -> bool {
        if self.flags.is_block_container() {
            margin_storage::block_has_children(self.n_placed_children)
        } else {
            self.n_placed_children != 0
        }
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).flags.0 == (old(self).flags.0 & !NodeFlags::FIXED_LEAF),
            final(self).fixed_leaf_summary.is_empty(),
            *final(self) == (NodeLayoutData {
                flags: final(self).flags, fixed_leaf_summary: final(self).fixed_leaf_summary,
                ..*old(self)
            }),
        no_unwind
    ))]
    pub(crate) fn forget_fixed_pixels(&mut self) {
        fixed_leaf_cache::invalidate(&mut self.flags.0, NodeFlags::FIXED_LEAF, &mut self.fixed_leaf_summary);
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(index =>
        ensures index == if self.flags.0 & NodeFlags::BLOCK_CONTAINER != 0 {
            margin_storage::margin_index(F::word(self.values@[cycle_rules::slot_index(0, Kind::EvenShare) as int]),
                self.n_placed_children)
        } else { None },
        no_unwind
    ))]
    pub(crate) fn block_margin_index<F: FrameFloat>(&self) -> Option<usize> {
        if self.flags.is_block_container() {
            margin_storage::margin_index(F::bits(self.values[slot_index(X, Kind::EvenShare)]), self.n_placed_children)
        } else {
            None
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData {
            values: final(self).values, n_placed_children: final(self).n_placed_children, ..*old(self)
        }),
        final(self).values@ == old(self).values@.update(cycle_rules::slot_index(0, Kind::EvenShare) as int,
            final(self).values@[cycle_rules::slot_index(0, Kind::EvenShare) as int]),
        margin_storage::margin_index(
            F::word(final(self).values@[cycle_rules::slot_index(0, Kind::EvenShare) as int]), final(self).n_placed_children)
            == match index { Some(i) if i < isize::MAX as usize => Some(i), _ => None },
        margin_storage::block_has_children(final(self).n_placed_children)
            == margin_storage::block_has_children(old(self).n_placed_children),
        no_unwind
    ))]
    pub(crate) fn set_block_margin_index<F: FrameFloat>(&mut self, index: Option<usize>) {
        let (word, children) = margin_storage::margin_words(index, self.n_placed_children);
        self.values[slot_index(X, Kind::EvenShare)] = F::from_word(word);
        self.n_placed_children = children;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(cell =>
        ensures F::word(cell.x) == self.parent_flow[0], F::word(cell.y) == self.parent_flow[1],
        no_unwind
    ))]
    pub(crate) fn grid_cell<F: FrameFloat>(&self) -> Xy<f32> {
        let (x, y) = grid_state::published_cell(self.parent_flow);
        Xy::new(F::from_word(x), F::from_word(y))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData {
            parent_flow: grid_state::physical_pair(F::word(position), F::word(line), main.index() == 1),
            ..*old(self)
        }),
        no_unwind
    ))]
    pub(crate) fn set_grid_cell<F: FrameFloat>(&mut self, main: Axis, position: f32, line: f32) {
        self.parent_flow = grid_state::physical_pair(F::bits(position), F::bits(line), main.index() == 1);
    }

    // Grids hold track dimensions in the slots used by Stack and Block producers.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData { values: final(self).values, ..*old(self) }),
            final(self).values@ == old(self).values@
                .update(cycle_rules::slot_index(0, Kind::EvenShare) as int, lines.x)
                .update(cycle_rules::slot_index(1, Kind::Flow) as int, lines.y),
        no_unwind
    ))]
    pub(crate) fn set_grid_lines(&mut self, lines: Xy<f32>) {
        grid_state::publish_tracks(
            &mut self.values, slot_index(X, Kind::EvenShare), slot_index(Y, Kind::Flow), (lines.x, lines.y),
        );
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.values@ =~= old(self).values@
                .update(cycle_rules::slot_index(0, Kind::EvenShare) as int, lines.x)
                .update(cycle_rules::slot_index(1, Kind::Flow) as int, lines.y));
        }
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(lines =>
        ensures lines.x == self.values[cycle_rules::slot_index(0, Kind::EvenShare) as int],
            lines.y == self.values[cycle_rules::slot_index(1, Kind::Flow) as int],
        no_unwind
    ))]
    pub(crate) fn grid_lines(&self) -> Xy<f32> {
        let (x, y) = grid_state::published_tracks(
            &self.values, slot_index(X, Kind::EvenShare), slot_index(Y, Kind::Flow),
        );
        Xy::new(x, y)
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(bits =>
        ensures bits == (
            F::word(self.values[cycle_rules::slot_index(0, Kind::EvenShare) as int]),
            F::word(self.values[cycle_rules::slot_index(1, Kind::Flow) as int]),
        ),
        no_unwind
    ))]
    pub(crate) fn grid_line_bits<F: FrameFloat>(&self) -> (u32, u32) {
        let lines = self.grid_lines();
        (F::bits(lines.x), F::bits(lines.y))
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData { flags: final(self).flags, ..*old(self) }),
            final(self).flags.0 == old(self).flags.0 | NodeFlags::WRAP_LINE_START,
            final(self).flags.0 & !NodeFlags::WRAP_LINE_START == old(self).flags.0 & !NodeFlags::WRAP_LINE_START,
        no_unwind
    ))]
    pub(crate) fn mark_wrap_start(&mut self) {
        self.flags.0 = wrap_metrics::mark_start(self.flags.0, NodeFlags::WRAP_LINE_START);
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData { parent_flow: final(self).parent_flow, ..*old(self) }),
            final(self).parent_flow[kind.word() as int] == bits,
            final(self).parent_flow[1 - kind.word() as int] == old(self).parent_flow[1 - kind.word() as int],
        no_unwind
    ))]
    pub(crate) fn set_wrap_metric(&mut self, kind: wrap_metrics::Metric, bits: u32) {
        wrap_metrics::store_metric(&mut self.parent_flow, kind, bits);
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires index < N_SLOTS,
        ensures final(self).values@ == old(self).values@.update(index as int, value),
            final(self).flags.0 == cycle_rules::phase_word(old(self).flags.0, index as u32, cycle_rules::SOLVED),
            cycle_rules::read_state(final(self).flags.0, index as u32) == cycle_rules::SOLVED,
            forall |other: u32| other < 16 && other != index ==>
                #[trigger] cycle_rules::read_state(final(self).flags.0, other) == cycle_rules::read_state(old(self).flags.0, other),
            *final(self) == (NodeLayoutData { flags: final(self).flags, values: final(self).values, ..*old(self) }),
        no_unwind
    ))]
    pub(crate) fn publish_slot(&mut self, index: usize, value: f32) {
        cycle_rules::publish_finished_slot(&mut self.flags.0, &mut self.values, index, value);
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(published =>
        ensures if published {
            &&& !old(self).flags.is_block_item()
            &&& F::finite_word(old(self).values[cycle_rules::slot_index(axis.index(), Kind::Regular) as int])
            &&& !intrinsic || old(self).flags.0 & NodeFlags::flex_child(axis) == 0
            &&& final(self).values@ == old(self).values@.update(
                cycle_rules::slot_index(axis.index(), Kind::Final) as int,
                old(self).values[cycle_rules::slot_index(axis.index(), Kind::Regular) as int],
            )
            &&& final(self).flags.0 == cycle_rules::phase_word(
                old(self).flags.0, cycle_rules::slot_index(axis.index(), Kind::Final) as u32, cycle_rules::SOLVED)
            &&& cycle_rules::read_state(final(self).flags.0, cycle_rules::slot_index(axis.index(), Kind::Final) as u32)
                == cycle_rules::SOLVED
            &&& *final(self) == (NodeLayoutData { flags: final(self).flags, values: final(self).values, ..*old(self) })
        } else { *final(self) == *old(self) },
        no_unwind
    ))]
    pub(crate) fn try_finish_unbounded_final<F: FrameFloat>(&mut self, axis: Axis, intrinsic: bool) -> bool {
        let value = self.values[slot_index(axis, Kind::Regular)];
        if self.flags.is_block_item() || !F::finite(value)
            || intrinsic && self.flags.0 & NodeFlags::flex_child(axis) != 0
        {
            return false;
        }
        cycle_rules::publish_finished_slot(&mut self.flags.0, &mut self.values, slot_index(axis, Kind::Final), value);
        true
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures ({
            let reg = cycle_rules::slot_index(axis.index(), Kind::Regular) as int;
            let fin = cycle_rules::slot_index(axis.index(), Kind::Final) as int;
            &&& final(self).values@ == old(self).values@.update(reg, regular).update(fin, resolved)
            &&& final(self).levels@ == old(self).levels@.update(reg, _regular_level)
                .update(fin, dependency_rules::next_level(_regular_level))
            &&& final(self).flags.0 == cycle_rules::phase_word(
                cycle_rules::phase_word(old(self).flags.0, reg as u32, cycle_rules::SOLVED), fin as u32, cycle_rules::SOLVED,
            )
            &&& final(self).flags.0 & 0xfff0_0000u32 == old(self).flags.0 & 0xfff0_0000u32
            &&& cycle_rules::read_state(final(self).flags.0, reg as u32) == cycle_rules::SOLVED
            &&& cycle_rules::read_state(final(self).flags.0, fin as u32) == cycle_rules::SOLVED
            &&& forall |index: u32| index < 16 && index != reg && index != fin ==>
                #[trigger] cycle_rules::read_state(final(self).flags.0, index) == cycle_rules::read_state(old(self).flags.0, index)
        }),
        *final(self) == (NodeLayoutData { flags: final(self).flags, values: final(self).values,
            levels: final(self).levels, ..*old(self) }),
        no_unwind
    ))]
    pub(crate) fn publish_axis(&mut self, axis: Axis, regular: f32, resolved: f32, _regular_level: u16) {
        let regular_index = slot_index(axis, Kind::Regular);
        let final_index = slot_index(axis, Kind::Final);
        cycle_rules::publish_finished_pair(
            &mut self.flags.0, &mut self.values, (regular_index, regular), (final_index, resolved),
        );
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        dependency_rules::publish_levels(&mut self.levels, regular_index, final_index, _regular_level);
        #[cfg(verus_keep_ghost)]
        proof! {
            let old_flags = old(self).flags.0;
            let first = cycle_rules::phase_word(old_flags, regular_index as u32, cycle_rules::SOLVED);
            cycle_rules::phase_preserves_layout_flags(old_flags, regular_index as u32, cycle_rules::SOLVED);
            cycle_rules::phase_preserves_layout_flags(first, final_index as u32, cycle_rules::SOLVED);
        }
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl NodeLayoutData {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData {
            structural_change: old(self).structural_change.with_move(), ..*old(self)
        }),
        no_unwind
    ))]
    pub(crate) fn mark_moved(&mut self) {
        self.structural_change = self.structural_change.with_move();
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData { structural_change: StructuralChange::Subtree, ..*old(self) }),
        no_unwind
    ))]
    pub(crate) fn mark_subtree_changed(&mut self) {
        self.structural_change = StructuralChange::Subtree;
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData {
            structural_change: old(self).structural_change.with_children(), ..*old(self)
        }),
        no_unwind
    ))]
    pub(crate) fn mark_children_changed(&mut self) {
        self.structural_change = self.structural_change.with_children();
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == (NodeLayoutData { placement: PlacementWork::Subtree, ..*old(self) }),
        no_unwind
    ))]
    pub(crate) fn mark_placement_changed(&mut self) {
        self.placement = PlacementWork::Subtree;
    }
}
