// DFS slot entry and measurement routing shared with the cyclic replay proof.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    Regular,
    Final,
    Min,
    Max,
    EvenShare,
    Flow,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const N_SLOTS: usize = 10;

/// Four slots per axis, plus the node's shared Fill and flow slots.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(index =>
    requires axis < 2,
    ensures index < N_SLOTS, index < 16,
    returns slot_index(axis, kind),
    no_unwind
))]
pub(crate) const fn slot_index(axis: usize, kind: Kind) -> usize {
    match kind {
        Kind::EvenShare => 8,
        Kind::Flow => 9,
        _ => kind as usize * 2 + axis,
    }
}

/// Population counts are stored as u32 even when an adapter uses wider IDs.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == vstd::math::min(total as int + added, u32::MAX as int),
    no_unwind
))]
pub(crate) fn add_count(total: u32, added: u32) -> u32 {
    total.saturating_add(added)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const UNSOLVED: u32 = 0;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const IN_PROGRESS: u32 = 1;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const SOLVED: u32 = 2;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const CHECK_INTRINSIC: u32 = 3;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Entry { Reuse, BackEdge, CheckIntrinsic, Compute }

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns enter(state)))]
pub fn enter(state: u32) -> Entry {
    match state {
        SOLVED => Entry::Reuse,
        IN_PROGRESS => Entry::BackEdge,
        CHECK_INTRINSIC => Entry::CheckIntrinsic,
        _ => Entry::Compute,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg(any(feature = "incremental", verus_keep_ghost))]
pub enum Route { Structural, Cycle, Flow, Queue }

#[inline]
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns route(structural, cyclic, flow, window_changed)))]
pub fn route(structural: bool, cyclic: bool, flow: bool, window_changed: bool) -> Route {
    if structural { Route::Structural }
    else if cyclic { Route::Cycle }
    else if flow && window_changed { Route::Flow }
    else { Route::Queue }
}

// The root and declaration orders are observable when a dependency reads an
// in-progress slot. Full and regional measurement both use these sequences.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns canonical_axes(x, y)))]
pub const fn canonical_axes<T: Copy>(x: T, y: T) -> [T; 2] {
    [x, y]
}

#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns declaration_order(regular, min, max)))]
pub const fn declaration_order<T: Copy>(regular: T, min: T, max: T) -> [T; 3] {
    [regular, min, max]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns ready_pixel_finals(finite, has_min, has_max, block_item, width_grid_axis)))]
pub fn ready_pixel_finals(finite: bool, has_min: bool, has_max: bool, block_item: bool, width_grid_axis: bool) -> bool {
    finite && !has_min && !has_max && !block_item && !width_grid_axis
}

/// Every fresh slot reads as zero on a back edge, except Max, which starts at infinity.
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns provisional_bits(is_max)))]
pub const fn provisional_bits(is_max: bool) -> u32 {
    // IEEE binary32 positive infinity and positive zero.
    if is_max { 0x7f80_0000 } else { 0 }
}

/// A cached intrinsic slot must expose its fresh provisional value before DFS
/// follows its dependencies and checks whether the remembered value is valid.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(previous =>
    ensures previous == *old(value), *final(value) == provisional,
))]
pub fn erase_cached_slot<T: Copy>(value: &mut T, provisional: T) -> T {
    let previous = *value;
    *value = provisional;
    previous
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires index < 16,
    ensures read_state(*final(flags), index) == SOLVED, *final(slot) == value,
        forall |other:u32| other < 16 && other != index ==>
            #[trigger] read_state(*final(flags), other) == read_state(*old(flags), other),
    no_unwind
))]
pub fn publish_finished_slot<T: Copy>(flags: &mut u32, slot: &mut T, index: u32, value: T) {
    *slot = value;
    *flags = write_state(*flags, index, SOLVED);
}

/// Publish the regular and final values produced by a specialized sizing path.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires regular.0 < old(values).len(), resolved.0 < old(values).len(),
        regular.0 < 16, resolved.0 < 16, regular.0 != resolved.0,
    ensures
        final(values)@ == old(values)@.update(regular.0 as int, regular.1).update(resolved.0 as int, resolved.1),
        read_state(*final(flags), regular.0 as u32) == SOLVED,
        read_state(*final(flags), resolved.0 as u32) == SOLVED,
        forall |i: u32| i < 16 && i != regular.0 && i != resolved.0 ==>
            #[trigger] read_state(*final(flags), i) == read_state(*old(flags), i),
    no_unwind
))]
pub fn publish_finished_pair<T: Copy>(flags: &mut u32, values: &mut [T], regular: (usize, T), resolved: (usize, T)) {
    publish_finished_slot(flags, &mut values[regular.0], regular.0 as u32, regular.1);
    publish_finished_slot(flags, &mut values[resolved.0], resolved.0 as u32, resolved.1);
}

/// A slot occupies two bits. The remaining high bits belong to node flags.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires index < 16,
    returns read_state(word, index),
    no_unwind
))]
pub fn read_state(word: u32, index: u32) -> u32 {
    (word >> (2 * index)) & 3
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires index < 16, state < 4,
    ensures read_state(result, index) == state,
        forall|other:u32| other < 16 && other != index ==>
            #[trigger] read_state(result, other) == read_state(word, other),
        result & !(3u32 << (2 * index)) == word & !(3u32 << (2 * index)),
    no_unwind
))]
pub fn write_state(word: u32, index: u32, state: u32) -> u32 {
    let mask = 3u32 << (2 * index);
    let result = (word & !mask) | (state << (2 * index));
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(((result >> (2 * index)) & 3u32) == state && (result & !mask) == (word & !mask))
            by(bit_vector) requires index < 16, state < 4,
                mask == 3u32 << (2 * index), result == (word & !mask) | (state << (2 * index));
        assert forall|other:u32| other < 16 && other != index implies
            #[trigger] read_state(result, other) == read_state(word, other) by {
            assert(((result >> (2 * other)) & 3u32) == ((word >> (2 * other)) & 3u32))
                by(bit_vector) requires index < 16, state < 4, other < 16, other != index,
                    mask == 3u32 << (2 * index), result == (word & !mask) | (state << (2 * index));
        }
    }
    result
}

/// The cached intrinsic measurement was made at this exact opposite size.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns same_intrinsic_constraint(opposite_state, resolved_bits, saved_bits)))]
pub fn same_intrinsic_constraint(opposite_state: u32, resolved_bits: u32, saved_bits: u32) -> bool {
    opposite_state == SOLVED && resolved_bits == saved_bits
}
