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
pub(crate) const CYCLE_X: u32 = 1 << (2 * N_SLOTS);
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const CYCLE_Y: u32 = 1 << (2 * N_SLOTS + 1);

/// Record the first back edge on this axis without modifying any slot phase.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(first =>
    ensures {
        let mask = if vertical { CYCLE_Y } else { CYCLE_X };
        &&& first == (*old(flags) & mask == 0)
        &&& *final(flags) == *old(flags) | mask
        &&& forall |i: u32| i < N_SLOTS ==>
            #[trigger] read_state(*final(flags), i) == read_state(*old(flags), i)
    },
    no_unwind
))]
pub(crate) fn record_cycle_flag(flags: &mut u32, vertical: bool) -> bool {
    let mask = if vertical { CYCLE_Y } else { CYCLE_X };
    let before = *flags;
    let first = before & mask == 0;
    *flags = before | mask;
    #[cfg(verus_keep_ghost)]
    proof! {
        let updated = *flags;
        assert(CYCLE_X == 0x100000 && CYCLE_Y == 0x200000) by (compute_only);
        assert forall |i: u32| i < N_SLOTS implies
            #[trigger] read_state(updated, i) == read_state(before, i) by {
            assert(((updated >> (2 * i)) & 3) == ((before >> (2 * i)) & 3))
                by(bit_vector) requires i < 10, mask == 0x100000 || mask == 0x200000,
                    updated == before | mask;
        }
    }
    first
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const UNSOLVED: u32 = 0;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const IN_PROGRESS: u32 = 1;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const SOLVED: u32 = 2;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const CHECK_INTRINSIC: u32 = 3;

/// Every slot always contains an initialized value. The stored value of an
/// in-progress slot is the provisional value observed by a cyclic read.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires axis < 2,
    ensures value == values@[slot_index(axis, kind) as int],
    no_unwind
))]
pub(crate) fn read_slot<T: Copy>(values: &[T; N_SLOTS], axis: usize, kind: Kind) -> T {
    values[slot_index(axis, kind)]
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Entry { Reuse, BackEdge, CheckIntrinsic, Compute }

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns enter(state), no_unwind))]
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
#[cfg_attr(verus_keep_ghost, verus_spec(returns route(structural, cyclic, flow, window_changed), no_unwind))]
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
#[cfg_attr(verus_keep_ghost, verus_spec(returns canonical_axes(x, y), no_unwind))]
pub const fn canonical_axes<T: Copy>(x: T, y: T) -> [T; 2] {
    [x, y]
}

#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns declaration_order(regular, min, max), no_unwind))]
pub const fn declaration_order<T: Copy>(regular: T, min: T, max: T) -> [T; 3] {
    [regular, min, max]
}

/// Decode a request's ordinal in the fixed declaration order.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == if index < 3 {
        Some(declaration_order(Kind::Regular, Kind::Min, Kind::Max)@[index as int])
    } else { None },
    returns declared_kind(index),
    no_unwind
))]
pub(crate) fn declared_kind(index: usize) -> Option<Kind> {
    match index {
        0 => Some(Kind::Regular),
        1 => Some(Kind::Min),
        2 => Some(Kind::Max),
        _ => None,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns ready_pixel_finals(finite, has_min, has_max, block_item, width_grid_axis), no_unwind))]
pub fn ready_pixel_finals(finite: bool, has_min: bool, has_max: bool, block_item: bool, width_grid_axis: bool) -> bool {
    finite && !has_min && !has_max && !block_item && !width_grid_axis
}

/// Every fresh slot reads as zero on a back edge, except Max, which starts at infinity.
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns provisional_bits(is_max), no_unwind))]
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
    no_unwind
))]
pub fn erase_cached_slot<T: Copy>(value: &mut T, provisional: T) -> T {
    let previous = *value;
    *value = provisional;
    previous
}

#[cfg(verus_keep_ghost)]
verus! {
pub open spec fn phase_word(word: u32, index: u32, phase: u32) -> u32 {
    (word & !(3u32 << (2 * index))) | (phase << (2 * index))
}

/// Slot writes preserve the flag bits above the ten packed phases.
pub proof fn phase_preserves_layout_flags(word: u32, index: u32, phase: u32)
    requires index < 10, phase < 4,
    ensures phase_word(word, index, phase) & 0xfff0_0000u32 == word & 0xfff0_0000u32,
{
    assert(((word & !(3u32 << (2 * index))) | (phase << (2 * index))) & 0xfff0_0000u32
        == word & 0xfff0_0000u32) by(bit_vector) requires index < 10, phase < 4;
}
}

/// Mark the slot open before requesting dependencies. A constraint recheck
/// erases the old value before a dependency can reach it through a cycle.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(previous =>
    requires index < N_SLOTS, index < 16,
    ensures read_state(*final(flags), index as u32) == IN_PROGRESS,
        final(values)@ == if check {
            old(values)@.update(index as int, initial@[index as int])
        } else { old(values)@ },
        previous == if check { old(values)@[index as int] } else { empty },
        forall |other: u32| other < 16 && other != index ==>
            #[trigger] read_state(*final(flags), other) == read_state(*old(flags), other),
    no_unwind
))]
pub(crate) fn open_packed_slot<T: Copy>(flags: &mut u32, values: &mut [T; N_SLOTS], initial: &[T; N_SLOTS],
    index: usize, check: bool, empty: T,
) -> T {
    *flags = write_state(*flags, index as u32, IN_PROGRESS);
    if check { erase_cached_slot(&mut values[index], initial[index]) } else { empty }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires index < 16, index < old(values).len(),
    ensures read_state(*final(flags), index as u32) == SOLVED,
        *final(flags) == phase_word(*old(flags), index as u32, SOLVED),
        final(values)@ == old(values)@.update(index as int, value),
        *final(flags) & !(3u32 << (2 * index)) == *old(flags) & !(3u32 << (2 * index)),
        forall |other:u32| other < 16 && other != index ==>
            #[trigger] read_state(*final(flags), other) == read_state(*old(flags), other),
    no_unwind
))]
pub fn publish_finished_slot<T: Copy>(flags: &mut u32, values: &mut [T], index: usize, value: T) {
    values[index] = value;
    *flags = write_state(*flags, index as u32, SOLVED);
}

/// Publish the regular and final values produced by a specialized sizing path.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires regular.0 < old(values).len(), resolved.0 < old(values).len(),
        regular.0 < 16, resolved.0 < 16, regular.0 != resolved.0,
    ensures
        *final(flags) == phase_word(phase_word(*old(flags), regular.0 as u32, SOLVED), resolved.0 as u32, SOLVED),
        final(values)@ == old(values)@.update(regular.0 as int, regular.1).update(resolved.0 as int, resolved.1),
        read_state(*final(flags), regular.0 as u32) == SOLVED,
        read_state(*final(flags), resolved.0 as u32) == SOLVED,
        forall |i: u32| i < 16 && i != regular.0 && i != resolved.0 ==>
            #[trigger] read_state(*final(flags), i) == read_state(*old(flags), i),
    no_unwind
))]
pub fn publish_finished_pair<T: Copy>(flags: &mut u32, values: &mut [T], regular: (usize, T), resolved: (usize, T)) {
    publish_finished_slot(flags, values, regular.0, regular.1);
    publish_finished_slot(flags, values, resolved.0, resolved.1);
}

/// Read the packed phase and select its dependency-entry behavior.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(entry =>
    requires axis < 2,
    ensures entry == enter(read_state(flags, slot_index(axis, kind) as u32)),
    no_unwind
))]
pub(crate) fn enter_packed_slot(flags: u32, axis: usize, kind: Kind) -> Entry {
    enter(read_state(flags, slot_index(axis, kind) as u32))
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
    ensures result == phase_word(word, index, state),
        read_state(result, index) == state,
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
#[cfg_attr(verus_keep_ghost, verus_spec(returns same_intrinsic_constraint(opposite_state, resolved_bits, saved_bits), no_unwind))]
pub fn same_intrinsic_constraint(opposite_state: u32, resolved_bits: u32, saved_bits: u32) -> bool {
    opposite_state == SOLVED && resolved_bits == saved_bits
}


// Binary32 bit access is a total primitive and preserves every representation.
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
pub(crate) trait SlotBits: Copy {
    fn bits(self) -> u32;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait SlotBits: Copy {
    spec fn word(self) -> u32;
    fn bits(self) -> (result: u32)
        ensures result == self.word(),
        no_unwind;
}
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
impl SlotBits for f32 {
    #[inline(always)]
    fn bits(self) -> u32 { self.to_bits() }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(same =>
    requires axis < 2,
    ensures same == solved_pixel_matches(flags, cached, fresh, axis, kind),
    no_unwind
))]
fn same_solved_pixel<T: SlotBits>(
    flags: u32, cached: &[T; N_SLOTS], fresh: &[T; N_SLOTS], axis: usize, kind: Kind,
) -> bool {
    let index = slot_index(axis, kind);
    read_state(flags, index as u32) == SOLVED && cached[index].bits() == fresh[index].bits()
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn solved_pixel_matches<T: SlotBits>(
    flags: u32, cached: &[T; N_SLOTS], fresh: &[T; N_SLOTS], axis: usize, kind: Kind,
) -> bool {
    let index = slot_index(axis, kind);
    read_state(flags, index as u32) == SOLVED && cached@[index as int].word() == fresh@[index as int].word()
}
}

/// Retention requires both the Regular and Final slots on both axes to be
/// solved and to match the corresponding freshly seeded binary32 words.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(same =>
    ensures same == (
        solved_pixel_matches(flags, cached, fresh, 0, Kind::Regular)
        && solved_pixel_matches(flags, cached, fresh, 0, Kind::Final)
        && solved_pixel_matches(flags, cached, fresh, 1, Kind::Regular)
        && solved_pixel_matches(flags, cached, fresh, 1, Kind::Final)
    ),
    no_unwind
))]
pub(crate) fn same_solved_pixels<T: SlotBits>(flags: u32, cached: &[T; N_SLOTS], fresh: &[T; N_SLOTS]) -> bool {
    same_solved_pixel(flags, cached, fresh, 0, Kind::Regular)
        && same_solved_pixel(flags, cached, fresh, 0, Kind::Final)
        && same_solved_pixel(flags, cached, fresh, 1, Kind::Regular)
        && same_solved_pixel(flags, cached, fresh, 1, Kind::Final)
}
