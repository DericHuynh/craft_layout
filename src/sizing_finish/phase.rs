//! Packed slot state and rank changes during one sizing visit.
#![allow(unexpected_cfgs)]

use super::{cycle_rules, store_size, Request, StoredSize};
use crate::declarations::Axis;
use crate::node_data::NodeLayoutData;
use crate::node_flags::slot_index;
use crate::prepare_frame::FrameFloat;
#[cfg(verus_keep_ghost)]
use crate::prepare_frame::FrameWords;
use cycle_rules::{Entry, N_SLOTS};
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::solve::dependency_rules;
#[cfg(verus_keep_ghost)]
use crate::dependencies::rules as dependency_rules;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct OpenSlot<I> {
    pub(crate) slot: Request<I>,
    previous: f32,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    outer_level: u16,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<I> OpenSlot<I> {
    pub(crate) closed spec fn requested(self) -> Request<I> { self.slot }
    pub(crate) closed spec fn saved_value(self) -> f32 { self.previous }
    pub(crate) closed spec fn saved_level(self) -> u16 { self.outer_level }
}

pub(crate) trait PhaseModel<I> {
    spec fn phase_records(&self) -> spec_fn(I) -> NodeLayoutData;
    spec fn provisional() -> [f32; N_SLOTS];
    spec fn dependency_level(&self) -> u16;
}

pub(crate) open spec fn phase_index<I>(slot: Request<I>) -> usize {
    cycle_rules::slot_index(slot.vertical as usize, slot.kind)
}

pub(crate) open spec fn phase<I, A: PhaseModel<I> + ?Sized>(host: &A, slot: Request<I>) -> u32 {
    cycle_rules::read_state(host.phase_records()(slot.node).flags.0, phase_index(slot) as u32)
}

pub(crate) open spec fn changes_phase<I, A: PhaseModel<I> + ?Sized>(
    before: &A, after: &A, slot: Request<I>, state: u32,
) -> bool {
    forall |request: Request<I>| #[trigger] phase(after, request) ==
        if phase_index(request) == phase_index(slot) && request.node == slot.node { state }
        else { phase(before, request) }
}

pub(crate) open spec fn same_phases<I, A: PhaseModel<I> + ?Sized>(before: &A, after: &A) -> bool {
    forall |request: Request<I>| #[trigger] phase(after, request) == phase(before, request)
}

fn save_phases<I, A: PhaseModel<I> + ?Sized>(host: &A)
    -> (saved: Ghost<spec_fn(Request<I>) -> u32>)
    ensures forall |req: Request<I>| #[trigger] saved@(req) == phase(host, req),
    no_unwind
{ Ghost(|req: Request<I>| phase(host, req)) }

pub(crate) open spec fn constraint_matches<F: FrameFloat, I>(record: NodeLayoutData, slot: Request<I>) -> bool {
    let opposite = cycle_rules::slot_index((!slot.vertical) as usize, cycle_rules::Kind::Final);
    let saved = cycle_rules::slot_index(1, cycle_rules::Kind::Flow);
    cycle_rules::same_intrinsic_constraint(cycle_rules::read_state(record.flags.0, opposite as u32),
        F::word(record.values[opposite as int]), F::word(record.values[saved as int]))
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait PhaseModel<I> {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized, I> PhaseModel<I> for T {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait PhaseAccess: PhaseModel<Self::Id> {
    type Id: Copy;
    type Float: FrameFloat;

    #[cfg_attr(verus_keep_ghost, verus_spec(record => ensures *record == self.phase_records()(node), no_unwind))]
    fn node_record(&self, node: Self::Id) -> &NodeLayoutData;

    #[cfg_attr(verus_keep_ghost, verus_spec(record =>
        ensures *record == old(self).phase_records()(node),
            final(self).phase_records()(node) == *final(record),
            final(self).dependency_level() == old(self).dependency_level(),
            forall |other: Self::Id| other != node ==>
                #[trigger] final(self).phase_records()(other) == old(self).phase_records()(other),
        no_unwind
    ))]
    fn edit_record(&mut self, node: Self::Id) -> &mut NodeLayoutData;

    #[cfg_attr(verus_keep_ghost, verus_spec(values => ensures *values == Self::provisional(), no_unwind))]
    fn initial_values() -> &'static [f32; N_SLOTS];

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(level =>
        ensures *level == old(self).dependency_level(), final(self).dependency_level() == *final(level),
            final(self).phase_records() == old(self).phase_records(),
        no_unwind
    ))]
    fn current_level(&mut self) -> &mut u16;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).phase_records() == old(self).phase_records(),
            final(self).dependency_level() == old(self).dependency_level(),
        no_unwind
    ))]
    fn saw_cycle(&mut self);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).phase_records() == old(self).phase_records(),
            final(self).dependency_level() == old(self).dependency_level(),
        no_unwind
    ))]
    fn warn_cycle(&mut self, node: Self::Id, axis: Axis);

    #[cfg_attr(verus_keep_ghost, verus_spec(stored =>
        ensures changes_phase(old(self), final(self), slot, cycle_rules::SOLVED),
            final(self).dependency_level() == old(self).dependency_level(),
            stored.slot == slot, stored.value == final(self).phase_records()(slot.node).values@[phase_index(slot) as int],
        no_unwind
    ))]
    fn recompute(&mut self, slot: Request<Self::Id>) -> StoredSize<Self::Id>;
}

#[cold]
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures same_phases::<A::Id, A>(old(host), final(host)),
        final(host).dependency_level() == old(host).dependency_level(),
    no_unwind
))]
fn record_cycle<A: PhaseAccess + ?Sized>(host: &mut A, slot: Request<A::Id>) {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    host.saw_cycle();
    let flags = &mut host.edit_record(slot.node).flags;
    let first = cycle_rules::record_cycle_flag(&mut flags.0, slot.vertical);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |req: Request<A::Id>| #[trigger] phase(host, req) == phase(old(host), req) by {
            assert(phase_index(req) < N_SLOTS);
            if req.node != slot.node { assert(host.phase_records()(req.node) == old(host).phase_records()(req.node)); }
        }
    }
    if first {
        host.warn_cycle(slot.node, slot.axis());
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    ensures next == match cycle_rules::enter(cycle_rules::read_state(
        old(host).phase_records()(slot.node).flags.0, phase_index(slot) as u32,
    )) {
        Entry::Reuse | Entry::BackEdge => None,
        Entry::CheckIntrinsic => Some(true),
        Entry::Compute => Some(false),
    },
        same_phases::<A::Id, A>(old(host), final(host)),
        final(host).dependency_level() == if phase(old(host), slot) == cycle_rules::SOLVED {
            dependency_rules::include_level(old(host).dependency_level(),
                old(host).phase_records()(slot.node).levels@[phase_index(slot) as int])
        } else { old(host).dependency_level() },
    no_unwind
))]
pub(crate) fn enter_slot<A: PhaseAccess + ?Sized>(host: &mut A, slot: Request<A::Id>) -> Option<bool> {
    let record = host.node_record(slot.node);
    let axis = slot.axis().index();
    let entry = cycle_rules::enter_packed_slot(record.flags.0, axis, slot.kind);
    match entry {
        Entry::Reuse => {
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            {
                let level = cycle_rules::read_slot(&record.levels, axis, slot.kind);
                let current = host.current_level();
                *current = dependency_rules::include_level(*current, level);
            }
            None
        }
        Entry::BackEdge => {
            record_cycle(host, slot);
            None
        }
        Entry::CheckIntrinsic => Some(cfg!(any(feature = "incremental", verus_keep_ghost))),
        Entry::Compute => Some(false),
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(opened =>
    ensures opened.requested() == slot,
        changes_phase(old(host), final(host), slot, cycle_rules::IN_PROGRESS),
        opened.saved_level() == old(host).dependency_level(), final(host).dependency_level() == 0,
        CHECK ==> opened.saved_value() == old(host).phase_records()(slot.node).values[phase_index(slot) as int],
        final(host).phase_records()(slot.node).values@ == if CHECK {
            old(host).phase_records()(slot.node).values@.update(phase_index(slot) as int, A::provisional()[phase_index(slot) as int])
        } else { old(host).phase_records()(slot.node).values@ },
    no_unwind
))]
pub(crate) fn open_slot<A: PhaseAccess + ?Sized, const CHECK: bool>(
    host: &mut A, slot: Request<A::Id>,
) -> OpenSlot<A::Id> {
    let data = host.edit_record(slot.node);
    let index = slot_index(slot.axis(), slot.kind);
    // Cycle reads observe the provisional word while the former constraint is checked.
    let previous = cycle_rules::open_packed_slot(&mut data.flags.0, &mut data.values, A::initial_values(), index, CHECK, 0.0);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |req: Request<A::Id>| #[trigger] phase(host, req) ==
            (if phase_index(req) == phase_index(slot) && req.node == slot.node { cycle_rules::IN_PROGRESS }
            else { phase(old(host), req) }) by {
            assert(phase_index(req) < N_SLOTS);
            if req.node != slot.node { assert(host.phase_records()(req.node) == old(host).phase_records()(req.node)); }
        }
    }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let outer_level = dependency_rules::capture_level(host.current_level());
    OpenSlot {
        slot,
        previous,
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        outer_level,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(matched =>
    ensures matched == constraint_matches::<A::Float, A::Id>(*record, slot),
    no_unwind
))]
fn cached_constraint<A: PhaseAccess + ?Sized>(record: &NodeLayoutData, slot: Request<A::Id>) -> bool {
    let opposite = slot.axis().other();
    cycle_rules::same_intrinsic_constraint(
        record.flags.check_state(opposite, cycle_rules::Kind::Final),
        A::Float::bits(cycle_rules::read_slot(&record.values, opposite.index(), cycle_rules::Kind::Final)),
        A::Float::bits(cycle_rules::read_slot(&record.values, 1, cycle_rules::Kind::Flow)),
    )
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(stored =>
    ensures changes_phase(old(host), final(host), opened.requested(), cycle_rules::SOLVED),
        final(host).phase_records()(opened.requested().node).levels@[phase_index(opened.requested()) as int]
            == old(host).dependency_level(),
        final(host).dependency_level() == dependency_rules::include_level(opened.saved_level(), old(host).dependency_level()),
        CHECK && constraint_matches::<A::Float, A::Id>(old(host).phase_records()(opened.requested().node), opened.requested())
        ==> ({
            let slot = opened.requested();
            let final_record = final(host).phase_records()(slot.node);
            &&& final_record.values@[phase_index(slot) as int] == opened.saved_value()
            &&& cycle_rules::read_state(final_record.flags.0, phase_index(slot) as u32) == cycle_rules::SOLVED
        }),
        stored.slot == opened.requested(),
        stored.value == final(host).phase_records()(stored.slot.node).values@[phase_index(stored.slot) as int],
    no_unwind
))]
pub(crate) fn finish_open_slot<A: PhaseAccess + ?Sized, const CHECK: bool>(host: &mut A, opened: OpenSlot<A::Id>) -> StoredSize<A::Id> {
    let slot = opened.slot;
    let record = host.node_record(slot.node);
    let stored = if CHECK && cached_constraint::<A>(record, slot) {
        let stored = store_size(host.edit_record(slot.node), slot, opened.previous);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |req: Request<A::Id>| #[trigger] phase(host, req) ==
                (if phase_index(req) == phase_index(slot) && req.node == slot.node { cycle_rules::SOLVED }
                else { phase(old(host), req) }) by {
                assert(phase_index(req) < N_SLOTS);
                if req.node != slot.node { assert(host.phase_records()(req.node) == old(host).phase_records()(req.node)); }
            }
        }
        stored
    } else {
        host.recompute(slot)
    };
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    {
        #[cfg(verus_keep_ghost)]
        let prior = save_phases::<A::Id, A>(host);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(changes_phase(old(host), host, slot, cycle_rules::SOLVED));
            assert forall |req: Request<A::Id>| #[trigger] prior@(req) ==
                (if phase_index(req) == phase_index(slot) && req.node == slot.node { cycle_rules::SOLVED }
                else { phase(old(host), req) }) by {
                assert(prior@(req) == phase(host, req));
            }
        }
        let current = host.current_level();
        let level = *current;
        *current = dependency_rules::include_level(opened.outer_level, level);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |req: Request<A::Id>| #[trigger] phase(host, req) == prior@(req) by {
                assert(prior@(req) == phase(host, req));
            }
        }
        dependency_rules::publish_level(&mut host.edit_record(slot.node).levels, slot_index(slot.axis(), slot.kind), level);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |req: Request<A::Id>| #[trigger] phase(host, req) == prior@(req) by {
                assert(prior@(req) == phase(host, req));
            }
        }
    }
    stored
}

/// The inline DFS and the spill driver share the same packed slot transitions.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(start =>
    ensures match start {
        Some((opened, check)) => opened.requested() == slot && changes_phase(old(host), final(host), slot, cycle_rules::IN_PROGRESS)
            && check == (phase(old(host), slot) == cycle_rules::CHECK_INTRINSIC),
        None => same_phases::<A::Id, A>(old(host), final(host))
            && (phase(old(host), slot) == cycle_rules::SOLVED || phase(old(host), slot) == cycle_rules::IN_PROGRESS),
    },
    no_unwind
))]
pub(crate) fn start_slot<A: PhaseAccess + ?Sized>(host: &mut A, slot: Request<A::Id>) -> Option<(OpenSlot<A::Id>, bool)> {
    let check = enter_slot(host, slot)?;
    let opened = if check { open_slot::<_, true>(host, slot) } else { open_slot::<_, false>(host, slot) };
    Some((opened, check))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(stored =>
    ensures changes_phase(old(host), final(host), opened.requested(), cycle_rules::SOLVED),
        final(host).phase_records()(opened.requested().node).levels@[phase_index(opened.requested()) as int]
            == old(host).dependency_level(),
        final(host).dependency_level() == dependency_rules::include_level(opened.saved_level(), old(host).dependency_level()),
        stored.slot == opened.requested(),
        stored.value == final(host).phase_records()(stored.slot.node).values@[phase_index(stored.slot) as int],
    no_unwind
))]
pub(crate) fn resume_slot<A: PhaseAccess + ?Sized>(host: &mut A, opened: OpenSlot<A::Id>, check: bool) -> StoredSize<A::Id> {
    if check { finish_open_slot::<_, true>(host, opened) }
    else { finish_open_slot::<_, false>(host, opened) }
}
