//! The bounded driver for ranked incremental sizing work.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use crate::publication::IncrementalRelayoutOutcome;
#[cfg(not(verus_keep_ghost))]
use super::IncrementalRelayoutOutcome;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::{Kind, N_SLOTS, SOLVED, UNSOLVED, read_state, slot_index, write_state};
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::{Kind, N_SLOTS, SOLVED, UNSOLVED, read_state, slot_index, write_state};
#[cfg(verus_keep_ghost)]
use crate::dependencies::rules::{charge_queue_slot, queueable};
#[cfg(not(verus_keep_ghost))]
use crate::solve::dependency_rules::{charge_queue_slot, queueable};
#[cfg(verus_keep_ghost)]
use crate::grid::frame::state::count_changed;
#[cfg(not(verus_keep_ghost))]
use crate::grid_state::count_changed;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::sizing_tape::{self, CaptureInputs, Datum, SlotProgram};
#[cfg(verus_keep_ghost)]
use crate::dependencies::sizing_requests::Request;
use super::intake::{self, ChangeBuffers, Changes, WindowChange};
use super::tape::{self, Axes, EditEquality, Tape};
use super::tape_plan::{self, Ranked};
use crate::vec_memory::{FallibleVecMemory, VecMemory, try_append};
#[cfg(verus_keep_ghost)]
use crate::prepare_nodes::live;
use crate::node_data::NodeLayoutData;
use crate::prepare_frame::FrameFloat;
#[cfg(verus_keep_ghost)]
use crate::prepare_frame::FrameWords;
#[cfg(verus_keep_ghost)]
use super::{did_pop, well_formed, kernel::WorkQueue};
#[cfg(not(verus_keep_ghost))]
use super::WorkQueue;

#[path = "produce.rs"]
pub(crate) mod produce;
#[cfg(verus_keep_ghost)]
#[path = "producers.rs"]
pub(crate) mod producers;

#[cfg(verus_keep_ghost)]
#[path = "registered_pixels.rs"]
pub(crate) mod registered_pixels;

#[cfg(verus_keep_ghost)]
#[path = "root_viewport.rs"]
pub(crate) mod root_viewport;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum QueuePoll<T> {
    Next(T),
    Empty,
    Fallback(IncrementalRelayoutOutcome),
}

/// A pending fallback takes priority over every queued slot. Otherwise the
/// native queue returns the lowest rank and clears storage once exhausted.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires well_formed(old(queue)),
    ensures well_formed(final(queue)), match out {
        QueuePoll::Fallback(reason) => pending == Some(reason) && *final(queue) == *old(queue),
        QueuePoll::Empty => pending.is_none() && did_pop(old(queue), final(queue), None),
        QueuePoll::Next((rank, slot)) => pending.is_none() && did_pop(old(queue), final(queue), Some(slot))
            && rank == final(queue).first_level as int + final(queue).cursor,
    },
    no_unwind
))]
pub(crate) fn poll_queue<T: Copy, M: VecMemory>(
    queue: &mut WorkQueue<T>, pending: Option<IncrementalRelayoutOutcome>,
) -> QueuePoll<(u16, T)> {
    if let Some(reason) = pending {
        QueuePoll::Fallback(reason)
    } else {
        match queue.pop_with::<M>() {
            Some(slot) => QueuePoll::Next(slot),
            None => QueuePoll::Empty,
        }
    }
}

/// Invalidate the one exact packed slot for a ranked push.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires axis < 2,
    ensures ({
        let i = slot_index(axis, kind) as u32;
        if read_state(*old(flags), i) == SOLVED {
            &&& out == Some(levels@[i as int])
            &&& read_state(*final(flags), i) == UNSOLVED
            &&& forall |j: u32| j < 16 && j != i ==> #[trigger] read_state(*final(flags), j) == read_state(*old(flags), j)
        } else { out.is_none() && *final(flags) == *old(flags) }
    }),
    no_unwind
))]
pub(crate) fn invalidate_solved(
    levels: &[u16; N_SLOTS], flags: &mut u32, axis: usize, kind: Kind,
) -> Option<u16> {
    let index = slot_index(axis, kind);
    if read_state(*flags, index as u32) != SOLVED { return None; }
    *flags = write_state(*flags, index as u32, UNSOLVED);
    Some(levels[index])
}

/// Only an admissible slot yields a token for reading the same word again.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Copy))]
pub(crate) struct SlotObservation<T> {
    index: usize,
    pub value: T,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<T> SlotObservation<T> {
    pub(crate) closed spec fn valid(self) -> bool {
        self.index < N_SLOTS
    }

    pub(crate) closed spec fn at(self, values: Seq<T>) -> T {
        values[self.index as int]
    }

    pub(crate) closed spec fn previous(self) -> T {
        self.value
    }
}
}

impl<T: Copy> SlotObservation<T> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(value =>
        requires self.valid(),
        ensures value == self.at(values@),
        no_unwind
    ))]
    pub(crate) fn load(self, values: &[T; N_SLOTS]) -> T {
        values[self.index]
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires axis < 2,
    ensures out.is_some() == ((allow_flow || !(kind is Flow)) && state == UNSOLVED && queueable(rank)
            && levels@[slot_index(axis, kind) as int] == rank),
        out.is_some() ==> out.unwrap().valid()
            && out.unwrap().previous() == values@[slot_index(axis, kind) as int]
            && out.unwrap().at(values@) == out.unwrap().previous()
            && forall |v: Seq<T>| #[trigger] out.unwrap().at(v) == v[slot_index(axis, kind) as int],
    no_unwind
))]
fn inspect_slot<T: Copy>(
    levels: &[u16; N_SLOTS], values: &[T; N_SLOTS], axis: usize, kind: Kind, state: u32, rank: u16,
    allow_flow: bool,
) -> Option<SlotObservation<T>> {
    let index = slot_index(axis, kind);
    if (!allow_flow && matches!(kind, Kind::Flow)) || state != UNSOLVED || !queueable(rank) || levels[index] != rank {
        return None;
    }
    Some(SlotObservation { index, value: values[index] })
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct SlotWords<'a, T> {
    pub levels: &'a [u16; N_SLOTS],
    pub values: &'a [T; N_SLOTS],
    pub state: u32,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires axis < 2,
    ensures out.state == read_state(flags, slot_index(axis, kind) as u32), out.levels == levels, out.values == values,
    no_unwind
))]
pub(crate) fn slot_words<'a, T>(
    levels: &'a [u16; N_SLOTS], values: &'a [T; N_SLOTS], flags: u32, axis: usize, kind: Kind,
) -> SlotWords<'a, T> {
    SlotWords { levels, values, state: read_state(flags, slot_index(axis, kind) as u32) }
}

// This bit belongs to the current numeric attempt. Placement only
// consumes its own bits in the same word.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const BUDGET_OWNER: u8 = 128;
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const PLACEMENT_BITS: u8 = 127;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns marked(word), no_unwind))]
pub(crate) fn marked(word: u8) -> bool {
    word & BUDGET_OWNER != 0
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures marked(*final(word)) == checked, *final(word) & PLACEMENT_BITS == *old(word) & PLACEMENT_BITS,
    no_unwind
))]
fn set_mark(word: &mut u8, checked: bool) {
    let before = *word;
    *word = if checked { before | BUDGET_OWNER } else { before & PLACEMENT_BITS };
    #[cfg(verus_keep_ghost)]
    proof! {
        let after = *word;
        assert(BUDGET_OWNER == 128 && PLACEMENT_BITS == 127);
        if checked {
            assert(after == before | 128u8);
            assert(after & 128u8 != 0 && after & 127u8 == before & 127u8)
                by (bit_vector) requires after == before | 128u8;
        } else {
            assert(after == before & 127u8);
            assert(after & 128u8 == 0 && after & 127u8 == before & 127u8)
                by (bit_vector) requires after == before & 127u8;
        }
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures
        marked(final(record).prepared_placement) == checked,
        final(record).prepared_placement & PLACEMENT_BITS == old(record).prepared_placement & PLACEMENT_BITS,
        *final(record) == (NodeLayoutData { prepared_placement: final(record).prepared_placement, ..*old(record) }),
    no_unwind
))]
pub(crate) fn mark_record(record: &mut NodeLayoutData, checked: bool) {
    set_mark(&mut record.prepared_placement, checked);
}

#[cfg(verus_keep_ghost)]
verus! {
/// Projection for dependency graphs with one scalar binary32 value per slot.
pub(crate) struct ScalarQueue<I> {
    pub(crate) program: SlotProgram<I>,
    pub(crate) words: Seq<Datum>,
    pub(crate) pending: Set<int>,
}

impl<I> ScalarQueue<I> {
    pub(crate) open spec fn sound(self) -> bool {
        self.program.valid() && self.program.queue_sound(self.words, self.pending)
    }

    pub(crate) open spec fn consume(self, slot: int) -> Self {
        ScalarQueue { pending: self.pending.remove(slot), ..self }
    }

    pub(crate) open spec fn evaluate(self, slot: int) -> Self {
        ScalarQueue {
            words: self.words.update(slot, self.program.word_at(self.words, slot)),
            ..self
        }
    }
}

pub(crate) trait QueueModel: intake::Model {
    type Slot: Copy;

    spec fn resolved(&self) -> nat;
    spec fn queue_empty(&self) -> bool;
    spec fn budget_marked(&self) -> Set<Self::Id>;
    spec fn owner(slot: Self::Slot) -> Self::Id;
    spec fn live_slot(&self, slot: Self::Slot) -> bool;
    spec fn physical_request(&self, slot: Self::Slot) -> Request<Self::Id>;
}
}
#[cfg(not(verus_keep_ghost))]
pub(crate) trait QueueModel: intake::Model {
    type Slot: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn certified_scalar_queue<Q: QueueModel + ?Sized>(work: &Q) -> bool {
    intake::scalar(work).is_some() && intake::scalar(work).unwrap().sound()
}

pub(crate) open spec fn covered_scalar_inputs<S: intake::Model + ?Sized>(
    source: &S, program: SlotProgram<S::Id>, pending: Set<int>,
    seeds: Seq<intake::Seed<S::Id, S::Change>>,
) -> bool {
    &&& source.scalar_mode()
    &&& program.valid() && program.previous(source.slot_words())
    &&& forall |i: int| 0 <= i < program.keys.len() && program.previous_inputs[i] != program.inputs[i]
        ==> pending.contains(i) || exists |j: int| 0 <= j < seeds.len()
            && (source.seed_positions())(#[trigger] seeds[j]).contains(i)
}

pub(crate) open spec fn seeds_for<S: ChangeBuffers<W> + ?Sized, W: Copy>(
    work: &S, axes: Axes, changes: Seq<(S::Id, S::Change)>, content: Seq<S::Id>,
) -> Seq<intake::Seed<S::Id, S::Change>> {
    intake::window_seeds(work.recorded_root(), axes.horizontal, axes.vertical)
        + intake::node_seeds(changes) + intake::content_seeds(content)
}

fn save_scalar<Q: QueueModel + ?Sized>(work: &Q) -> (out: Ghost<Option<ScalarQueue<Q::Id>>>)
    ensures out@ == intake::scalar(work),
    no_unwind
{ Ghost(intake::scalar(work)) }

fn save_request<Q: QueueModel + ?Sized>(work: &Q, slot: Q::Slot) -> (out: Ghost<Request<Q::Id>>)
    ensures out@ == work.physical_request(slot),
    no_unwind
{ Ghost(work.physical_request(slot)) }
}

/// The native bindings expose slot-record words, the queue storage, and the
/// two sizing operations that consume a computed slot or propagate its result.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait QueueActions: QueueModel {
    type BudgetMemory: VecMemory + FallibleVecMemory;

    // The numeric driver gives back this buffer only after clearing all marks.
    #[cfg_attr(verus_keep_ghost, verus_spec(nodes =>
        ensures nodes@.len() == 0, final(self).budget_marked().is_empty(),
            final(self).resolved() == old(self).resolved(), final(self).order() == old(self).order(),
            final(self).queue_empty() == old(self).queue_empty(),
            intake::scalar(final(self)) == intake::scalar(old(self)),
        no_unwind
    ))]
    fn take_budget_nodes(&mut self) -> Vec<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires nodes@.len() == 0, old(self).budget_marked().is_empty(),
        ensures final(self).budget_marked().is_empty(),
            final(self).resolved() == old(self).resolved(), final(self).order() == old(self).order(),
            final(self).queue_empty() == old(self).queue_empty(),
            intake::scalar(final(self)) == intake::scalar(old(self)),
        no_unwind
    ))]
    fn recycle_budget_nodes(&mut self, nodes: Vec<Self::Id>);

    #[cfg_attr(verus_keep_ghost, verus_spec(marked =>
        requires live(self, node),
        ensures marked == self.budget_marked().contains(node),
        no_unwind
    ))]
    fn budget_mark(&self, node: Self::Id) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node),
        ensures final(self).budget_marked() == if marked {
                old(self).budget_marked().insert(node)
            } else { old(self).budget_marked().remove(node) },
            final(self).resolved() == old(self).resolved(), final(self).order() == old(self).order(),
            final(self).queue_empty() == old(self).queue_empty(),
            intake::scalar(final(self)) == intake::scalar(old(self)),
            forall |slot: Self::Slot| #[trigger] final(self).live_slot(slot) == old(self).live_slot(slot),
            forall |slot: Self::Slot| #[trigger] final(self).physical_request(slot) == old(self).physical_request(slot),
        no_unwind
    ))]
    fn mark_budget_node(&mut self, node: Self::Id, marked: bool);


    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures
            final(self).resolved() == old(self).resolved(),
            final(self).order() == old(self).order(), final(self).budget_marked() == old(self).budget_marked(),
            out is Empty ==> final(self).queue_empty(),
            if let QueuePoll::Next(slot) = out { final(self).live_slot(slot) } else { true },
            if let Some(scalar) = intake::scalar(old(self)) {
                match out {
                    QueuePoll::Next(slot) => {
                        let request = old(self).physical_request(slot);
                        let at = scalar.program.position(request);
                        &&& scalar.program.keys.contains(request)
                        &&& scalar.pending.contains(at)
                        &&& final(self).physical_request(slot) == request
                        &&& intake::scalar(final(self)) == Some(scalar.consume(at))
                    },
                    QueuePoll::Empty => scalar.pending.is_empty() && intake::scalar(final(self)) == Some(scalar),
                    QueuePoll::Fallback(_) => true,
                }
            } else { intake::scalar(final(self)).is_none() },
        no_unwind
    ))]
    fn poll(&mut self) -> QueuePoll<Self::Slot>;

    #[cfg_attr(verus_keep_ghost, verus_spec(fields =>
        requires self.live_slot(slot),
        ensures fields.1 < 2, live(self, fields.0), fields.0 == Self::owner(slot),
            intake::scalar(self).is_some() ==> {
                let request = self.physical_request(slot);
                request.node == fields.0 && request.axis().index() == fields.1 && request.kind == fields.2
            },
        no_unwind
    ))]
    fn position(&self, slot: Self::Slot) -> (Self::Id, usize, Kind, u16);

    #[cfg_attr(verus_keep_ghost, verus_spec(record =>
        requires self.live_slot(slot),
        ensures *record == self.layout_record(Self::owner(slot)),
            intake::scalar(self).is_some() ==> {
                let scalar = intake::scalar(self).unwrap();
                let request = self.physical_request(slot);
                let at = scalar.program.position(request);
                scalar.program.keys.contains(request) ==>
                    scalar.words[at] == seq![Self::Float::word(record.values[
                        slot_index(request.axis().index(), request.kind) as int])]
            },
        no_unwind
    ))]
    fn slot_record(&self, slot: Self::Slot) -> &NodeLayoutData;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires self.live_slot(slot),
        no_unwind
    ))]
    fn writes_width_grid(&self, slot: Self::Slot) -> bool;

    #[cfg(any(test, verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).order() == old(self).order(), no_unwind))]
    fn simple_wrap_queue(&mut self) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(requires self.live_slot(slot), no_unwind))]
    fn writes_wrap_lines(&self, slot: Self::Slot) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(slot =>
        requires self.live().contains(step.request.node),
        ensures self.live_slot(slot), self.physical_request(slot) == step.request,
        no_unwind
    ))]
    fn ranked_slot(&self, step: Ranked<Self::Id>) -> Self::Slot;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).live_slot(slot),
        ensures final(self).resolved() == old(self).resolved() + 1, final(self).live_slot(slot),
            final(self).order() == old(self).order(), final(self).budget_marked() == old(self).budget_marked(),
            final(self).physical_request(slot) == old(self).physical_request(slot),
            final(self).live() == old(self).live(), final(self).queue_empty() == old(self).queue_empty(),
            final(self).slot_program() == old(self).slot_program(),
            ({
                let program = old(self).slot_program();
                let words = old(self).slot_words();
                let request = old(self).physical_request(slot);
                let index = program.position(request);
                program.keys.contains(request) && 0 <= index < words.len()
                    ==> final(self).slot_words() == words.update(index, program.word_at(words, index))
            }),
            intake::scalar(final(self)) == if let Some(scalar) = intake::scalar(old(self)) {
                Some(scalar.evaluate(scalar.program.position(old(self).physical_request(slot))))
            } else { None },
        no_unwind
    ))]
    fn compute(&mut self, slot: Self::Slot);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).live_slot(slot),
        ensures final(self).resolved() == old(self).resolved(), final(self).order() == old(self).order(),
            final(self).budget_marked() == old(self).budget_marked(),
            final(self).physical_request(slot) == old(self).physical_request(slot),
            if let Some(before) = intake::scalar(old(self)) {
                let after = intake::scalar(final(self)).unwrap();
                let input = before.program.position(old(self).physical_request(slot));
                &&& intake::scalar(final(self)).is_some()
                &&& after.program == before.program && after.words == before.words
                &&& before.pending.subset_of(after.pending)
                &&& forall |i: int| 0 <= i < before.words.len() && before.program.order.reads[i].contains(input)
                    ==> #[trigger] after.pending.contains(i)
            } else { intake::scalar(final(self)).is_none() },
        no_unwind
    ))]
    fn send_to_readers(&mut self, slot: Self::Slot);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node),
        ensures final(self).resolved() == old(self).resolved(), final(self).order() == old(self).order(),
            final(self).budget_marked() == old(self).budget_marked(),
            final(self).queue_empty() == old(self).queue_empty(),
            intake::scalar(final(self)) == intake::scalar(old(self)),
            forall |slot: Self::Slot| #[trigger] final(self).live_slot(slot) == old(self).live_slot(slot),
            forall |slot: Self::Slot| #[trigger] final(self).physical_request(slot) == old(self).physical_request(slot),
        no_unwind
    ))]
    fn mark_output(&mut self, node: Self::Id, sibling_extent_changed: bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).queue_empty(), final(self).resolved() == old(self).resolved(), final(self).order() == old(self).order(),
        final(self).budget_marked() == old(self).budget_marked(),
        no_unwind
    ))]
    fn discard_queue(&mut self);
}

#[cfg(verus_keep_ghost)]
verus! {
/// One ranked epoch can visit each physical slot of an owner only once.
/// Bound its complete work by the number of admitted owners.
pub(crate) proof fn epoch_slot_count<I>(slots: Seq<(I, usize)>, nodes: Seq<I>)
    requires
        slots.no_duplicates(),
        forall |i: int| 0 <= i < slots.len() ==> {
            let slot = #[trigger] slots[i];
            nodes.contains(slot.0) && slot.1 < N_SLOTS
        },
    ensures slots.len() <= nodes.len() * N_SLOTS,
{
    let encode = |slot: (I, usize)| nodes.index_of_first(slot.0).unwrap() * N_SLOTS + slot.1;
    let packed = slots.map_values(encode);
    assert forall |i: int, j: int| 0 <= i < j < packed.len()
        implies (#[trigger] packed[i]) != (#[trigger] packed[j]) by {
        let left = slots[i];
        let right = slots[j];
        let a = nodes.index_of_first(left.0).unwrap();
        let b = nodes.index_of_first(right.0).unwrap();
        nodes.index_of_first_ensures(left.0);
        nodes.index_of_first_ensures(right.0);
        assert(packed[i] == a * N_SLOTS + left.1);
        assert(packed[j] == b * N_SLOTS + right.1);
        assert(left.1 < N_SLOTS && right.1 < N_SLOTS);
        if a == b {
            assert(nodes[a] == left.0 && nodes[b] == right.0);
            assert(left != right);
            assert(left.1 != right.1);
        } else if a < b {
            assert(a * N_SLOTS + left.1 < b * N_SLOTS + right.1);
        } else {
            assert(b * N_SLOTS + right.1 < a * N_SLOTS + left.1);
        }
    }
    assert(packed.no_duplicates());
    packed.unique_seq_to_set();
    let range = vstd::set_lib::set_int_range(0, nodes.len() * N_SLOTS);
    let packed_set = packed.to_set();
    assert(packed_set.subset_of(range)) by {
        assert forall |position: int| #[trigger] packed_set.contains(position)
            implies range.contains(position) by {
            assert(packed.contains(position));
            let i = choose |i: int| 0 <= i < packed.len() && packed[i] == position;
            let slot = slots[i];
            nodes.index_of_first_ensures(slot.0);
            assert(0 <= position < nodes.len() * N_SLOTS);
        }
    }
    vstd::set_lib::lemma_len_subset(packed_set, range);
}


pub(crate) open spec fn owners<I>(nodes: Seq<I>) -> Set<I> {
    nodes.to_set()
}

proof fn clear_owner<I>(node: I, remaining: Seq<I>)
    requires !remaining.contains(node)
    ensures owners(seq![node] + remaining).remove(node) == owners(remaining)
{
    let empty = Seq::<I>::empty();
    let first = seq![node];
    empty.to_set_ensures();
    empty.lemma_push_to_set_commute(node);
    assert(owners(empty) =~= Set::<I>::empty());
    assert(owners(first) =~= Set::<I>::empty().insert(node));
    vstd::seq_lib::seq_to_set_distributes_over_add(first, remaining);
    remaining.to_set_ensures();
    assert(!owners(remaining).contains(node));
    assert(owners(first + remaining).remove(node) =~= owners(remaining));
}

pub(crate) open spec fn scope<Q: QueueModel + ?Sized>(work: &Q, touched: Seq<Q::Id>, limit: u32) -> bool {
    &&& touched.len() <= limit
    &&& touched.no_duplicates()
    &&& work.budget_marked() == owners(touched)
    &&& forall |i: int| 0 <= i < touched.len() ==> live(work, #[trigger] touched[i])
}

fn observe_touches<I: Copy>(touched: &Vec<I>) -> (seen: Ghost<Seq<I>>)
    ensures seen@ == touched@,
    no_unwind
{
    Ghost(touched@)
}
}

/// Count an owner once. Reserve storage before setting the record bit.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(admitted =>
    requires scope(old(work), old(touched)@, limit), live(old(work), node),
    ensures scope(final(work), final(touched)@, limit),
        final(work).order() == old(work).order(), final(work).resolved() == old(work).resolved(),
        admitted ==> final(work).budget_marked() == old(work).budget_marked().insert(node),
        final(touched)@ == if admitted && !old(work).budget_marked().contains(node) {
            old(touched)@.push(node)
        } else {
            old(touched)@
        },
        !admitted ==> final(work).budget_marked() == old(work).budget_marked(),
        forall |slot: Q::Slot| #[trigger] final(work).live_slot(slot) == old(work).live_slot(slot),
        forall |slot: Q::Slot| #[trigger] final(work).physical_request(slot) == old(work).physical_request(slot),
        intake::scalar(final(work)) == intake::scalar(old(work)),
    no_unwind
))]
fn admit<Q: QueueActions + ?Sized>(work: &mut Q, touched: &mut Vec<Q::Id>, node: Q::Id, limit: u32) -> bool {
    if work.budget_mark(node) { return true; }
    #[cfg(verus_keep_ghost)]
    let before = observe_touches(touched);
    if touched.len() as u128 >= limit as u128
        || !try_append::<_, Q::BudgetMemory>(touched, node)
    {
        return false;
    }
    work.mark_budget_node(node, true);
    #[cfg(verus_keep_ghost)]
    proof! {
        before@.to_set_ensures();
        assert(!before@.contains(node));
        before@.lemma_push_to_set_commute(node);
        assert(touched@.no_duplicates());
        assert forall |i: int| 0 <= i < touched@.len() implies live(work, #[trigger] touched@[i]) by {
            if i < before@.len() { assert(touched@[i] == before@[i]); }
            else { assert(touched@[i] == node); }
        }
    }
    true
}

/// The slot ceiling bounds even a malformed sequence of admissible repeats.
/// A stable ranked frame has at most N_SLOTS distinct slot indices per owner.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(cap =>
    ensures cap == vstd::math::min(limit as int * N_SLOTS as int, u32::MAX as int),
    no_unwind
))]
fn owner_slot_limit(limit: u32) -> u32 {
    limit.saturating_mul(N_SLOTS as u32)
}

/// A track or Wrap partition can change placement inside a node whose
/// outer extent is unchanged. Only a changed Final can move its siblings.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(effect =>
    ensures effect.is_some() == (rebuilt_lines || kind is Final && changed),
        effect.is_some() ==> effect.unwrap() == (kind is Final && value_changed),
    no_unwind
))]
fn placement_effect(kind: Kind, changed: bool, value_changed: bool, rebuilt_lines: bool) -> Option<bool> {
    if rebuilt_lines || matches!(kind, Kind::Final) && changed {
        Some(matches!(kind, Kind::Final) && value_changed)
    } else {
        None
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct QueueAttempt<I> {
    outcome: IncrementalRelayoutOutcome,
    #[cfg(verus_keep_ghost)]
    computed_owners: Ghost<Seq<I>>,
    marker: core::marker::PhantomData<I>,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.outcome == outcome, result.computed_owners@ == computed_owners@,
    no_unwind
))]
fn queue_attempt<I>(
    outcome: IncrementalRelayoutOutcome,
    #[cfg(verus_keep_ghost)] computed_owners: Ghost<Seq<I>>,
) -> QueueAttempt<I> {
    QueueAttempt { outcome, #[cfg(verus_keep_ghost)] computed_owners, marker: core::marker::PhantomData }
}

#[cfg(verus_keep_ghost)]
verus! {
fn empty_computations<I>() -> (entries: Ghost<Seq<I>>)
    ensures entries@ == Seq::<I>::empty(),
    no_unwind
{ Ghost(Seq::empty()) }

fn push_computation<I>(entries: Ghost<Seq<I>>, owner: I) -> (next: Ghost<Seq<I>>)
    ensures next@ == entries@.push(owner),
    no_unwind
{ Ghost(entries@.push(owner)) }
}

/// Charge each admissible slot before computation. A fallback discards
/// pending work so it cannot carry unsolved slots into later incremental runs.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires scope(old(work), old(touched)@, limit),
    ensures final(work).queue_empty(),
        final(work).order() == old(work).order(),
        old(work).resolved() <= final(work).resolved() <= old(work).resolved() + slot_limit,
        scope(final(work), final(touched)@, limit),
        final(work).resolved() == old(work).resolved() + out.computed_owners@.len(),
        final(work).budget_marked()
            == old(work).budget_marked().union(owners(out.computed_owners@)),
        forall |i: int| 0 <= i < out.computed_owners@.len()
            ==> live(final(work), #[trigger] out.computed_owners@[i]),
        if let IncrementalRelayoutOutcome::Success { computed } = out.outcome {
            &&& out.computed_owners@.len() == computed
            &&& certified_scalar_queue(old(work)) ==> {
                let scalar = intake::scalar(final(work)).unwrap();
                &&& intake::scalar(final(work)).is_some()
                &&& scalar.program == intake::scalar(old(work)).unwrap().program
                &&& scalar.words == scalar.program.fresh()
            }
        } else { true },
        !(out.outcome is CheckedIncrementalRelayoutMismatch),
    no_unwind
))]
fn run_queue<Q: QueueActions + ?Sized>(
    work: &mut Q, limit: u32, slot_limit: u32, touched: &mut Vec<Q::Id>, track_output: bool, allow_flow: bool,
) -> QueueAttempt<Q::Id> {
    use IncrementalRelayoutOutcome::*;
    let mut computed = 0;
    #[cfg(verus_keep_ghost)]
    let mut computed_owners = empty_computations::<Q::Id>();
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(owners(computed_owners@) =~= Set::<Q::Id>::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant computed <= slot_limit, work.resolved() == old(work).resolved() + computed,
            work.order() == old(work).order(),
            certified_scalar_queue(old(work)) ==> {
                &&& certified_scalar_queue(work)
                &&& intake::scalar(work).unwrap().program == intake::scalar(old(work)).unwrap().program
            },
            scope(work, touched@, limit), computed_owners@.len() == computed,
            work.budget_marked() == old(work).budget_marked().union(owners(computed_owners@)),
            forall |i: int| 0 <= i < computed_owners@.len() ==> live(work, #[trigger] computed_owners@[i]),
        decreases slot_limit - computed,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        let initial = save_scalar(work);
        let slot = match work.poll() {
            QueuePoll::Fallback(reason) => {
                work.discard_queue();
                return queue_attempt(reason.as_fallback(), #[cfg(verus_keep_ghost)] computed_owners);
            }
            QueuePoll::Empty => {
                #[cfg(verus_keep_ghost)]
                proof! {
                    if certified_scalar_queue(old(work)) {
                        let scalar = initial@.unwrap();
                        assert(scalar.pending =~= Set::<int>::empty());
                        sizing_tape::settled_queue_words(scalar.program, scalar.words);
                    }
                }
                return queue_attempt(Success { computed }, #[cfg(verus_keep_ghost)] computed_owners);
            },
            QueuePoll::Next(slot) => slot,
        };
        let Some(next) = charge_queue_slot(computed, slot_limit) else {
            work.discard_queue();
            return queue_attempt(FallbackTooMuchWork, #[cfg(verus_keep_ghost)] computed_owners);
        };
        let (node, axis, kind, rank) = work.position(slot);
        #[cfg(verus_keep_ghost)]
        let request = save_request(work, slot);
        let record = work.slot_record(slot);
        let words = slot_words(&record.levels, &record.values, record.flags.0, axis, kind);
        let Some(before) = inspect_slot(words.levels, words.values, axis, kind, words.state, rank, allow_flow) else {
            work.discard_queue();
            return queue_attempt(FallbackTooMuchWork, #[cfg(verus_keep_ghost)] computed_owners);
        };
        let grid = if matches!(kind, Kind::Final) && work.writes_width_grid(slot) {
            Some(record.grid_line_bits::<Q::Float>())
        } else {
            None
        };
        if !admit(work, touched, node, limit) {
            work.discard_queue();
            return queue_attempt(FallbackTooMuchWork, #[cfg(verus_keep_ghost)] computed_owners);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if certified_scalar_queue(old(work)) {
                let data = initial@.unwrap();
                data.program.keys.index_of_first_ensures(request@);
                let at = data.program.position(request@);
                assert(data.words[at] == seq![Q::Float::word(before.previous())]);
            }
        }
        work.compute(slot);
        #[cfg(verus_keep_ghost)]
        let previous_owners = computed_owners;
        #[cfg(verus_keep_ghost)]
        { computed_owners = push_computation(computed_owners, node); }
        #[cfg(verus_keep_ghost)]
        proof! {
            let before = previous_owners@;
            before.lemma_push_to_set_commute(node);
            assert forall |i: int| 0 <= i < computed_owners@.len()
                implies live(work, #[trigger] computed_owners@[i]) by {
                if i < before.len() { assert(computed_owners@[i] == before[i]); }
                else { assert(computed_owners@[i] == node); }
            }
        }
        let record = work.slot_record(slot);
        let previous = before.value;
        let value_changed = Q::Float::bits(before.load(&record.values)) != Q::Float::bits(previous);
        #[cfg(verus_keep_ghost)]
        proof! {
            if certified_scalar_queue(old(work)) {
                let data = initial@.unwrap();
                let after = intake::scalar(work).unwrap();
                let at = data.program.position(request@);
                assert(after.words[at] == seq![Q::Float::word(before.at(record.values@))]);
                if !value_changed { assert(after.words[at] == data.words[at]); }
            }
        }
        let changed = value_changed || match grid {
            Some(old_tracks) => count_changed(old_tracks, record.grid_line_bits::<Q::Float>()),
            None => false,
        };
        let rebuilt_lines = allow_flow && matches!(kind, Kind::EvenShare) && work.writes_wrap_lines(slot);
        if changed || rebuilt_lines {
            if track_output {
                if let Some(sibling_extent_changed) = placement_effect(kind, changed, value_changed, rebuilt_lines) {
                    work.mark_output(node, sibling_extent_changed);
                }
            }
            work.send_to_readers(slot);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if certified_scalar_queue(old(work)) {
                let data = initial@.unwrap();
                let after = intake::scalar(work).unwrap();
                let at = data.program.position(request@);
                assert(data.pending.remove(at).subset_of(after.pending));
                assert forall |i: int| 0 <= i < data.words.len() && i != at && data.words[at] != after.words[at]
                    && data.program.order.reads[i].contains(at) implies #[trigger] after.pending.contains(i) by {
                    assert(value_changed);
                }
                sizing_tape::published_and_notified(data.program, data.words, after.words, data.pending, after.pending, at);
            }
        }
        computed = next;
    }
}

/// Clear the exact admitted prefix before placement, fallback or another frame.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires scope(old(work), touched@, u32::MAX),
    ensures final(work).budget_marked().is_empty(),
        final(work).queue_empty() == old(work).queue_empty(),
        final(work).resolved() == old(work).resolved(), final(work).order() == old(work).order(),
        intake::scalar(final(work)) == intake::scalar(old(work)),
    no_unwind
))]
fn clear_budget_marks<Q: QueueActions + ?Sized>(work: &mut Q, touched: &[Q::Id]) {
    let mut index = 0;
    #[cfg(verus_keep_ghost)]
    proof! { assert(touched@.skip(0) =~= touched@); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= touched.len(), scope(old(work), touched@, u32::MAX),
            work.order() == old(work).order(), work.resolved() == old(work).resolved(),
            work.queue_empty() == old(work).queue_empty(),
            intake::scalar(work) == intake::scalar(old(work)),
            work.budget_marked() == owners(touched@.skip(index as int)),
        decreases touched.len() - index,
    ))]
    while index < touched.len() {
        let node = touched[index];
        work.mark_budget_node(node, false);
        #[cfg(verus_keep_ghost)]
        proof! {
            let remaining = touched@.skip(index as int + 1);
            assert(touched@.skip(index as int) =~= seq![node] + remaining);
            assert(!remaining.contains(node));
            clear_owner(node, remaining);
            assert(work.budget_marked() == owners(remaining));
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(touched@.skip(index as int) =~= Seq::<Q::Id>::empty());
        Seq::<Q::Id>::empty().to_set_ensures();
        assert(owners(Seq::<Q::Id>::empty()) =~= Set::<Q::Id>::empty());
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures !(out is CheckedIncrementalRelayoutMismatch), final(work).order() == old(work).order(),
        final(work).budget_marked().is_empty(), final(work).queue_empty(),
        out is Success && certified_scalar_queue(old(work)) ==> {
            let scalar = intake::scalar(final(work)).unwrap();
            &&& intake::scalar(final(work)).is_some()
            &&& scalar.program == intake::scalar(old(work)).unwrap().program
            &&& scalar.words == scalar.program.fresh()
        },
    no_unwind
))]
fn run_owner_queue<Q: QueueActions + ?Sized>(work: &mut Q, limit: u32, track_output: bool, allow_flow: bool) -> IncrementalRelayoutOutcome {
    let mut touched = work.take_budget_nodes();
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(touched@ =~= Seq::<Q::Id>::empty());
        touched@.to_set_ensures();
        assert(owners(touched@) =~= Set::<Q::Id>::empty());
        assert(work.budget_marked() =~= Set::<Q::Id>::empty());
        assert(scope(work, touched@, limit));
    }
    let outcome = run_queue(work, limit, owner_slot_limit(limit), &mut touched, track_output, allow_flow).outcome;
    #[cfg(verus_keep_ghost)]
    proof! { assert(scope(work, touched@, u32::MAX)); }
    clear_budget_marks(work, touched.as_slice());
    Q::BudgetMemory::clear(&mut touched);
    work.recycle_budget_nodes(touched);
    outcome
}

#[cfg(verus_keep_ghost)]
verus! {
fn save_intake<W: Copy, S: ChangeBuffers<W> + ?Sized>(
    work: &S, axes: Axes, changes: &Changes<S::Id, S::Change>,
) -> (out: Ghost<(SlotProgram<S::Id>, Set<int>, Seq<intake::Seed<S::Id, S::Change>>, bool)>)
    ensures out@.0 == work.slot_program(), out@.1 == work.scalar_pending(),
        out@.2 == seeds_for::<S, W>(work, axes, changes.declarations@, changes.content@),
        out@.3 == covered_scalar_inputs(work, out@.0, out@.1, out@.2),
    no_unwind
{
    let ghost program = work.slot_program();
    let ghost pending = work.scalar_pending();
    let ghost seeds = seeds_for::<S, W>(work, axes, changes.declarations@, changes.content@);
    Ghost((program, pending, seeds, covered_scalar_inputs(work, program, pending, seeds)))
}

pub(crate) open spec fn scalar_frame_seeds<W: Copy, A: intake::WindowInputs<W> + ?Sized>(
    work: &A, window: W,
) -> bool {
    let change = work.window_change(window);
    let axes = Axes { horizontal: change.horizontal, vertical: change.vertical };
    covered_scalar_inputs(work, work.program_for_window(window), work.scalar_pending(),
        intake::window_seeds(work.recorded_root(), axes.horizontal, axes.vertical)
            + intake::node_seeds(work.pending_declarations())
            + intake::content_seeds(work.pending_content()))
}

pub(crate) open spec fn known_tape_rejection<W: Copy, A: intake::WindowInputs<W> + ?Sized>(
    work: &A, window: W,
) -> bool {
    let change = work.window_change(window);
    let axes = Axes { horizontal: change.horizontal, vertical: change.vertical };
    let tape = work.retained_tape();
    &&& tape.steps.len() == 0 && tape.axes.covers(axes)
    &&& tape.declarations == work.pending_declarations()
    &&& tape.content == work.pending_content()
}

/// The direct ranked route and an exact previously rejected tape key both
/// seed every locally changed producer.
pub(crate) open spec fn certified_scalar_seeded_frame<W: Copy, A: intake::WindowInputs<W> + ?Sized>(
    work: &A, window: W, track_output: bool,
) -> bool {
    let change = work.window_change(window);
    let axes = Axes { horizontal: change.horizontal, vertical: change.vertical };
    !idle_numeric(work, window)
        && (track_output || !axes.any() || change.budget < 32 || !work.clean_diagnostics()
            || known_tape_rejection(work, window))
        && scalar_frame_seeds(work, window)
}

pub(crate) open spec fn capture_inputs<W: Copy, A: CachedQueue<W> + ?Sized>(work: &A, window: W) -> CaptureInputs<A::Id> {
    let change = work.window_change(window);
    CaptureInputs {
        root: work.recorded_root(),
        axes: Axes { horizontal: change.horizontal, vertical: change.vertical },
        declarations: work.pending_declarations(),
        content: work.pending_content(),
    }
}

/// A resize miss builds a new tape from the live graph, or seeds the same
/// local changes if the bounded capture skips or rejects it.
pub(crate) open spec fn certified_first_capture_frame<W: Copy, A: CachedQueue<W> + ?Sized>(
    work: &A, window: W, track_output: bool,
) -> bool {
    let input = capture_inputs(work, window);
    let program = work.program_for_window(window);
    &&& !track_output && input.axes.any() && work.window_change(window).budget >= 32
    &&& work.clean_diagnostics() && retained_tape_hit(work, window).is_none()
    &&& sizing_tape::capture_bindings(sizing_tape::capture_dispatch(work), work.wrap_queue(), program, input)
    &&& scalar_frame_seeds(work, window)
}

pub(crate) open spec fn certified_tape_hit<W: Copy, A: intake::WindowInputs<W> + ?Sized>(
    work: &A, window: W,
) -> bool {
    let program = work.program_for_window(window);
    retained_tape_hit(work, window).is_some()
        && program.valid() && program.previous(work.slot_words())
        && program.ready_plan(work.retained_tape().steps)
}

fn save_program<W: Copy, A: intake::WindowInputs<W> + ?Sized>(
    work: &A,
) -> (saved: Ghost<(SlotProgram<A::Id>, Seq<Datum>)>)
    ensures saved@.0 == work.slot_program(), saved@.1 == work.slot_words(),
    no_unwind
{ Ghost((work.slot_program(), work.slot_words())) }

/// Observe the exact no-work predicate before the viewport is stored.
pub(crate) open spec fn idle_numeric<W: Copy, A: intake::WindowInputs<W> + ?Sized>(work: &A, window: W) -> bool {
    let delta = work.window_change(window);
    !delta.horizontal && !delta.vertical && !delta.edits_pending
}

/// The idle branch preserves the prior canonical solution when its local
/// inputs and dependency order are unchanged.
pub(crate) open spec fn certified_idle_frame<W: Copy, A: intake::WindowInputs<W> + ?Sized>(
    work: &A, window: W,
) -> bool {
    let program = work.program_for_window(window);
    &&& idle_numeric(work, window)
    &&& program.valid() && program.previous(work.slot_words())
    &&& program.previous_inputs == program.inputs
}

/// The stored schedule is accepted only for the exact ordered registration
/// lists and a resize within the viewport axes already captured.
pub(crate) open spec fn retained_tape_hit<W: Copy, A: intake::WindowInputs<W> + ?Sized>(
    work: &A, window: W,
) -> Option<u32> {
    let delta = work.window_change(window);
    let axes = Axes { horizontal: delta.horizontal, vertical: delta.vertical };
    let tape = work.retained_tape();
    if axes.any() && delta.budget >= 32 && work.clean_diagnostics()
        && 0 < tape.steps.len() <= tape::CAPACITY
        && tape.axes.covers(axes)
        && tape.declarations == work.pending_declarations()
        && tape.content == work.pending_content()
    { Some(tape.steps.len() as u32) } else { None }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct NumericContext {
    pub wrap: bool,
    pub clean: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait CachedQueue<W: Copy>: QueueActions + ChangeBuffers<W> + tape_plan::Events {
    type Equality: EditEquality<Self::Id, Self::Change>;

    #[cfg_attr(verus_keep_ghost, verus_spec(cache =>
        ensures final(self).order() == old(self).order(), final(self).live() == old(self).live(),
            cache.steps.len() <= tape::CAPACITY, tape_plan::live_steps(final(self).live(), cache.steps@),
            cache.view() == old(self).retained_tape(),
            tape_plan::ordered_prefix(cache.steps@, cache.steps.len() as int),
            tape_plan::unique_requests(cache.steps@),
        final(self).slot_program() == old(self).slot_program(),
        final(self).slot_words() == old(self).slot_words(),
        intake::capture_frame(old(self), final(self)),
        intake::seed_frame(old(self), final(self)),
        final(self).recorded_root() == old(self).recorded_root(),
        no_unwind))]
    fn take_tape(&mut self) -> Tape<Self::Id, Self::Change, Ranked<Self::Id>>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires cache.steps.len() <= tape::CAPACITY, tape_plan::live_steps(old(self).live(), cache.steps@),
            tape_plan::ordered_prefix(cache.steps@, cache.steps.len() as int),
            tape_plan::unique_requests(cache.steps@),
        ensures final(self).order() == old(self).order(), final(self).live() == old(self).live(),
            final(self).retained_tape() == cache.view(),
        final(self).slot_program() == old(self).slot_program(),
        final(self).slot_words() == old(self).slot_words(),
        intake::seed_frame(old(self), final(self)),
        final(self).recorded_root() == old(self).recorded_root(),
        no_unwind))]
    fn keep_tape(&mut self, cache: Tape<Self::Id, Self::Change, Ranked<Self::Id>>);

    #[cfg_attr(verus_keep_ghost, verus_spec(context =>
        ensures final(self).order() == old(self).order(), final(self).live() == old(self).live(),
            final(self).retained_tape() == old(self).retained_tape(),
            final(self).pending_declarations() == old(self).pending_declarations(),
            final(self).pending_content() == old(self).pending_content(),
            context.clean == old(self).clean_diagnostics(),
            context.wrap == old(self).wrap_queue(),
            intake::capture_frame(old(self), final(self)),
            final(self).clean_diagnostics() == old(self).clean_diagnostics(),
        final(self).slot_program() == old(self).slot_program(),
        final(self).slot_words() == old(self).slot_words(),
        intake::seed_frame(old(self), final(self)),
        final(self).recorded_root() == old(self).recorded_root(),
        no_unwind))]
    fn numeric_context(&mut self) -> NumericContext;
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires tape_plan::live_steps(old(work).live(), steps@),
        tape_plan::ordered_prefix(steps@, steps.len() as int), tape_plan::unique_requests(steps@),
    ensures final(work).order() == old(work).order(), final(work).live() == old(work).live(),
        final(work).resolved() == old(work).resolved() + steps.len(),
        final(work).budget_marked() == old(work).budget_marked(), final(work).queue_empty() == old(work).queue_empty(),
        final(work).slot_program() == old(work).slot_program(),
        ({
            let program = old(work).slot_program();
            program.valid() && program.previous(old(work).slot_words()) && program.ready_plan(steps@)
                ==> final(work).slot_words() == program.fresh()
        }),
    no_unwind
))]
fn replay<W: Copy, A: CachedQueue<W> + ?Sized>(work: &mut A, steps: &[Ranked<A::Id>]) {
    #[cfg(verus_keep_ghost)]
    let saved = save_program::<W, A>(work);
    #[cfg(verus_keep_ghost)]
    proof! {
        let (program, previous) = saved@;
        if program.valid() && program.previous(previous) && program.ready_plan(steps@) {
            sizing_tape::start_physical_replay(program, previous);
            assert(steps@.take(0) =~= Seq::<Ranked<A::Id>>::empty());
        }
    }
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= steps.len(), work.order() == old(work).order(), work.live() == old(work).live(),
            tape_plan::live_steps(work.live(), steps@), work.resolved() == old(work).resolved() + index,
            work.budget_marked() == old(work).budget_marked(), work.queue_empty() == old(work).queue_empty(),
            saved@.0 == old(work).slot_program(), saved@.1 == old(work).slot_words(),
            work.slot_program() == saved@.0,
            ({
                let (program, previous) = saved@;
                program.valid() && program.previous(previous) && program.ready_plan(steps@)
                    ==> program.replayed_prefix(previous, work.slot_words(), steps@.take(index as int))
            }),
        decreases steps.len() - index,
    ))]
    while index < steps.len() {
        #[cfg(verus_keep_ghost)]
        let before = save_program::<W, A>(work);
        let slot = work.ranked_slot(steps[index]);
        work.compute(slot);
        #[cfg(verus_keep_ghost)]
        proof! {
            let (program, previous) = saved@;
            if program.valid() && program.previous(previous) && program.ready_plan(steps@) {
                assert(program.replayed_prefix(previous, before@.1, steps@.take(index as int)));
                sizing_tape::advance_physical_replay(program, previous, before@.1, steps@, index as int);
            }
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let (program, previous) = saved@;
        if program.valid() && program.previous(previous) && program.ready_plan(steps@) {
            assert(steps@.take(index as int) =~= steps@);
            sizing_tape::end_physical_replay(program, previous, work.slot_words(), steps@);
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures !(out is CheckedIncrementalRelayoutMismatch), final(work).order() == old(work).order(),
        idle_numeric(old(work), window) ==> (
            out == (IncrementalRelayoutOutcome::Success { computed: 0 })
            && final(work).slot_words() == old(work).slot_words()
        ),
        certified_idle_frame(old(work), window)
            ==> final(work).slot_words() == old(work).program_for_window(window).fresh(),
        if let Some(computed) = retained_tape_hit(old(work), window) {
            !track_output ==> out == (IncrementalRelayoutOutcome::Success { computed })
        } else { true },
        !track_output && certified_tape_hit(old(work), window)
            ==> final(work).slot_words() == old(work).program_for_window(window).fresh(),
        out is Success && (certified_scalar_seeded_frame(old(work), window, track_output)
            || certified_first_capture_frame(old(work), window, track_output))
            ==> final(work).slot_words() == old(work).program_for_window(window).fresh(),
    no_unwind
))]
pub(crate) fn measure_cached<W: Copy, A: CachedQueue<W> + ?Sized, M: VecMemory>(
    work: &mut A, window: W, track_output: bool,
) -> IncrementalRelayoutOutcome {
    let change = work.set_window(window);
    let axes = Axes { horizontal: change.horizontal, vertical: change.vertical };
    if !axes.any() && !change.edits_pending {
        #[cfg(verus_keep_ghost)]
        proof! {
            if certified_idle_frame(old(work), window) {
                let program = old(work).program_for_window(window);
                let words = work.slot_words();
                sizing_tape::seeded_queue_words(program, words, Set::empty());
                sizing_tape::settled_queue_words(program, words);
            }
        }
        return IncrementalRelayoutOutcome::Success { computed: 0 };
    }
    let context = work.numeric_context();
    let allow_flow = context.wrap;
    let mut edits = work.take_changes();
    if track_output || !axes.any() || change.budget < 32 || !context.clean {
        return measure_seeded::<W, A, M>(work, change, axes, edits, track_output, allow_flow);
    }
    let mut cache = work.take_tape();
    let same = cache.same_edits::<A::Equality>(&edits);
    if !same || !cache.axes.covers(axes) {
        let wanted = if same { axes.union(cache.axes) } else { axes };
        if cache.copy_key::<A::BudgetMemory>(&edits) {
            let root = work.numeric_root();
            let captured = tape_plan::capture::<A, M>(work, root, wanted, &edits, change.budget, allow_flow, &mut cache.steps);
            if !captured || cache.steps.len() < tape::MIN_STEPS {
                A::BudgetMemory::clear(&mut cache.steps);
            } else {
                #[cfg(verus_keep_ghost)]
                proof! {
                    if certified_first_capture_frame(old(work), window, track_output) {
                        let program = old(work).program_for_window(window);
                        let input = capture_inputs(old(work), window);
                        assert(input.root == root && input.axes == axes);
                        assert(input.declarations == edits.declarations@ && input.content == edits.content@);
                        assert(intake::capture_frame(old(work), work));
                        assert(allow_flow == old(work).wrap_queue());
                        assert(sizing_tape::capture_dispatch(work) == sizing_tape::capture_dispatch(old(work)));
                        assert(sizing_tape::capture_bindings(
                            sizing_tape::capture_dispatch(work), allow_flow, program, input,
                        ));
                        sizing_tape::capture_readies_program(work, allow_flow, cache.steps@, program, input, wanted);
                    }
                }
            }
            // A rejected shape is still remembered for this edit footprint.
            cache.axes = wanted;
        }
    }
    if cache.steps.is_empty() {
        work.keep_tape(cache);
        return measure_seeded::<W, A, M>(work, change, axes, edits, track_output, allow_flow);
    }
    intake::clear_edits(work, edits.declarations.as_slice(), edits.content.as_slice());
    M::clear(&mut edits.declarations);
    M::clear(&mut edits.content);
    work.recycle_changes(edits);
    let computed = cache.steps.len() as u32;
    replay::<W, A>(work, cache.steps.as_slice());
    if !work.numeric_context().clean { cache.invalidate::<M>(); }
    work.keep_tape(cache);
    IncrementalRelayoutOutcome::Success { computed }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires forall |i: int| 0 <= i < edits.declarations.len() ==>
            old(work).live().contains((#[trigger] edits.declarations@[i]).0),
        forall |i: int| 0 <= i < edits.content.len() ==> old(work).live().contains(#[trigger] edits.content@[i]),
    ensures !(out is CheckedIncrementalRelayoutMismatch), final(work).order() == old(work).order(),
        out is Success && covered_scalar_inputs(old(work), old(work).slot_program(), old(work).scalar_pending(),
            seeds_for::<A, W>(old(work), axes, edits.declarations@, edits.content@))
                ==> final(work).slot_words() == old(work).slot_program().fresh(),
    no_unwind
))]
fn measure_seeded<W: Copy, A: QueueActions + ChangeBuffers<W> + ?Sized, M: VecMemory>(
    work: &mut A, change: WindowChange, axes: Axes, mut edits: Changes<A::Id, A::Change>,
    track_output: bool, allow_flow: bool,
) -> IncrementalRelayoutOutcome {
    let root = work.numeric_root();
    #[cfg(verus_keep_ghost)]
    let entry = save_intake::<W, A>(work, axes, &edits);
    intake::seed_edits(work, root, axes.horizontal, axes.vertical, edits.declarations.as_slice(), edits.content.as_slice());
    M::clear(&mut edits.declarations);
    M::clear(&mut edits.content);
    work.recycle_changes(edits);
    #[cfg(verus_keep_ghost)]
    proof! {
        let (program, pending, seeds, certified) = entry@;
        if certified {
            assert forall |i: int| 0 <= i < program.keys.len()
                && program.previous_inputs[i] != program.inputs[i]
                implies #[trigger] work.scalar_pending().contains(i) by {
                if !pending.contains(i) {
                    let j = choose |j: int| 0 <= j < seeds.len()
                        && (work.seed_positions())(#[trigger] seeds[j]).contains(i);
                    assert((work.seed_positions())(seeds[j]).subset_of(work.scalar_pending()));
                }
            }
            sizing_tape::seeded_queue_words(program, work.slot_words(), work.scalar_pending());
        }
    }
    run_owner_queue(work, change.budget, track_output, allow_flow)
}

#[cfg(any(test, verus_keep_ghost))]
/// Execute the entire numeric attempt from the viewport and previously
/// recorded edits. Edits are retired before the first ranked read.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures !(out is CheckedIncrementalRelayoutMismatch), final(work).order() == old(work).order(),
    no_unwind
))]
pub(crate) fn measure<W: Copy, A: QueueActions + ChangeBuffers<W> + ?Sized, M: VecMemory>(
    work: &mut A, window: W, track_output: bool,
) -> IncrementalRelayoutOutcome {
    let change = work.set_window(window);
    if !change.horizontal && !change.vertical && !change.edits_pending {
        return IncrementalRelayoutOutcome::Success { computed: 0 };
    }
    let allow_flow = work.simple_wrap_queue();
    let edits = work.take_changes();
    let axes = Axes { horizontal: change.horizontal, vertical: change.vertical };
    measure_seeded::<W, A, M>(work, change, axes, edits, track_output, allow_flow)
}
