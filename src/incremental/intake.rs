//! Seed ranked work from live viewport, declaration, and content edits.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::SlotBits;
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::SlotBits;
use crate::prepare_nodes::RecordModel;

#[cfg(verus_keep_ghost)]
use crate::sizing_tape::{Datum, SlotProgram};
#[cfg(verus_keep_ghost)]
use super::numeric::ScalarQueue;
#[cfg(verus_keep_ghost)]
use super::tape_plan::{capture_ranks, capture_reader_inputs};

#[cfg(not(verus_keep_ghost))]
pub(crate) trait Model: RecordModel {
    type Change: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) enum Seed<I, C> {
    Window(I, usize),
    Declaration(I, C),
    Content(I),
}

pub(crate) trait Model: RecordModel {
    type Change: Copy;

    spec fn live(&self) -> Set<Self::Id>;
    spec fn clean(&self, node: Self::Id) -> bool;
    spec fn seeded(&self) -> Seq<Seed<Self::Id, Self::Change>>;
    spec fn slot_program(&self) -> SlotProgram<Self::Id>;
    spec fn slot_words(&self) -> Seq<Datum>;
    spec fn scalar_mode(&self) -> bool;
    spec fn scalar_pending(&self) -> Set<int>;
    spec fn seed_positions(&self) -> spec_fn(Seed<Self::Id, Self::Change>) -> Set<int>;
    spec fn wrap_queue(&self) -> bool;
}

pub(crate) open spec fn scalar<S: Model + ?Sized>(source: &S) -> Option<ScalarQueue<S::Id>> {
    if source.scalar_mode() {
        Some(ScalarQueue {
            program: source.slot_program(), words: source.slot_words(), pending: source.scalar_pending(),
        })
    } else { None }
}

#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(C)]
pub(crate) struct SeedState<I, C> {
    pub(crate) queue: Option<ScalarQueue<I>>,
    pub(crate) positions: spec_fn(Seed<I, C>) -> Set<int>,
}

pub(crate) open spec fn seed_state<S: Model + ?Sized>(source: &S) -> SeedState<S::Id, S::Change> {
    SeedState { queue: scalar(source), positions: source.seed_positions() }
}

/// Admitted requests and requests covered by a pending fallback both preserve
/// the seeding obligation until the driver either takes the entry or falls back.
pub(crate) open spec fn seed_effects<I, C>(
    before: SeedState<I, C>, after: SeedState<I, C>, seeds: Seq<Seed<I, C>>,
) -> bool {
    if let Some(old) = before.queue {
        let new = after.queue.unwrap();
        &&& after.queue.is_some()
        &&& new.program == old.program
        &&& new.words == old.words
        &&& after.positions == before.positions
        &&& old.pending.subset_of(new.pending)
        &&& forall |i: int| 0 <= i < seeds.len()
            ==> (before.positions)(#[trigger] seeds[i]).subset_of(new.pending)
    } else { after.queue.is_none() }
}

/// These reads depend on stable links, declarations, and settled rank words.
pub(crate) open spec fn capture_frame<S: Model + ?Sized>(before: &S, after: &S) -> bool {
    &&& capture_reader_inputs(after) == capture_reader_inputs(before)
    &&& capture_ranks(after) == capture_ranks(before)
    &&& after.wrap_queue() == before.wrap_queue()
}

pub(crate) open spec fn seed_frame<S: Model + ?Sized>(before: &S, after: &S) -> bool {
    &&& after.scalar_mode() == before.scalar_mode()
    &&& after.scalar_pending() == before.scalar_pending()
    &&& after.seed_positions() == before.seed_positions()
}

proof fn extend_seed_effects<I, C>(
    entry: SeedState<I, C>, prior: SeedState<I, C>, result: SeedState<I, C>,
    before: Seq<Seed<I, C>>, added: Seed<I, C>,
)
    requires seed_effects(entry, prior, before), seed_effects(prior, result, seq![added]),
    ensures seed_effects(entry, result, before.push(added)),
{
    if entry.queue.is_some() {
        let seeds = before.push(added);
        let old = prior.queue.unwrap().pending;
        let new = result.queue.unwrap().pending;
        assert forall |i: int| 0 <= i < seeds.len()
            implies (entry.positions)(#[trigger] seeds[i]).subset_of(new) by {
            if i < before.len() {
                assert(seeds[i] == before[i]);
                assert((entry.positions)(before[i]).subset_of(old));
            } else {
                assert(seeds[i] == added);
                assert((prior.positions)((seq![added])[0]).subset_of(new));
            }
        }
    }
}

fn tracked_state<S: Model + ?Sized>(source: &S) -> (saved: Ghost<SeedState<S::Id, S::Change>>)
    ensures saved@ == seed_state(source),
    no_unwind
{ Ghost(seed_state(source)) }

pub(crate) open spec fn window_seeds<I, C>(root: I, horizontal: bool, vertical: bool) -> Seq<Seed<I, C>> {
    (if horizontal { seq![Seed::Window(root, 0)] } else { Seq::empty() })
        + if vertical { seq![Seed::Window(root, 1)] } else { Seq::empty() }
}

pub(crate) open spec fn node_seeds<I, C>(changes: Seq<(I, C)>) -> Seq<Seed<I, C>> {
    Seq::new(changes.len(), |index: int| Seed::Declaration(changes[index].0, changes[index].1))
}

pub(crate) open spec fn content_seeds<I, C>(changes: Seq<I>) -> Seq<Seed<I, C>> {
    Seq::new(changes.len(), |index: int| Seed::Content(changes[index]))
}

fn log<T: Model + ?Sized>(source: &T) -> (before: Ghost<Seq<Seed<T::Id, T::Change>>>)
    ensures before@ == source.seeded(),
    no_unwind
{
    Ghost(source.seeded())
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: Model {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).live().contains(root), axis < 2,
        ensures final(self).live() == old(self).live(),
            final(self).order() == old(self).order(),
            final(self).seeded() == old(self).seeded().push(Seed::Window(root, axis)),
            seed_effects(seed_state(old(self)), seed_state(final(self)), seq![Seed::Window(root, axis)]),
        no_unwind
    ))]
    fn window_seed(&mut self, root: Self::Id, axis: usize);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).live().contains(node),
        ensures final(self).live() == old(self).live(), final(self).clean(node),
            final(self).order() == old(self).order(),
            final(self).seeded() == old(self).seeded(),
            seed_frame(old(self), final(self)),
            final(self).slot_program() == old(self).slot_program(),
            final(self).slot_words() == old(self).slot_words(),
            forall |other: Self::Id| old(self).live().contains(other) && other != node
                ==> #[trigger] final(self).clean(other) == old(self).clean(other),
        no_unwind
    ))]
    fn clear_mark(&mut self, node: Self::Id);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).live().contains(node), old(self).clean(node),
        ensures final(self).live() == old(self).live(),
            final(self).order() == old(self).order(),
            final(self).seeded() == old(self).seeded().push(Seed::Declaration(node, change)),
            seed_effects(seed_state(old(self)), seed_state(final(self)), seq![Seed::Declaration(node, change)]),
        no_unwind
    ))]
    fn declaration_seed(&mut self, node: Self::Id, change: Self::Change);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).live().contains(node), old(self).clean(node),
        ensures final(self).live() == old(self).live(),
            final(self).order() == old(self).order(),
            final(self).seeded() == old(self).seeded().push(Seed::Content(node)),
            seed_effects(seed_state(old(self)), seed_state(final(self)), seq![Seed::Content(node)]),
        no_unwind
    ))]
    fn content_seed(&mut self, node: Self::Id);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct WindowChange {
    pub horizontal: bool,
    pub vertical: bool,
    pub edits_pending: bool,
    pub budget: u32,
}

/// Copy the new viewport and compare its two exact binary32 input words.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(change =>
    ensures *final(horizontal) == next_x, *final(vertical) == next_y,
        change.horizontal == (old(horizontal).word() != next_x.word()),
        change.vertical == (old(vertical).word() != next_y.word()),
        change.edits_pending == edits_pending, change.budget == population / 2,
    no_unwind
))]
pub(crate) fn replace_viewport<T: SlotBits>(
    horizontal: &mut T, vertical: &mut T, next_x: T, next_y: T, edits_pending: bool, population: u32,
) -> WindowChange {
    let x = *horizontal;
    let y = *vertical;
    *horizontal = next_x;
    *vertical = next_y;
    WindowChange {
        horizontal: x.bits() != next_x.bits(),
        vertical: y.bits() != next_y.bits(),
        edits_pending,
        budget: population / 2,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Changes<I, C> {
    pub declarations: Vec<(I, C)>,
    pub content: Vec<I>,
}

#[cfg(verus_keep_ghost)]
verus! {
/// Inputs read by the production numeric entry and its retained schedule key.
pub(crate) trait WindowInputs<W: Copy>: Model {
    spec fn window_change(&self, window: W) -> WindowChange;
    spec fn recorded_root(&self) -> Self::Id;
    spec fn program_for_window(&self, window: W) -> crate::sizing_tape::SlotProgram<Self::Id>;
    spec fn pending_declarations(&self) -> Seq<(Self::Id, Self::Change)>;
    spec fn pending_content(&self) -> Seq<Self::Id>;
    spec fn clean_diagnostics(&self) -> bool;
    spec fn retained_tape(&self) -> super::tape::TapeView<
        Self::Id, Self::Change, super::tape_plan::Ranked<Self::Id>,
    >;
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait WindowInputs<W: Copy>: Model {}

/// The window and its two reusable edit buffers are isolated from the
/// adapter during seeding so reads and writes of live records can proceed.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait ChangeBuffers<W: Copy>: Access + WindowInputs<W> {
    #[cfg_attr(verus_keep_ghost, verus_spec(root => ensures self.live().contains(root), root == self.recorded_root(), no_unwind))]
    fn numeric_root(&self) -> Self::Id;

    #[cfg_attr(verus_keep_ghost, verus_spec(change =>
        ensures final(self).live() == old(self).live(), final(self).order() == old(self).order(),
            change == old(self).window_change(window),
            final(self).slot_program() == old(self).program_for_window(window),
            seed_frame(old(self), final(self)),
            capture_frame(old(self), final(self)),
            final(self).recorded_root() == old(self).recorded_root(),
            final(self).slot_words() == old(self).slot_words(),
            final(self).pending_declarations() == old(self).pending_declarations(),
            final(self).pending_content() == old(self).pending_content(),
            final(self).retained_tape() == old(self).retained_tape(),
            final(self).clean_diagnostics() == old(self).clean_diagnostics(),
        no_unwind
    ))]
    fn set_window(&mut self, window: W) -> WindowChange;

    #[cfg_attr(verus_keep_ghost, verus_spec(edits =>
        ensures final(self).live() == old(self).live(),
            final(self).order() == old(self).order(),
            edits.declarations@ == old(self).pending_declarations(),
            edits.content@ == old(self).pending_content(),
            final(self).pending_declarations().len() == 0, final(self).pending_content().len() == 0,
            final(self).retained_tape() == old(self).retained_tape(),
            final(self).clean_diagnostics() == old(self).clean_diagnostics(),
            forall |i: int| 0 <= i < edits.declarations.len() ==>
                final(self).live().contains((#[trigger] edits.declarations@[i]).0),
            forall |i: int| 0 <= i < edits.content.len() ==>
                final(self).live().contains(#[trigger] edits.content@[i]),
        final(self).slot_program() == old(self).slot_program(),
        seed_frame(old(self), final(self)),
        capture_frame(old(self), final(self)),
        final(self).recorded_root() == old(self).recorded_root(),
        final(self).slot_words() == old(self).slot_words(),
        no_unwind
    ))]
    fn take_changes(&mut self) -> Changes<Self::Id, Self::Change>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires edits.declarations.len() == 0, edits.content.len() == 0,
        ensures final(self).live() == old(self).live(), final(self).order() == old(self).order(), final(self).slot_program() == old(self).slot_program(),
        final(self).slot_words() == old(self).slot_words(),
        seed_frame(old(self), final(self)),
        no_unwind
    ))]
    fn recycle_changes(&mut self, edits: Changes<Self::Id, Self::Change>);
}

/// Apply the recorded work in its original order. A removed ID can only
/// occur in structural work, which discards these lists before this pass.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).live().contains(root),
        forall |index: int| 0 <= index < declarations.len() ==>
            old(source).live().contains((#[trigger] declarations@[index]).0),
        forall |index: int| 0 <= index < content.len() ==>
            old(source).live().contains(#[trigger] content@[index]),
    ensures final(source).live() == old(source).live(),
        final(source).order() == old(source).order(),
        final(source).seeded() == old(source).seeded() + window_seeds(root, horizontal, vertical)
            + node_seeds(declarations@) + content_seeds(content@),
        seed_effects(seed_state(old(source)), seed_state(final(source)),
            window_seeds(root, horizontal, vertical) + node_seeds(declarations@) + content_seeds(content@)),
    no_unwind
))]
pub(crate) fn seed_edits<S: Access + ?Sized>(
    source: &mut S, root: S::Id, horizontal: bool, vertical: bool,
    declarations: &[(S::Id, S::Change)], content: &[S::Id],
) {
    if horizontal { source.window_seed(root, 0); }
    #[cfg(verus_keep_ghost)]
    let first_axis = tracked_state(source);
    if vertical { source.window_seed(root, 1); }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(source.seeded() =~= old(source).seeded() + window_seeds(root, horizontal, vertical));
        let prior = window_seeds(root, horizontal, false);
        assert(seed_effects(seed_state(old(source)), first_axis@, prior));
        if vertical {
            extend_seed_effects(seed_state(old(source)), first_axis@, seed_state(source), prior, Seed::Window(root, 1));
            assert(window_seeds(root, horizontal, vertical) =~= prior.push(Seed::Window(root, 1)));
        }
    }
    #[cfg(verus_keep_ghost)]
    let viewport = log(source);
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            index <= declarations.len(),
            source.live() == old(source).live(),
            source.order() == old(source).order(),
            source.seeded() == viewport@ + node_seeds(declarations@).take(index as int),
            seed_effects(seed_state(old(source)), seed_state(source),
                window_seeds(root, horizontal, vertical) + node_seeds(declarations@).take(index as int)),
            forall |j: int| 0 <= j < declarations.len() ==>
                old(source).live().contains((#[trigger] declarations@[j]).0),
        decreases declarations.len() - index,
    ))]
    while index < declarations.len() {
        let (node, change) = declarations[index];
        #[cfg(verus_keep_ghost)]
        let preceding = tracked_state(source);
        source.clear_mark(node);
        source.declaration_seed(node, change);
        #[cfg(verus_keep_ghost)]
        proof! {
            let seeds = node_seeds(declarations@);
            assert(seeds[index as int] == Seed::Declaration(node, change));
            assert(seeds.take(index as int).push(seeds[index as int]) =~= seeds.take(index as int + 1));
            assert(source.seeded() =~= viewport@ + seeds.take(index as int + 1));
            let prior = window_seeds(root, horizontal, vertical) + seeds.take(index as int);
            extend_seed_effects(seed_state(old(source)), preceding@, seed_state(source), prior, Seed::Declaration(node, change));
            assert(prior.push(Seed::Declaration(node, change))
                =~= window_seeds(root, horizontal, vertical) + seeds.take(index as int + 1));
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(node_seeds(declarations@).take(index as int) =~= node_seeds(declarations@));
    }
    #[cfg(verus_keep_ghost)]
    let declared = log(source);
    index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            index <= content.len(),
            source.live() == old(source).live(),
            source.order() == old(source).order(),
            source.seeded() == declared@ + content_seeds::<S::Id, S::Change>(content@).take(index as int),
            seed_effects(seed_state(old(source)), seed_state(source), window_seeds(root, horizontal, vertical) + node_seeds(declarations@)
                + content_seeds::<S::Id, S::Change>(content@).take(index as int)),
            forall |j: int| 0 <= j < content.len() ==> old(source).live().contains(#[trigger] content@[j]),
        decreases content.len() - index,
    ))]
    while index < content.len() {
        let node = content[index];
        #[cfg(verus_keep_ghost)]
        let preceding = tracked_state(source);
        source.clear_mark(node);
        source.content_seed(node);
        #[cfg(verus_keep_ghost)]
        proof! {
            let seeds = content_seeds::<S::Id, S::Change>(content@);
            assert(seeds[index as int] == Seed::Content(node));
            assert(seeds.take(index as int).push(seeds[index as int]) =~= seeds.take(index as int + 1));
            assert(source.seeded() =~= declared@ + seeds.take(index as int + 1));
            let prefix = window_seeds(root, horizontal, vertical) + node_seeds(declarations@);
            let prior = prefix + seeds.take(index as int);
            extend_seed_effects(seed_state(old(source)), preceding@, seed_state(source), prior, Seed::Content(node));
            assert(prior.push(Seed::Content(node)) =~= prefix + seeds.take(index as int + 1));
        }
        index += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let seeds = content_seeds::<S::Id, S::Change>(content@);
        assert(seeds.take(index as int) =~= seeds);
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn declaration_mark<I, C>(items: Seq<(I, C)>, count: int, node: I) -> bool {
    exists |i: int| 0 <= i < count && (#[trigger] items[i]).0 == node
}

pub(crate) open spec fn content_mark<I>(items: Seq<I>, count: int, node: I) -> bool {
    exists |i: int| 0 <= i < count && #[trigger] items[i] == node
}
}

/// Retire the same live dirty marks when a cached schedule already contains
/// every request the edits would seed.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires forall |i: int| 0 <= i < declarations.len() ==>
        old(source).live().contains((#[trigger] declarations@[i]).0),
        forall |i: int| 0 <= i < content.len() ==> old(source).live().contains(#[trigger] content@[i]),
    ensures final(source).order() == old(source).order(), final(source).live() == old(source).live(),
        final(source).seeded() == old(source).seeded(),
        final(source).slot_program() == old(source).slot_program(),
        final(source).slot_words() == old(source).slot_words(),
        forall |i: int| 0 <= i < declarations.len()
            ==> final(source).clean((#[trigger] declarations@[i]).0),
        forall |i: int| 0 <= i < content.len()
            ==> final(source).clean(#[trigger] content@[i]),
        forall |node: S::Id| old(source).live().contains(node)
            && !declaration_mark(declarations@, declarations.len() as int, node)
            && !content_mark(content@, content.len() as int, node)
            ==> #[trigger] final(source).clean(node) == old(source).clean(node),
    no_unwind
))]
pub(crate) fn clear_edits<S: Access + ?Sized>(source: &mut S, declarations: &[(S::Id, S::Change)], content: &[S::Id]) {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= declarations.len(), source.order() == old(source).order(),
            source.live() == old(source).live(), source.seeded() == old(source).seeded(),
            source.slot_program() == old(source).slot_program(), source.slot_words() == old(source).slot_words(),
            forall |i: int| 0 <= i < declarations.len() ==>
                old(source).live().contains((#[trigger] declarations@[i]).0),
            forall |i: int| 0 <= i < index ==> source.clean((#[trigger] declarations@[i]).0),
            forall |node: S::Id| old(source).live().contains(node)
                && !declaration_mark(declarations@, index as int, node)
                ==> #[trigger] source.clean(node) == old(source).clean(node),
        decreases declarations.len() - index,
    ))]
    while index < declarations.len() {
        let node = declarations[index].0;
        source.clear_mark(node);
        #[cfg(verus_keep_ghost)]
        proof! { assert(declaration_mark(declarations@, index as int + 1, node)); }
        index += 1;
    }
    index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= content.len(), source.order() == old(source).order(),
            source.live() == old(source).live(), source.seeded() == old(source).seeded(),
            source.slot_program() == old(source).slot_program(), source.slot_words() == old(source).slot_words(),
            forall |i: int| 0 <= i < content.len() ==> old(source).live().contains(#[trigger] content@[i]),
            forall |i: int| 0 <= i < declarations.len() ==>
                old(source).live().contains((#[trigger] declarations@[i]).0)
                    && source.clean(declarations@[i].0),
            forall |i: int| 0 <= i < index ==> source.clean(#[trigger] content@[i]),
            forall |node: S::Id| old(source).live().contains(node)
                && !declaration_mark(declarations@, declarations.len() as int, node)
                && !content_mark(content@, index as int, node)
                ==> #[trigger] source.clean(node) == old(source).clean(node),
        decreases content.len() - index,
    ))]
    while index < content.len() {
        let node = content[index];
        source.clear_mark(node);
        #[cfg(verus_keep_ghost)]
        proof! { assert(content_mark(content@, index as int + 1, node)); }
        index += 1;
    }
}
