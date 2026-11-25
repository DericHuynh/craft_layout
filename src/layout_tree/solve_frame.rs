//! Select the owned frame path from its pending edits and retained layout state.
#![allow(unexpected_cfgs)]

use crate::declarations::{LayoutParams, Xy};
#[cfg(not(verus_keep_ghost))]
use crate::SameInput;
#[cfg(verus_keep_ghost)]
use crate::placement::kernel::PlacementWork;
#[cfg(not(verus_keep_ghost))]
use crate::{IncrementalRelayoutOutcome, structural_changes::TailDelta};
#[cfg(verus_keep_ghost)]
use crate::{publication::IncrementalRelayoutOutcome, structural::kernel::TailDelta};
#[cfg(verus_keep_ghost)]
use crate::{Geometry, placement::modes::{SiblingInputs, subtree_writes},
    placement_complete::{PlacementDelta, placement_only_keeps_skipped_rectangles},
    replay_view::Draw, requested};
#[cfg(verus_keep_ghost)]
use crate::{placement::entry::{RootEvidence, RootPlacement}, publication::{self, FrameResult}};
#[cfg(not(verus_keep_ghost))]
use crate::{place::placement_entry::RootPlacement, incremental::FrameResult};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Consecutive pushes and pops leave the prefix before `first_added` unchanged.
#[derive(Debug, Clone, Copy, Default)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(super) enum TailEdits<I: Copy> {
    #[default]
    None,
    Placement,
    Stack { parent: I, delta: TailDelta<I> },
    Other,
}

/// Compare declarations with the four placement fields held constant.
#[cfg(not(verus_keep_ghost))]
pub(super) fn same_sizing_inputs(old: LayoutParams, new: LayoutParams) -> bool {
    old.same_input(&replace_placement(new, old))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns replace_placement(params, retained), no_unwind))]
pub(super) fn replace_placement(params: LayoutParams, retained: LayoutParams) -> LayoutParams {
    LayoutParams {
        position: retained.position,
        anchor: retained.anchor,
        children_origin_flipped: retained.children_origin_flipped,
        window_overflow: retained.window_overflow,
        ..params
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait MarkModel { type Id: Copy; }

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait MarkModel {
    type Id: Copy;
    spec fn parents(&self) -> Map<Self::Id, Option<Self::Id>>;
    spec fn marks(&self) -> Map<Self::Id, PlacementWork>;
}

pub(crate) open spec fn next_at<I>(path: Seq<I>, i: int) -> Option<I> {
    if 0 <= i < path.len() { Some(path[i]) } else { None }
}

pub(crate) open spec fn parent_path<I>(parents: Map<I, Option<I>>, path: Seq<I>) -> bool {
    forall|i: int| 0 <= i < path.len() ==> {
        &&& parents.contains_key(#[trigger] path[i])
        &&& parents[path[i]] == next_at(path, i + 1)
    }
}

pub(crate) open spec fn on_prefix<I>(path: Seq<I>, len: int, node: I) -> bool {
    exists|i: int| 0 <= i < len && (#[trigger] path[i]) == node
}

proof fn extend_prefix<I>(path: Seq<I>, len: int, node: I)
    requires 0 <= len < path.len(),
    ensures on_prefix(path, len + 1, node) == (on_prefix(path, len, node) || path[len] == node),
{
    if on_prefix(path, len + 1, node) {
        let i = choose|i: int| 0 <= i < len + 1 && (#[trigger] path[i]) == node;
        if i < len { assert(on_prefix(path, len, node)); }
    } else if on_prefix(path, len, node) {
        let i = choose|i: int| 0 <= i < len && (#[trigger] path[i]) == node;
        assert(0 <= i < len + 1);
        assert(on_prefix(path, len + 1, node));
    } else if path[len] == node {
        assert(on_prefix(path, len + 1, node));
    }
}

fn saved_marks<A: MarkModel>(tree: &A) -> (marks: Ghost<Map<A::Id, PlacementWork>>)
    ensures marks@ == tree.marks(),
    no_unwind
{ Ghost(tree.marks()) }

fn path_start() -> (i: Ghost<int>)
    ensures i@ == 0,
    no_unwind
{ Ghost(0int) }

fn path_next(i: Ghost<int>) -> (j: Ghost<int>)
    ensures j@ == i@ + 1,
    no_unwind
{ Ghost(i@ + 1) }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait MarkAncestors: MarkModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires old(self).parents().contains_key(id), old(self).marks().contains_key(id),
        ensures next == old(self).parents()[id],
            final(self).parents() == old(self).parents(),
            final(self).marks() == old(self).marks().insert(
                id, old(self).marks()[id].with_child(PlacementWork::Subtree, false)),
        no_unwind
    ))]
    fn mark_ancestor(&mut self, id: Self::Id) -> Option<Self::Id>;
}

/// Retain the old frames along the path while making each edited branch reachable.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires next == next_at(path@, 0), parent_path(old(tree).parents(), path@),
        old(tree).parents().dom() == old(tree).marks().dom(),
    ensures final(tree).parents() == old(tree).parents(),
        final(tree).marks().dom() == old(tree).marks().dom(),
        forall|id: A::Id| old(tree).marks().contains_key(id) ==> #[trigger] final(tree).marks()[id]
            == if on_prefix(path@, path@.len() as int, id) {
                old(tree).marks()[id].with_child(PlacementWork::Subtree, false)
            } else { old(tree).marks()[id] },
        forall|i: int| 0 <= i < path@.len() ==>
            (#[trigger] final(tree).marks()[path@[i]]).visits(false),
        forall|id: A::Id| old(tree).marks().contains_key(id) && !path@.contains(id) ==> #[trigger] final(tree).marks()[id] == old(tree).marks()[id],
        forall|id: A::Id| old(tree).marks().contains_key(id) && old(tree).marks()[id] is Subtree
            ==> #[trigger] final(tree).marks()[id] is Subtree,
    no_unwind
))]
pub(crate) fn mark_parents<A: MarkAncestors>(
    tree: &mut A, mut next: Option<A::Id>, #[cfg(verus_keep_ghost)] path: Ghost<Seq<A::Id>>,
) {
    #[cfg(verus_keep_ghost)]
    let mut i = path_start();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= i@ <= path@.len(), next == next_at(path@, i@),
            tree.parents() == old(tree).parents(), parent_path(tree.parents(), path@),
            tree.marks().dom() == old(tree).marks().dom(),
            old(tree).marks().dom() == old(tree).parents().dom(),
            forall|id: A::Id| old(tree).marks().contains_key(id) ==> #[trigger] tree.marks()[id]
                == if on_prefix(path@, i@, id) {
                    old(tree).marks()[id].with_child(PlacementWork::Subtree, false)
                } else { old(tree).marks()[id] },
            forall|j: int| 0 <= j < i@ ==> (#[trigger] tree.marks()[path@[j]]).visits(false),
            forall|id: A::Id| old(tree).marks().contains_key(id) && !path@.contains(id) ==> #[trigger] tree.marks()[id] == old(tree).marks()[id],
            forall|id: A::Id| old(tree).marks().contains_key(id) && old(tree).marks()[id] is Subtree
                ==> #[trigger] tree.marks()[id] is Subtree,
        decreases path@.len() - i@,
    ))]
    loop {
        let Some(id) = next else {
            #[cfg(verus_keep_ghost)]
            proof! { assert(i@ == path@.len()); }
            return;
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(i@ < path@.len() && id == path@[i@]);
            assert(tree.parents().contains_key(id));
            assert(tree.marks().contains_key(id));
            assert(tree.parents()[id] == next_at(path@, i@ + 1));
            assert(path@.contains(id));
            assert(tree.marks()[id].with_child(PlacementWork::Subtree, false).visits(false));
        }
        #[cfg(verus_keep_ghost)]
        let before = saved_marks(tree);
        next = tree.mark_ancestor(id);
        #[cfg(verus_keep_ghost)]
        {
            proof! {
                assert forall|key: A::Id| old(tree).marks().contains_key(key) implies
                    #[trigger] tree.marks()[key] == if on_prefix(path@, i@ + 1, key) {
                        old(tree).marks()[key].with_child(PlacementWork::Subtree, false)
                    } else { old(tree).marks()[key] } by {
                    extend_prefix(path@, i@, key);
                    let prior = old(tree).marks()[key];
                    let raised = prior.with_child(PlacementWork::Subtree, false);
                    assert(before@[key] == if on_prefix(path@, i@, key) { raised } else { prior });
                    assert(raised.with_child(PlacementWork::Subtree, false) == raised);
                };
            }
            i = path_next(i);
        }
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(super) struct IdleState {
    pub same_viewport: bool,
    pub needs_full_solve: bool,
    pub sizing_dirty: bool,
    pub scale_changed: bool,
    pub has_cycle: bool,
}

impl IdleState {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.reusable(), no_unwind))]
    pub(super) fn reusable(self) -> bool {
        self.same_viewport && !self.needs_full_solve && !self.sizing_dirty
            && !self.scale_changed && !self.has_cycle
    }
}

#[cfg(not(verus_keep_ghost))]
pub(super) trait FrameModel { type Id: Copy; }

#[cfg(verus_keep_ghost)]
verus! {
pub(super) trait FrameModel {
    type Id: Copy;
    type Document;
    type Environment;
    type Rect;

    spec fn recorded(&self) -> TailEdits<Self::Id>;
    spec fn idle_state(&self, window: Xy<f32>) -> IdleState;
    spec fn solved_population(&self) -> u32;
    spec fn document(&self) -> Self::Document;
    spec fn last_document(&self) -> Self::Document;
    spec fn environment(&self, window: Xy<f32>) -> Self::Environment;
    spec fn last_environment(&self) -> Self::Environment;
    spec fn view(&self) -> Map<Self::Id, Self::Rect>;
    spec fn full(doc: Self::Document, env: Self::Environment) -> Map<Self::Id, Self::Rect>;
    spec fn placement_mark_inputs(&self) -> SiblingInputs<Self::Id>;
    spec fn placement_root(&self) -> Self::Id;
    spec fn placement_delta(&self, window: Xy<f32>) -> PlacementDelta;
    spec fn placement_draw(&self) -> Draw;
    spec fn visible_ids(&self) -> Seq<Self::Id>;
    spec fn visible_index(&self, id: Self::Id) -> int;
    spec fn observed_geometry(geometry: Geometry) -> Self::Rect;
}

pub(super) open spec fn placement_writes<F: FrameModel + ?Sized>(frame: &F) -> Set<F::Id> {
    subtree_writes(frame.placement_mark_inputs(), frame.placement_root(), true).to_set()
}

/// The owned edit classifier supplies unchanged sizing storage, raw placement
/// inputs, and the mark routing for their visible nodes.
pub(super) open spec fn placement_inputs<F: FrameModel + ?Sized>(frame: &F, window: Xy<f32>) -> bool {
    let delta = frame.placement_delta(window);
    let draw = frame.placement_draw();
    let visible = frame.visible_ids();
    let prior = F::full(frame.last_document(), frame.last_environment());
    let current = F::full(frame.document(), frame.environment(window));
    &&& delta.marks_cover_primitives()
    &&& delta.before_sizing == delta.after_sizing
    &&& prior.dom() == visible.to_set() && current.dom() == visible.to_set()
    &&& forall|id: F::Id| #[trigger] current.contains_key(id) ==> {
        let i = frame.visible_index(id);
        let key = delta.after[i].key;
        let before = delta.before_placement(draw);
        let after = delta.after_placement(draw);
        &&& 0 <= i < delta.after.len()
        &&& before.contains_key(key) && after.contains_key(key)
        &&& prior[id] == F::observed_geometry(before[key].result.output)
        &&& current[id] == F::observed_geometry(after[key].result.output)
        &&& placement_writes(frame).contains(id) == requested((delta.plan)(key))
    }
}

fn placement_before<F: Frame>(frame: &F, window: Xy<f32>) -> (before: Ghost<(
    Map<F::Id, F::Rect>, Map<F::Id, F::Rect>, Map<F::Id, F::Rect>, Set<F::Id>
)>)
    requires placement_inputs(frame, window),
    ensures before@ == (frame.view(),
        F::full(frame.last_document(), frame.last_environment()),
        F::full(frame.document(), frame.environment(window)), placement_writes(frame)),
        before@.1.dom() == before@.2.dom(),
        forall|id: F::Id| before@.2.contains_key(id) && !before@.3.contains(id)
            ==> #[trigger] before@.2[id] == before@.1[id],
    no_unwind
{
    let ghost prior = F::full(frame.last_document(), frame.last_environment());
    let ghost current = F::full(frame.document(), frame.environment(window));
    proof {
        let delta = frame.placement_delta(window);
        let draw = frame.placement_draw();
        placement_only_keeps_skipped_rectangles(delta, draw);
        assert forall|id: F::Id| current.contains_key(id) && !placement_writes(frame).contains(id) implies
            #[trigger] current[id] == prior[id] by {
            let i = frame.visible_index(id);
            assert(0 <= i < delta.after.len());
            assert(!requested((delta.plan)(delta.after[i].key)));
        };
    }
    Ghost((frame.view(), prior, current, placement_writes(frame)))
}

fn frame_window(window: Xy<f32>) -> (input: Ghost<Xy<f32>>)
    ensures input@ == window,
    no_unwind
{
    Ghost(window)
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) trait Frame: FrameModel {
    // The owned entry accounts for every mutation in its edit classification.
    #[cfg_attr(verus_keep_ghost, verus_spec(edits =>
        ensures edits == old(self).recorded(),
            edits is None ==> old(self).document() == old(self).last_document(),
            final(self).view() == old(self).view(),
            final(self).idle_state(window@) == old(self).idle_state(window@),
            final(self).environment(window@) == old(self).environment(window@),
            final(self).last_environment() == old(self).last_environment(),
            final(self).document() == old(self).document(),
            final(self).last_document() == old(self).last_document(),
            final(self).placement_mark_inputs() == old(self).placement_mark_inputs(),
            final(self).placement_root() == old(self).placement_root(),
            edits is Placement && old(self).idle_state(window@).reusable()
                ==> placement_inputs(final(self), window@),
        no_unwind
    ))]
    fn take_edits(&mut self, #[cfg(verus_keep_ghost)] window: Ghost<Xy<f32>>) -> TailEdits<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result.is_some() ==> !old(self).idle_state(window).needs_full_solve
                && !final(self).idle_state(window).needs_full_solve
                && delta.removed <= old(self).solved_population()
                && final(self).solved_population() == old(self).solved_population() as int - delta.removed + delta.added,
            result.is_none() && !final(self).idle_state(window).needs_full_solve
                ==> final(self).solved_population() == old(self).solved_population(),
        no_unwind
    ))]
    fn try_tail(&mut self, parent: Self::Id, delta: TailDelta<Self::Id>, window: Xy<f32>) -> Option<u32>;

    #[cfg_attr(verus_keep_ghost, verus_spec(state =>
        ensures state == self.idle_state(window),
            state.reusable() ==> self.environment(window) == self.last_environment(),
        no_unwind
    ))]
    fn idle_inputs(&self, window: Xy<f32>) -> IdleState;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn clear_tail(&mut self);

    // The owned writer retains skipped rectangles and overwrites the live write set.
    #[cfg_attr(verus_keep_ghost, verus_spec(placed =>
        ensures final(self).view().dom() == old(self).view().dom(),
            placed.evidence@.valid(), placed.evidence@.partial, placed.evidence@.start.ordinary,
            forall|id: Self::Id| final(self).view().contains_key(id) ==> (#[trigger] final(self).view()[id]) ==
                if placement_writes(old(self)).contains(id) {
                    Self::full(old(self).document(), old(self).environment(window))[id]
                } else { old(self).view()[id] },
        no_unwind
    ))]
    fn place_retained(&mut self, window: Xy<f32>) -> RootPlacement<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures publication::frame_result(result, false), no_unwind))]
    fn solve_incremental(&mut self, window: Xy<f32>) -> FrameResult<Self::Id>;
}

#[cfg(verus_keep_ghost)]
verus! {
#[verifier::reject_recursive_types(I)]
pub(super) enum OwnedEvidence<I> {
    Tail(u32),
    Idle,
    Placement(RootEvidence<I>),
    Engine(FrameResult<I>),
}

pub(super) open spec fn completed<I>(result: OwnedFrame<I>) -> bool {
    match result.evidence@ {
        OwnedEvidence::Tail(computed) => result.outcome == IncrementalRelayoutOutcome::Success { computed },
        OwnedEvidence::Idle => result.outcome == IncrementalRelayoutOutcome::Success { computed: 0 },
        OwnedEvidence::Placement(p) => p.valid() && p.partial && p.start.ordinary
            && result.outcome == IncrementalRelayoutOutcome::Success { computed: 0 },
        OwnedEvidence::Engine(frame) => result.outcome == frame.outcome && publication::frame_result(frame, false),
    }
}

fn tail_evidence<I>(computed: u32) -> (value: Ghost<OwnedEvidence<I>>)
    ensures value@ == OwnedEvidence::Tail(computed), no_unwind
{ Ghost(OwnedEvidence::Tail(computed)) }

fn idle_evidence<I>() -> (value: Ghost<OwnedEvidence<I>>)
    ensures value@ == OwnedEvidence::Idle, no_unwind
{ Ghost(OwnedEvidence::Idle) }

fn placement_evidence<I>(placement: RootPlacement<I>) -> (value: Ghost<OwnedEvidence<I>>)
    ensures value@ == OwnedEvidence::Placement(placement.evidence@), no_unwind
{ Ghost(OwnedEvidence::Placement(placement.evidence@)) }

fn engine_evidence<I>(result: FrameResult<I>) -> (value: Ghost<OwnedEvidence<I>>)
    ensures value@ == OwnedEvidence::Engine(result), no_unwind
{ Ghost(OwnedEvidence::Engine(result)) }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
pub(super) struct OwnedFrame<I> {
    pub(super) outcome: IncrementalRelayoutOutcome,
    #[cfg(verus_keep_ghost)]
    pub(super) evidence: Ghost<OwnedEvidence<I>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(frame =>
    ensures frame.outcome == outcome, frame.evidence == evidence, no_unwind
))]
fn owned_result<I>(outcome: IncrementalRelayoutOutcome, #[cfg(verus_keep_ghost)] evidence: Ghost<OwnedEvidence<I>>) -> OwnedFrame<I> {
    OwnedFrame {
        outcome,
        #[cfg(verus_keep_ghost)]
        evidence,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures completed(result),
    old(frame).recorded() is None && old(frame).idle_state(window).reusable() ==> {
        &&& result.evidence@ is Idle
        &&& result.outcome == IncrementalRelayoutOutcome::Success { computed: 0 }
        &&& final(frame).view() == old(frame).view()
        &&& (old(frame).view() == F::full(old(frame).last_document(), old(frame).last_environment())
                ==> final(frame).view() == F::full(old(frame).document(), old(frame).environment(window)))
    },
    old(frame).recorded() is Placement && old(frame).idle_state(window).reusable() ==> {
        &&& result.evidence@ is Placement
        &&& result.outcome == IncrementalRelayoutOutcome::Success { computed: 0 }
        &&& (old(frame).view() == F::full(old(frame).last_document(), old(frame).last_environment())
                ==> final(frame).view() == F::full(old(frame).document(), old(frame).environment(window)))
    },
    no_unwind
))]
pub(super) fn run<F: Frame>(frame: &mut F, window: Xy<f32>) -> OwnedFrame<F::Id> {
    let edits = frame.take_edits(#[cfg(verus_keep_ghost)] frame_window(window));
    if let TailEdits::Stack { parent, delta } = edits {
        if let Some(computed) = frame.try_tail(parent, delta, window) {
            return owned_result(IncrementalRelayoutOutcome::Success { computed }, #[cfg(verus_keep_ghost)] tail_evidence(computed));
        }
    }
    if matches!(edits, TailEdits::None | TailEdits::Placement) {
        let state = frame.idle_inputs(window);
        if state.reusable() {
            if matches!(edits, TailEdits::Placement) {
                #[cfg(verus_keep_ghost)]
                let before = placement_before(frame, window);
                let _placement = frame.place_retained(window);
                #[cfg(verus_keep_ghost)]
                proof! {
                    let (published, prior, current, writes) = before@;
                    if published == prior {
                        assert(frame.view().dom() == current.dom());
                        assert forall|id: F::Id| current.contains_key(id)
                            implies #[trigger] frame.view()[id] == current[id] by {
                            if !writes.contains(id) {
                                assert(prior[id] == current[id]);
                            }
                        };
                        assert(frame.view() =~= current);
                    }
                }
                return owned_result(IncrementalRelayoutOutcome::Success { computed: 0 },
                    #[cfg(verus_keep_ghost)] placement_evidence(_placement));
            }
            return owned_result(IncrementalRelayoutOutcome::Success { computed: 0 }, #[cfg(verus_keep_ghost)] idle_evidence());
        }
        // Idle frames can separate edits to the same stack.
        if matches!(edits, TailEdits::Placement) || !state.same_viewport || state.needs_full_solve { frame.clear_tail(); }
    } else {
        frame.clear_tail();
    }
    let result = frame.solve_incremental(window);
    owned_result(result.outcome, #[cfg(verus_keep_ghost)] engine_evidence(result))
}
