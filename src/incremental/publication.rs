//! Drive an incremental sizing pass and publish exactly one resulting view.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::prepare_nodes::Records;
#[cfg(verus_keep_ghost)]
use crate::prepare_nodes::RecordModel;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::{N_SLOTS, Route, SlotBits};
#[cfg(verus_keep_ghost)]
use crate::{checked_view::kernel as checked_view, queue_storage::numeric, regions::regional};
#[cfg(verus_keep_ghost)]
use checked_view::FrameEvent;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::route;
#[cfg(verus_keep_ghost)]
use crate::placement::kernel::partial_placement;
#[cfg(verus_keep_ghost)]
use crate::placement::{entry::{RootEvidence, RootPlacement}, node::PlacementLinks};
#[cfg(not(verus_keep_ghost))]
use crate::{placement_work::partial_placement, solve::cycle_rules::{N_SLOTS, Route, SlotBits, route}};
#[cfg(not(verus_keep_ghost))]
use crate::place::placement_entry::RootPlacement;
#[cfg(not(verus_keep_ghost))]
use super::{checked_view, numeric, regional};

/// What `solve_layout_incremental` did. The `Fallback` variants give the reason for a full solve.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IncrementalRelayoutOutcome {
    /// The relayout was incremental.
    Success {
        /// Slot computations.
        computed: u32,
    },
    /// The checked pass could not confirm equal sizing values and output rectangles.
    /// The tree keeps the result of the canonical full solve.
    CheckedIncrementalRelayoutMismatch,
    /// The incremental relayout fell back to a full relayout because the full layout was never solved before.
    FallbackNeverSolved,
    /// Legacy outcome retained for API compatibility. Structural edits use incremental measurement.
    FallbackStructuralChange,
    /// The previous solve found a cycle and this pass has no structural edits to rebuild its dependencies.
    FallbackCycle,
    /// A block or wrapping flow must rebuild its line or collapsed-margin data.
    FallbackFlow,
    /// The queued work exceeded its budget, or a dependency rank exceeded the queue's representable ordering.
    FallbackTooMuchWork,
    /// The incremental relayout fell back to a full relayout because `LayoutTree::invalidate()` was called explicitly.
    FallbackInvalidated,
}

impl IncrementalRelayoutOutcome {
    /// The pending-full flag always chooses a full pass.
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.as_fallback(), no_unwind))]
    pub(crate) fn as_fallback(self) -> Self {
        match self {
            Self::Success { .. } | Self::CheckedIncrementalRelayoutMismatch => Self::FallbackInvalidated,
            reason => reason,
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct FramePlan {
    pub pending: Option<IncrementalRelayoutOutcome>,
    pub route: Route,
    pub root_replay: Option<regional::RootReplay>,
    pub partial: bool,
    pub numeric_placement: bool,
    pub remember_after: bool,
    #[cfg(verus_keep_ghost)]
    pub(crate) inputs: Ghost<FrameInputs>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct FrameInputs {
    pub pending: Option<IncrementalRelayoutOutcome>,
    pub has_topology: bool,
    pub structural: bool,
    pub unknown_structure: bool,
    pub replay_pending: bool,
    pub same_window: bool,
    pub scale_changed: bool,
    pub has_cycle: bool,
    pub has_flow: bool,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(same =>
    ensures same == (old_x.word() == new_x.word() && old_y.word() == new_y.word()),
    no_unwind
))]
pub(crate) fn same_viewport<T: SlotBits>(old_x: T, old_y: T, new_x: T, new_y: T) -> bool {
    old_x.bits() == new_x.bits() && old_y.bits() == new_y.bits()
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(plan =>
    ensures *final(tracking), plan.inputs@ == inputs, plan.pending == inputs.pending,
        placement_planned(&plan),
        plan.route == route(inputs.structural, inputs.has_cycle, inputs.has_flow, !inputs.same_window),
        plan.root_replay == regional::root_replay(inputs.pending, inputs.replay_pending, !inputs.same_window,
            inputs.has_flow, !inputs.structural && !inputs.unknown_structure && !inputs.has_cycle),
        plan.partial == (
            inputs.structural && (!inputs.has_topology || *old(tracking)) && inputs.same_window
                && !inputs.scale_changed
        ),
        plan.numeric_placement == (!inputs.has_topology && !inputs.structural
            && inputs.same_window && !inputs.scale_changed),
        plan.remember_after == (inputs.has_topology && !*old(tracking) && !inputs.structural),
    no_unwind
))]
pub(crate) fn plan_frame(inputs: FrameInputs, tracking: &mut bool) -> FramePlan {
    #[cfg(verus_keep_ghost)]
    let before = save_plan_inputs(&inputs);
    let needs_topology = inputs.has_topology && !*tracking;
    *tracking = true;
    FramePlan {
        pending: inputs.pending,
        route: route(inputs.structural, inputs.has_cycle, inputs.has_flow, !inputs.same_window),
        root_replay: regional::root_replay(inputs.pending, inputs.replay_pending, !inputs.same_window,
            inputs.has_flow, !inputs.structural && !inputs.unknown_structure && !inputs.has_cycle),
        partial: partial_placement(inputs.structural, needs_topology, inputs.same_window, inputs.scale_changed),
        // The owned tree uses live edit marks instead of a topology snapshot.
        numeric_placement: !inputs.has_topology && !inputs.structural && inputs.same_window && !inputs.scale_changed,
        remember_after: needs_topology && !inputs.structural,
        #[cfg(verus_keep_ghost)]
        inputs: before,
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn valid_frame<F: RecordModel + ?Sized>(frame: &F) -> bool {
    frame.order().ordered() && frame.order().closed_subtrees()
}

fn save_plan_inputs(inputs: &FrameInputs) -> (before: Ghost<FrameInputs>)
    ensures before@ == *inputs, no_unwind
{ Ghost(*inputs) }

/// Both sources of retained placement require unchanged viewport and scale;
/// the flags identify whether the planner or ranked queue supplies the marks.
pub(crate) open spec fn placement_planned(plan: &FramePlan) -> bool {
    let inputs = plan.inputs@;
    &&& plan.partial ==> inputs.structural && inputs.same_window && !inputs.scale_changed
    &&& plan.numeric_placement == (!inputs.has_topology && !inputs.structural
        && inputs.same_window && !inputs.scale_changed)
}

pub(crate) enum SizingRoute {
    RootReplay(regional::RootReplay),
    Pending(IncrementalRelayoutOutcome),
    Structural,
    Cycle,
    Flow,
    Queue,
}

pub(crate) open spec fn sizing_route(plan: FramePlan) -> SizingRoute {
    if let Some(replay) = plan.root_replay {
        SizingRoute::RootReplay(replay)
    } else if let Some(reason) = plan.pending {
        SizingRoute::Pending(reason)
    } else {
        match plan.route {
            Route::Structural => SizingRoute::Structural,
            Route::Cycle => SizingRoute::Cycle,
            Route::Flow => SizingRoute::Flow,
            Route::Queue => SizingRoute::Queue,
        }
    }
}

pub(crate) open spec fn numeric_fast_outcome<W: Copy, F: numeric::CachedQueue<W> + ?Sized>(
    frame: &F, window: W, route: SizingRoute, track_output: bool, measured: IncrementalRelayoutOutcome,
) -> bool {
    &&& (route is Queue && numeric::idle_numeric(frame, window))
        ==> measured == (IncrementalRelayoutOutcome::Success { computed: 0 })
    &&& (route is Queue && !track_output && numeric::retained_tape_hit(frame, window).is_some())
        ==> measured == (IncrementalRelayoutOutcome::Success {
            computed: numeric::retained_tape_hit(frame, window).unwrap(),
        })
}

pub(crate) open spec fn certified_numeric_inputs<W: Copy, F: numeric::CachedQueue<W> + ?Sized>(
    frame: &F, window: W, track_output: bool,
) -> bool {
    (!track_output && numeric::certified_tape_hit(frame, window))
        || numeric::certified_scalar_seeded_frame(frame, window, track_output)
        || numeric::certified_first_capture_frame(frame, window, track_output)
        || numeric::certified_idle_frame(frame, window)
}

pub(crate) open spec fn numeric_sizing_exact<W: Copy, F: numeric::CachedQueue<W> + ?Sized>(
    before: &F, after: &F, window: W, route: SizingRoute, track_output: bool, measured: IncrementalRelayoutOutcome,
) -> bool {
    route is Queue && measured is Success && certified_numeric_inputs(before, window, track_output)
        ==> after.slot_words() == before.program_for_window(window).fresh()
}

}

/// Primitive frame state and publication boundaries. The queue, regional,
/// and checked controls below execute their verified implementations directly.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FrameActions<W: Copy>: Records + regional::Scene<Window = W>
    + numeric::CachedQueue<W> + checked_view::Reference<W, N_SLOTS>
{
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(),
            numeric::idle_numeric(final(self), window) == numeric::idle_numeric(old(self), window),
            numeric::retained_tape_hit(final(self), window) == numeric::retained_tape_hit(old(self), window),
            forall |track: bool| #[trigger] certified_numeric_inputs(final(self), window, track)
                == certified_numeric_inputs(old(self), window, track),
            final(self).program_for_window(window) == old(self).program_for_window(window),
        no_unwind
    ))]
    fn frame_inputs(&mut self, window: W) -> (FrameInputs, &mut bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(retained => ensures retained == self.retains_view(), no_unwind))]
    fn retains_rectangles(&self) -> bool;

    // The public adapter can override its ordinary full solve.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires valid_frame(old(self)),
        ensures final(self).order() == old(self).order(),
            final(self).frame_events() == old(self).frame_events().push(FrameEvent::AdapterFull),
        no_unwind
    ))]
    fn publish_full_solve(&mut self, window: W);

    #[cfg_attr(verus_keep_ghost, verus_spec(placed =>
        requires valid_frame(old(self)),
        ensures final(self).order() == old(self).order(),
            final(self).slot_words() == old(self).slot_words(),
            placed.evidence@.valid(), placed.evidence@.start.ordinary,
            placed.evidence@.partial == partial, placed.evidence@.links == PlacementLinks::from_order(old(self).order()),
            final(self).frame_events() == old(self).frame_events().push(FrameEvent::Placement(partial)),
        no_unwind
    ))]
    fn publish_placement(&mut self, partial: bool) -> RootPlacement<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires valid_frame(old(self)),
        ensures final(self).order() == old(self).order(),
            final(self).slot_words() == old(self).slot_words(),
            final(self).frame_events() == old(self).frame_events().push(FrameEvent::RememberTopology),
        no_unwind
    ))]
    fn remember(&mut self);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
pub(crate) struct FrameResult<I> {
    pub outcome: IncrementalRelayoutOutcome,
    #[cfg(verus_keep_ghost)]
    pub evidence: Ghost<FrameEvidence<I>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
struct FrameSizing<I> {
    outcome: IncrementalRelayoutOutcome,
    #[cfg(verus_keep_ghost)]
    work: Ghost<RegionalWork<I>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[cfg(verus_keep_ghost)]
verus! {
#[verifier::reject_recursive_types(I)]
pub(crate) enum RegionalWork<I> {
    None,
    Structural(regional::RegionWork<I>),
    Root(regional::RootWork<I>),
}

pub(crate) struct CheckedCandidate<I> {
    pub sizes: Seq<checked_view::SizingRecord<I, N_SLOTS>>,
    pub rectangles: Seq<checked_view::OutputRecord<I>>,
}

pub(crate) struct CheckedEvidence<I> {
    pub candidate: CheckedCandidate<I>,
    pub complete: bool,
    pub agrees: bool,
}

/// The sizing result and the observations used by the publication decision.
#[verifier::reject_recursive_types(I)]
pub(crate) struct FrameEvidence<I> {
    pub inputs: FrameInputs,
    pub route: SizingRoute,
    pub measured: IncrementalRelayoutOutcome,
    pub work: RegionalWork<I>,
    pub track_output: bool,
    // Sizing and adapter callbacks have already run when this trace begins.
    pub before_publication: Seq<FrameEvent>,
    pub retains_view: bool,
    pub partial: bool,
    pub remember: bool,
    pub placement: Option<RootEvidence<I>>,
    pub comparison: Option<CheckedEvidence<I>>,
}

pub(crate) open spec fn publication_events<I>(evidence: FrameEvidence<I>, check: bool) -> Seq<FrameEvent> {
    if check {
        evidence.before_publication.push(FrameEvent::CanonicalFull)
    } else if evidence.measured is Success {
        let placed = evidence.before_publication.push(FrameEvent::Placement(evidence.partial));
        if evidence.remember { placed.push(FrameEvent::RememberTopology) } else { placed }
    } else {
        evidence.before_publication.push(FrameEvent::AdapterFull)
    }
}

pub(crate) open spec fn sizing_work<I>(
    route: SizingRoute, outcome: IncrementalRelayoutOutcome, work: RegionalWork<I>,
) -> bool {
    use IncrementalRelayoutOutcome::*;
    match (route, work) {
        (SizingRoute::Structural, RegionalWork::Structural(work)) => work.valid(outcome),
        (SizingRoute::RootReplay(replay), RegionalWork::Root(work)) => work.valid(replay, outcome),
        (SizingRoute::Pending(reason), RegionalWork::None) => outcome == reason.as_fallback(),
        (SizingRoute::Cycle, RegionalWork::None) => outcome == FallbackCycle,
        (SizingRoute::Flow, RegionalWork::None) => outcome == FallbackFlow,
        (SizingRoute::Queue, RegionalWork::None) => !(outcome is CheckedIncrementalRelayoutMismatch),
        _ => false,
    }
}

pub(crate) open spec fn frame_result<I>(result: FrameResult<I>, check: bool) -> bool {
    let evidence = result.evidence@;
    &&& sizing_work(evidence.route, evidence.measured, evidence.work)
    &&& !(evidence.measured is CheckedIncrementalRelayoutMismatch)
    &&& evidence.comparison.is_some() == (check && evidence.measured is Success)
    &&& evidence.placement.is_some() == (!check && evidence.measured is Success)
    &&& evidence.placement.is_some() ==> {
        let placed = evidence.placement.unwrap();
        placed.valid() && placed.start.ordinary && placed.partial == evidence.partial
    }
    &&& evidence.comparison.is_some() && evidence.comparison.unwrap().agrees
        ==> evidence.comparison.unwrap().complete
    &&& result.outcome == if evidence.comparison.is_some() && !evidence.comparison.unwrap().agrees {
            IncrementalRelayoutOutcome::CheckedIncrementalRelayoutMismatch
        } else { evidence.measured }
    &&& (evidence.partial || evidence.remember) ==> !check && evidence.measured is Success
    &&& evidence.partial ==> evidence.retains_view && evidence.inputs.same_window
        && !evidence.inputs.scale_changed
        && (evidence.inputs.structural || evidence.track_output)
}

pub(crate) open spec fn checked_agreement<F: checked_view::ReferenceModel<N_SLOTS> + ?Sized>(
    reference: &F, evidence: FrameEvidence<F::Id>,
) -> bool {
    if let Some(comparison) = evidence.comparison {
        comparison.agrees == (comparison.complete
            && checked_view::ordered_sizes(reference) == comparison.candidate.sizes
            && reference.last_reference_view() == comparison.candidate.rectangles)
    } else { true }
}

fn start_evidence<F: checked_view::ReferenceModel<N_SLOTS> + ?Sized>(
    frame: &F, plan: &FramePlan, sizing: &FrameSizing<F::Id>, check: bool,
) -> (evidence: Ghost<FrameEvidence<F::Id>>)
    ensures evidence@ == (FrameEvidence {
        inputs: plan.inputs@,
        route: sizing_route(*plan), measured: sizing.outcome, work: sizing.work@,
        track_output: plan.numeric_placement && !check,
        before_publication: frame.frame_events(), retains_view: frame.retains_view(),
        partial: false, remember: false, comparison: None, placement: None,
    }),
    no_unwind
{
    Ghost(FrameEvidence {
        inputs: plan.inputs@,
        route: sizing_route(*plan), measured: sizing.outcome, work: sizing.work@,
        track_output: plan.numeric_placement && !check,
        before_publication: frame.frame_events(), retains_view: frame.retains_view(),
        partial: false, remember: false, comparison: None, placement: None,
    })
}

fn checked_candidate<F: checked_view::ReferenceModel<N_SLOTS> + ?Sized>(
    frame: &F,
) -> (candidate: Ghost<CheckedCandidate<F::Id>>)
    ensures candidate@.sizes == checked_view::ordered_sizes(frame), candidate@.rectangles == frame.candidate_view(),
    no_unwind
{
    Ghost(CheckedCandidate { sizes: checked_view::ordered_sizes(frame), rectangles: frame.candidate_view() })
}

fn comparison_evidence<I>(
    evidence: Ghost<FrameEvidence<I>>, candidate: Ghost<CheckedCandidate<I>>, complete: bool, agrees: bool,
) -> (next: Ghost<FrameEvidence<I>>)
    ensures next@ == (FrameEvidence { comparison: Some(CheckedEvidence { candidate: candidate@, complete, agrees }), ..evidence@ }),
    no_unwind
{
    Ghost(FrameEvidence { comparison: Some(CheckedEvidence { candidate: candidate@, complete, agrees }), ..evidence@ })
}

fn placement_evidence<I>(
    evidence: Ghost<FrameEvidence<I>>, placed: Ghost<RootEvidence<I>>, partial: bool, remember: bool,
) -> (next: Ghost<FrameEvidence<I>>)
    ensures next@ == (FrameEvidence { partial, remember, placement: Some(placed@), ..evidence@ }),
    no_unwind
{
    Ghost(FrameEvidence { partial, remember, placement: Some(placed@), ..evidence@ })
}

fn no_regional_work<I>() -> (work: Ghost<RegionalWork<I>>)
    ensures work@ == RegionalWork::None,
    no_unwind
{
    Ghost(RegionalWork::None)
}

fn structural_work<I>(result: &regional::StructuralResult<I>) -> (work: Ghost<RegionalWork<I>>)
    ensures work@ == RegionalWork::Structural(result.work@),
    no_unwind
{
    Ghost(RegionalWork::Structural(result.work@))
}

fn root_work<I>(result: &regional::RootResult<I>) -> (work: Ghost<RegionalWork<I>>)
    ensures work@ == RegionalWork::Root(result.work@),
    no_unwind
{
    Ghost(RegionalWork::Root(result.work@))
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.outcome == outcome, result.evidence == evidence, no_unwind
))]
fn published<I>(
    outcome: IncrementalRelayoutOutcome, #[cfg(verus_keep_ghost)] evidence: Ghost<FrameEvidence<I>>,
) -> FrameResult<I> {
    FrameResult {
        outcome,
        #[cfg(verus_keep_ghost)]
        evidence,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.outcome == outcome, result.work == work, no_unwind
))]
fn sized<I>(
    outcome: IncrementalRelayoutOutcome,
    #[cfg(verus_keep_ghost)] work: Ghost<RegionalWork<I>>,
) -> FrameSizing<I> {
    FrameSizing {
        outcome,
        #[cfg(verus_keep_ghost)]
        work,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires valid_frame(old(frame)),
    ensures final(frame).order() == old(frame).order(),
        sizing_work(sizing_route(*plan), result.outcome, result.work@),
        !(result.outcome is CheckedIncrementalRelayoutMismatch),
        numeric_fast_outcome(old(frame), window, sizing_route(*plan), plan.numeric_placement && !check, result.outcome),
        numeric_sizing_exact(old(frame), final(frame), window, sizing_route(*plan),
            plan.numeric_placement && !check, result.outcome),
    no_unwind
))]
fn measure_frame<W: Copy, F: FrameActions<W> + ?Sized>(
    frame: &mut F, plan: &FramePlan, window: W, check: bool,
) -> FrameSizing<F::Id> {
    use IncrementalRelayoutOutcome::*;
    let outcome = if let Some(replay) = plan.root_replay {
        let result = regional::replay_root(frame, window, replay);
        return sized(result.outcome, #[cfg(verus_keep_ghost)] root_work(&result));
    } else if let Some(reason) = plan.pending {
        reason.as_fallback()
    } else {
        match plan.route {
            Route::Structural => {
                let result = regional::relayout(frame, window);
                return sized(result.outcome, #[cfg(verus_keep_ghost)] structural_work(&result));
            }
            Route::Cycle => FallbackCycle,
            Route::Flow => FallbackFlow,
            Route::Queue => numeric::measure_cached::<_, _, F::Memory>(frame, window, plan.numeric_placement && !check),
        }
    };
    sized(outcome, #[cfg(verus_keep_ghost)] no_regional_work())
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires valid_frame(old(frame)), placement_planned(&plan),
    ensures final(frame).order() == old(frame).order(), frame_result(result, check),
        checked_agreement(final(frame), result.evidence@),
        result.evidence@.route == sizing_route(plan),
        numeric_fast_outcome(old(frame), window, result.evidence@.route,
            result.evidence@.track_output, result.evidence@.measured),
        !check ==> numeric_sizing_exact(old(frame), final(frame), window,
            result.evidence@.route, result.evidence@.track_output, result.evidence@.measured),
        result.evidence@.partial == (!check && result.evidence@.measured is Success
            && plan.root_replay.is_none() && (plan.partial || plan.numeric_placement) && result.evidence@.retains_view),
        result.evidence@.remember == (!check && result.evidence@.measured is Success
            && plan.remember_after && plan.root_replay.is_none()),
        final(frame).frame_events() == publication_events(result.evidence@, check),
    no_unwind
))]
fn run_frame<W: Copy, F: FrameActions<W> + ?Sized>(
    frame: &mut F, plan: FramePlan, window: W, check: bool,
) -> FrameResult<F::Id> {
    let sizing = measure_frame(frame, &plan, window, check);
    finish_frame(frame, plan, window, check, sizing)
}

/// A failed sizing pass cannot publish an incremental candidate. A checked
/// frame publishes the canonical result regardless of capture or comparison.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires valid_frame(old(frame)), sizing_work(sizing_route(plan), sizing.outcome, sizing.work@),
        !(sizing.outcome is CheckedIncrementalRelayoutMismatch), placement_planned(&plan),
    ensures final(frame).order() == old(frame).order(), frame_result(result, check),
        checked_agreement(final(frame), result.evidence@),
        result.evidence@.route == sizing_route(plan), result.evidence@.measured == sizing.outcome,
        result.evidence@.work == sizing.work@,
        result.evidence@.track_output == (plan.numeric_placement && !check),
        !check && sizing.outcome is Success ==> final(frame).slot_words() == old(frame).slot_words(),
        result.evidence@.before_publication == old(frame).frame_events(),
        result.evidence@.retains_view == old(frame).retains_view(),
        result.evidence@.comparison.is_some() ==> {
            let candidate = result.evidence@.comparison.unwrap().candidate;
            candidate.sizes == checked_view::ordered_sizes(old(frame)) && candidate.rectangles == old(frame).candidate_view()
        },
        result.evidence@.partial == (!check && sizing.outcome is Success
            && plan.root_replay.is_none() && (plan.partial || plan.numeric_placement) && old(frame).retains_view()),
        result.evidence@.remember == (!check && sizing.outcome is Success && plan.remember_after && plan.root_replay.is_none()),
        final(frame).frame_events() == publication_events(result.evidence@, check),
    no_unwind
))]
fn finish_frame<W: Copy, F: FrameActions<W> + ?Sized>(
    frame: &mut F, plan: FramePlan, window: W, check: bool, sizing: FrameSizing<F::Id>,
) -> FrameResult<F::Id> {
    use IncrementalRelayoutOutcome::*;
    #[cfg(verus_keep_ghost)]
    let evidence = start_evidence(frame, &plan, &sizing, check);
    let outcome = sizing.outcome;
    if !matches!(outcome, Success { .. }) {
        if check {
            // The checked API always publishes the engine's reference view.
            // There is no incremental candidate to capture on this route.
            frame.publish_reference(window);
            return published::<F::Id>(outcome, #[cfg(verus_keep_ghost)] evidence);
        }
        frame.publish_full_solve(window);
        return published::<F::Id>(outcome, #[cfg(verus_keep_ghost)] evidence);
    }
    if check {
        #[cfg(verus_keep_ghost)]
        let candidate = checked_candidate(frame);
        let comparison = checked_view::checked::<_, _, F::Memory, N_SLOTS>(frame, window);
        let result = if comparison.agrees { outcome } else { CheckedIncrementalRelayoutMismatch };
        return published::<F::Id>(result,
            #[cfg(verus_keep_ghost)]
            comparison_evidence(evidence, candidate, comparison.complete, comparison.agrees),
        );
    }
    let partial = plan.root_replay.is_none() && (plan.partial || plan.numeric_placement) && frame.retains_rectangles();
    let _placed = frame.publish_placement(partial);
    let remember = plan.remember_after && plan.root_replay.is_none();
    if remember { frame.remember(); }
    published::<F::Id>(outcome, #[cfg(verus_keep_ghost)] placement_evidence(evidence, _placed.evidence, partial, remember))
}

/// Start the native incremental entry from the actual pending work and
/// retained topology flag before borrowing the tree for measurement.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires valid_frame(old(frame)),
    ensures final(frame).order() == old(frame).order(), frame_result(result, check),
        checked_agreement(final(frame), result.evidence@),
        numeric_fast_outcome(old(frame), window, result.evidence@.route,
            result.evidence@.track_output, result.evidence@.measured),
        !check ==> numeric_sizing_exact(old(frame), final(frame), window,
            result.evidence@.route, result.evidence@.track_output, result.evidence@.measured),
        final(frame).frame_events() == publication_events(result.evidence@, check),
    no_unwind
))]
pub(crate) fn enter_frame<W: Copy, F: FrameActions<W> + ?Sized>(
    frame: &mut F, window: W, check: bool,
) -> FrameResult<F::Id> {
    let plan = {
        let (inputs, tracking) = frame.frame_inputs(window);
        plan_frame(inputs, tracking)
    };
    run_frame(frame, plan, window, check)
}
