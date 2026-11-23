//! Refinement of the owned tree's packed fixed leaf declarations and reuse gates.
use super::structural::kernel::StructuralChange;
use vstd::prelude::*;

#[path = "../src/fixed_leaf_cache.rs"]
pub(crate) mod runtime;
use runtime::Summary;

verus! {

pub struct Declaration {
    pub enabled: bool,
    pub free: bool,
    pub span_x: u16,
    pub span_y: u16,
    pub zero_margins: bool,
    pub start_x: bool,
    pub start_y: bool,
}

pub(crate) open spec fn describes(summary: Summary, live: Declaration) -> bool {
    live.enabled && summary.describes(live.free, live.span_x > 1 || live.span_y > 1,
        live.zero_margins && live.start_x && live.start_y)
}

pub(crate) open spec fn current(summary: Summary, live: Declaration) -> bool {
    summary.is_empty() || describes(summary, live)
}

proof fn empty_summary_is_inert(summary: Summary)
    requires summary.is_empty(),
    ensures !summary.is_ready(), !summary.stack_start(),
{
    let bits = summary.0;
    assert(bits & runtime::READY == 0 && bits & runtime::STACK_START == 0)
        by(bit_vector) requires bits == 0;
}

proof fn current_summary_decodes(summary: Summary, live: Declaration)
    requires current(summary, live),
    ensures summary.is_ready() == !summary.is_empty(),
        summary.stack_start() ==> describes(summary, live),
{
    if summary.is_empty() { empty_summary_is_inert(summary); }
}

/// The direct counting contribution from the enabled ordinary leaf's live parameters.
pub open spec fn add_leaf(
    live: Declaration, counts: (u32, u32, u32), grid_spans: u32,
) -> (int, int, u32) {
    (
        counts.0 + 1,
        if live.free { counts.1 as int } else { counts.1 + 1 },
        if !live.free && (live.span_x > 1 || live.span_y > 1) {
            counts.2 | grid_spans
        } else {
            counts.2
        },
    )
}

/// Record the actual projection used by the solver, including the independent
/// free-placement path that need not read the remaining style fields.
pub(crate) fn record_live(live: Declaration) -> (summary: Summary)
    requires live.enabled,
    ensures describes(summary, live),
{
    if live.free {
        runtime::record(true, false, false)
    } else {
        let spans = live.span_x > 1 || live.span_y > 1;
        let simple_start = live.start_x && live.start_y && live.zero_margins;
        runtime::record(false, spans, simple_start)
    }
}

pub open spec fn exact_fixed_slots(flags: u32, marker: u32, solved: u32) -> bool {
    &&& flags & !0xffu32 == marker
    &&& flags & 3 == solved
    &&& (flags >> 2) & 3 == solved
    &&& (flags >> 4) & 3 == solved
    &&& (flags >> 6) & 3 == solved
}

proof fn fixed_word_matches_individual_slots(flags: u32, marker: u32, solved: u32)
    requires marker & 0xffu32 == 0, solved < 4,
    ensures (flags == runtime::registered_flags(marker, solved)) == exact_fixed_slots(flags, marker, solved),
{
    assert((flags == (marker | solved | (solved << 2) | (solved << 4) | (solved << 6)))
        == (flags & !0xffu32 == marker && flags & 3 == solved && (flags >> 2) & 3 == solved
            && (flags >> 4) & 3 == solved && (flags >> 6) & 3 == solved))
        by(bit_vector) requires marker & 0xffu32 == 0, solved < 4;
}

/// Check the preparation decision against live declarations. The surrounding
/// solver establishes that the child still has no children and that its parent
/// uses this ordinary preparation path before calling the packed kernel.
pub(crate) fn prepare_from_summary(
    summary: Summary, flags: u32, marker: u32, solved: u32, flow: &[u32; 2], mark: &mut StructuralChange,
    counts: (u32, u32, u32), grid_spans: u32, Ghost(live): Ghost<Declaration>,
) -> (out: Option<(u32, u32, u32)>)
    requires current(summary, live), counts.0 < u32::MAX, counts.1 < u32::MAX,
        marker & 0xffu32 == 0, solved < 4,
    ensures out.is_some() == (!summary.is_empty() && exact_fixed_slots(flags, marker, solved)
            && flow[0] == 0 && flow[1] == 0),
        out.is_some() ==> live.enabled,
        out.is_some() ==> ({
            let actual = out.unwrap();
            (actual.0 as int, actual.1 as int, actual.2) == add_leaf(live, counts, grid_spans)
        }),
        *final(mark) == if out.is_some() { StructuralChange::Clean } else { *old(mark) },
{
    proof! {
        current_summary_decodes(summary, live);
        fixed_word_matches_individual_slots(flags, marker, solved);
    }
    if summary.is_ready() && runtime::reuse_registered(flags, runtime::registered_flags(marker, solved), flow, mark) {
        let nodes = counts.0 + 1;
        let placed = counts.1 + (if summary.in_flow() { 1 } else { 0 });
        let flags = if summary.spans() { counts.2 | grid_spans } else { counts.2 };
        Some((nodes, placed, flags))
    } else {
        None
    }
}

/// Invalidation clears the prepared byte for every next style, and preserves
/// all flags outside the fixed-leaf marker.
pub(crate) fn change_declarations(
    flags: &mut u32, marker: u32, summary: &mut Summary,
)
    ensures *final(flags) == (*old(flags) & !marker),
        forall |next: Declaration| #[trigger] current(*final(summary), next),
        !final(summary).stack_start(),
{
    runtime::invalidate(flags, marker, summary);
    proof! { empty_summary_is_inert(*summary); }
}

#[derive(PartialEq, Eq)]
pub enum Placement {
    Disabled,
    Free,
    Start,
    General,
}

pub open spec fn direct(live: Declaration, forward: bool, cross_x: bool) -> Placement {
    if !live.enabled {
        Placement::Disabled
    } else if live.free {
        Placement::Free
    } else if forward && live.zero_margins && (if cross_x { live.start_x } else { live.start_y }) {
        Placement::Start
    } else {
        Placement::General
    }
}

/// The cached route can skip the parameter read only for a live start-aligned
/// in-flow item, for either cross axis. All other items keep the original route.
pub(crate) fn place_from_summary(
    summary: Summary, live: Declaration, partial: bool, retained: bool,
    forward: bool, cross_x: bool,
) -> (out: (Placement, bool))
    requires current(summary, live),
    ensures out.0 == direct(live, forward, cross_x),
        out.1 ==> (!partial && retained && forward && out.0 == Placement::Start),
{
    proof! { current_summary_decodes(summary, live); }
    let allowed = !partial && forward && retained;
    if allowed && summary.stack_start() {
        (Placement::Start, true)
    } else if !live.enabled {
        (Placement::Disabled, false)
    } else if live.free {
        (Placement::Free, false)
    } else if live.zero_margins && forward && (if cross_x { live.start_x } else { live.start_y }) {
        (Placement::Start, false)
    } else {
        (Placement::General, false)
    }
}

}
