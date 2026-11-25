//! Update pending edit buffers without losing the fallback that covers them.
#![allow(unexpected_cfgs)]

use crate::vec_memory::{FallibleVecMemory, try_append};
#[cfg(verus_keep_ghost)]
use crate::{dependencies::registration as rules, publication::IncrementalRelayoutOutcome};
#[cfg(not(verus_keep_ghost))]
use super::{registration_rules as rules, IncrementalRelayoutOutcome};
use IncrementalRelayoutOutcome::{FallbackFlow, FallbackTooMuchWork};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns tracks_structure(pending), no_unwind))]
pub(crate) fn tracks_structure(pending: Option<IncrementalRelayoutOutcome>) -> bool {
    matches!(pending, None | Some(FallbackFlow | FallbackTooMuchWork))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(changed =>
    ensures changed == tracks_structure(*old(pending)),
        *final(pending) == if changed { None } else { *old(pending) },
        *final(children) == (*old(children) || changed),
        !*final(replay),
    no_unwind
))]
pub(crate) fn start_children_change(
    pending: &mut Option<IncrementalRelayoutOutcome>, children: &mut bool, replay: &mut bool,
) -> bool {
    *replay = false;
    if !tracks_structure(*pending) { return false; }
    // Regional measurement includes earlier sizing marks, regardless of edit order.
    *pending = None;
    *children = true;
    true
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(pending) == if tracks_structure(*old(pending)) { Some(reason) } else { *old(pending) },
        !*final(replay),
    no_unwind
))]
pub(crate) fn request_full_solve(
    pending: &mut Option<IncrementalRelayoutOutcome>, replay: &mut bool, reason: IncrementalRelayoutOutcome,
) {
    *replay = false;
    if tracks_structure(*pending) { *pending = Some(reason); }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Limits {
    pub structural: bool,
    pub cycle: bool,
    pub flow: bool,
    pub population: u32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum Edit<I, C> {
    Declaration(I, C),
    Content(I),
}

/// Keep live marks in the caller even if a full or regional solve covers the
/// edit. The numeric buffers only grow on the numeric route.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(added =>
    ensures
        *final(replay) == ((*final(pending) == Some(FallbackFlow) || *final(pending) == Some(FallbackTooMuchWork))
            && (old(pending).is_none() || *old(pending) == *final(pending) && *old(replay))),
        added ==> old(pending).is_none() && !limits.structural && !limits.cycle && !limits.flow
            && old(declarations).len() + old(content).len() < limits.population / 2
            && *final(pending) == *old(pending),
        match edit {
            Edit::Declaration(node, change) =>
                final(content)@ == old(content)@
                && final(declarations)@ == (if added { old(declarations)@.push((node, change)) } else { old(declarations)@ }),
            Edit::Content(node) =>
                final(declarations)@ == old(declarations)@
                && final(content)@ == (if added { old(content)@.push(node) } else { old(content)@ }),
        },
        ({
            let at_limit = old(declarations).len() + old(content).len() >= limits.population / 2;
            let route = rules::intake(old(pending).is_some(), limits.cycle, limits.structural, limits.flow, at_limit);
            *final(pending) == match route {
                rules::Intake::Flow => Some(FallbackFlow),
                rules::Intake::Budget => Some(FallbackTooMuchWork),
                rules::Intake::Queue if !added => Some(FallbackTooMuchWork),
                _ => *old(pending),
            }
        }),
    no_unwind
))]
pub(crate) fn submit<I: Copy, C: Copy, M: FallibleVecMemory>(
    pending: &mut Option<IncrementalRelayoutOutcome>, replay: &mut bool, declarations: &mut Vec<(I, C)>,
    content: &mut Vec<I>, limits: Limits, edit: Edit<I, C>,
) -> bool {
    let already_pending = pending.is_some();
    let at_limit = rules::change_budget_exhausted(declarations.len(), content.len(), (limits.population / 2) as usize);
    let added = match rules::intake(already_pending, limits.cycle, limits.structural, limits.flow, at_limit) {
        rules::Intake::Pending | rules::Intake::Cycle | rules::Intake::Region => false,
        rules::Intake::Flow => {
            *pending = Some(FallbackFlow);
            false
        }
        rules::Intake::Budget => {
            *pending = Some(FallbackTooMuchWork);
            false
        }
        rules::Intake::Queue => {
            let added = match edit {
                Edit::Declaration(node, change) => try_append::<_, M>(declarations, (node, change)),
                Edit::Content(node) => try_append::<_, M>(content, node),
            };
            if !added { *pending = Some(FallbackTooMuchWork); }
            added
        }
    };
    // Only retry fallbacks raised here, while all dirty marks are still live.
    *replay = matches!(*pending, Some(FallbackFlow | FallbackTooMuchWork)) && (!already_pending || *replay);
    added
}
