//! Preorder transition for full and partial subtree placement.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::work_stack::WorkStack;
use crate::vec_memory::VecMemory;
#[cfg(not(verus_keep_ghost))]
use crate::solve::UNSOLVED;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::UNSOLVED;

/// The projected traversal uses the same consume-before-publish order as the
/// native mode loops, so a child branch saves the actual following sibling.
#[cfg(verus_keep_ghost)]
macro_rules! place_siblings {
    ($(#[$attr:meta])* ; ($cursor:expr, $id:ident); { $($before:tt)* }; $following:expr; $disabled:expr; $place:block) => {
        walk_siblings!($(#[$attr])* ; ($cursor, $id); { $($before)* }; $following; $disabled; {
            if let Some(branch) = $place {
                return Some(branch);
            }
        });
    };
}
#[cfg(verus_keep_ghost)]
pub(crate) use place_siblings;

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn pending_in_visit_order<T>(items: Seq<T>) -> Seq<T>
    decreases items.len(),
{
    if items.len() == 0 {
        Seq::empty()
    } else {
        seq![items.last()] + pending_in_visit_order(items.drop_last())
    }
}

pub(crate) open spec fn frontier<T>(current: Option<T>, pending: Seq<T>) -> Seq<T> {
    match current {
        Some(cursor) => seq![cursor] + pending_in_visit_order(pending),
        None => pending_in_visit_order(pending),
    }
}

pub(crate) open spec fn next_frontier<T>(
    child: Option<T>, parent: T, more_siblings: bool, pending: Seq<T>,
) -> Seq<T> {
    match child {
        Some(branch) => seq![branch] + frontier(if more_siblings { Some(parent) } else { None }, pending),
        None => pending_in_visit_order(pending),
    }
}
}

/// A Wrap line reads the cross-axis base size and each declared, non-flex
/// bound. A slot with a provisional value can be read during a dependency cycle.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(ready => ensures
    ready == (forall |i: int| 0 <= i < 3 && needed[i] ==> states[i] != UNSOLVED),
    no_unwind
))]
pub(crate) fn wrap_reads_ready(needed: [bool; 3], states: [u32; 3]) -> bool {
    let [regular, min, max] = needed;
    let [regular_state, min_state, max_state] = states;
    (!regular || regular_state != UNSOLVED)
        && (!min || min_state != UNSOLVED)
        && (!max || max_state != UNSOLVED)
}

/// Enter a child branch, keeping the parent cursor only if siblings remain.
/// After a completed branch, resume the nearest unfinished ancestor.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(pending).valid(),
    ensures final(pending).valid(),
        old(pending).uses_inline_only() && (!(child.is_some() && more_siblings) || old(pending).can_push_inline())
            ==> final(pending).uses_inline_only(),
        frontier(result, final(pending).items()) == next_frontier(child, *parent, more_siblings, old(pending).items()),
        match child {
            Some(branch) => result == Some(branch)
                && final(pending).items() == (if more_siblings {
                    old(pending).items().push(*parent)
                } else { old(pending).items() }),
            None => if old(pending).items().len() > 0 {
                result == Some(old(pending).items().last())
                    && final(pending).items() == old(pending).items().drop_last()
            } else {
                result.is_none() && final(pending).items().len() == 0
            },
        },
    no_unwind
))]
pub(crate) fn next<T: Copy, const N: usize, M: VecMemory>(pending: &mut WorkStack<T, N>, child: Option<T>, parent: &T, more_siblings: bool) -> Option<T> {
    if let Some(branch) = child {
        if more_siblings {
            pending.push::<M>(*parent);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(pending.items().drop_last() =~= old(pending).items());
                assert(pending.items().last() == *parent);
            }
        }
        Some(branch)
    } else {
        pending.pop()
    }
}
