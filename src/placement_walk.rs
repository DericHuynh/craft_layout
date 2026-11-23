//! Preorder transition for full and partial subtree placement.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::work_stack::WorkStack;

/// Enter a child branch, keeping the parent cursor only if siblings remain.
/// After a completed branch, resume the nearest unfinished ancestor.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(pending).valid(),
    ensures final(pending).valid(),
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
))]
pub(crate) fn next<T: Copy, const N: usize>(pending: &mut WorkStack<T, N>, child: Option<T>, parent: &T, more_siblings: bool) -> Option<T> {
    if let Some(branch) = child {
        if more_siblings { pending.push(*parent); }
        Some(branch)
    } else {
        pending.pop()
    }
}
