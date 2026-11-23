// This module is included directly by the retained-view proof.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlacementWork {
    Clean,
    Descendants,
    Subtree,
}

impl PlacementWork {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.for_parent(children_changed, coupled)))]
    pub fn for_parent(self, children_changed: bool, coupled: bool) -> Self {
        if matches!(self, Self::Subtree) || children_changed && coupled {
            Self::Subtree
        } else {
            // Child traversal below recomputes whether any descendants need placement.
            Self::Clean
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.with_child(child, coupled_size_change)))]
    pub fn with_child(self, child: Self, coupled_size_change: bool) -> Self {
        if coupled_size_change {
            Self::Subtree
        } else if matches!(self, Self::Clean) && !matches!(child, Self::Clean) {
            Self::Descendants
        } else {
            self
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.visits(force)))]
    pub fn visits(self, force: bool) -> bool {
        force || !matches!(self, Self::Clean)
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.writes(force)))]
    pub fn writes(self, force: bool) -> bool {
        force || matches!(self, Self::Subtree)
    }
}

/// A partial pass can reuse the output host only when the environment and
/// topology baseline are the same ones used by the preceding pass.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns partial_placement(structural,needs_topology,same_window,scale_changed)))]
pub fn partial_placement(structural: bool, needs_topology: bool, same_window: bool, scale_changed: bool) -> bool {
    structural && !needs_topology && same_window && !scale_changed
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns update_scale_dirty(dirty,changed)))]
pub fn update_scale_dirty(dirty: bool, changed: bool) -> bool {
    dirty || changed
}

/// A free child never consumes a sibling's placement inputs. An in-flow
/// child can be repositioned by another child's sizing or flow contribution.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns coupled_child_changed(coupled,sizing_changed,free_child)))]
pub fn coupled_child_changed(coupled: bool, sizing_changed: bool, free_child: bool) -> bool {
    coupled && sizing_changed && !free_child
}
