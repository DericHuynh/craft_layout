// Shared by the structural edit implementation and its Verus proofs.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum StructuralChange {
    #[default]
    Clean,
    Children,
    /// This node has a new parent. Its own style and intrinsic content are unchanged.
    Moved,
    Subtree,
    /// A clean, fixed-size region skipped during the current structural measurement.
    Retained,
}

impl StructuralChange {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.with_move()))]
    pub fn with_move(self) -> Self {
        match self {
            Self::Clean => Self::Moved,
            Self::Children => Self::Subtree,
            mark => mark,
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.with_children()))]
    pub fn with_children(self) -> Self {
        match self {
            Self::Clean => Self::Children,
            Self::Moved => Self::Subtree,
            mark => mark,
        }
    }
}

/// Decide which cached measurements may survive attachment to the live parent.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns parent_change(prior, current, reusable)))]
pub fn parent_change(prior: Option<usize>, current: Option<usize>, reusable: bool) -> StructuralChange {
    match prior {
        Some(old) if matches!(current, Some(new) if new == old) => StructuralChange::Clean,
        Some(_) if reusable => StructuralChange::Moved,
        _ => StructuralChange::Subtree,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Copy)]
pub struct TailDelta<I: Copy> {
    pub first_added: Option<I>,
    pub added: u32,
    pub removed: u32,
}

impl<I: Copy> Clone for TailDelta<I> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures
    r.first_added == None, r.added == 0, r.removed == 0))]
pub fn empty_delta<I: Copy>() -> TailDelta<I> {
    TailDelta { first_added: None, added: 0, removed: 0 }
}

impl<I: Copy> TailDelta<I> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures r == record_spec(self, id, inserting)))]
    pub fn record(self, id: I, inserting: bool) -> Option<Self> {
        if inserting {
            Some(Self {
                first_added: if self.first_added.is_none() { Some(id) } else { self.first_added },
                added: self.added.checked_add(1)?,
                ..self
            })
        } else if self.added > 0 {
            let added = self.added - 1;
            Some(Self { first_added: if added == 0 { None } else { self.first_added }, added, ..self })
        } else {
            Some(Self { removed: self.removed.checked_add(1)?, ..self })
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(r => ensures
        r.is_some() == (self.removed <= old && old as int - self.removed + self.added <= u32::MAX),
        r.is_some() ==> r.unwrap() as int == old as int - self.removed + self.added))]
    pub fn update_count(self, old: u32) -> Option<u32> {
        old.checked_sub(self.removed)?.checked_add(self.added)
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn record_spec<I: Copy>(before: TailDelta<I>, id: I, inserting: bool) -> Option<TailDelta<I>> {
        if inserting {
            if before.added == u32::MAX { None } else {
                Some(TailDelta {
                    first_added: if before.first_added.is_none() { Some(id) } else { before.first_added },
                    added: (before.added + 1) as u32, ..before
                })
            }
        } else if before.added > 0 {
            Some(TailDelta { first_added: if before.added == 1 { None } else { before.first_added },
                added: (before.added - 1) as u32, ..before })
        } else if before.removed < u32::MAX {
            Some(TailDelta { removed: (before.removed + 1) as u32, ..before })
        } else { None }
    }
}

/// A snapshot occupies [first, next). Zero remains the sentinel for fresh nodes.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r => ensures
    r.is_some() == (first as int + count <= u64::MAX),
    r.is_some() ==> r.unwrap() as int == first as int + count,
    no_unwind
))]
pub fn advance_tickets(first: u64, count: usize) -> Option<u64> {
    first.checked_add(count as u64)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(r =>
    ensures r == ticket_index_spec(first, count, ticket),
    no_unwind
))]
pub fn ticket_index(first: u64, count: usize, ticket: u64) -> Option<usize> {
    let offset = ticket.checked_sub(first)?;
    if offset < count as u64 { Some(offset as usize) } else { None }
}

#[cfg(verus_keep_ghost)]
verus! {
    pub open spec fn ticket_index_spec(first: u64, count: usize, ticket: u64) -> Option<usize> {
        if first <= ticket && ticket < first as int + count {
            Some((ticket - first) as usize)
        } else { None }
    }
}

/// Tracks the next direct child of an old preorder subtree during live reconciliation.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub struct ChildCursor {
    pub expected: usize,
    pub changed: bool,
}

impl ChildCursor {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.observe(old_identity, following)))]
    pub fn observe(self, old_identity: Option<usize>, following: Option<usize>) -> Self {
        match following {
            Some(expected) => Self {
                expected,
                changed: self.changed || !matches!(old_identity, Some(index) if index == self.expected),
            },
            None => Self { changed: true, ..self },
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.needs_invalidation(end)))]
    pub fn needs_invalidation(self, end: usize) -> bool {
        self.changed || self.expected != end
    }
}

/// A changed share can invalidate cross-axis measurements in a dependent leaf.
/// A bitwise positive-zero cached share survives a proven exhausted budget.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns tail_can_reuse(exhausted, old_share, independent)))]
pub fn tail_can_reuse(exhausted: bool, old_share: u32, independent: bool) -> bool {
    independent || (exhausted && old_share == 0)
}

/// Start alignment with unmodified output scale lets surviving siblings retain their rectangles.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns tail_replaces_prefix(old_share, new_share, scale_changed, start)))]
pub fn tail_replaces_prefix(old_share: u32, new_share: u32, scale_changed: bool, start: bool) -> bool {
    old_share != new_share || scale_changed || !start
}
