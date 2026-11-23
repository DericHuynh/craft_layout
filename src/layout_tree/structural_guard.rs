//! Bounds and validation used before editing the owned tree.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const KEY_LIMIT: usize = u32::MAX as usize;

// The upper bit shares the cold identity word with rectangle publication.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const RECT_PUBLISHED: u64 = 1 << 63;

/// Why a layout-tree operation could not be completed.
#[cfg_attr(not(verus_keep_ghost), non_exhaustive)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TreeError {
    /// The handle belongs to another tree.
    ForeignNode,
    /// The node was removed.
    StaleNode,
    /// A move would make a node an ancestor of itself.
    WouldCreateCycle,
    /// A node cannot be moved before itself.
    BeforeSelf,
    /// The node has no published rectangle, or is disabled.
    LayoutUnavailable,
    /// The requested capacity or another insertion cannot be reserved.
    Capacity,
}

/// A requested reservation must leave room for the arena sentinel and root.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.is_some() == (requested < KEY_LIMIT),
        out.is_some() ==> 1 <= out.unwrap() < KEY_LIMIT,
        out.is_some() ==> out.unwrap() == (if requested < 1 { 1usize } else { requested }),
    no_unwind
))]
pub(crate) fn root_capacity(requested: usize) -> Option<usize> {
    if requested >= KEY_LIMIT { None }
    else { Some(if requested == 0 { 1 } else { requested }) }
}

/// There is room for one more live key in addition to the arena sentinel.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns can_insert(live), no_unwind))]
pub(crate) fn can_insert(live: usize) -> bool {
    live < KEY_LIMIT - 1
}

/// An admitted insertion cannot overflow or reuse the publication bit.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.is_some() == (live + 1 < KEY_LIMIT && current < RECT_PUBLISHED),
        out.is_some() ==> out.unwrap() == current + 1 && out.unwrap() <= RECT_PUBLISHED,
        out.is_some() ==> current & RECT_PUBLISHED == 0,
    no_unwind
))]
pub(crate) fn next_incarnation(live: usize, current: u64) -> Option<u64> {
    if !can_insert(live) || current >= RECT_PUBLISHED { return None; }
    #[cfg(verus_keep_ghost)]
    proof! { assert(current & RECT_PUBLISHED == 0) by(bit_vector) requires current < RECT_PUBLISHED; }
    Some(current + 1)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns incarnation(word), no_unwind))]
pub(crate) fn incarnation(word: u64) -> u64 {
    word & !RECT_PUBLISHED
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures incarnation(out) == incarnation(word),
        (out & RECT_PUBLISHED != 0) == published,
    no_unwind
))]
pub(crate) fn publish_rect(word: u64, published: bool) -> u64 {
    let bits = if published { word | RECT_PUBLISHED } else { word & !RECT_PUBLISHED };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((bits & !RECT_PUBLISHED) == (word & !RECT_PUBLISHED)
            && ((bits & RECT_PUBLISHED) != 0) == published) by(bit_vector)
            requires bits == (if published { word | RECT_PUBLISHED } else { word & !RECT_PUBLISHED });
    }
    bits
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait ParentModel {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait ParentModel {
    type Id: Copy;
    spec fn links(&self) -> Map<Self::Id, Option<Self::Id>>;
}
}

/// Read one live parent link and reject the node being moved.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait MoveParents: ParentModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == if ancestor == moving {
            Err(TreeError::WouldCreateCycle)
        } else if self.links().contains_key(ancestor) {
            Ok(self.links()[ancestor])
        } else {
            Err(TreeError::StaleNode)
        },
        no_unwind
    ))]
    fn parent_for_move(&self, ancestor: Self::Id, moving: Self::Id) -> Result<Option<Self::Id>, TreeError>;
}

/// Verify that attaching under `parent` cannot create a cycle, without changing
/// any links. A malformed, nonterminating chain exhausts the live-node bound.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures complete_path(store.links(), path@, parent, live) ==>
        out == if path@.contains(moving) { Err(TreeError::WouldCreateCycle) } else { Ok(()) },
    no_unwind
))]
pub(crate) fn validate_ancestry<A: MoveParents>(
    store: &A, parent: A::Id, moving: A::Id, live: usize,
    #[cfg(verus_keep_ghost)] path: Ghost<Seq<A::Id>>,
) -> Result<(), TreeError> {
    let mut remaining = live;
    let mut ancestor = Some(parent);
    #[cfg(verus_keep_ghost)]
    let complete = path_is_complete(store, path, parent, live);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining <= live, complete@ == complete_path(store.links(), path@, parent, live),
            complete@ ==> live - remaining <= path@.len(),
            complete@ ==> ancestor == ancestor_at(path@, live - remaining),
            complete@ ==> (forall |j: int| 0 <= j < live - remaining ==> #[trigger] path@[j] != moving),
        ensures complete@ ==> live - remaining == path@.len(),
            complete@ ==> (forall |j: int| 0 <= j < live - remaining ==> #[trigger] path@[j] != moving),
        decreases remaining,
    ))]
    while let Some(current) = ancestor {
        if remaining == 0 {
            #[cfg(verus_keep_ghost)]
            proof! { assert(!complete@); }
            return Err(TreeError::WouldCreateCycle);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if complete@ {
                assert(store.links().contains_key(current));
                assert(store.links()[current] == ancestor_at(path@, live - remaining + 1));
            }
        }
        ancestor = match store.parent_for_move(current, moving) {
            Ok(parent) => parent,
            Err(err) => {
                #[cfg(verus_keep_ghost)]
                proof! { assert(complete@ ==> path@.contains(moving)); }
                return Err(err);
            }
        };
        remaining -= 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(complete@ ==> !path@.contains(moving)); }
    Ok(())
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn ancestor_at<I>(path: Seq<I>, i: int) -> Option<I> {
    if i < path.len() { Some(path[i]) } else { None }
}

pub(crate) open spec fn complete_path<I>(
    links: Map<I, Option<I>>, path: Seq<I>, parent: I, live: usize,
) -> bool {
    &&& 0 < path.len() <= live
    &&& path[0] == parent
    &&& forall |i: int| 0 <= i < path.len() ==> {
        let node = #[trigger] path[i];
        links.contains_key(node) && links[node] == ancestor_at(path, i + 1)
    }
}

fn path_is_complete<A: MoveParents>(
    store: &A, path: Ghost<Seq<A::Id>>, parent: A::Id, live: usize,
) -> (complete: Ghost<bool>)
    ensures complete@ == complete_path(store.links(), path@, parent, live),
    no_unwind
{
    Ghost(complete_path(store.links(), path@, parent, live))
}

}
