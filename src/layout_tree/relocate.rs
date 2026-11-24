//! The owned relocation controller after both handles have been checked.
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(not(verus_keep_ghost))]
use super::{LinkStore, attach, detach};
#[cfg(verus_keep_ghost)]
use crate::{
    owned_guard::{HandleLookup, MoveParents, ParentModel, TreeError, incarnation, resolve_record, validate_ancestry},
    owned_records::Node,
};
#[cfg(not(verus_keep_ghost))]
use super::super::{
    records::Node,
    structural_guard::{HandleLookup, MoveParents, ParentModel, TreeError, resolve_record, validate_ancestry},
};

#[cfg(verus_keep_ghost)]
use crate::prepare_frame::Order;
#[cfg(verus_keep_ghost)]
use super::{
    ancestry::{ordered_path, parent_column},
    branch_move::{
        detach_preserves_ranks, detach_table,
        reattach::{admitted, joined_move_is_valid, moved_links, moved_order, preceding},
    },
    coherence::{child, coherent},
    preorder::{order, valid},
};

/// The owner check reads the tree identity before the arena is borrowed mutably.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(in super::super) struct Handle<I> {
    pub same_owner: bool,
    pub key: I,
    pub incarnation: u64,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(in super::super) enum MoveDestination<I> {
    LastChildOf(Handle<I>),
    Before(Handle<I>),
}

#[cfg(verus_keep_ghost)]
verus! {

pub(in crate::removal) open spec fn handle_status<A: HandleLookup>(arena: &A, handle: Handle<A::Key>)
    -> Result<(), TreeError>
{
    if !handle.same_owner { Err(TreeError::ForeignNode) }
    else if !arena.records().contains_key(handle.key)
        || incarnation(A::record_identity(&arena.records()[handle.key])) != handle.incarnation {
        Err(TreeError::StaleNode)
    } else { Ok(()) }
}

pub(in crate::removal) open spec fn child_status<A, I: Copy, C>(arena: &A, handle: Handle<I>)
    -> Result<I, TreeError>
    where A: HandleLookup<Key = I, Record = Node<I, C>>,
{
    match handle_status(arena, handle) {
        Err(error) => Err(error),
        Ok(()) => match arena.records()[handle.key].parent {
            Some(parent) if arena.records().contains_key(parent) => Ok(parent),
            _ => Err(TreeError::StaleNode),
        },
    }
}

pub(in crate::removal) open spec fn destination_status<A, I: Copy, C>(arena: &A, to: MoveDestination<I>)
    -> Result<(I, Option<I>), TreeError>
    where A: HandleLookup<Key = I, Record = Node<I, C>>,
{
    match to {
        MoveDestination::LastChildOf(parent) => match handle_status(arena, parent) {
            Ok(()) => Ok((parent.key, None)),
            Err(error) => Err(error),
        },
        MoveDestination::Before(node) => match child_status(arena, node) {
            Ok(parent) => Ok((parent, Some(node.key))),
            Err(error) => Err(error),
        },
    }
}

}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match child_status(arena, handle) {
        Ok(parent) => result.is_ok() && result.unwrap().0 == handle.key && result.unwrap().1 == parent
            && *result.unwrap().2 == arena.records()[handle.key],
        Err(error) => result == Err(error),
    },
    no_unwind
))]
pub(in super::super) fn resolve_child<A, I: Copy, C>(arena: &A, handle: Handle<I>)
    -> Result<(I, I, &Node<I, C>), TreeError>
    where A: HandleLookup<Key = I, Record = Node<I, C>>,
{
    let node = match resolve_record(arena, handle.same_owner, handle.key, handle.incarnation) {
        Ok(node) => node,
        Err(error) => return Err(error),
    };
    let Some(parent) = node.parent else { return Err(TreeError::StaleNode); };
    if arena.read_record(parent).is_none() { return Err(TreeError::StaleNode); }
    Ok((handle.key, parent, node))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == destination_status(arena, destination),
    no_unwind
))]
fn resolve_destination<A, I: Copy, C>(arena: &A, destination: MoveDestination<I>)
    -> Result<(I, Option<I>), TreeError>
    where A: HandleLookup<Key = I, Record = Node<I, C>>,
{
    match destination {
        MoveDestination::LastChildOf(parent) => match resolve_record(arena, parent.same_owner, parent.key, parent.incarnation) {
            Ok(_) => Ok((parent.key, None)),
            Err(error) => Err(error),
        },
        MoveDestination::Before(sibling) => match resolve_child(arena, sibling) {
            Ok((key, parent, _)) => Ok((parent, Some(key))),
            Err(error) => Err(error),
        },
    }
}

/// These notifications update layout data. The controller owns the link edits.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(in super::super) trait MoveEffects: LinkStore {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures LinkModel::links(final(self)) == LinkModel::links(old(self)),
        no_unwind
    ))]
    fn begin_move(&mut self);

    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (left == right), no_unwind))]
    fn same_link(&self, left: Option<Self::Id>, right: Option<Self::Id>) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures LinkModel::links(final(self)) == LinkModel::links(old(self)),
            result == if LinkModel::links(old(self)).contains_key(source) {
                Ok(())
            } else { Err(TreeError::StaleNode) },
        no_unwind
    ))]
    fn after_detach(&mut self, moved: Self::Id, source: Self::Id) -> Result<(), TreeError>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures LinkModel::links(final(self)) == LinkModel::links(old(self)),
        no_unwind
    ))]
    fn before_attach(&mut self, destination: Self::Id);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures LinkModel::links(final(self)) == LinkModel::links(old(self)),
        no_unwind
    ))]
    fn after_attach(&mut self, moved: Self::Id, destination: Self::Id);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures LinkModel::links(final(self)) == LinkModel::links(old(self)),
        no_unwind
    ))]
    fn finish_move(&mut self, moved: Self::Id, destination: Self::Id);
}

// Use the splice's checked physical records for ancestry as well.
#[cfg_attr(verus_keep_ghost, verus_verify)]
struct ParentProjection<'a, A: MoveEffects>(&'a A);

#[cfg(not(verus_keep_ghost))]
impl<A: MoveEffects> ParentModel for ParentProjection<'_, A> {
    type Id = A::Id;
}

#[cfg(verus_keep_ghost)]
verus! {
impl<A: MoveEffects> ParentModel for ParentProjection<'_, A> {
    type Id = A::Id;

    closed spec fn links(&self) -> Map<A::Id, Option<A::Id>> {
        parent_column(LinkModel::links(self.0))
    }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<A: MoveEffects> MoveParents for ParentProjection<'_, A> {
    #[inline]
    fn parent_for_move(&self, ancestor: A::Id, moving: A::Id) -> Result<Option<A::Id>, TreeError> {
        if self.0.same_link(Some(ancestor), Some(moving)) { return Err(TreeError::WouldCreateCycle); }
        match self.0.read_links(ancestor) {
            Some(record) => Ok(record.parent),
            None => Err(TreeError::StaleNode),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {

pub(in crate::removal) open spec fn resolved_move<I: Copy>(links: Map<I, Links<I>>, actual: Map<I, Links<I>>,
    before: Order<I>, source: I, moved: I, destination: I, sibling: Option<I>, result: Result<(), TreeError>,
) -> bool {
    if sibling == Some(moved) {
        &&& result == Err(TreeError::BeforeSelf)
        &&& actual == links
    } else if before.inside(moved, destination) {
        &&& result == Err(TreeError::WouldCreateCycle)
        &&& actual == links
    } else if source == destination && links[moved].next == sibling {
        &&& result == Ok(())
        &&& actual == links
    } else {
        &&& result == Ok(())
        &&& actual == moved_links(links, source, moved, destination, sibling)
        &&& coherent(actual) && valid(moved_order(links, before, source, moved, destination, sibling))
    }
}

proof fn outside_destination_admits_move<I>(links: Map<I, Links<I>>, before: Order<I>, moved: I,
    destination: I, sibling: Option<I>)
    requires
        before == order(links, before.interval, before.depth), valid(before),
        links.contains_key(moved), links.contains_key(destination), !before.inside(moved, destination),
        sibling.is_some() ==> child(links, destination, sibling.unwrap()) && sibling != Some(moved),
    ensures admitted(links, before, moved, destination, sibling),
{
    if let Some(next) = sibling {
        assert((before.live)(next) && (before.parent)(next) == Some(destination));
        if before.inside(moved, next) {
            assert(before.inside(moved, destination));
        }
    }
}

fn linked_snapshot<A: MoveEffects>(arena: &A) -> (snapshot: Ghost<Map<A::Id, Links<A::Id>>>)
    ensures snapshot@ == LinkModel::links(arena),
    no_unwind
{
    Ghost(LinkModel::links(arena))
}

}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        LinkModel::links(old(arena)).dom().len() <= live,
        before@ == order(LinkModel::links(old(arena)), before@.interval, before@.depth), valid(before@),
        coherent(LinkModel::links(old(arena))), child(LinkModel::links(old(arena)), source, moved),
        LinkModel::links(old(arena)).contains_key(destination),
        sibling.is_some() ==> child(LinkModel::links(old(arena)), destination, sibling.unwrap()),
    ensures resolved_move(LinkModel::links(old(arena)), LinkModel::links(final(arena)),
        before@, source, moved, destination, sibling, result),
    no_unwind
))]
pub(in super::super) fn move_resolved<A: MoveEffects>(
    arena: &mut A, source: A::Id, moved: A::Id, destination: A::Id, sibling: Option<A::Id>,
    live: usize, #[cfg(verus_keep_ghost)] before: Ghost<Order<A::Id>>,
) -> Result<(), TreeError> {
    #[cfg(verus_keep_ghost)]
    let prior = linked_snapshot(arena);
    if arena.same_link(sibling, Some(moved)) { return Err(TreeError::BeforeSelf); }
    let same_parent = arena.same_link(Some(source), Some(destination));
    if same_parent {
        // Reordering siblings leaves the existing parent chain unchanged.
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((before@.live)(source) && (before@.live)(moved));
            assert((before@.parent)(moved) == Some(source));
            assert(before@.child(source, moved));
            assert(!before@.inside(moved, destination));
        }
        let Some(current) = arena.read_links(moved) else {
            return Err(TreeError::StaleNode);
        };
        if arena.same_link(current.next, sibling) { return Ok(()); }
    } else {
        #[cfg(verus_keep_ghost)]
        let path = ordered_path(destination, moved, live, prior, before);
        if let Err(error) = validate_ancestry(&ParentProjection(arena), destination, moved, live, #[cfg(verus_keep_ghost)] path) {
            return Err(error);
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        outside_destination_admits_move(prior@, before@, moved, destination, sibling);
        detach_preserves_ranks(prior@, before@, source, moved);
    }
    arena.begin_move();
    if !detach(arena, moved, source) { return Err(TreeError::StaleNode); }
    if let Err(error) = arena.after_detach(moved, source) { return Err(error); }
    #[cfg(verus_keep_ghost)]
    proof! { joined_move_is_valid(prior@, before@, source, moved, destination, sibling); }
    // The surviving links identify the destination gap after detachment.
    let target = sibling.unwrap_or(destination);
    let Some(position) = arena.read_links(target) else { return Err(TreeError::StaleNode); };
    let previous = if sibling.is_some() { position.previous } else { position.last };
    #[cfg(verus_keep_ghost)]
    proof! { assert(previous == preceding(detach_table(prior@, source, moved), destination, sibling)); }
    arena.before_attach(destination);
    attach(arena, moved, destination, previous, sibling);
    arena.after_attach(moved, destination);
    if !same_parent {
        // A reorder preserves the subtree's own size dependencies and pending edits.
        arena.finish_move(moved, destination);
    }
    Ok(())
}

/// Check both handles and apply the owned edit to their current physical links.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        LinkModel::links(old(arena)) == projected_links(old(arena).records()),
        LinkModel::links(old(arena)).dom().len() <= live,
        before@ == order(LinkModel::links(old(arena)), before@.interval, before@.depth),
        valid(before@), coherent(LinkModel::links(old(arena))),
    ensures ({
        let prior = LinkModel::links(old(arena));
        let actual = LinkModel::links(final(arena));
        match child_status(old(arena), moved) {
            Err(error) => result == Err(error) && actual == prior,
            Ok(source) => match destination_status(old(arena), to) {
                Err(error) => result == Err(error) && actual == prior,
                Ok((destination, sibling)) => resolved_move(prior, actual, before@, source, moved.key, destination, sibling, result),
            },
        }
    }),
    no_unwind
))]
pub(in super::super) fn move_handles<A, I: Copy, C>(
    arena: &mut A, moved: Handle<I>, to: MoveDestination<I>, live: usize,
    #[cfg(verus_keep_ghost)] before: Ghost<Order<I>>,
) -> Result<(), TreeError>
    where A: MoveEffects<Id = I> + HandleLookup<Key = I, Record = Node<I, C>>,
{
    let (node, source, _) = match resolve_child(arena, moved) {
        Ok(child) => child,
        Err(error) => return Err(error),
    };
    let (destination, sibling) = match resolve_destination(arena, to) {
        Ok(position) => position,
        Err(error) => return Err(error),
    };
    move_resolved(arena, source, node, destination, sibling, live, #[cfg(verus_keep_ghost)] before)
}
