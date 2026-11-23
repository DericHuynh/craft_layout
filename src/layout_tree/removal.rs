// The removal walk uses the arena links as its continuation.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub trait ArenaModel {
        type Id: Copy;
        type Payload;
        spec fn records(&self) -> Store<Self::Id,Self::Payload>;
    }
}
#[cfg(not(verus_keep_ghost))]
pub(super) trait ArenaModel {
    type Id: Copy;
}

type RemovedLinks<I> = (Option<I>, Option<I>, Option<I>);

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) trait DetachedNodes: ArenaModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(r =>
        requires old(self).records().contains_key(id),
        ensures final(self).records() == old(self).records().remove(id),
            r == (old(self).records()[id].prev,old(self).records()[id].first,old(self).records()[id].last),
        no_unwind
    ))]
    fn remove_links(&mut self, id: Self::Id) -> RemovedLinks<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).records().contains_key(id),
        ensures final(self).records() == redirect(old(self).records(),id,after),
        no_unwind
    ))]
    fn set_previous(&mut self, id: Self::Id, after: Option<Self::Id>);
}

#[cfg(not(verus_keep_ghost))]
struct Removal<'a, T> {
    tree: &'a mut super::LayoutTree<T>,
    retired_contexts: Vec<T>,
}

#[cfg(not(verus_keep_ghost))]
pub(super) fn remove_owned_tree<T>(tree: &mut super::LayoutTree<T>, root: super::NodeKey) {
    // User destructors run after every node is gone. An unwind must never
    // leave accessible descendants attached to a removed parent's handle.
    let mut removal = Removal { tree, retired_contexts: Vec::new() };
    remove_detached(&mut removal, root);
}

#[cfg(not(verus_keep_ghost))]
impl<T> ArenaModel for Removal<'_, T> {
    type Id = super::NodeKey;
}

#[cfg(not(verus_keep_ghost))]
impl<T> DetachedNodes for Removal<'_, T> {
    #[inline]
    fn remove_links(&mut self, id: Self::Id) -> RemovedLinks<Self::Id> {
        let node = self.tree.nodes.remove(id).unwrap();
        if let Some(key) = node.context {
            self.retired_contexts.extend(self.tree.contexts.as_mut().unwrap().remove(key));
        }
        (node.prev_sibling, node.first_child, node.last_child)
    }

    #[inline]
    fn set_previous(&mut self, id: Self::Id, after: Option<Self::Id>) {
        self.tree.nodes[id].prev_sibling = after;
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    fn deletion_order<I>(root: I, children: Ghost<Forest<I>>) -> (plan: Ghost<Seq<I>>)
        ensures plan@ == order(detached(root,children@)),
    no_unwind
    {
        Ghost(order(detached(root,children@)))
    }

    fn snapshot<A: ArenaModel>(arena: &A, cursor: Option<A::Id>) -> (state: Ghost<State<A::Id,A::Payload>>)
        ensures state@ == (State{nodes:arena.records(),cursor}),
    no_unwind
    {
        Ghost(State{nodes:arena.records(),cursor})
    }

    fn advance<I>(plan: Ghost<Seq<I>>) -> (tail: Ghost<Seq<I>>)
        requires plan@.len() > 0,
        ensures tail@ == plan@.drop_first(),
        no_unwind
    {
        Ghost(plan@.drop_first())
    }
}

/// Splice the pending continuation into the first child's previous-sibling link.
/// Visiting from the last child recovers that continuation after its siblings.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires proper(detached(root,children@)), stores(old(arena).records(),detached(root,children@),None),
    ensures final(arena).records() == erase(old(arena).records(),ids(detached(root,children@))),
    no_unwind
))]
pub(super) fn remove_detached<A: DetachedNodes>(
    arena: &mut A,
    root: A::Id,
    #[cfg(verus_keep_ghost)] children: Ghost<Forest<A::Id>>,
) {
    let mut next = Some(root);
    #[cfg(verus_keep_ghost)]
    let mut remaining = deletion_order(root, children);
    #[cfg(verus_keep_ghost)]
    proof! { forest_replays(arena.records(),detached(root,children@),None); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant replay(State{nodes:arena.records(),cursor:next},remaining@) ==
            Some(State{nodes:erase(old(arena).records(),ids(detached(root,children@))),cursor:None}),
        ensures arena.records() == erase(old(arena).records(),ids(detached(root,children@))),
        decreases remaining@.len(),
    ))]
    while let Some(id) = next {
        #[cfg(verus_keep_ghost)]
        let prior = snapshot(arena, next);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(remaining@.len() > 0);
            assert(safe_pop(prior@,remaining@.first()));
            assert(id == remaining@.first());
        }
        let (after, first, last) = arena.remove_links(id);
        next = after;
        if let Some(first) = first {
            arena.set_previous(first, after);
            next = last;
        }
        #[cfg(verus_keep_ghost)]
        proof! { assert(State{nodes:arena.records(),cursor:next} == pop(prior@,id)); }
        #[cfg(verus_keep_ghost)]
        {
            remaining = advance(remaining);
        }
    }
}
