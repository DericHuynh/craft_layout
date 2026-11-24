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
        ensures final(self).records() == old(self).records().remove(id),
            r == if old(self).records().contains_key(id) {
                Some((old(self).records()[id].prev, old(self).records()[id].first, old(self).records()[id].last))
            } else { None },
        no_unwind
    ))]
    fn remove_links(&mut self, id: Self::Id) -> Option<RemovedLinks<Self::Id>>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).records() == if old(self).records().contains_key(id) {
            redirect(old(self).records(), id, after)
        } else { old(self).records() },
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
pub(super) fn remove_owned_tree<T>(tree: &mut super::LayoutTree<T>, root: super::NodeKey) -> Result<(), super::TreeError> {
    // User destructors run after every node is gone. An unwind must never
    // leave accessible descendants attached to a removed parent's handle.
    let mut removal = Removal { tree, retired_contexts: Vec::new() };
    if remove_detached(&mut removal, root) { Ok(()) } else { Err(super::TreeError::StaleNode) }
}

#[cfg(not(verus_keep_ghost))]
impl<T> ArenaModel for Removal<'_, T> {
    type Id = super::NodeKey;
}

#[cfg(not(verus_keep_ghost))]
impl<T> DetachedNodes for Removal<'_, T> {
    #[inline]
    fn remove_links(&mut self, id: Self::Id) -> Option<RemovedLinks<Self::Id>> {
        let node = self.tree.nodes.remove(id)?;
        if let Some(context) = node.context.and_then(|key| self.tree.contexts.as_mut()?.remove(key)) {
            // Each retired value came from a larger slot in the same arena.
            // If amortized growth overreaches, try the representable exact size.
            if self.retired_contexts.try_reserve(1).is_err() {
                self.retired_contexts.reserve_exact(1);
            }
            self.retired_contexts.push(context);
        }
        Some((node.prev_sibling, node.first_child, node.last_child))
    }

    #[inline]
    fn set_previous(&mut self, id: Self::Id, after: Option<Self::Id>) {
        if let Some(node) = self.tree.nodes.get_mut(id) {
            node.prev_sibling = after;
        }
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
        ensures plan@.len() > 0 ==> tail@ == plan@.drop_first(),
        no_unwind
    {
        Ghost(if plan@.len() > 0 { plan@.drop_first() } else { plan@ })
    }

    fn detached_matches<A: ArenaModel>(arena: &A, root: A::Id, children: Ghost<Forest<A::Id>>) -> (ok: Ghost<bool>)
        ensures ok@ == valid_detachment(arena.records(), root, children@),
        no_unwind
    {
        Ghost(valid_detachment(arena.records(), root, children@))
    }
}

/// Splice the pending continuation into the first child's previous-sibling link.
/// Visiting from the last child recovers that continuation after its siblings.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(complete =>
    ensures valid_detachment(old(arena).records(), root, children@) ==>
        complete && final(arena).records() == erase(old(arena).records(),ids(detached(root,children@))),
    no_unwind
))]
pub(super) fn remove_detached<A: DetachedNodes>(
    arena: &mut A,
    root: A::Id,
    #[cfg(verus_keep_ghost)] children: Ghost<Forest<A::Id>>,
) -> bool {
    let mut next = Some(root);
    #[cfg(verus_keep_ghost)]
    let certified = detached_matches(arena, root, children);
    #[cfg(verus_keep_ghost)]
    let mut remaining = deletion_order(root, children);
    #[cfg(verus_keep_ghost)]
    proof! {
        if certified@ { forest_replays(arena.records(), detached(root, children@), None); }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant certified@ == valid_detachment(old(arena).records(), root, children@),
            certified@ ==> replay(State{nodes:arena.records(),cursor:next},remaining@) ==
                Some(State{nodes:erase(old(arena).records(),ids(detached(root,children@))),cursor:None}),
        ensures certified@ ==> arena.records() == erase(old(arena).records(),ids(detached(root,children@))),
        decreases arena.records().dom().len(),
    ))]
    while let Some(id) = next {
        #[cfg(verus_keep_ghost)]
        let prior = snapshot(arena, next);
        #[cfg(verus_keep_ghost)]
        proof! {
            if certified@ {
                assert(remaining@.len() > 0);
                assert(safe_pop(prior@, remaining@.first()));
                assert(id == remaining@.first());
            }
        }
        let Some((after, first, last)) = arena.remove_links(id) else { return false; };
        next = after;
        if let Some(first) = first {
            arena.set_previous(first, after);
            next = last;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(prior@.nodes.contains_key(id));
            assert(arena.records().dom() =~= prior@.nodes.dom().remove(id));
            vstd::set::lemma_set_remove_len(prior@.nodes.dom(), id);
            if certified@ { assert(State{nodes:arena.records(),cursor:next} == pop(prior@,id)); }
        }
        #[cfg(verus_keep_ghost)]
        {
            remaining = advance(remaining);
        }
    }
    true
}
