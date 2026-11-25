//! Link updates for the owned arena. The SlotMap adapter supplies live records.
#![allow(unexpected_cfgs)]

use crate::node_data::NodeLayoutData;
#[cfg(not(verus_keep_ghost))]
use super::records::Node;
#[cfg(verus_keep_ghost)]
use crate::owned_records::Node;
use crate::node_flags::NodeFlags;
#[cfg(verus_keep_ghost)]
use crate::owned_guard::{RECT_PUBLISHED, incarnation, publish_rect};
#[cfg(verus_keep_ghost)]
use crate::structural_changes::StructuralChange;
#[cfg(not(verus_keep_ghost))]
use super::structural_guard::publish_rect;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) struct Links<I> {
    pub parent: Option<I>,
    pub previous: Option<I>,
    pub next: Option<I>,
    pub first: Option<I>,
    pub last: Option<I>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) enum Edit<I> {
    Position(Option<I>, Option<I>, Option<I>),
    Previous(Option<I>),
    Next(Option<I>),
    First(Option<I>),
    Last(Option<I>),
}

impl<I: Copy> Edit<I> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.update(links), no_unwind))]
    pub(super) fn update(self, links: Links<I>) -> Links<I> {
        match self {
            Self::Position(parent, previous, next) => Links { parent, previous, next, ..links },
            Self::Previous(previous) => Links { previous, ..links },
            Self::Next(next) => Links { next, ..links },
            Self::First(first) => Links { first, ..links },
            Self::Last(last) => Links { last, ..links },
        }
    }
}

#[cfg(not(verus_keep_ghost))]
pub(super) trait LinkModel {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(super) trait LinkModel {
        type Id: Copy;
        spec fn links(&self) -> Map<Self::Id, Links<Self::Id>>;
    }

    pub(super) open spec fn read<I>(links: Map<I, Links<I>>, node: I) -> Option<Links<I>> {
        if links.contains_key(node) { Some(links[node]) } else { None }
    }

    pub(super) open spec fn edited<I: Copy>(links: Map<I, Links<I>>, node: I, edit: Edit<I>) -> Map<I, Links<I>> {
        if links.contains_key(node) { links.insert(node, edit.update(links[node])) } else { links }
    }

    pub(super) open spec fn set_gap<I: Copy>(links: Map<I, Links<I>>, parent: I,
        previous: Option<I>, next: Option<I>, node: Option<I>,
    ) -> Map<I, Links<I>> {
        let after = match previous {
            Some(previous) => edited(links, previous, Edit::Next(if node.is_some() { node } else { next })),
            None => edited(links, parent, Edit::First(if node.is_some() { node } else { next })),
        };
        match next {
            Some(next) => edited(after, next, Edit::Previous(if node.is_some() { node } else { previous })),
            None => edited(after, parent, Edit::Last(if node.is_some() { node } else { previous })),
        }
    }

    pub(super) proof fn edit_keeps_keys<I: Copy>(links: Map<I, Links<I>>, node: I, edit: Edit<I>)
        ensures edited(links, node, edit).dom() == links.dom(),
    {
        assert(edited(links, node, edit).dom() =~= links.dom());
    }

    pub(super) proof fn set_gap_keeps_keys<I: Copy>(links: Map<I, Links<I>>, parent: I,
        previous: Option<I>, next: Option<I>, node: Option<I>,
    )
        ensures set_gap(links, parent, previous, next, node).dom() == links.dom(),
    {
        let following = if node.is_some() { node } else { next };
        let after = match previous {
            Some(previous) => {
                edit_keeps_keys(links, previous, Edit::Next(following));
                edited(links, previous, Edit::Next(following))
            },
            None => {
                edit_keeps_keys(links, parent, Edit::First(following));
                edited(links, parent, Edit::First(following))
            },
        };
        let preceding = if node.is_some() { node } else { previous };
        match next {
            Some(next) => edit_keeps_keys(after, next, Edit::Previous(preceding)),
            None => edit_keeps_keys(after, parent, Edit::Last(preceding)),
        }
    }

    pub(super) open spec fn gap_between<I>(links: Map<I, Links<I>>, parent: I, node: I,
        previous: Option<I>, next: Option<I>,
    ) -> bool {
        &&& links.contains_key(parent) && links.contains_key(node) && parent != node
        &&& match previous {
            Some(previous) => previous != parent && previous != node && Some(previous) != next
                && links.contains_key(previous) && links[previous].next == next,
            None => links[parent].first == next,
        }
        &&& match next {
            Some(next) => next != parent && next != node
                && links.contains_key(next) && links[next].previous == previous,
            None => links[parent].last == previous,
        }
    }

    /// The splice and its inverse write reciprocal links, preserve the live
    /// key set, and leave the moved node's own children in place.
    pub(super) proof fn splice_round_trip<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I,
        previous: Option<I>, next: Option<I>,
    )
        requires gap_between(links, parent, node, previous, next),
            links[node].parent.is_none(), links[node].previous.is_none(), links[node].next.is_none(),
        ensures ({
            let joined = set_gap(edited(links, node, Edit::Position(Some(parent), previous, next)),
                parent, previous, next, Some(node));
            &&& joined.dom() == links.dom()
            &&& joined[node] == (Links { parent: Some(parent), previous, next, ..links[node] })
            &&& match previous {
                Some(previous) => joined[previous].next == Some(node),
                None => joined[parent].first == Some(node),
            }
            &&& match next {
                Some(next) => joined[next].previous == Some(node),
                None => joined[parent].last == Some(node),
            }
            &&& set_gap(edited(joined, node, Edit::Position(None, None, None)), parent, previous, next, None) == links
        }),
    {
        let joined = set_gap(edited(links, node, Edit::Position(Some(parent), previous, next)),
            parent, previous, next, Some(node));
        let undone = set_gap(edited(joined, node, Edit::Position(None, None, None)), parent, previous, next, None);
        assert(joined.dom() =~= links.dom());
        match (previous, next) {
            (None, None) => { assert(undone =~= links); }
            (Some(_), None) => { assert(undone =~= links); }
            (None, Some(_)) => { assert(undone =~= links); }
            (Some(_), Some(_)) => { assert(undone =~= links); }
        }
    }

    pub(super) open spec fn ranked_parents<I>(links: Map<I, Links<I>>, depth: spec_fn(I) -> nat) -> bool {
        forall |id: I| #[trigger] links.contains_key(id) ==> match links[id].parent {
            Some(parent) => links.contains_key(parent) && depth(parent) < depth(id),
            None => true,
        }
    }

    pub(super) open spec fn in_branch<I>(links: Map<I, Links<I>>, depth: spec_fn(I) -> nat, root: I, id: I) -> bool
        decreases depth(id),
    {
        id == root || links.contains_key(id) && match links[id].parent {
            Some(parent) => depth(parent) < depth(id) && in_branch(links, depth, root, parent),
            None => false,
        }
    }

    proof fn reaches_no_shallower<I>(links: Map<I, Links<I>>, depth: spec_fn(I) -> nat, root: I, id: I)
        requires in_branch(links, depth, root, id),
        ensures depth(root) <= depth(id),
        decreases depth(id),
    {
        if id != root {
            reaches_no_shallower(links, depth, root, links[id].parent.unwrap());
        }
    }

    pub(super) open spec fn moved_depth<I>(links: Map<I, Links<I>>, depth: spec_fn(I) -> nat,
        moving: I, destination: I, id: I,
    ) -> nat {
        if in_branch(links, depth, moving, id) {
            depth(destination) + 1 + (depth(id) - depth(moving)) as nat
        } else { depth(id) }
    }

    /// Detaching and attaching changes just one parent edge. The destination
    /// check allows the old depths to be shifted uniformly inside the branch.
    pub(super) proof fn reparent_keeps_finite_ancestry<I>(
        before: Map<I, Links<I>>, after: Map<I, Links<I>>, depth: spec_fn(I) -> nat,
        moving: I, destination: I,
    )
        requires ranked_parents(before, depth), before.contains_key(moving), before.contains_key(destination),
            !in_branch(before, depth, moving, destination), before.dom() == after.dom(),
            forall |id: I| after.contains_key(id) ==> (#[trigger] after[id]).parent ==
                if id == moving { Some(destination) } else { before[id].parent },
        ensures ranked_parents(after, |id: I| moved_depth(before, depth, moving, destination, id)),
    {
        let shifted = |id: I| moved_depth(before, depth, moving, destination, id);
        assert forall |id: I| #[trigger] after.contains_key(id) implies match after[id].parent {
            Some(parent) => after.contains_key(parent) && shifted(parent) < shifted(id),
            None => true,
        } by {
            if let Some(parent) = after[id].parent {
                if id == moving {
                    assert(parent == destination);
                } else {
                    assert(before.contains_key(id));
                    assert(before[id].parent == Some(parent));
                    assert(before.contains_key(parent) && depth(parent) < depth(id));
                    assert(in_branch(before, depth, moving, id) == in_branch(before, depth, moving, parent));
                    if in_branch(before, depth, moving, id) {
                        reaches_no_shallower(before, depth, moving, parent);
                    }
                }
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(super) open spec fn record_links<I,C>(node: &Node<I,C>) -> Links<I> {
    Links {
        parent: node.parent, previous: node.prev_sibling, next: node.next_sibling,
        first: node.first_child, last: node.last_child,
    }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == record_links(node), no_unwind))]
pub(super) fn project<I: Copy, C>(node: &Node<I,C>) -> Links<I> {
    Links {
        parent: node.parent, previous: node.prev_sibling, next: node.next_sibling,
        first: node.first_child, last: node.last_child,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures ({
        let changed = edit.update(record_links(old(node)));
        &&& record_links(final(node)) == changed
        &&& *final(node) == (Node {
            parent: changed.parent, prev_sibling: changed.previous, next_sibling: changed.next,
            first_child: changed.first, last_child: changed.last, ..*old(node)
        })
    }),
    no_unwind
))]
pub(super) fn apply<I: Copy, C>(node: &mut Node<I,C>, edit: Edit<I>) {
    let updated = edit.update(project(node));
    node.parent = updated.parent;
    node.prev_sibling = updated.previous;
    node.next_sibling = updated.next;
    node.first_child = updated.first;
    node.last_child = updated.last;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) trait LinkStore: LinkModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == read(self.links(), node),
        no_unwind
    ))]
    fn read_links(&self, node: Self::Id) -> Option<Links<Self::Id>>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).links() == edited(old(self).links(), node, edit),
        no_unwind
    ))]
    fn edit_links(&mut self, node: Self::Id, edit: Edit<Self::Id>);
}

/// Set the two ends of the gap in the parent's child list.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(store).links() == set_gap(old(store).links(), parent, previous, next, node),
    no_unwind
))]
fn set_siblings<A: LinkStore>(store: &mut A, parent: A::Id, previous: Option<A::Id>, next: Option<A::Id>, node: Option<A::Id>) {
    let following = if node.is_some() { node } else { next };
    match previous {
        Some(previous) => store.edit_links(previous, Edit::Next(following)),
        None => store.edit_links(parent, Edit::First(following)),
    }
    let preceding = if node.is_some() { node } else { previous };
    match next {
        Some(next) => store.edit_links(next, Edit::Previous(preceding)),
        None => store.edit_links(parent, Edit::Last(preceding)),
    }
}

/// Insert the node between its two new siblings.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(store).links() == set_gap(
        edited(old(store).links(), node, Edit::Position(Some(parent), previous, next)),
        parent, previous, next, Some(node)),
        final(store).links().dom() == old(store).links().dom(),
        coherence::coherent(old(store).links())
            && coherence::valid_gap(old(store).links(), parent, node, previous, next)
            ==> coherence::coherent(final(store).links()),
    no_unwind
))]
pub(super) fn attach<A: LinkStore>(store: &mut A, node: A::Id, parent: A::Id, previous: Option<A::Id>, next: Option<A::Id>) {
    let edit = Edit::Position(Some(parent), previous, next);
    #[cfg(verus_keep_ghost)]
    proof! {
        edit_keeps_keys(old(store).links(), node, edit);
        set_gap_keeps_keys(edited(old(store).links(), node, edit), parent, previous, next, Some(node));
        let before = old(store).links();
        if coherence::coherent(before) && coherence::valid_gap(before, parent, node, previous, next) {
            coherence::attach_keeps_coherent(before, parent, node, previous, next);
        }
    }
    store.edit_links(node, edit);
    set_siblings(store, parent, previous, next, Some(node));
}

/// Remove the node from its parent's child list and clear its position links.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(found =>
    ensures found == old(store).links().contains_key(node),
        final(store).links() == if found {
            let live = old(store).links()[node];
            set_gap(edited(old(store).links(), node, Edit::Position(None, None, None)),
                parent, live.previous, live.next, None)
        } else { old(store).links() },
        final(store).links().dom() == old(store).links().dom(),
        found && parent != node && old(store).links()[node].previous != Some(node)
            && old(store).links()[node].next != Some(node) ==> final(store).links()[node] ==
                (Links { parent: None, previous: None, next: None, ..old(store).links()[node] }),
        coherence::coherent(old(store).links())
            && (!found || (coherence::child(old(store).links(), parent, node) &&
                coherence::distinct_gap(parent, node, old(store).links()[node].previous, old(store).links()[node].next)))
            ==> coherence::coherent(final(store).links()),
    no_unwind
))]
pub(super) fn detach<A: LinkStore>(store: &mut A, node: A::Id, parent: A::Id) -> bool {
    let Some(live) = store.read_links(node) else { return false; };
    let edit = Edit::Position(None, None, None);
    #[cfg(verus_keep_ghost)]
    proof! {
        edit_keeps_keys(old(store).links(), node, edit);
        set_gap_keeps_keys(edited(old(store).links(), node, edit), parent, live.previous, live.next, None);
        let before = old(store).links();
        if coherence::coherent(before) && coherence::child(before, parent, node)
            && coherence::distinct_gap(parent, node, live.previous, live.next) {
            coherence::detach_keeps_coherent(before, parent, node);
        }
        if parent != node && live.previous != Some(node) && live.next != Some(node) {
            let cleared = edited(old(store).links(), node, edit);
            match (live.previous, live.next) {
                (None, None) => { assert(set_gap(cleared, parent, None, None, None)[node] == cleared[node]); }
                (Some(prev), None) => { assert(set_gap(cleared, parent, Some(prev), None, None)[node] == cleared[node]); }
                (None, Some(next)) => { assert(set_gap(cleared, parent, None, Some(next), None)[node] == cleared[node]); }
                (Some(prev), Some(next)) => { assert(set_gap(cleared, parent, Some(prev), Some(next), None)[node] == cleared[node]); }
            }
        }
    }
    store.edit_links(node, edit);
    set_siblings(store, parent, live.previous, live.next, None);
    true
}

/// Apply inherited visibility to one record without changing its incarnation.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(flag) == disabled,
        *final(identity) == (if disabled { *old(identity) & !RECT_PUBLISHED } else { *old(identity) }),
        incarnation(*final(identity)) == incarnation(*old(identity)),
        final(record).has_dormant_grid() == (is_root && old(record).has_dormant_grid()),
        final(record).fixed_leaf_summary.is_empty(),
        final(record).values == old(record).values,
        final(record).levels == old(record).levels,
        final(record).parent_flow == old(record).parent_flow,
        !is_root && *old(flag) && !disabled && !old(record).hidden_epoch_matches(epoch)
            ==> final(record).flags == NodeFlags::EMPTY && final(record).structural_change == StructuralChange::Subtree,
        disabled && !*old(flag) && (!is_root || !old(record).has_dormant_grid())
            ==> final(record).topology_index() == epoch as u64,
    no_unwind
))]
pub(super) fn apply_visibility(
    flag: &mut bool, identity: &mut u64, record: &mut NodeLayoutData, is_root: bool, disabled: bool, epoch: u32,
) {
    let was_disabled = *flag;
    let stale = !is_root && was_disabled && !disabled && !record.hidden_epoch_matches(epoch);
    if !is_root { record.clear_dormant_grid(); }
    *flag = disabled;
    record.forget_fixed_pixels();
    if stale {
        // Full sizing may have skipped this hidden descendant. Clearing its
        // readiness also prevents a later move from retaining its old sizes.
        record.flags = NodeFlags::EMPTY;
        record.mark_subtree_changed();
    }
    if disabled {
        if !was_disabled && !record.has_dormant_grid() { record.set_topology_index(epoch as u64); }
        *identity = publish_rect(*identity, false);
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(super) struct Visibility {
    pub disabled: bool,
    pub identity: u64,
    pub dormant: bool,
}

pub(super) trait VisibilityModel: LinkModel {
    spec fn visibility(&self) -> Map<Self::Id, Visibility>;
    spec fn reverse_next(links: Map<Self::Id, Links<Self::Id>>, root: Self::Id, node: Self::Id) -> Option<Self::Id>;
}

pub(super) open spec fn visibility_value(before: Visibility, root: bool, disabled: bool) -> Visibility {
    Visibility {
        disabled,
        identity: if disabled { before.identity & !RECT_PUBLISHED } else { before.identity },
        dormant: root && before.dormant,
    }
}

pub(super) open spec fn visible_at<I>(path: Seq<I>, index: int) -> Option<I> {
    if 0 <= index < path.len() { Some(path[index]) } else { None }
}

pub(super) open spec fn visibility_path<A: VisibilityModel>(
    store: &A, root: A::Id, path: Seq<A::Id>, capacity: usize,
) -> bool {
    &&& visible_at(path, 0) == Some(root)
    &&& path.len() <= capacity
    &&& path.no_duplicates()
    &&& forall |i: int| 0 <= i < path.len() ==> {
        let id = #[trigger] path[i];
        &&& store.visibility().contains_key(id)
        &&& A::reverse_next(store.links(), root, id) == visible_at(path, i + 1)
    }
}

pub(super) closed spec fn visibility_prefix<I>(
    before: Map<I, Visibility>, root: I, path: Seq<I>, count: int, disabled: bool,
) -> Map<I, Visibility> {
    Map::new(before.dom(), |id: I|
        if path.take(count).contains(id) { visibility_value(before[id], id == root, disabled) }
        else { before[id] })
}

proof fn first_visibility<I>(before: Map<I, Visibility>, root: I, path: Seq<I>, disabled: bool)
    ensures visibility_prefix(before, root, path, 0, disabled) == before,
{
    assert(visibility_prefix(before, root, path, 0, disabled) =~= before);
}

proof fn extend_visibility<I>(
    before: Map<I, Visibility>, root: I, path: Seq<I>, at: int, disabled: bool,
)
    requires 0 <= at < path.len(), path.no_duplicates(), before.contains_key(path[at]),
    ensures ({
        let id = path[at];
        let prior = visibility_prefix(before, root, path, at, disabled);
        let after = visibility_prefix(before, root, path, at + 1, disabled);
        &&& prior.contains_key(id)
        &&& after == prior.insert(id, visibility_value(prior[id], id == root, disabled))
    }),
{
    let id = path[at];
    let visited = path.take(at);
    let extended = path.take(at + 1);
    assert(extended =~= visited.push(id));
    assert(!visited.contains(id)) by {
        if visited.contains(id) {
            let i = choose|i: int| 0 <= i < visited.len() && visited[i] == id;
            assert(path[i] == visited[i]);
            assert(path[i] != path[at]);
        }
    }
    let prior = visibility_prefix(before, root, path, at, disabled);
    let after = visibility_prefix(before, root, path, at + 1, disabled);
    assert(prior.contains_key(id));
    let updated = prior.insert(id, visibility_value(prior[id], id == root, disabled));
    assert(after.dom() =~= updated.dom());
    assert forall |other: I| #[trigger] before.contains_key(other) implies after[other] == updated[other] by {
        if other == id {
            assert(0 <= at < extended.len() && extended[at] == other);
            assert(extended.contains(other));
        } else {
            if extended.contains(other) {
                let i = choose|i: int| 0 <= i < extended.len() && extended[i] == other;
                assert(i != at && 0 <= i < visited.len() && visited[i] == other);
            }
            if visited.contains(other) {
                let i = choose|i: int| 0 <= i < visited.len() && visited[i] == other;
                assert(0 <= i < extended.len() && extended[i] == other);
            }
            assert(extended.contains(other) == visited.contains(other));
        }
    }
    assert(after =~= updated);
}

fn complete_visibility<A: VisibilityModel>(store: &A, root: A::Id, path: Ghost<Seq<A::Id>>, capacity: usize)
    -> (complete: Ghost<bool>)
    ensures complete@ == visibility_path(store, root, path@, capacity),
    no_unwind
{
    Ghost(visibility_path(store, root, path@, capacity))
}
}

#[cfg(not(verus_keep_ghost))]
pub(super) trait VisibilityModel: LinkModel {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) trait VisibilityWalk: VisibilityModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(count =>
        ensures count == self.visibility().dom().len(),
        no_unwind
    ))]
    fn node_count(&self) -> usize;

    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        ensures final(self).links() == old(self).links(),
            next == Self::reverse_next(old(self).links(), root, node),
            final(self).visibility() == if old(self).visibility().contains_key(node) {
                old(self).visibility().insert(node, visibility_value(old(self).visibility()[node], root == node, disabled))
            } else { old(self).visibility() },
        no_unwind
    ))]
    fn change_visibility(&mut self, root: Self::Id, node: Self::Id, disabled: bool, epoch: u32) -> Option<Self::Id>;
}

/// Apply visibility along the reverse preorder. The arena count bounds the
/// number of visits even if a link is stale.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(store).links() == old(store).links(),
        final(store).visibility().dom() == old(store).visibility().dom(),
        visibility_path(old(store), root, path@, old(store).visibility().dom().len() as usize) ==>
            final(store).visibility() == visibility_prefix(old(store).visibility(), root, path@, path@.len() as int, disabled),
    no_unwind
))]
pub(super) fn set_subtree_visibility<A: VisibilityWalk>(
    store: &mut A, root: A::Id, disabled: bool, epoch: u32, #[cfg(verus_keep_ghost)] path: Ghost<Seq<A::Id>>,
) {
    let mut next = Some(root);
    let total = store.node_count();
    let mut remaining = total;
    #[cfg(verus_keep_ghost)]
    let complete = complete_visibility(store, root, path, remaining);
    #[cfg(verus_keep_ghost)]
    proof! { first_visibility(old(store).visibility(), root, path@, disabled); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant store.links() == old(store).links(),
            store.visibility().dom() == old(store).visibility().dom(),
            total == old(store).visibility().dom().len(), remaining <= total,
            complete@ == visibility_path(old(store), root, path@, total),
            complete@ ==> total - remaining <= path@.len(),
            complete@ ==> next == visible_at(path@, total - remaining),
            complete@ ==> store.visibility() == visibility_prefix(old(store).visibility(), root, path@, total - remaining, disabled),
        ensures complete@ ==> total - remaining == path@.len(),
        decreases remaining,
    ))]
    while let Some(node) = next {
        if remaining == 0 {
            #[cfg(verus_keep_ghost)]
            proof! { assert(!complete@); }
            break;
        }
        #[cfg(verus_keep_ghost)]
        let before = remember_visibility(store);
        remaining -= 1;
        next = store.change_visibility(root, node, disabled, epoch);
        #[cfg(verus_keep_ghost)]
        proof! {
            if complete@ {
                let i = total - remaining - 1;
                assert(before@ == visibility_prefix(old(store).visibility(), root, path@, i, disabled));
                assert(node == path@[i]);
                assert(old(store).visibility().contains_key(node));
                assert(next == visible_at(path@, i + 1));
                extend_visibility(old(store).visibility(), root, path@, i, disabled);
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
fn remember_visibility<A: VisibilityModel>(source: &A) -> (saved: Ghost<Map<A::Id, Visibility>>)
    ensures saved@ == source.visibility(),
    no_unwind
{
    Ghost(source.visibility())
}
}

#[cfg(verus_keep_ghost)]
#[path = "preorder.rs"]
pub(super) mod preorder;

#[cfg(verus_keep_ghost)]
verus! {
    pub(super) open spec fn projected_links<I,C>(nodes: Map<I, Node<I,C>>) -> Map<I, Links<I>> {
        Map::new(nodes.dom(), |id: I| record_links(&nodes[id]))
    }

    /// A successful pinned SlotMap lookup projects precisely the record used
    /// to obtain the prepare/placement traversal links.
    proof fn record_and_link_orders_match<I,C>(
        nodes: Map<I, Node<I,C>>, interval: spec_fn(I) -> (nat,nat), depth: spec_fn(I) -> nat,
    )
        ensures crate::owned_records::order(nodes, interval, depth)
            == preorder::order(projected_links(nodes), interval, depth),
    {
        let projected = projected_links(nodes);
        let records = crate::owned_records::order(nodes, interval, depth);
        let links = preorder::order(projected, interval, depth);
        assert forall |id: I| #[trigger] projected.contains_key(id) implies
            projected[id] == record_links(&nodes[id]) by {};
        assert(records.live =~= links.live);
        assert(records.parent =~= links.parent);
        assert(records.first =~= links.first);
        assert(records.sibling =~= links.sibling);
    }

    /// Pinned SlotMap insert and remove update the live map by one key. The
    /// projection performs the same change and hides inactive physical slots.
    proof fn project_entry_change<I,C>(nodes: Map<I, Node<I,C>>, id: I, node: Node<I,C>)
        ensures projected_links(nodes.insert(id, node)) == projected_links(nodes).insert(id, record_links(&node)),
            projected_links(nodes.remove(id)) == projected_links(nodes).remove(id),
    {
        assert(projected_links(nodes.insert(id, node)) =~= projected_links(nodes).insert(id, record_links(&node)));
        assert(projected_links(nodes.remove(id)) =~= projected_links(nodes).remove(id));
    }
}

#[cfg(verus_keep_ghost)]
#[path = "coherence.rs"]
pub(super) mod coherence;

#[cfg(verus_keep_ghost)]
#[path = "ancestry.rs"]
mod ancestry;

#[cfg(verus_keep_ghost)]
#[path = "before_sibling.rs"]
mod before_sibling;

#[cfg(verus_keep_ghost)]
#[path = "branch_move.rs"]
mod branch_move;

#[path = "relocate.rs"]
pub(super) mod relocate;
