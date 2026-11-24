//! Preorder interval witnesses for edits of the physical owned links.

use super::*;
use crate::prepare_frame::Order;

verus! {

pub(in crate::removal) open spec fn order<I>(
    links: Map<I, Links<I>>, interval: spec_fn(I) -> (nat, nat), depth: spec_fn(I) -> nat,
) -> Order<I> {
    Order {
        live: |id: I| links.contains_key(id),
        interval,
        depth,
        parent: |id: I| if links.contains_key(id) { links[id].parent } else { None },
        first: |id: I| if links.contains_key(id) { links[id].first } else { None },
        sibling: |id: I| if links.contains_key(id) { links[id].next } else { None },
    }
}

pub(in crate::removal) open spec fn partitioned<I>(before: Order<I>) -> bool {
    forall |left: I, right: I| #[trigger] (before.live)(left)
        && #[trigger] (before.live)(right) && left != right ==> {
        let l = (before.interval)(left);
        let r = (before.interval)(right);
        &&& l.0 != r.0
        &&& l.1 <= r.0 || r.1 <= l.0 || before.inside(left, right) || before.inside(right, left)
    }
}

pub(in crate::removal) open spec fn valid<I>(before: Order<I>) -> bool {
    before.ordered() && before.closed_subtrees() && partitioned(before)
}

pub(super) open spec fn leaf<I>() -> Links<I> {
    Links { parent: None, previous: None, next: None, first: None, last: None }
}

/// An empty child list at the physical root needs only one preorder position.
proof fn singleton_root<I>(root: I)
    ensures valid(order(Map::empty().insert(root, leaf()), |_: I| (0nat, 1nat), |_: I| 0nat)),
{
    let before = order(Map::empty().insert(root, leaf()), |_: I| (0nat, 1nat), |_: I| 0nat);
    assert forall |id: I| #[trigger] (before.live)(id) implies id == root by {};
}

pub(super) open spec fn final_gap<I>(links: Map<I, Links<I>>, parent: I, last: Option<I>) -> bool {
    &&& links.contains_key(parent)
    &&& links[parent].last == last
    &&& match last {
        Some(last) => links.contains_key(last) && last != parent
            && links[last].parent == Some(parent) && links[last].next.is_none(),
        None => links[parent].first.is_none(),
    }
}

pub(super) open spec fn appended<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I, last: Option<I>) -> Map<I, Links<I>> {
    let new_leaf = links.insert(node, leaf());
    set_gap(edited(new_leaf, node, Edit::Position(Some(parent), last, None)), parent, last, None, Some(node))
}

pub(super) open spec fn appended_interval<I>(before: Order<I>, parent: I, node: I, id: I) -> (nat, nat) {
    let end = (before.interval)(parent).1;
    let old = (before.interval)(id);
    if id == node {
        ((2 * end - 1) as nat, 2 * end)
    } else {
        (2 * old.0, if old.1 == end && !before.inside(id, parent) {
            (2 * old.1 - 1) as nat
        } else { 2 * old.1 })
    }
}

pub(super) open spec fn appended_order<I: Copy>(
    links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I, last: Option<I>,
) -> Order<I> {
    order(appended(links, parent, node, last),
        |id: I| appended_interval(before, parent, node, id),
        |id: I| if id == node { (before.depth)(parent) + 1 } else { (before.depth)(id) })
}

proof fn append_fields<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I, last: Option<I>)
    requires !links.contains_key(node), final_gap(links, parent, last),
    ensures
        appended(links, parent, node, last).dom() == links.dom().insert(node),
        appended(links, parent, node, last)[node] == (Links { parent: Some(parent), previous: last, ..leaf() }),
        forall |id: I| links.contains_key(id) ==> (#[trigger] appended(links, parent, node, last)[id]) ==
            (Links {
                next: if Some(id) == last { Some(node) } else { links[id].next },
                first: if id == parent && last.is_none() { Some(node) } else { links[id].first },
                last: if id == parent { Some(node) } else { links[id].last },
                ..links[id]
            }),
{
    let before = links.insert(node, leaf());
    let edit = Edit::Position(Some(parent), last, None);
    edit_keeps_keys(before, node, edit);
    set_gap_keeps_keys(edited(before, node, edit), parent, last, None, Some(node));
    match last {
        Some(tail) => {
            assert(tail != parent && tail != node);
        },
        None => {},
    }
}

proof fn old_interval<I>(before: Order<I>, parent: I, node: I, id: I)
    requires before.ordered(), (before.live)(parent), (before.live)(id), node != id,
    ensures ({
        let old = (before.interval)(id);
        let new = appended_interval(before, parent, node, id);
        &&& new.0 == 2 * old.0
        &&& 2 * old.1 - 1 <= new.1 <= 2 * old.1
        &&& new.0 < new.1
    }),
{
    before.node_facts(parent);
    before.node_facts(id);
}

proof fn old_inside<I>(before: Order<I>, after: Order<I>, parent: I, node: I, root: I, id: I)
    requires before.ordered(), (before.live)(parent), (before.live)(root), (before.live)(id),
        (after.live)(id), root != node, id != node,
        (after.interval)(root) == appended_interval(before, parent, node, root),
        (after.interval)(id) == appended_interval(before, parent, node, id),
    ensures before.inside(root, id) == after.inside(root, id),
{
    old_interval(before, parent, node, root);
    old_interval(before, parent, node, id);
    if before.inside(root, id) && before.inside(id, parent) {
        assert(before.inside(root, parent));
    }
}

proof fn leaf_inside<I>(before: Order<I>, after: Order<I>, parent: I, node: I, id: I)
    requires valid(before), (before.live)(parent), (before.live)(id),
        (after.live)(id), (after.live)(node), id != node,
        (after.interval)(node) == appended_interval(before, parent, node, node),
        (after.interval)(id) == appended_interval(before, parent, node, id),
    ensures after.inside(id, node) == before.inside(id, parent),
        !after.inside(node, id),
        (after.interval)(node).0 != (after.interval)(id).0,
        (after.interval)(node).1 <= (after.interval)(id).0
            || (after.interval)(id).1 <= (after.interval)(node).0 || after.inside(id, node),
{
    before.node_facts(parent);
    old_interval(before, parent, node, id);
    let end = (before.interval)(parent).1;
    let old = (before.interval)(id);
    let new = (after.interval)(id);
    if id == parent {
        assert(before.inside(parent, parent));
    } else if old.0 < end && end < old.1 {
        assert(partitioned(before));
        assert(before.inside(id, parent));
    }
    if !(old.0 < end) {
        assert(2 * end <= new.0);
    } else if !before.inside(id, parent) {
        if old.1 < end {
            assert(new.1 <= 2 * end - 1);
        } else {
            assert(old.1 == end);
            assert(new.1 == 2 * end - 1);
        }
    }
}


proof fn old_child<I>(before: Order<I>, after: Order<I>, parent: I, node: I, owner: I, child: I)
    requires before.ordered(), (before.live)(parent), (before.live)(owner), before.child(owner, child),
        (after.live)(child), owner != node, child != node,
        (after.parent)(child) == (before.parent)(child),
        (after.depth)(owner) == (before.depth)(owner), (after.depth)(child) == (before.depth)(child),
        (after.interval)(owner) == appended_interval(before, parent, node, owner),
        (after.interval)(child) == appended_interval(before, parent, node, child),
    ensures after.child(owner, child),
{
    old_inside(before, after, parent, node, owner, child);
    old_interval(before, parent, node, owner);
    old_interval(before, parent, node, child);
}

proof fn ordered_append<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I, last: Option<I>,
    interval: spec_fn(I) -> (nat, nat), depth: spec_fn(I) -> nat,
)
    requires !links.contains_key(node), final_gap(links, parent, last), valid(order(links, interval, depth)),
    ensures appended_order(links, order(links, interval, depth), parent, node, last).ordered(),
{
    let before = order(links, interval, depth);
    let after = appended_order(links, before, parent, node, last);
    let joined = appended(links, parent, node, last);
    append_fields(links, parent, node, last);
    leaf_inside(before, after, parent, node, parent);
    before.node_facts(parent);
    old_interval(before, parent, node, parent);
    assert((after.interval)(parent).0 < (after.interval)(node).0 < (after.interval)(node).1);
    assert((after.parent)(node) == Some(parent));
    assert((after.depth)(parent) < (after.depth)(node));
    assert(after.child(parent, node));
    assert(before.ordered());
    assert forall |id: I| #[trigger] (after.live)(id) implies {
        &&& (after.interval)(id).0 < (after.interval)(id).1
        &&& match (after.first)(id) { Some(child) => after.child(id, child), None => true }
        &&& match (after.parent)(id) {
            Some(owner) => (after.live)(owner) && after.child(owner, id) && match (after.sibling)(id) {
                Some(next) => after.child(owner, next) && (after.interval)(id).1 <= (after.interval)(next).0,
                None => true,
            },
            None => (after.sibling)(id).is_none(),
        }
    } by {
        if id != node {
            assert(links.contains_key(id));
            assert((before.live)(id));
            assert(joined[id].parent == links[id].parent);
            before.node_facts(id);
            old_interval(before, parent, node, id);
            if let Some(child) = (after.first)(id) {
                if id == parent && last.is_none() {
                    assert(child == node);
                } else {
                    assert((before.first)(id) == Some(child));
                    assert(before.child(id, child));
                    old_child(before, after, parent, node, id, child);
                }
            }
            if let Some(owner) = (after.parent)(id) {
                assert((before.parent)(id) == Some(owner));
                assert((before.live)(owner) && before.child(owner, id));
                old_child(before, after, parent, node, owner, id);
                if let Some(next) = (after.sibling)(id) {
                    if Some(id) == last {
                        assert(next == node && owner == parent);
                        assert(!before.inside(id, parent));
                        assert((before.interval)(id).1 <= (before.interval)(parent).1);
                        assert((after.interval)(id).1 <= (after.interval)(node).0);
                    } else {
                        assert((before.sibling)(id) == Some(next));
                        assert(before.child(owner, next) && (before.interval)(id).1 <= (before.interval)(next).0);
                        old_child(before, after, parent, node, owner, next);
                        old_interval(before, parent, node, next);
                    }
                }
            } else {
                assert(Some(id) != last);
                assert((before.sibling)(id).is_none() && (after.sibling)(id).is_none());
            }
        }
    }
}

/// Appending a freshly initialized leaf opens one position at the parent's
/// former end. An interval that ended there keeps the new leaf only when
/// it already contained the parent. Depths of older nodes do not change.
pub(super) proof fn append_leaf<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I, last: Option<I>,
    interval: spec_fn(I) -> (nat, nat), depth: spec_fn(I) -> nat,
)
    requires !links.contains_key(node), final_gap(links, parent, last), valid(order(links, interval, depth)),
    ensures valid(appended_order(links, order(links, interval, depth), parent, node, last)),
{
    let before = order(links, interval, depth);
    let after = appended_order(links, before, parent, node, last);
    let joined = appended(links, parent, node, last);
    append_fields(links, parent, node, last);
    ordered_append(links, parent, node, last, interval, depth);
    assert forall |root: I, id: I| #[trigger] after.inside(root, id) && (after.live)(root) && root != id implies {
        &&& (after.parent)(id).is_some() && after.inside(root, (after.parent)(id).unwrap())
        &&& (after.sibling)(id).is_some() ==> after.inside(root, (after.sibling)(id).unwrap())
    } by {
        if id == node {
            leaf_inside(before, after, parent, node, root);
            old_inside(before, after, parent, node, root, parent);
        } else if root == node {
            leaf_inside(before, after, parent, node, id);
        } else {
            assert(links.contains_key(root) && links.contains_key(id));
            old_inside(before, after, parent, node, root, id);
            assert(before.inside(root, id));
            assert((before.parent)(id).is_some() && before.inside(root, (before.parent)(id).unwrap()));
            let owner = (before.parent)(id).unwrap();
            assert((before.live)(owner));
            assert(joined[id].parent == Some(owner));
            old_inside(before, after, parent, node, root, owner);
            if let Some(next) = (after.sibling)(id) {
                if Some(id) == last {
                    assert(owner == parent && next == node);
                    leaf_inside(before, after, parent, node, root);
                } else {
                    assert((before.sibling)(id) == Some(next));
                    assert(before.inside(root, next));
                    old_inside(before, after, parent, node, root, next);
                }
            }
        }
    }
    assert forall |left: I, right: I| #[trigger] (after.live)(left)
        && #[trigger] (after.live)(right) && left != right implies {
        let l = (after.interval)(left);
        let r = (after.interval)(right);
        &&& l.0 != r.0
        &&& l.1 <= r.0 || r.1 <= l.0 || after.inside(left, right) || after.inside(right, left)
    } by {
        if left == node {
            leaf_inside(before, after, parent, node, right);
        } else if right == node {
            leaf_inside(before, after, parent, node, left);
        } else {
            assert((before.live)(left) && (before.live)(right));
            assert((before.interval)(left).0 != (before.interval)(right).0);
            old_interval(before, parent, node, left);
            old_interval(before, parent, node, right);
            old_inside(before, after, parent, node, left, right);
            old_inside(before, after, parent, node, right, left);
        }
    }
}


/// Use the initialized native leaf and the actual arena splice. The ghost
/// inputs describe surviving records before insertion into the arena.
fn attach_initialized_leaf<A: LinkStore>(
    arena: &mut A, parent: A::Id, node: A::Id, last: Option<A::Id>,
    prior: Ghost<Map<A::Id, Links<A::Id>>>, before: Ghost<Order<A::Id>>,
)
    requires
        old(arena).links() == prior@.insert(node, leaf()),
        !prior@.contains_key(node), final_gap(prior@, parent, last),
        before@ == order(prior@, before@.interval, before@.depth), valid(before@),
    ensures
        final(arena).links() == appended(prior@, parent, node, last),
        valid(appended_order(prior@, before@, parent, node, last)),
    no_unwind
{
    attach(arena, node, parent, last, None);
    proof { append_leaf(prior@, parent, node, last, before@.interval, before@.depth); }
}

/// References crossing the leaf boundary are exactly its parent and adjacent
/// siblings. This is the local consequence of reciprocal child lists.
pub(super) open spec fn leaf_gap<I>(links: Map<I, Links<I>>, parent: I, node: I) -> bool {
    let at = links[node];
    &&& links.contains_key(node) && links.contains_key(parent) && parent != node
    &&& at.parent == Some(parent) && at.first.is_none() && at.last.is_none()
    &&& match at.previous {
        Some(prev) => links.contains_key(prev) && prev != node && prev != parent
            && links[prev].parent == Some(parent) && links[prev].next == Some(node),
        None => links[parent].first == Some(node),
    }
    &&& match at.next {
        Some(next) => links.contains_key(next) && next != node && next != parent
            && Some(next) != at.previous && links[next].parent == Some(parent)
            && links[next].previous == Some(node),
        None => links[parent].last == Some(node),
    }
    &&& forall |id: I| #[trigger] links.contains_key(id) && id != node ==> {
        &&& links[id].parent != Some(node)
        &&& (links[id].first == Some(node)) == (id == parent && at.previous.is_none())
        &&& (links[id].next == Some(node)) == (Some(id) == at.previous)
    }
}

pub(super) open spec fn without_leaf<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I) -> Map<I, Links<I>> {
    let at = links[node];
    set_gap(edited(links, node, Edit::Position(None, None, None)), parent, at.previous, at.next, None).remove(node)
}

pub(super) proof fn cut_fields<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I)
    requires leaf_gap(links, parent, node),
    ensures
        without_leaf(links, parent, node).dom() == links.dom().remove(node),
        set_gap(edited(links, node, Edit::Position(None, None, None)), parent,
            links[node].previous, links[node].next, None) == without_leaf(links, parent, node).insert(node, leaf()),
        forall |id: I| #[trigger] without_leaf(links, parent, node).contains_key(id) ==> {
            let after = without_leaf(links, parent, node)[id];
            &&& after.parent == links[id].parent
            &&& after.first == (if links[id].first == Some(node) { links[node].next } else { links[id].first })
            &&& after.next == (if links[id].next == Some(node) { links[node].next } else { links[id].next })
        },
{
    let at = links[node];
    let cleared = edited(links, node, Edit::Position(None, None, None));
    let spliced = set_gap(cleared, parent, at.previous, at.next, None);
    edit_keeps_keys(links, node, Edit::Position(None, None, None));
    set_gap_keeps_keys(cleared, parent, at.previous, at.next, None);
    assert(spliced.remove(node).dom() =~= links.dom().remove(node));
    match (at.previous, at.next) {
        (Some(_), Some(_)) => { assert(spliced[node] == leaf()); },
        (Some(_), None) => { assert(spliced[node] == leaf()); },
        (None, Some(_)) => { assert(spliced[node] == leaf()); },
        (None, None) => { assert(spliced[node] == leaf()); },
    }
    assert(spliced =~= spliced.remove(node).insert(node, leaf()));
}

proof fn leaf_has_no_descendants<I>(before: Order<I>, node: I, id: I)
    requires before.ordered(), before.closed_subtrees(), (before.live)(node),
        forall |key: I| (before.live)(key) ==> (#[trigger] (before.parent)(key)) != Some(node),
        before.inside(node, id),
    ensures id == node,
    decreases (before.depth)(id),
{
    if id != node {
        assert((before.live)(id));
        assert((before.parent)(id).is_some());
        let owner = (before.parent)(id).unwrap();
        assert(before.inside(node, owner));
        assert(before.child(owner, id));
        assert((before.parent)(id) != Some(node));
        leaf_has_no_descendants(before, node, owner);
    }
}

/// Removing the leaf leaves every surviving interval and depth unchanged.
pub(super) proof fn remove_leaf<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I,
    interval: spec_fn(I) -> (nat, nat), depth: spec_fn(I) -> nat,
)
    requires leaf_gap(links, parent, node), valid(order(links, interval, depth)),
    ensures valid(order(without_leaf(links, parent, node), interval, depth)),
{
    let before = order(links, interval, depth);
    before.node_facts(node);
    assert(before.inside(node, node));
    assert forall |id: I| (before.live)(id) implies (#[trigger] (before.parent)(id)) != Some(node) by {
        if id == node { assert((before.parent)(id) == Some(parent)); }
    }
    assert forall |id: I| #[trigger] before.inside(node, id) implies id == node by {
        leaf_has_no_descendants(before, node, id);
    }
    assert(branch_gap(links, before, parent, node));
    assert(without_branch(links, before, parent, node) =~= without_leaf(links, parent, node));
    remove_branch(links, parent, node, interval, depth);
}

/// Detach the physical leaf. The ghost deletion map describes the subsequent
/// SlotMap retirement, or the temporary forest into which a move reattaches it.
pub(super) fn detach_leaf<A: LinkStore>(
    arena: &mut A, parent: A::Id, node: A::Id,
    prior: Ghost<Map<A::Id, Links<A::Id>>>, before: Ghost<Order<A::Id>>,
) -> (found: bool)
    requires old(arena).links() == prior@, leaf_gap(prior@, parent, node),
        before@ == order(prior@, before@.interval, before@.depth), valid(before@),
    ensures found, final(arena).links() == without_leaf(prior@, parent, node).insert(node, leaf()),
        valid(order(without_leaf(prior@, parent, node), before@.interval, before@.depth)),
    no_unwind
{
    let present = detach(arena, node, parent);
    proof {
        cut_fields(prior@, parent, node);
        remove_leaf(prior@, parent, node, before@.interval, before@.depth);
    }
    present
}

/// The native last-child move splices the same initialized leaf into the
/// destination's gap after detachment changes the original child list.
fn move_leaf_to_end<A: LinkStore>(
    arena: &mut A, parent: A::Id, node: A::Id, destination: A::Id, last: Option<A::Id>,
    prior: Ghost<Map<A::Id, Links<A::Id>>>, before: Ghost<Order<A::Id>>,
    cut: Ghost<Map<A::Id, Links<A::Id>>>, remaining: Ghost<Order<A::Id>>,
)
    requires old(arena).links() == prior@, leaf_gap(prior@, parent, node),
        before@ == order(prior@, before@.interval, before@.depth), valid(before@),
        cut@ == without_leaf(prior@, parent, node),
        remaining@ == order(cut@, before@.interval, before@.depth),
        final_gap(cut@, destination, last),
    ensures final(arena).links() == appended(cut@, destination, node, last),
        valid(appended_order(cut@, remaining@, destination, node, last)),
    no_unwind
{
    detach_leaf(arena, parent, node, prior, before);
    proof { cut_fields(prior@, parent, node); }
    attach_initialized_leaf(arena, destination, node, last, cut, remaining);
}


pub(in crate::removal) open spec fn branch_gap<I>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I) -> bool {
    let at = links[node];
    &&& links.contains_key(node) && links.contains_key(parent) && parent != node
    &&& at.parent == Some(parent)
    &&& match at.previous {
        Some(prev) => links.contains_key(prev) && prev != node && prev != parent
            && links[prev].parent == Some(parent) && links[prev].next == Some(node),
        None => links[parent].first == Some(node),
    }
    &&& match at.next {
        Some(next) => links.contains_key(next) && next != node && next != parent
            && Some(next) != at.previous && links[next].parent == Some(parent)
            && links[next].previous == Some(node),
        None => links[parent].last == Some(node),
    }
    &&& forall |id: I| #[trigger] links.contains_key(id) && !before.inside(node, id) ==> {
        &&& (links[id].first == Some(node)) == (id == parent && at.previous.is_none())
        &&& (links[id].next == Some(node)) == (Some(id) == at.previous)
    }
}

/// After the root's real splice, retirement restricts the live map to the
/// remaining preorder intervals. Retired slots no longer contribute links.
pub(in crate::removal) open spec fn without_branch<I: Copy>(
    links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I,
) -> Map<I, Links<I>> {
    let at = links[node];
    let spliced = set_gap(edited(links, node, Edit::Position(None, None, None)), parent, at.previous, at.next, None);
    Map::new(links.dom().filter(|id: I| !before.inside(node, id)), |id: I| spliced[id])
}

proof fn branch_fields<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I)
    requires branch_gap(links, before, parent, node), before.ordered(), (before.live)(node),
    ensures
        forall |id: I| #[trigger] without_branch(links, before, parent, node).contains_key(id) ==
            (links.contains_key(id) && !before.inside(node, id)),
        forall |id: I| #[trigger] without_branch(links, before, parent, node).contains_key(id) ==> {
            let after = without_branch(links, before, parent, node)[id];
            &&& after.parent == links[id].parent
            &&& after.first == (if links[id].first == Some(node) { links[node].next } else { links[id].first })
            &&& after.next == (if links[id].next == Some(node) { links[node].next } else { links[id].next })
        },
{
    before.node_facts(node);
    assert(before.inside(node, node));
}

proof fn kept_parent<I>(before: Order<I>, removed: I, child: I, parent: I)
    requires (before.live)(parent), before.child(parent, child), !before.inside(removed, child),
    ensures !before.inside(removed, parent),
{
    if before.inside(removed, parent) {
        assert(before.inside(removed, child));
    }
}

proof fn kept_child<I>(before: Order<I>, removed: I, parent: I, child: I)
    requires before.closed_subtrees(), (before.live)(removed), before.child(parent, child),
        !before.inside(removed, parent), child != removed,
    ensures !before.inside(removed, child),
{
    if before.inside(removed, child) {
        assert(before.inside(removed, parent));
    }
}
pub(in crate::removal) proof fn remove_branch<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I,
    interval: spec_fn(I) -> (nat, nat), depth: spec_fn(I) -> nat,
)
    requires branch_gap(links, order(links, interval, depth), parent, node), valid(order(links, interval, depth)),
    ensures valid(order(without_branch(links, order(links, interval, depth), parent, node), interval, depth)),
{
    let before = order(links, interval, depth);
    let cut = without_branch(links, before, parent, node);
    let after = order(cut, interval, depth);
    branch_fields(links, before, parent, node);
    assert((before.live)(node) && (before.parent)(node) == Some(parent));
    before.node_facts(node);
    assert forall |id: I| #[trigger] (after.live)(id) implies {
        &&& (after.interval)(id).0 < (after.interval)(id).1
        &&& match (after.first)(id) { Some(child) => after.child(id, child), None => true }
        &&& match (after.parent)(id) {
            Some(owner) => (after.live)(owner) && after.child(owner, id) && match (after.sibling)(id) {
                Some(next) => after.child(owner, next) && (after.interval)(id).1 <= (after.interval)(next).0,
                None => true,
            },
            None => (after.sibling)(id).is_none(),
        }
    } by {
        assert((before.live)(id));
        before.node_facts(id);
        assert((after.parent)(id) == (before.parent)(id));
        if let Some(child) = (after.first)(id) {
            if (before.first)(id) == Some(node) {
                assert(id == parent && (before.sibling)(node) == Some(child));
                assert(before.child(parent, child));
            } else {
                assert((before.first)(id) == Some(child));
                assert(before.child(id, child));
            }
            kept_child(before, node, id, child);
            assert(child != node && (after.live)(child));
            assert((after.parent)(child) == (before.parent)(child));
        }
        if let Some(owner) = (after.parent)(id) {
            assert((before.live)(owner) && before.child(owner, id));
            kept_parent(before, node, id, owner);
            assert((after.live)(owner));
            if let Some(next) = (after.sibling)(id) {
                if (before.sibling)(id) == Some(node) {
                    assert(owner == parent && (before.sibling)(node) == Some(next));
                    assert((before.interval)(id).1 <= (before.interval)(node).0);
                    assert(before.child(owner, next) && (before.interval)(node).1 <= (before.interval)(next).0);
                } else {
                    assert((before.sibling)(id) == Some(next));
                    assert(before.child(owner, next) && (before.interval)(id).1 <= (before.interval)(next).0);
                }
                kept_child(before, node, owner, next);
                assert(next != node && (after.live)(next));
                assert((after.parent)(next) == (before.parent)(next));
            }
        } else {
            assert((before.sibling)(id).is_none());
        }
    }
    assert forall |root: I, id: I| #[trigger] after.inside(root, id) && (after.live)(root) && root != id implies {
        &&& (after.parent)(id).is_some() && after.inside(root, (after.parent)(id).unwrap())
        &&& (after.sibling)(id).is_some() ==> after.inside(root, (after.sibling)(id).unwrap())
    } by {
        assert(before.inside(root, id) && (before.live)(root));
        assert((after.parent)(id) == (before.parent)(id));
        let owner = (before.parent)(id).unwrap();
        assert((before.parent)(id).is_some() && before.inside(root, owner));
        assert((before.live)(owner) && before.child(owner, id));
        kept_parent(before, node, id, owner);
        assert((after.live)(owner));
        if let Some(next) = (after.sibling)(id) {
            if (before.sibling)(id) == Some(node) {
                assert(before.inside(root, node));
                assert(root != node && (before.sibling)(node) == Some(next));
                assert(before.inside(root, next));
            } else {
                assert((before.sibling)(id) == Some(next));
                assert(before.inside(root, next));
            }
            assert(before.child(owner, next));
            kept_child(before, node, owner, next);
            assert(next != node && (after.live)(next));
        }
    }
    assert forall |left: I, right: I| #[trigger] (after.live)(left)
        && #[trigger] (after.live)(right) && left != right implies {
        let l = (after.interval)(left);
        let r = (after.interval)(right);
        &&& l.0 != r.0
        &&& l.1 <= r.0 || r.1 <= l.0 || after.inside(left, right) || after.inside(right, left)
    } by {
        assert((before.live)(left) && (before.live)(right));
    }
}

}
