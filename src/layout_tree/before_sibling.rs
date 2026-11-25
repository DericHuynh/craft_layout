//! Preserve preorder ranks when a detached leaf enters before an existing child.
use super::*;
use crate::prepare_frame::Order;
use coherence::{child, coherent, spliced};
use preorder::{leaf, order, valid};

verus! {

spec fn inserted<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I, sibling: I) -> Map<I, Links<I>> {
    spliced(links.insert(node, leaf()), parent, node, links[sibling].previous, Some(sibling), true)
}

spec fn interval<I>(before: Order<I>, node: I, sibling: I, id: I) -> (nat, nat) {
    if id == node {
        let start = (before.interval)(sibling).0;
        (2 * start, 2 * start + 1)
    } else {
        let (start, end) = (before.interval)(id);
        (2 * start + 1, 2 * end)
    }
}

spec fn inserted_order<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I, sibling: I) -> Order<I> {
    order(inserted(links, parent, node, sibling),
        |id: I| interval(before, node, sibling, id),
        |id: I| if id == node { (before.depth)(parent) + 1 } else { (before.depth)(id) })
}

proof fn prior_contains<I>(before: Order<I>, after: Order<I>, node: I, sibling: I, root: I, id: I)
    requires before.ordered(), (before.live)(root), (before.live)(id), (after.live)(id),
        root != node, id != node,
        (after.interval)(root) == interval(before, node, sibling, root),
        (after.interval)(id) == interval(before, node, sibling, id),
    ensures after.inside(root, id) == before.inside(root, id),
{
    before.node_facts(id);
}

proof fn prior_child<I>(before: Order<I>, after: Order<I>, node: I, sibling: I, root: I, id: I)
    requires before.ordered(), (before.live)(root), before.child(root, id),
        root != node, id != node, (after.live)(id), (after.parent)(id) == Some(root),
        (after.interval)(root) == interval(before, node, sibling, root),
        (after.interval)(id) == interval(before, node, sibling, id),
        (after.depth)(root) == (before.depth)(root),
        (after.depth)(id) == (before.depth)(id),
    ensures after.child(root, id),
{
    prior_contains(before, after, node, sibling, root, id);
}

proof fn inserted_containment<I>(before: Order<I>, after: Order<I>, parent: I, node: I, sibling: I, id: I)
    requires valid(before), (before.live)(parent), before.child(parent, sibling), (before.live)(id),
        (after.live)(node), (after.live)(id), node != id,
        (after.interval)(node) == interval(before, node, sibling, node),
        (after.interval)(id) == interval(before, node, sibling, id),
    ensures after.inside(id, node) == before.inside(id, parent),
        !after.inside(node, id),
        (after.interval)(id).0 != (after.interval)(node).0,
        (after.interval)(id).1 <= (after.interval)(node).0
            || (after.interval)(node).1 <= (after.interval)(id).0 || after.inside(id, node),
{
    let start = (before.interval)(sibling).0;
    let extent = (before.interval)(id);
    before.node_facts(id);
    before.node_facts(sibling);
    if extent.0 < start && start < extent.1 {
        assert(preorder::partitioned(before));
        assert(id != sibling);
        assert(!before.inside(sibling, id));
        assert(before.inside(id, sibling));
        assert(before.inside(id, parent));
    }
    if before.inside(id, parent) {
        assert(extent.0 < start && start < extent.1);
    }
    if start <= extent.0 {
        assert((after.interval)(node).1 <= (after.interval)(id).0);
    } else if extent.1 <= start {
        assert((after.interval)(id).1 <= (after.interval)(node).0);
    }
}

proof fn insertion_links<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I, sibling: I)
    requires coherent(links), child(links, parent, sibling), !links.contains_key(node),
    ensures ({
        let after = inserted(links, parent, node, sibling);
        let previous = links[sibling].previous;
        &&& after.dom() == links.dom().insert(node)
        &&& coherent(after)
        &&& after[node] == (Links { parent: Some(parent), previous, next: Some(sibling), ..leaf() })
        &&& forall |id: I| #[trigger] links.contains_key(id) ==> {
            let row = after[id];
            &&& row.parent == links[id].parent
            &&& row.first == if id == parent && previous.is_none() { Some(node) } else { links[id].first }
            &&& row.next == if previous == Some(id) { Some(node) } else { links[id].next }
        }
    }),
{
    let initialized = links.insert(node, leaf());
    let previous = links[sibling].previous;
    coherence::insert_empty_keeps_coherent(links, node);
    coherence::before_child_gap(initialized, parent, node, sibling);
    coherence::splice_fields(initialized, parent, node, previous, Some(sibling), true);
    coherence::attach_keeps_coherent(initialized, parent, node, previous, Some(sibling));
}

proof fn preserves_order<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I, sibling: I)
    requires before == order(links, before.interval, before.depth), valid(before),
        coherent(links), child(links, parent, sibling), !links.contains_key(node),
    ensures inserted_order(links, before, parent, node, sibling).ordered(),
{
    let after = inserted_order(links, before, parent, node, sibling);
    let joined = inserted(links, parent, node, sibling);
    let previous = links[sibling].previous;
    insertion_links(links, parent, node, sibling);
    assert((before.live)(parent) && (before.live)(sibling));
    assert(before.child(parent, sibling));
    inserted_containment(before, after, parent, node, sibling, parent);
    assert(after.child(parent, node));
    prior_child(before, after, node, sibling, parent, sibling);
    assert((after.interval)(node).1 == (after.interval)(sibling).0);
    assert forall |id: I| #[trigger] (after.live)(id) implies {
        &&& (after.interval)(id).0 < (after.interval)(id).1
        &&& match (after.first)(id) { Some(kid) => after.child(id, kid), None => true }
        &&& match (after.parent)(id) {
            Some(owner) => (after.live)(owner) && after.child(owner, id) && match (after.sibling)(id) {
                Some(next) => after.child(owner, next) && (after.interval)(id).1 <= (after.interval)(next).0,
                None => true,
            },
            None => (after.sibling)(id).is_none(),
        }
    } by {
        if id != node {
            assert((before.live)(id));
            assert(joined[id].parent == links[id].parent);
            before.node_facts(id);
            if let Some(kid) = (after.first)(id) {
                if id == parent && previous.is_none() {
                    assert(kid == node);
                } else {
                    assert((before.first)(id) == Some(kid));
                    prior_child(before, after, node, sibling, id, kid);
                }
            }
            if let Some(owner) = (after.parent)(id) {
                assert((before.parent)(id) == Some(owner));
                assert((before.live)(owner) && before.child(owner, id));
                prior_child(before, after, node, sibling, owner, id);
                if let Some(next) = (after.sibling)(id) {
                    if previous == Some(id) {
                        assert(coherence::position(links, sibling));
                        assert(owner == parent && next == node);
                        assert((before.sibling)(id) == Some(sibling));
                        assert((before.interval)(id).1 <= (before.interval)(sibling).0);
                        assert((after.interval)(id).1 <= (after.interval)(node).0);
                    } else {
                        assert((before.sibling)(id) == Some(next));
                        assert(before.child(owner, next) && (before.interval)(id).1 <= (before.interval)(next).0);
                        prior_child(before, after, node, sibling, owner, next);
                    }
                }
            } else {
                assert(coherence::position(links, sibling));
                assert(previous != Some(id));
                assert((before.sibling)(id).is_none() && (after.sibling)(id).is_none());
            }
        }
    }
}

/// Native before-sibling insertion opens one preorder slot at the sibling's
/// starting rank. All older containment and relative order remain intact.
proof fn preserves_intervals<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I, sibling: I)
    requires before == order(links, before.interval, before.depth), valid(before),
        coherent(links), child(links, parent, sibling), !links.contains_key(node),
    ensures valid(inserted_order(links, before, parent, node, sibling)),
{
    let after = inserted_order(links, before, parent, node, sibling);
    let joined = inserted(links, parent, node, sibling);
    let previous = links[sibling].previous;
    insertion_links(links, parent, node, sibling);
    preserves_order(links, before, parent, node, sibling);
    assert((before.live)(parent) && before.child(parent, sibling));
    assert forall |root: I, id: I| #[trigger] after.inside(root, id) && (after.live)(root) && root != id implies {
        &&& (after.parent)(id).is_some() && after.inside(root, (after.parent)(id).unwrap())
        &&& (after.sibling)(id).is_some() ==> after.inside(root, (after.sibling)(id).unwrap())
    } by {
        if id == node {
            inserted_containment(before, after, parent, node, sibling, root);
            prior_contains(before, after, node, sibling, root, parent);
            prior_contains(before, after, node, sibling, root, sibling);
            assert(before.inside(root, sibling));
        } else if root == node {
            inserted_containment(before, after, parent, node, sibling, id);
        } else {
            assert((before.live)(root) && (before.live)(id));
            prior_contains(before, after, node, sibling, root, id);
            assert((before.parent)(id).is_some());
            let owner = (before.parent)(id).unwrap();
            assert((before.live)(owner) && before.inside(root, owner));
            assert(joined[id].parent == Some(owner));
            prior_contains(before, after, node, sibling, root, owner);
            if let Some(next) = (after.sibling)(id) {
                if previous == Some(id) {
                    assert(coherence::position(links, sibling));
                    assert(owner == parent && next == node);
                    inserted_containment(before, after, parent, node, sibling, root);
                } else {
                    assert((before.sibling)(id) == Some(next));
                    assert(before.inside(root, next));
                    prior_contains(before, after, node, sibling, root, next);
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
            inserted_containment(before, after, parent, node, sibling, right);
        } else if right == node {
            inserted_containment(before, after, parent, node, sibling, left);
        } else {
            assert((before.live)(left) && (before.live)(right));
            assert(preorder::partitioned(before));
            prior_contains(before, after, node, sibling, left, right);
            prior_contains(before, after, node, sibling, right, left);
        }
    }
}

/// Read the destination's previous link after detachment, as the public move
/// does, then use the actual arena splice on the now isolated leaf.
fn attach_before<A: LinkStore>(
    arena: &mut A, parent: A::Id, node: A::Id, sibling: A::Id,
    prior: Ghost<Map<A::Id, Links<A::Id>>>, before: Ghost<Order<A::Id>>,
)
    requires old(arena).links() == prior@.insert(node, leaf()),
        before@ == order(prior@, before@.interval, before@.depth), valid(before@),
        coherent(prior@), child(prior@, parent, sibling), !prior@.contains_key(node),
    ensures final(arena).links() == inserted(prior@, parent, node, sibling),
        coherent(final(arena).links()), valid(inserted_order(prior@, before@, parent, node, sibling)),
    no_unwind
{
    let Some(destination) = arena.read_links(sibling) else {
        proof { assert(false); }
        return;
    };
    proof {
        insertion_links(prior@, parent, node, sibling);
        preserves_intervals(prior@, before@, parent, node, sibling);
    }
    attach(arena, node, parent, destination.previous, Some(sibling));
}


/// A physical leaf move first cuts the old gap. The destination predecessor
/// then comes from the surviving sibling record, even for a same-parent move.
fn move_leaf_before<A: LinkStore>(
    arena: &mut A, parent: A::Id, node: A::Id, destination: A::Id, sibling: A::Id,
    prior: Ghost<Map<A::Id, Links<A::Id>>>, before: Ghost<Order<A::Id>>,
    cut: Ghost<Map<A::Id, Links<A::Id>>>, remaining: Ghost<Order<A::Id>>,
)
    requires old(arena).links() == prior@, preorder::leaf_gap(prior@, parent, node),
        coherent(prior@), before@ == order(prior@, before@.interval, before@.depth), valid(before@),
        child(prior@, destination, sibling), node != sibling,
        cut@ == preorder::without_leaf(prior@, parent, node),
        remaining@ == order(cut@, before@.interval, before@.depth),
    ensures final(arena).links() == inserted(cut@, destination, node, sibling),
        coherent(final(arena).links()),
        valid(inserted_order(cut@, remaining@, destination, node, sibling)),
    no_unwind
{
    preorder::detach_leaf(arena, parent, node, prior, before);
    proof {
        preorder::cut_fields(prior@, parent, node);
        assert(!(cut@.contains_key(node)));
        assert(destination != node);
        assert(child(cut@, destination, sibling));
        let detached = cut@.insert(node, leaf());
        let live = prior@[node];
        assert(coherence::distinct_gap(parent, node, live.previous, live.next));
        coherence::detach_keeps_coherent(prior@, parent, node);
        assert(coherent(detached));
        assert forall |id: A::Id| detached.contains_key(id) && (#[trigger] detached[id]).parent.is_some() implies
            cut@.contains_key(id) == cut@.contains_key(detached[id].parent.unwrap()) by {
            assert(id != node);
            assert(detached[id].parent == prior@[id].parent);
            assert(detached[id].parent != Some(node));
            assert(coherence::position(detached, id));
        }
        coherence::retire_component_keeps_coherent(detached, cut@.dom());
        assert(coherence::keep_entries(detached, cut@.dom()) =~= cut@);
    }
    attach_before(arena, destination, node, sibling, cut, remaining);
}

}
