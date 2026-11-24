//! Preserve the detached component's witnesses before a subtree move.
use super::*;
use crate::prepare_frame::Order;
use coherence::{child, coherent, spliced};
use preorder::{order, valid, without_branch};

verus! {

pub(in crate::removal) open spec fn detach_table<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I) -> Map<I, Links<I>> {
    let at = links[node];
    spliced(links, parent, node, at.previous, at.next, false)
}

pub(in crate::removal::links) closed spec fn component<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I) -> Map<I, Links<I>> {
    Map::new(links.dom().filter(|id: I| before.inside(node, id)), |id: I| detach_table(links, parent, node)[id])
}

proof fn cut_outside_branch<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I)
    requires before == order(links, before.interval, before.depth), valid(before),
        coherent(links), child(links, parent, node),
    ensures ({
        let at = links[node];
        &&& !before.inside(node, parent)
        &&& at.previous.is_some() ==> !before.inside(node, at.previous.unwrap())
        &&& at.next.is_some() ==> !before.inside(node, at.next.unwrap())
        &&& detach_table(links, parent, node).dom() == links.dom()
        &&& detach_table(links, parent, node)[node] == (Links {
            parent: None, previous: None, next: None, ..at
        })
        &&& forall|id: I| #[trigger] before.inside(node, id) && id != node
            ==> detach_table(links, parent, node)[id] == links[id]
    }),
{
    let at = links[node];
    assert((before.live)(node) && (before.live)(parent));
    before.node_facts(node);
    assert(before.child(parent, node));
    assert(!before.inside(node, parent));
    coherence::branch_gap_from_links(links, before, parent, node);
    assert(coherence::distinct_gap(parent, node, at.previous, at.next));
    coherence::splice_fields(links, parent, node, at.previous, at.next, false);
    if let Some(previous) = at.previous {
        assert((before.live)(previous));
        before.node_facts(previous);
        assert((before.interval)(previous).1 <= (before.interval)(node).0);
    }
    if let Some(next) = at.next {
        assert((before.live)(next));
        assert(before.child(parent, next));
        assert((before.interval)(node).1 <= (before.interval)(next).0);
        before.node_facts(next);
    }
}

proof fn component_child<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, detached: Order<I>,
    parent: I, moved: I, owner: I, id: I)
    requires valid(before), before == order(links, before.interval, before.depth),
        detached == order(component(links, before, parent, moved), before.interval, before.depth),
        before.inside(moved, owner), before.child(owner, id),
        (detached.live)(id), id != moved,
        detach_table(links, parent, moved)[id] == links[id],
    ensures detached.child(owner, id),
{}

proof fn component_keeps_order<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, moved: I)
    requires before == order(links, before.interval, before.depth), valid(before),
        coherent(links), child(links, parent, moved),
    ensures ({
        let members = component(links, before, parent, moved);
        let detached = order(members, before.interval, before.depth);
        &&& valid(detached) && (detached.live)(moved)
        &&& (detached.parent)(moved).is_none() && (detached.sibling)(moved).is_none()
        &&& forall|id: I| #[trigger] (detached.live)(id) == before.inside(moved, id)
    }),
{
    let members = component(links, before, parent, moved);
    let detached = order(members, before.interval, before.depth);
    cut_outside_branch(links, before, parent, moved);
    assert((before.live)(moved));
    before.node_facts(moved);
    assert(before.inside(moved, moved));
    assert((detached.live)(moved));
    assert forall |id: I| #[trigger] (detached.live)(id) implies {
        &&& (detached.interval)(id).0 < (detached.interval)(id).1
        &&& match (detached.first)(id) { Some(kid) => detached.child(id, kid), None => true }
        &&& match (detached.parent)(id) {
            Some(owner) => (detached.live)(owner) && detached.child(owner, id) && match (detached.sibling)(id) {
                Some(next) => detached.child(owner, next) && (detached.interval)(id).1 <= (detached.interval)(next).0,
                None => true,
            },
            None => (detached.sibling)(id).is_none(),
        }
    } by {
        assert(before.inside(moved, id));
        before.node_facts(id);
        assert((detached.first)(id) == (before.first)(id));
        if let Some(kid) = (detached.first)(id) {
            assert(before.child(id, kid));
            assert(before.inside(moved, kid) && (detached.live)(kid));
            assert(kid != moved);
            component_child(links, before, detached, parent, moved, id, kid);
        }
        if id != moved {
            assert((detached.parent)(id) == (before.parent)(id));
            assert((detached.sibling)(id) == (before.sibling)(id));
            assert((before.parent)(id).is_some());
            let owner = (before.parent)(id).unwrap();
            assert(before.inside(moved, owner) && (detached.live)(owner));
            component_child(links, before, detached, parent, moved, owner, id);
            if let Some(next) = (detached.sibling)(id) {
                assert(before.inside(moved, next) && (detached.live)(next));
                assert(before.child(owner, next) && (before.interval)(id).1 <= (before.interval)(next).0);
                assert(next != moved);
                component_child(links, before, detached, parent, moved, owner, next);
            }
        }
    }
    assert forall |root: I, id: I| #[trigger] detached.inside(root, id) && (detached.live)(root) && root != id implies {
        &&& (detached.parent)(id).is_some() && detached.inside(root, (detached.parent)(id).unwrap())
        &&& (detached.sibling)(id).is_some() ==> detached.inside(root, (detached.sibling)(id).unwrap())
    } by {
        assert(before.inside(moved, root) && before.inside(moved, id));
        if id == moved {
            assert(preorder::partitioned(before));
            assert((before.interval)(id).0 != (before.interval)(root).0);
            assert(false);
        } else {
            assert(before.inside(root, id));
            assert((detached.parent)(id) == (before.parent)(id));
            assert((detached.sibling)(id) == (before.sibling)(id));
            let owner = (before.parent)(id).unwrap();
            assert(before.inside(moved, owner) && before.inside(root, owner));
            if let Some(next) = (before.sibling)(id) {
                assert(before.inside(moved, next) && before.inside(root, next));
            }
        }
    }
    assert(preorder::partitioned(before));
    assert forall |left: I, right: I| #[trigger] (detached.live)(left)
        && #[trigger] (detached.live)(right) && left != right implies {
        let l = (detached.interval)(left);
        let r = (detached.interval)(right);
        &&& l.0 != r.0
        &&& l.1 <= r.0 || r.1 <= l.0 || detached.inside(left, right) || detached.inside(right, left)
    } by {
        assert((before.live)(left) && (before.live)(right));
    }
}

proof fn split_physical_records<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I)
    requires detach_table(links, parent, node).dom() == links.dom(),
    ensures ({
        let exterior = without_branch(links, before, parent, node);
        let branch = component(links, before, parent, node);
        &&& exterior.dom().disjoint(branch.dom())
        &&& detach_table(links, parent, node) == exterior.union_prefer_right(branch)
    }),
{
    let exterior = without_branch(links, before, parent, node);
    let branch = component(links, before, parent, node);
    let detached = detach_table(links, parent, node);
    let joined = exterior.union_prefer_right(branch);
    assert forall|id: I| #[trigger] joined.contains_key(id) == detached.contains_key(id) by {
        if links.contains_key(id) {
            assert(exterior.contains_key(id) == !before.inside(node, id));
            assert(branch.contains_key(id) == before.inside(node, id));
        }
    }
    assert(detached =~= joined);
}

pub(in crate::removal::links) proof fn detach_preserves_ranks<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I)
    requires before == order(links, before.interval, before.depth), valid(before),
        coherent(links), child(links, parent, node),
    ensures coherence::distinct_gap(parent, node, links[node].previous, links[node].next), ({
        let exterior = without_branch(links, before, parent, node);
        let branch = component(links, before, parent, node);
        &&& valid(order(exterior, before.interval, before.depth))
        &&& valid(order(branch, before.interval, before.depth))
        &&& exterior.dom().disjoint(branch.dom())
        &&& detach_table(links, parent, node) == exterior.union_prefer_right(branch)
    }),
{
    coherence::branch_gap_from_links(links, before, parent, node);
    cut_outside_branch(links, before, parent, node);
    preorder::remove_branch(links, parent, node, before.interval, before.depth);
    component_keeps_order(links, before, parent, node);
    split_physical_records(links, before, parent, node);
}

/// After the actual splice, both resulting components keep valid ranks.
/// Their maps partition the original records without consulting stale keys.
fn detach_for_move<A: LinkStore>(
    arena: &mut A, parent: A::Id, node: A::Id, before: Ghost<Order<A::Id>>,
) -> (found: bool)
    requires before@ == order(old(arena).links(), before@.interval, before@.depth), valid(before@),
        coherent(old(arena).links()), child(old(arena).links(), parent, node),
    ensures found, final(arena).links() == detach_table(old(arena).links(), parent, node),
        coherent(final(arena).links()), ({
            let exterior = without_branch(old(arena).links(), before@, parent, node);
            let branch = component(old(arena).links(), before@, parent, node);
            &&& valid(order(exterior, before@.interval, before@.depth))
            &&& valid(order(branch, before@.interval, before@.depth))
            &&& exterior.dom().disjoint(branch.dom())
            &&& final(arena).links() == exterior.union_prefer_right(branch)
        }),
    no_unwind
{
    proof { detach_preserves_ranks(old(arena).links(), before@, parent, node); }
    detach(arena, node, parent)
}

}

#[path = "reattach.rs"]
pub(super) mod reattach;
