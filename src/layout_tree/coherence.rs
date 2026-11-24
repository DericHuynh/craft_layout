//! Reciprocal endpoints of the actual doubly linked owned child lists.
use super::*;
use crate::prepare_frame::Order;

verus! {

pub(in crate::removal) open spec fn child<I>(links: Map<I, Links<I>>, parent: I, node: I) -> bool {
    links.contains_key(parent) && links.contains_key(node) && node != parent && links[node].parent == Some(parent)
}

pub(in crate::removal) open spec fn position<I>(links: Map<I, Links<I>>, id: I) -> bool {
    let at = links[id];
    match at.parent {
        Some(parent) => {
            &&& child(links, parent, id)
            &&& match at.previous {
                Some(prev) => child(links, parent, prev) && prev != id && links[prev].next == Some(id),
                None => links[parent].first == Some(id),
            }
            &&& match at.next {
                Some(next) => child(links, parent, next) && next != id && links[next].previous == Some(id),
                None => links[parent].last == Some(id),
            }
        },
        None => at.previous.is_none() && at.next.is_none(),
    }
}

pub(in crate::removal) open spec fn endpoints<I>(links: Map<I, Links<I>>, id: I) -> bool {
    let at = links[id];
    match (at.first, at.last) {
        (Some(first), Some(last)) => child(links, id, first) && child(links, id, last)
            && links[first].previous.is_none() && links[last].next.is_none(),
        (None, None) => true,
        _ => false,
    }
}

pub(in crate::removal) open spec fn coherent_at<I>(links: Map<I, Links<I>>, id: I) -> bool {
    position(links, id) && endpoints(links, id)
}

pub(in crate::removal) open spec fn coherent<I>(links: Map<I, Links<I>>) -> bool {
    forall |id: I| #[trigger] links.contains_key(id) ==> coherent_at(links, id)
}

pub(in crate::removal) open spec fn valid_gap<I>(links: Map<I, Links<I>>, parent: I, node: I,
    previous: Option<I>, next: Option<I>,
) -> bool {
    &&& gap_between(links, parent, node, previous, next)
    &&& links[node].parent.is_none()
    &&& previous.is_some() ==> child(links, parent, previous.unwrap())
    &&& next.is_some() ==> child(links, parent, next.unwrap())
}

pub(super) proof fn final_child_gap<I>(links: Map<I, Links<I>>, parent: I, node: I)
    requires coherent(links), links.contains_key(parent), links.contains_key(node), parent != node,
        links[node].parent.is_none(),
    ensures valid_gap(links, parent, node, links[parent].last, None),
{
    assert(coherent_at(links, parent));
    if let Some(tail) = links[parent].last {
        assert(child(links, parent, tail));
        assert(tail != node && tail != parent);
    } else { assert(links[parent].first.is_none()); }
}

pub(super) proof fn before_child_gap<I>(links: Map<I, Links<I>>, parent: I, node: I, next: I)
    requires coherent(links), child(links, parent, next), links.contains_key(node), parent != node,
        links[node].parent.is_none(),
    ensures valid_gap(links, parent, node, links[next].previous, Some(next)),
{
    assert(coherent_at(links, next));
    if let Some(prev) = links[next].previous {
        assert(child(links, parent, prev));
        assert(prev != node && prev != parent && prev != next);
    }
}

/// Follow the two directions of the physical list to characterize precisely
/// which records refer to an attached root as their first or next child.
pub(super) proof fn root_references<I>(links: Map<I, Links<I>>, parent: I, node: I)
    requires coherent(links), child(links, parent, node),
    ensures forall |id: I| #[trigger] links.contains_key(id) && id != node ==> {
        &&& (links[id].first == Some(node)) == (id == parent && links[node].previous.is_none())
        &&& (links[id].next == Some(node)) == (Some(id) == links[node].previous)
    },
{
    assert(coherent_at(links, node));
    assert forall |id: I| #[trigger] links.contains_key(id) && id != node implies {
        &&& (links[id].first == Some(node)) == (id == parent && links[node].previous.is_none())
        &&& (links[id].next == Some(node)) == (Some(id) == links[node].previous)
    } by {
        assert(coherent_at(links, id));
        if links[id].first == Some(node) {
            assert(child(links, id, node));
        }
        if links[id].next == Some(node) {
            assert(links[node].previous == Some(id));
        }
    }
}

pub(in crate::removal) proof fn branch_gap_from_links<I>(links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I)
    requires coherent(links), child(links, parent, node), before.ordered(),
        before == preorder::order(links, before.interval, before.depth),
    ensures preorder::branch_gap(links, before, parent, node),
{
    let current = links[node];
    assert(coherent_at(links, node));
    root_references(links, parent, node);
    assert((before.live)(node));
    before.node_facts(node);
    assert(before.inside(node, node));
    if let (Some(prev), Some(next)) = (current.previous, current.next) {
        assert(child(links, parent, prev) && child(links, parent, next));
        // Lower-level reciprocity admits a two-cycle. A preorder witness
        // excludes it by putting each successor after its sibling.
        before.node_facts(prev);
        assert((before.interval)(prev).1 <= (before.interval)(node).0);
        assert((before.interval)(node).1 <= (before.interval)(next).0);
        assert(prev != next);
    }
}


/// The five possible writes touch the edited node, its parent, or the two
/// neighboring siblings. Each role is distinct in a valid gap.
pub(in crate::removal) open spec fn spliced<I: Copy>(
    links: Map<I, Links<I>>, parent: I, node: I, previous: Option<I>, next: Option<I>, attach_node: bool,
) -> Map<I, Links<I>> {
    let position = if attach_node { Edit::Position(Some(parent), previous, next) }
        else { Edit::Position(None, None, None) };
    set_gap(edited(links, node, position), parent, previous, next, if attach_node { Some(node) } else { None })
}

pub(in crate::removal) open spec fn distinct_gap<I>(parent: I, node: I, previous: Option<I>, next: Option<I>) -> bool {
    &&& parent != node
    &&& previous != Some(parent) && previous != Some(node)
    &&& next != Some(parent) && next != Some(node)
    &&& previous.is_some() ==> previous != next
}

pub(in crate::removal) proof fn splice_fields<I: Copy>(
    links: Map<I, Links<I>>, parent: I, node: I, previous: Option<I>, next: Option<I>, attach_node: bool,
)
    requires distinct_gap(parent, node, previous, next),
    ensures
        spliced(links, parent, node, previous, next, attach_node).dom() == links.dom(),
        forall |id: I| links.contains_key(id) ==> (#[trigger]
            spliced(links, parent, node, previous, next, attach_node)[id]) == {
                let at = links[id];
                let forward = if attach_node { Some(node) } else { next };
                let backward = if attach_node { Some(node) } else { previous };
                if id == node {
                    if attach_node { Links { parent: Some(parent), previous, next, ..at } }
                    else { Links { parent: None, previous: None, next: None, ..at } }
                } else if id == parent {
                    Links { first: if previous.is_none() { forward } else { at.first },
                            last: if next.is_none() { backward } else { at.last }, ..at }
                } else if previous == Some(id) {
                    Links { next: forward, ..at }
                } else if next == Some(id) {
                    Links { previous: backward, ..at }
                } else { at }
            },
{
    let position = if attach_node { Edit::Position(Some(parent), previous, next) }
        else { Edit::Position(None, None, None) };
    edit_keeps_keys(links, node, position);
    set_gap_keeps_keys(edited(links, node, position), parent, previous, next,
        if attach_node { Some(node) } else { None });
    match (previous, next) {
        (Some(_), Some(_)) => {},
        (Some(_), None) => {},
        (None, Some(_)) => {},
        (None, None) => {},
    }
}

proof fn attach_keeps_endpoints<I: Copy>(
    links: Map<I, Links<I>>, parent: I, node: I, previous: Option<I>, next: Option<I>, id: I,
)
    requires coherent(links), valid_gap(links, parent, node, previous, next), links.contains_key(id),
    ensures ({
        let after = spliced(links, parent, node, previous, next, true);
        endpoints(after, id)
    }),
{
    let after = spliced(links, parent, node, previous, next, true);
    splice_fields(links, parent, node, previous, next, true);
    assert(coherent_at(links, id));
    if id == parent {
        if let Some(first) = links[id].first {
            assert(child(links, id, first) && links[first].previous.is_none());
        }
        if let Some(last) = links[id].last {
            assert(child(links, id, last) && links[last].next.is_none());
        }
        match (previous, next) {
            (None, None) => {},
            (Some(p), None) => {
                assert(links[id].last == Some(p));
            },
            (None, Some(n)) => {
                assert(links[id].first == Some(n));
            },
            (Some(_), Some(_)) => {},
        }
    } else if let (Some(first), Some(last)) = (links[id].first, links[id].last) {
        assert(child(links, id, first) && child(links, id, last));
        assert(first != node && last != node);
        assert(previous != Some(last) && next != Some(first));
        assert(after[first].previous.is_none() && after[last].next.is_none());
    }
}

proof fn attach_keeps_positions<I: Copy>(
    links: Map<I, Links<I>>, parent: I, node: I, previous: Option<I>, next: Option<I>, id: I,
)
    requires coherent(links), valid_gap(links, parent, node, previous, next), links.contains_key(id),
    ensures ({
        let after = spliced(links, parent, node, previous, next, true);
        position(after, id)
    }),
{
    let after = spliced(links, parent, node, previous, next, true);
    splice_fields(links, parent, node, previous, next, true);
    assert(coherent_at(links, id));
    if id == node {
        if let Some(prev) = previous { assert(child(links, parent, prev)); }
        if let Some(following) = next { assert(child(links, parent, following)); }
    } else if let Some(owner) = links[id].parent {
        assert(child(links, owner, id));
        if let Some(prev) = links[id].previous {
            assert(child(links, owner, prev) && links[prev].next == Some(id));
            assert(prev != node);
            if previous == Some(prev) { assert(next == Some(id)); }
        }
        if let Some(following) = links[id].next {
            assert(child(links, owner, following) && links[following].previous == Some(id));
            assert(following != node);
            if next == Some(following) { assert(previous == Some(id)); }
        }
    }
}

pub(super) proof fn attach_keeps_coherent<I: Copy>(
    links: Map<I, Links<I>>, parent: I, node: I, previous: Option<I>, next: Option<I>,
)
    requires coherent(links), valid_gap(links, parent, node, previous, next),
    ensures coherent(spliced(links, parent, node, previous, next, true)),
{
    let after = spliced(links, parent, node, previous, next, true);
    splice_fields(links, parent, node, previous, next, true);
    assert forall |id: I| #[trigger] after.contains_key(id) implies coherent_at(after, id) by {
        attach_keeps_endpoints(links, parent, node, previous, next, id);
        attach_keeps_positions(links, parent, node, previous, next, id);
    }
}


proof fn cut_keeps_endpoints<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I, id: I)
    requires coherent(links), child(links, parent, node), links.contains_key(id),
        distinct_gap(parent, node, links[node].previous, links[node].next),
    ensures ({
        let after = spliced(links, parent, node, links[node].previous, links[node].next, false);
        endpoints(after, id)
    }),
{
    let previous = links[node].previous;
    let next = links[node].next;
    let after = spliced(links, parent, node, previous, next, false);
    splice_fields(links, parent, node, previous, next, false);
    assert(coherent_at(links, node) && coherent_at(links, id));
    if id == parent {
        if let Some(first) = links[id].first {
            assert(child(links, id, first) && links[first].previous.is_none());
        }
        if let Some(last) = links[id].last {
            assert(child(links, id, last) && links[last].next.is_none());
        }
        match (previous, next) {
            (None, None) => {},
            (Some(p), None) => {
                assert(links[p].next == Some(node));
            },
            (None, Some(n)) => {
                assert(links[n].previous == Some(node));
            },
            (Some(_), Some(_)) => {},
        }
    } else if let (Some(first), Some(last)) = (links[id].first, links[id].last) {
        assert(child(links, id, first) && child(links, id, last));
        assert(first != node && last != node);
        assert(previous != Some(last) && next != Some(first));
        assert(after[first].previous.is_none() && after[last].next.is_none());
    }
}

proof fn cut_keeps_positions<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I, id: I)
    requires coherent(links), child(links, parent, node), links.contains_key(id),
        distinct_gap(parent, node, links[node].previous, links[node].next),
    ensures ({
        let after = spliced(links, parent, node, links[node].previous, links[node].next, false);
        position(after, id)
    }),
{
    let previous = links[node].previous;
    let next = links[node].next;
    let after = spliced(links, parent, node, previous, next, false);
    splice_fields(links, parent, node, previous, next, false);
    assert(coherent_at(links, node) && coherent_at(links, id));
    if id != node {
        if let Some(owner) = links[id].parent {
            assert(child(links, owner, id));
            if let Some(prev) = links[id].previous {
                assert(child(links, owner, prev) && links[prev].next == Some(id));
                if prev == node { assert(next == Some(id)); }
                if previous == Some(prev) { assert(id == node); }
            }
            if let Some(following) = links[id].next {
                assert(child(links, owner, following) && links[following].previous == Some(id));
                if following == node { assert(previous == Some(id)); }
                if next == Some(following) { assert(id == node); }
            }
        }
    }
}

pub(super) proof fn detach_keeps_coherent<I: Copy>(links: Map<I, Links<I>>, parent: I, node: I)
    requires coherent(links), child(links, parent, node),
        distinct_gap(parent, node, links[node].previous, links[node].next),
    ensures coherent(spliced(links, parent, node, links[node].previous, links[node].next, false)),
{
    let previous = links[node].previous;
    let next = links[node].next;
    let after = spliced(links, parent, node, previous, next, false);
    splice_fields(links, parent, node, previous, next, false);
    assert forall |id: I| #[trigger] after.contains_key(id) implies coherent_at(after, id) by {
        cut_keeps_endpoints(links, parent, node, id);
        cut_keeps_positions(links, parent, node, id);
    }
}


/// SlotMap insertion contributes one empty detached position. Existing
/// reciprocal fields continue to refer only to the surviving keys.
pub(super) proof fn insert_empty_keeps_coherent<I>(links: Map<I, Links<I>>, fresh: I)
    requires coherent(links), !links.contains_key(fresh),
    ensures coherent(links.insert(fresh, preorder::leaf())),
{
    let after = links.insert(fresh, preorder::leaf());
    assert forall |id: I| #[trigger] after.contains_key(id) implies coherent_at(after, id) by {
        if id != fresh {
            assert(coherent_at(links, id));
            let at = links[id];
            if let Some(owner) = at.parent {
                assert(owner != fresh);
                if let Some(prev) = at.previous { assert(prev != fresh); }
                if let Some(next) = at.next { assert(next != fresh); }
            }
            if let (Some(first), Some(last)) = (at.first, at.last) {
                assert(first != fresh && last != fresh);
            }
        }
    }
}

pub(in crate::removal) open spec fn keep_entries<I>(links: Map<I, Links<I>>, keep: Set<I>) -> Map<I, Links<I>> {
    Map::new(links.dom().intersect(keep), |id: I| links[id])
}

/// After a subtree root is detached, a retirement that removes the whole
/// component keeps both directions of every surviving child relationship.
pub(super) proof fn retire_component_keeps_coherent<I>(links: Map<I, Links<I>>, keep: Set<I>)
    requires coherent(links),
        forall |id: I| links.contains_key(id) && (#[trigger] links[id]).parent.is_some() ==>
            keep.contains(id) == keep.contains(links[id].parent.unwrap()),
    ensures coherent(keep_entries(links, keep)),
{
    let after = keep_entries(links, keep);
    assert forall |id: I| #[trigger] after.contains_key(id) implies coherent_at(after, id) by {
        assert(coherent_at(links, id));
        let at = links[id];
        if let Some(owner) = at.parent {
            assert(keep.contains(owner) && after.contains_key(owner));
            if let Some(prev) = at.previous { assert(links[prev].parent == Some(owner) && keep.contains(prev)); }
            if let Some(next) = at.next { assert(links[next].parent == Some(owner) && keep.contains(next)); }
        }
        if let (Some(first), Some(last)) = (at.first, at.last) {
            assert(links[first].parent == Some(id) && links[last].parent == Some(id));
            assert(keep.contains(first) && keep.contains(last));
        }
    }
}


proof fn detach_for_retirement<I: Copy>(
    links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I,
    detached: Map<I, Links<I>>,
)
    requires coherent(links), child(links, parent, node), before.ordered(),
        before == preorder::order(links, before.interval, before.depth),
        detached == spliced(links, parent, node, links[node].previous, links[node].next, false),
    ensures coherent(detached), detached.dom() == links.dom(),
        forall |id: I| detached.contains_key(id) ==> (#[trigger] detached[id]).parent ==
            if id == node { None } else { links[id].parent },
{
    let prev = links[node].previous;
    let next = links[node].next;
    branch_gap_from_links(links, before, parent, node);
    assert(distinct_gap(parent, node, prev, next));
    splice_fields(links, parent, node, prev, next, false);
    detach_keeps_coherent(links, parent, node);
}

proof fn keep_follows_parent<I>(before: Order<I>, detached: Map<I, Links<I>>, keep: Set<I>, node: I)
    requires before.ordered(), before.closed_subtrees(), (before.live)(node),
        forall |id: I| #[trigger] detached.contains_key(id) == (before.live)(id),
        forall |id: I| #[trigger] keep.contains(id) == ((before.live)(id) && !before.inside(node, id)),
        forall |id: I| detached.contains_key(id) && (#[trigger] detached[id]).parent.is_some() ==>
            id != node && (before.parent)(id) == detached[id].parent,
    ensures forall |id: I| detached.contains_key(id) && (#[trigger] detached[id]).parent.is_some() ==>
        keep.contains(id) == keep.contains(detached[id].parent.unwrap()),
{
    assert forall |id: I| detached.contains_key(id) && (#[trigger] detached[id]).parent.is_some() implies
        keep.contains(id) == keep.contains(detached[id].parent.unwrap()) by {
        let owner = detached[id].parent.unwrap();
        before.node_facts(id);
        assert(id != node && before.child(owner, id) && (before.live)(owner));
        if before.inside(node, id) {
            assert(before.inside(node, owner));
        } else if before.inside(node, owner) {
            assert(before.inside(node, id));
        }
    }
}

/// The physical splice disconnects the old preorder interval at exactly
/// its root parent edge. Retiring that interval preserves reciprocity.
pub(in crate::removal) proof fn retired_branch_keeps_coherent<I: Copy>(
    links: Map<I, Links<I>>, before: Order<I>, parent: I, node: I,
)
    requires coherent(links), child(links, parent, node), before.ordered(), before.closed_subtrees(),
        before == preorder::order(links, before.interval, before.depth),
    ensures coherent(preorder::without_branch(links, before, parent, node)),
{
    let detached = spliced(links, parent, node, links[node].previous, links[node].next, false);
    let keep = links.dom().filter(|id: I| !before.inside(node, id));
    detach_for_retirement(links, before, parent, node, detached);
    assert forall |id: I| detached.contains_key(id) && (#[trigger] detached[id]).parent.is_some() implies
        id != node && (before.parent)(id) == detached[id].parent by {
        assert(links.contains_key(id));
    }
    keep_follows_parent(before, detached, keep, node);
    retire_component_keeps_coherent(detached, keep);
    assert(preorder::without_branch(links, before, parent, node) =~= keep_entries(detached, keep));
}

}
