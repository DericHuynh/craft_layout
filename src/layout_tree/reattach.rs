//! Translate the detached preorder interval into the selected child-list gap.
use super::*;

verus! {

#[verifier::reject_recursive_types(I)]
struct Gap<I> {
    survivors: Order<I>,
    branch: Order<I>,
    moved: I,
    destination: I,
    sibling: Option<I>,
}

impl<I> Gap<I> {
    spec fn valid(self) -> bool {
        &&& valid(self.survivors) && valid(self.branch)
        &&& (self.survivors.live)(self.destination)
        &&& self.sibling.is_some() ==> self.survivors.child(self.destination, self.sibling.unwrap())
        &&& (self.branch.live)(self.moved)
        &&& forall|id: I| #[trigger] (self.branch.live)(id) ==> self.branch.inside(self.moved, id)
            && !(self.survivors.live)(id)
    }

    spec fn cut(self) -> nat {
        match self.sibling {
            Some(sibling) => (self.survivors.interval)(sibling).0,
            None => (self.survivors.interval)(self.destination).1,
        }
    }
    spec fn start(self) -> nat { (self.branch.interval)(self.moved).0 }
    spec fn end(self) -> nat { (self.branch.interval)(self.moved).1 }
    spec fn width(self) -> nat { (self.end() - self.start()) as nat }

    spec fn extended_end(self, id: I) -> bool {
        let end = (self.survivors.interval)(id).1;
        end > self.cut() || end == self.cut() && self.survivors.inside(id, self.destination)
    }

    spec fn interval(self, id: I) -> (nat, nat) {
        if (self.branch.live)(id) {
            let (start, end) = (self.branch.interval)(id);
            (self.cut() + (start - self.start()) as nat, self.cut() + (end - self.start()) as nat)
        } else {
            let (start, end) = (self.survivors.interval)(id);
            (if self.cut() <= start { start + self.width() } else { start },
             if self.extended_end(id) { end + self.width() } else { end })
        }
    }

    spec fn depth(self, id: I) -> nat {
        if (self.branch.live)(id) {
            (self.survivors.depth)(self.destination) + 1
                + ((self.branch.depth)(id) - (self.branch.depth)(self.moved)) as nat
        } else { (self.survivors.depth)(id) }
    }

    spec fn order_at(self, links: Map<I, Links<I>>) -> Order<I> {
        order(links, |id: I| self.interval(id), |id: I| self.depth(id))
    }
}

proof fn branch_depth<I>(branch: Order<I>, moved: I, id: I)
    requires branch.ordered(), branch.closed_subtrees(), (branch.live)(moved), branch.inside(moved, id),
    ensures (branch.depth)(moved) <= (branch.depth)(id),
    decreases (branch.depth)(id),
{
    if id != moved {
        assert((branch.parent)(id).is_some());
        let owner = (branch.parent)(id).unwrap();
        assert(branch.inside(moved, owner) && branch.child(owner, id));
        branch_depth(branch, moved, owner);
    }
}

proof fn prior_intervals<I>(gap: Gap<I>, a: I, b: I)
    requires gap.valid(), (gap.survivors.live)(a), (gap.survivors.live)(b),
    ensures ({
        let aa = gap.interval(a);
        let bb = gap.interval(b);
        let before = gap.survivors;
        let (al, ah) = (before.interval)(a);
        let (bl, bh) = (before.interval)(b);
        &&& aa.0 < aa.1 && bb.0 < bb.1
        &&& (al < bl) == (aa.0 < bb.0) && (al == bl) == (aa.0 == bb.0)
        &&& (al <= bl && bh <= ah) == (aa.0 <= bb.0 && bb.1 <= aa.1)
        &&& (ah <= bl) == (aa.1 <= bb.0)
    }),
{
    gap.survivors.node_facts(a);
    gap.survivors.node_facts(b);
    gap.branch.node_facts(gap.moved);
    let before = gap.survivors;
    let (al, ah) = (before.interval)(a);
    let (bl, bh) = (before.interval)(b);
    if al <= bl && ah == bh && ah == gap.cut() && before.inside(b, gap.destination) {
        assert(before.inside(a, gap.destination));
        assert(gap.extended_end(a));
    }
}

proof fn branch_intervals<I>(gap: Gap<I>, a: I, b: I)
    requires gap.valid(), (gap.branch.live)(a), (gap.branch.live)(b),
    ensures ({
        let aa = gap.interval(a);
        let bb = gap.interval(b);
        let before = gap.branch;
        let (al, ah) = (before.interval)(a);
        let (bl, bh) = (before.interval)(b);
        &&& gap.cut() <= aa.0 < aa.1 <= gap.cut() + gap.width()
        &&& gap.cut() <= bb.0 < bb.1 <= gap.cut() + gap.width()
        &&& (al < bl) == (aa.0 < bb.0) && (al == bl) == (aa.0 == bb.0)
        &&& (ah <= bh) == (aa.1 <= bb.1) && (ah <= bl) == (aa.1 <= bb.0)
        &&& ((before.depth)(a) < (before.depth)(b)) == (gap.depth(a) < gap.depth(b))
    }),
{
    branch_depth(gap.branch, gap.moved, a);
    branch_depth(gap.branch, gap.moved, b);
}

proof fn mixed_intervals<I>(gap: Gap<I>, exterior: I, moved: I)
    requires gap.valid(), (gap.survivors.live)(exterior), (gap.branch.live)(moved),
    ensures ({
        let outside = gap.interval(exterior);
        let inside = gap.interval(moved);
        &&& outside.0 != inside.0
        &&& (outside.0 <= inside.0 && inside.1 <= outside.1) == gap.survivors.inside(exterior, gap.destination)
        &&& !(inside.0 <= outside.0 && outside.1 <= inside.1)
        &&& outside.1 <= inside.0 || inside.1 <= outside.0 || outside.0 < inside.0 && inside.1 <= outside.1
    }),
{
    let before = gap.survivors;
    let cut = gap.cut();
    let (start, end) = (before.interval)(exterior);
    branch_intervals(gap, moved, moved);
    before.node_facts(exterior);
    if start < cut && cut < end {
        assert(preorder::partitioned(before));
        if let Some(sibling) = gap.sibling {
            assert(exterior != sibling);
            assert((before.live)(sibling));
            assert(before.inside(exterior, sibling));
            assert(before.inside(exterior, gap.destination));
        } else if exterior != gap.destination {
            assert(!before.inside(gap.destination, exterior));
            assert(before.inside(exterior, gap.destination));
        } else {
            assert(before.inside(exterior, gap.destination));
        }
    }
    if before.inside(exterior, gap.destination) {
        assert(start < cut && cut <= end);
        if gap.sibling.is_some() {
            assert(cut < end);
        }
        assert(gap.extended_end(exterior));
    }
    if start >= cut {
        assert(gap.interval(moved).1 <= gap.interval(exterior).0);
    } else if !before.inside(exterior, gap.destination) {
        assert(!gap.extended_end(exterior));
        assert(gap.interval(exterior).1 <= gap.interval(moved).0);
    }
}

proof fn old_child<I>(gap: Gap<I>, after: Order<I>, parent: I, node: I, internal: bool)
    requires gap.valid(),
        (after.live)(node), (after.parent)(node) == Some(parent),
        (after.interval)(parent) == gap.interval(parent), (after.interval)(node) == gap.interval(node),
        (after.depth)(parent) == gap.depth(parent), (after.depth)(node) == gap.depth(node),
        if internal { (gap.branch.live)(parent) && gap.branch.child(parent, node) }
        else { (gap.survivors.live)(parent) && gap.survivors.child(parent, node) },
    ensures after.child(parent, node),
{
    if internal {
        branch_intervals(gap, parent, node);
    } else {
        prior_intervals(gap, parent, node);
    }
}

proof fn no_cross_rank<I>(gap: Gap<I>, after: Order<I>, a: I, b: I)
    requires gap.valid(), (after.live)(a), (after.live)(b),
        (after.interval)(a) == gap.interval(a), (after.interval)(b) == gap.interval(b),
        (gap.branch.live)(a) || (gap.survivors.live)(a),
        (gap.branch.live)(b) || (gap.survivors.live)(b),
    ensures
        after.inside(a, b) == (if (gap.branch.live)(a) {
            (gap.branch.live)(b) && gap.branch.inside(a, b)
        } else if (gap.branch.live)(b) {
            gap.survivors.inside(a, gap.destination)
        } else {
            gap.survivors.inside(a, b)
        }),
{
    if (gap.branch.live)(a) {
        if (gap.branch.live)(b) {
            branch_intervals(gap, a, b);
        } else { mixed_intervals(gap, b, a); }
    } else if (gap.branch.live)(b) {
        mixed_intervals(gap, a, b);
    } else {
        prior_intervals(gap, a, b);
    }
}


spec fn reattached_links<I>(gap: Gap<I>, after: Order<I>, previous: Option<I>) -> bool {
    &&& previous.is_some() ==> gap.survivors.child(gap.destination, previous.unwrap())
        && (gap.survivors.sibling)(previous.unwrap()) == gap.sibling
    &&& forall|id: I| #[trigger] (after.live)(id) == ((gap.branch.live)(id) || (gap.survivors.live)(id))
    &&& forall|id: I| #[trigger] (after.live)(id) ==> {
        let prior = if (gap.branch.live)(id) { gap.branch } else { gap.survivors };
        &&& (after.parent)(id) == if id == gap.moved { Some(gap.destination) } else { (prior.parent)(id) }
        &&& (after.first)(id) == if id == gap.destination && previous.is_none() { Some(gap.moved) } else { (prior.first)(id) }
        &&& (after.sibling)(id) == if id == gap.moved { gap.sibling }
            else if previous == Some(id) { Some(gap.moved) } else { (prior.sibling)(id) }
        &&& (after.interval)(id) == gap.interval(id)
        &&& (after.depth)(id) == gap.depth(id)
    }
}

proof fn moved_root_order<I>(gap: Gap<I>, after: Order<I>, previous: Option<I>)
    requires gap.valid(), reattached_links(gap, after, previous),
    ensures after.child(gap.destination, gap.moved),
        gap.interval(gap.moved) == (gap.cut(), gap.cut() + gap.width()),
        gap.sibling.is_some() ==> after.child(gap.destination, gap.sibling.unwrap())
            && (after.interval)(gap.sibling.unwrap()).0 == gap.cut() + gap.width(),
{
    gap.branch.node_facts(gap.moved);
    assert((after.live)(gap.moved) && (after.live)(gap.destination));
    mixed_intervals(gap, gap.destination, gap.moved);
    if let Some(sibling) = gap.sibling {
        assert((after.live)(sibling));
        old_child(gap, after, gap.destination, sibling, false);
    }
}

proof fn ordered_record<I>(gap: Gap<I>, after: Order<I>, previous: Option<I>, id: I)
    requires gap.valid(), reattached_links(gap, after, previous), (after.live)(id),
    ensures {
        &&& (after.interval)(id).0 < (after.interval)(id).1
        &&& match (after.first)(id) { Some(kid) => after.child(id, kid), None => true }
        &&& match (after.parent)(id) {
            Some(owner) => (after.live)(owner) && after.child(owner, id) && match (after.sibling)(id) {
                Some(next) => after.child(owner, next) && (after.interval)(id).1 <= (after.interval)(next).0,
                None => true,
            },
            None => (after.sibling)(id).is_none(),
        }
    },
{
    moved_root_order(gap, after, previous);
    let internal = (gap.branch.live)(id);
    let prior = if internal { gap.branch } else { gap.survivors };
    prior.node_facts(id);
    if internal { branch_intervals(gap, id, id); } else { prior_intervals(gap, id, id); }
    if let Some(kid) = (after.first)(id) {
        if id == gap.destination && previous.is_none() {
            assert(kid == gap.moved);
        } else {
            assert((prior.first)(id) == Some(kid));
            assert((prior.live)(kid) && (after.live)(kid));
            if internal {
                assert((prior.interval)(kid).0 > (prior.interval)(id).0 >= gap.start());
                assert(kid != gap.moved);
            }
            old_child(gap, after, id, kid, internal);
        }
    }
    if id != gap.moved {
        if let Some(owner) = (after.parent)(id) {
            assert((prior.parent)(id) == Some(owner));
            assert((prior.live)(owner) && (after.live)(owner) && prior.child(owner, id));
            old_child(gap, after, owner, id, internal);
            if let Some(next) = (after.sibling)(id) {
                if previous == Some(id) {
                    assert(!internal && owner == gap.destination && next == gap.moved);
                    assert((prior.sibling)(id) == gap.sibling);
                    assert(!(prior.inside(id, gap.destination)));
                    assert((prior.interval)(id).1 <= gap.cut());
                    assert(!gap.extended_end(id));
                } else {
                    assert((prior.sibling)(id) == Some(next));
                    assert((prior.live)(next) && (after.live)(next));
                    if internal {
                        branch_intervals(gap, id, next);
                        assert((prior.interval)(next).0 >= (prior.interval)(id).1 > gap.start());
                        assert(next != gap.moved);
                    } else { prior_intervals(gap, id, next); }
                    old_child(gap, after, owner, next, internal);
                }
            }
        } else {
            assert(previous != Some(id));
        }
    }
}

proof fn ordered_after_join<I>(gap: Gap<I>, after: Order<I>, previous: Option<I>)
    requires gap.valid(), reattached_links(gap, after, previous),
    ensures after.ordered(),
{
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
        ordered_record(gap, after, previous, id);
    }
}

proof fn closed_record<I>(gap: Gap<I>, after: Order<I>, previous: Option<I>, root: I, id: I)
    requires gap.valid(), reattached_links(gap, after, previous),
        after.inside(root, id), (after.live)(root), root != id,
    ensures {
        &&& (after.parent)(id).is_some() && after.inside(root, (after.parent)(id).unwrap())
        &&& (after.sibling)(id).is_some() ==> after.inside(root, (after.sibling)(id).unwrap())
    },
{
    no_cross_rank(gap, after, root, id);
    if id == gap.moved {
        if (gap.branch.live)(root) {
            assert(preorder::partitioned(gap.branch));
            assert((gap.branch.interval)(root).0 != (gap.branch.interval)(id).0);
            assert(false);
        }
        assert(gap.survivors.inside(root, gap.destination));
        no_cross_rank(gap, after, root, gap.destination);
        if let Some(sibling) = gap.sibling {
            assert(gap.survivors.inside(root, sibling));
            assert((after.live)(sibling));
            no_cross_rank(gap, after, root, sibling);
        }
    } else if (gap.branch.live)(id) {
        assert(gap.branch.inside(gap.moved, id));
        assert((gap.branch.parent)(id).is_some());
        let owner = (gap.branch.parent)(id).unwrap();
        assert(gap.branch.inside(gap.moved, owner));
        if (gap.branch.live)(root) { assert(gap.branch.inside(root, owner)); }
        no_cross_rank(gap, after, root, owner);
        if let Some(next) = (after.sibling)(id) {
            assert((gap.branch.sibling)(id) == Some(next));
            assert(gap.branch.inside(gap.moved, next));
            if (gap.branch.live)(root) { assert(gap.branch.inside(root, next)); }
            assert((after.live)(next));
            no_cross_rank(gap, after, root, next);
        }
    } else {
        assert((gap.survivors.live)(root) && gap.survivors.inside(root, id));
        assert((gap.survivors.parent)(id).is_some());
        let owner = (gap.survivors.parent)(id).unwrap();
        assert(gap.survivors.inside(root, owner) && (after.live)(owner));
        no_cross_rank(gap, after, root, owner);
        if let Some(next) = (after.sibling)(id) {
            if previous == Some(id) {
                assert(owner == gap.destination && next == gap.moved);
            } else {
                assert((gap.survivors.sibling)(id) == Some(next));
                assert(gap.survivors.inside(root, next));
            }
            assert((after.live)(next));
            no_cross_rank(gap, after, root, next);
        }
    }
}

proof fn closed_after_join<I>(gap: Gap<I>, after: Order<I>, previous: Option<I>)
    requires gap.valid(), reattached_links(gap, after, previous),
    ensures after.closed_subtrees(),
{
    assert forall |root: I, id: I| #[trigger] after.inside(root, id) && (after.live)(root) && root != id implies {
        &&& (after.parent)(id).is_some() && after.inside(root, (after.parent)(id).unwrap())
        &&& (after.sibling)(id).is_some() ==> after.inside(root, (after.sibling)(id).unwrap())
    } by {
        closed_record(gap, after, previous, root, id);
    }
}

proof fn partition_after_join<I>(gap: Gap<I>, after: Order<I>, previous: Option<I>)
    requires gap.valid(), reattached_links(gap, after, previous),
    ensures preorder::partitioned(after),
{
    assert forall |a: I, b: I| #[trigger] (after.live)(a) && #[trigger] (after.live)(b) && a != b implies {
        let al = (after.interval)(a);
        let bl = (after.interval)(b);
        &&& al.0 != bl.0
        &&& al.1 <= bl.0 || bl.1 <= al.0 || after.inside(a, b) || after.inside(b, a)
    } by {
        no_cross_rank(gap, after, a, b);
        no_cross_rank(gap, after, b, a);
        if (gap.branch.live)(a) {
            if (gap.branch.live)(b) {
                assert(preorder::partitioned(gap.branch));
                branch_intervals(gap, a, b);
                branch_intervals(gap, b, a);
            } else { mixed_intervals(gap, b, a); }
        } else if (gap.branch.live)(b) {
            mixed_intervals(gap, a, b);
        } else {
            assert(preorder::partitioned(gap.survivors));
            prior_intervals(gap, a, b);
            prior_intervals(gap, b, a);
        }
    }
}



pub(in crate::removal::links) open spec fn admitted<I>(links: Map<I, Links<I>>, before: Order<I>, moved: I, destination: I, sibling: Option<I>) -> bool {
    &&& links.contains_key(destination) && !before.inside(moved, destination)
    &&& match sibling {
        Some(next) => child(links, destination, next) && !before.inside(moved, next),
        None => true,
    }
}

pub(in crate::removal) open spec fn preceding<I>(links: Map<I, Links<I>>, destination: I, sibling: Option<I>) -> Option<I> {
    match sibling {
        Some(next) => links[next].previous,
        None => links[destination].last,
    }
}

spec fn destination_gap<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, source: I,
    moved: I, destination: I, sibling: Option<I>) -> Gap<I>
{
    Gap {
        survivors: order(without_branch(links, before, source, moved), before.interval, before.depth),
        branch: order(component(links, before, source, moved), before.interval, before.depth),
        moved, destination, sibling,
    }
}

pub(in crate::removal) open spec fn moved_links<I: Copy>(links: Map<I, Links<I>>, source: I, moved: I, destination: I, sibling: Option<I>)
    -> Map<I, Links<I>>
{
    let detached = detach_table(links, source, moved);
    spliced(detached, destination, moved, preceding(detached, destination, sibling), sibling, true)
}

pub(in crate::removal) closed spec fn moved_order<I: Copy>(links: Map<I, Links<I>>, before: Order<I>,
    source: I, moved: I, destination: I, sibling: Option<I>) -> Order<I>
{
    destination_gap(links, before, source, moved, destination, sibling)
        .order_at(moved_links(links, source, moved, destination, sibling))
}

proof fn model_splice<I: Copy>(gap: Gap<I>, exterior: Map<I, Links<I>>,
    branch: Map<I, Links<I>>, detached: Map<I, Links<I>>, previous: Option<I>)
    requires
        gap.valid(),
        gap.survivors == order(exterior, gap.survivors.interval, gap.survivors.depth),
        gap.branch == order(branch, gap.branch.interval, gap.branch.depth),
        exterior.dom().disjoint(branch.dom()), detached == exterior.union_prefer_right(branch),
        coherence::valid_gap(detached, gap.destination, gap.moved, previous, gap.sibling),
        previous.is_some() ==> gap.survivors.child(gap.destination, previous.unwrap())
            && (gap.survivors.sibling)(previous.unwrap()) == gap.sibling,
    ensures ({
        let joined = spliced(detached, gap.destination, gap.moved, previous, gap.sibling, true);
        reattached_links(gap, gap.order_at(joined), previous)
    }),
{
    let joined = spliced(detached, gap.destination, gap.moved, previous, gap.sibling, true);
    let after = gap.order_at(joined);
    coherence::splice_fields(detached, gap.destination, gap.moved, previous, gap.sibling, true);
    assert forall|id: I| #[trigger] (after.live)(id) == ((gap.branch.live)(id) || (gap.survivors.live)(id)) by {
        assert(branch.contains_key(id) || exterior.contains_key(id) <==> detached.contains_key(id));
    }
    assert forall|id: I| #[trigger] (after.live)(id) implies {
        let prior = if (gap.branch.live)(id) { gap.branch } else { gap.survivors };
        &&& (after.parent)(id) == if id == gap.moved { Some(gap.destination) } else { (prior.parent)(id) }
        &&& (after.first)(id) == if id == gap.destination && previous.is_none() { Some(gap.moved) } else { (prior.first)(id) }
        &&& (after.sibling)(id) == if id == gap.moved { gap.sibling }
            else if previous == Some(id) { Some(gap.moved) } else { (prior.sibling)(id) }
        &&& (after.interval)(id) == gap.interval(id)
        &&& (after.depth)(id) == gap.depth(id)
    } by {
        assert(joined.contains_key(id) && detached.contains_key(id));
        if branch.contains_key(id) {
            assert(branch[id] == detached[id]);
        } else {
            assert(exterior.contains_key(id) && exterior[id] == detached[id]);
        }
    }
}

proof fn destination_is_live<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, source: I,
    moved: I, destination: I, sibling: Option<I>)
    requires
        before == order(links, before.interval, before.depth), valid(before), coherent(links),
        child(links, source, moved), admitted(links, before, moved, destination, sibling),
        coherent(detach_table(links, source, moved)),
    ensures ({
        let detached = detach_table(links, source, moved);
        let previous = preceding(detached, destination, sibling);
        &&& detached.contains_key(sibling.unwrap_or(destination))
        &&& coherence::valid_gap(detached, destination, moved, previous, sibling)
        &&& destination_gap(links, before, source, moved, destination, sibling).valid()
    }),
{
    let detached = detach_table(links, source, moved);
    let gap = destination_gap(links, before, source, moved, destination, sibling);
    detach_preserves_ranks(links, before, source, moved);
    cut_outside_branch(links, before, source, moved);
    coherence::splice_fields(links, source, moved, links[moved].previous, links[moved].next, false);
    before.node_facts(moved);
    assert(before.inside(moved, moved));
    assert(destination != moved);
    if let Some(next) = sibling {
        assert(next != moved);
        assert(child(detached, destination, next));
        coherence::before_child_gap(detached, destination, moved, next);
        assert((before.live)(destination) && (before.live)(next));
        assert(before.child(destination, next));
        assert(gap.survivors.child(destination, next));
    } else {
        assert(detached.contains_key(destination));
        coherence::final_child_gap(detached, destination, moved);
        assert((before.live)(destination));
        assert((gap.survivors.live)(destination));
    }
    assert((gap.branch.live)(moved));
    assert forall|id: I| #[trigger] (gap.branch.live)(id) implies
        gap.branch.inside(moved, id) && !(gap.survivors.live)(id) by {
        assert(before.inside(moved, id));
    }
}

proof fn previous_is_in_exterior<I: Copy>(gap: Gap<I>, exterior: Map<I, Links<I>>,
    branch: Map<I, Links<I>>, detached: Map<I, Links<I>>, previous: I)
    requires
        gap.valid(),
        gap.survivors == order(exterior, gap.survivors.interval, gap.survivors.depth),
        gap.branch == order(branch, gap.branch.interval, gap.branch.depth),
        exterior.dom().disjoint(branch.dom()), detached == exterior.union_prefer_right(branch),
        coherence::valid_gap(detached, gap.destination, gap.moved, Some(previous), gap.sibling),
    ensures gap.survivors.child(gap.destination, previous),
        (gap.survivors.sibling)(previous) == gap.sibling,
{
    assert(child(detached, gap.destination, previous) && detached[previous].next == gap.sibling);
    assert(previous != gap.moved);
    if branch.contains_key(previous) {
        assert((gap.branch.live)(previous));
        assert(gap.branch.inside(gap.moved, previous));
        assert((gap.branch.parent)(previous) == Some(gap.destination));
        assert(gap.branch.inside(gap.moved, gap.destination));
        assert(false);
    }
    assert(exterior.contains_key(previous) && exterior[previous] == detached[previous]);
    assert((gap.survivors.live)(previous) && (gap.survivors.parent)(previous) == Some(gap.destination));
}

proof fn physical_insertion<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, source: I,
    moved: I, destination: I, sibling: Option<I>)
    requires
        before == order(links, before.interval, before.depth), valid(before), coherent(links),
        child(links, source, moved), admitted(links, before, moved, destination, sibling),
        coherent(detach_table(links, source, moved)),
    ensures ({
        let detached = detach_table(links, source, moved);
        let previous = preceding(detached, destination, sibling);
        let joined = moved_links(links, source, moved, destination, sibling);
        let gap = destination_gap(links, before, source, moved, destination, sibling);
        &&& detached.contains_key(sibling.unwrap_or(destination)) && gap.valid()
        &&& coherence::valid_gap(detached, destination, moved, previous, sibling)
        &&& reattached_links(gap, gap.order_at(joined), previous)
    }),
{
    let detached = detach_table(links, source, moved);
    let previous = preceding(detached, destination, sibling);
    let gap = destination_gap(links, before, source, moved, destination, sibling);
    let exterior = without_branch(links, before, source, moved);
    let branch = component(links, before, source, moved);
    detach_preserves_ranks(links, before, source, moved);
    destination_is_live(links, before, source, moved, destination, sibling);
    if let Some(prev) = previous {
        previous_is_in_exterior(gap, exterior, branch, detached, prev);
    }
    model_splice(gap, exterior, branch, detached, previous);
}

pub(in crate::removal::links) proof fn joined_move_is_valid<I: Copy>(links: Map<I, Links<I>>, before: Order<I>, source: I,
    moved: I, destination: I, sibling: Option<I>)
    requires
        before == order(links, before.interval, before.depth), valid(before), coherent(links),
        child(links, source, moved), admitted(links, before, moved, destination, sibling),
        coherent(detach_table(links, source, moved)),
    ensures ({
        let detached = detach_table(links, source, moved);
        let previous = preceding(detached, destination, sibling);
        &&& detached.contains_key(sibling.unwrap_or(destination))
        &&& coherence::valid_gap(detached, destination, moved, previous, sibling)
        &&& valid(moved_order(links, before, source, moved, destination, sibling))
    }),
{
    physical_insertion(links, before, source, moved, destination, sibling);
    let gap = destination_gap(links, before, source, moved, destination, sibling);
    let joined = gap.order_at(moved_links(links, source, moved, destination, sibling));
    let previous = preceding(detach_table(links, source, moved), destination, sibling);
    ordered_after_join(gap, joined, previous);
    closed_after_join(gap, joined, previous);
    partition_after_join(gap, joined, previous);
}

fn saved_links<A: LinkStore>(arena: &A) -> (links: Ghost<Map<A::Id, Links<A::Id>>>)
    ensures links@ == arena.links(),
    no_unwind
{
    Ghost(arena.links())
}

/// Reattach any admitted subtree using the actual detach, record lookup,
/// and attach. The parent terminates the gap when no following sibling exists.
fn move_branch<A: LinkStore>(arena: &mut A, source: A::Id, moved: A::Id,
    destination: A::Id, sibling: Option<A::Id>, before: Ghost<Order<A::Id>>)
    requires
        before@ == order(old(arena).links(), before@.interval, before@.depth), valid(before@),
        coherent(old(arena).links()), child(old(arena).links(), source, moved),
        admitted(old(arena).links(), before@, moved, destination, sibling),
    ensures ({
        let links = old(arena).links();
        let joined = moved_links(links, source, moved, destination, sibling);
        let gap = destination_gap(links, before@, source, moved, destination, sibling);
        &&& final(arena).links() == joined
        &&& coherent(joined) && valid(gap.order_at(joined))
    }),
    no_unwind
{
    let prior = saved_links(arena);
    detach_for_move(arena, source, moved, before);
    proof { joined_move_is_valid(prior@, before@, source, moved, destination, sibling); }
    let target = sibling.unwrap_or(destination);
    let Some(position) = arena.read_links(target) else {
        proof { assert(false); }
        return;
    };
    let previous = if sibling.is_some() { position.previous } else { position.last };
    attach(arena, moved, destination, previous, sibling);
}

}
