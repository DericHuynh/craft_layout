//! Allocation-free removal of an owned detached subtree.
use vstd::prelude::*;
#[path = "../src/layout_tree/removal.rs"]
mod kernel;
#[path = "../src/layout_tree/links.rs"]
mod links;

verus! {

// Siblings are listed in the order the remover follows them, rightmost first.
pub enum Forest<I> {
    Empty,
    Node { id:I, children:Box<Forest<I>>, siblings:Box<Forest<I>> },
}

pub struct Record<I,V> {
    pub prev:Option<I>,
    pub first:Option<I>,
    pub last:Option<I>,
    // Includes the parent, next sibling and all other data preserved by a splice.
    pub payload:V,
}

pub type Store<I,V> = Map<I,Record<I,V>>;

pub open spec fn ids<I>(f:Forest<I>) -> Set<I>
    decreases f,
{
    match f {
        Forest::Empty => Set::empty(),
        Forest::Node{id,children,siblings} => ids(*children).union(ids(*siblings)).insert(id),
    }
}

pub open spec fn proper<I>(f:Forest<I>) -> bool
    decreases f,
{
    match f {
        Forest::Empty => true,
        Forest::Node{id,children,siblings} =>
            !ids(*children).contains(id) && !ids(*siblings).contains(id) && ids(*children).disjoint(ids(*siblings))
            && proper(*children) && proper(*siblings),
    }
}

pub open spec fn order<I>(f:Forest<I>) -> Seq<I>
    decreases f,
{
    match f {
        Forest::Empty => Seq::empty(),
        Forest::Node{id,children,siblings} => seq![id] + order(*children) + order(*siblings),
    }
}

pub open spec fn head<I>(f:Forest<I>, end:Option<I>) -> Option<I> {
    match f { Forest::Empty => end, Forest::Node{id,..} => Some(id) }
}

pub open spec fn oldest<I>(f:Forest<I>) -> Option<I>
    decreases f,
{
    match f {
        Forest::Empty => None,
        Forest::Node{id,siblings,..} => if *siblings is Empty {Some(id)} else {oldest(*siblings)},
    }
}

pub open spec fn stores<I,V>(s:Store<I,V>, f:Forest<I>, end:Option<I>) -> bool
    decreases f,
{
    match f {
        Forest::Empty => true,
        Forest::Node{id,children,siblings} => {
            &&& s.contains_key(id)
            &&& s[id].prev == head(*siblings,end)
            &&& s[id].first == oldest(*children)
            &&& s[id].last == head(*children,None)
            &&& stores(s,*children,None)
            &&& stores(s,*siblings,end)
        },
    }
}

pub open spec fn erase<I,V>(s:Store<I,V>, gone:Set<I>) -> Store<I,V> {
    Map::new(s.dom().difference(gone), |id:I| s[id])
}

proof fn local<I,V>(s:Store<I,V>, t:Store<I,V>, f:Forest<I>, end:Option<I>)
    requires stores(s,f,end),
        forall |id:I| #[trigger] ids(f).contains(id) ==> s.contains_key(id) && t.contains_key(id) && t[id] == s[id],
    ensures stores(t,f,end),
    decreases f,
{
    if let Forest::Node{id,children,siblings} = f {
        assert(ids(f).contains(id));
        assert(t.contains_key(id) && t[id] == s[id]);
        assert forall |j:I| #[trigger] ids(*children).contains(j) implies s.contains_key(j) && t.contains_key(j) && t[j]==s[j] by {
            assert(ids(f).contains(j));
        }
        assert forall |j:I| #[trigger] ids(*siblings).contains(j) implies s.contains_key(j) && t.contains_key(j) && t[j]==s[j] by {
            assert(ids(f).contains(j));
        }
        local(s,t,*children,None);
        local(s,t,*siblings,end);
        assert(stores(t,f,end));
    }
}

proof fn contains_records<I,V>(s:Store<I,V>, f:Forest<I>, end:Option<I>)
    requires stores(s,f,end),
    ensures forall |j:I| #[trigger] ids(f).contains(j) ==> s.contains_key(j),
    decreases f,
{
    if let Forest::Node{id,children,siblings} = f {
        contains_records(s,*children,None);
        contains_records(s,*siblings,end);
        assert forall |j:I| #[trigger] ids(f).contains(j) implies s.contains_key(j) by {
            if j == id {
                assert(s.contains_key(id));
            } else if ids(*children).contains(j) {
                assert(s.contains_key(j));
            } else {
                assert(ids(*siblings).contains(j));
            }
        }
    }
}

proof fn oldest_in_forest<I>(f:Forest<I>)
    ensures oldest(f).is_some() == !(f is Empty),
        oldest(f).is_some() ==> ids(f).contains(oldest(f).unwrap()),
    decreases f,
{
    if let Forest::Node{siblings,..} = f {oldest_in_forest(*siblings);}
}

pub open spec fn redirect<I,V>(s:Store<I,V>, id:I, end:Option<I>) -> Store<I,V> {
    s.insert(id,Record{prev:end,..s[id]})
}

// Only the leftmost sibling in this forest used to point to old. Replacing its
// prev link gives the entire forest a new successor at the end of its root list.
proof fn splice<I,V>(s:Store<I,V>, f:Forest<I>, old:Option<I>, end:Option<I>)
    requires stores(s,f,old), proper(f), !(f is Empty),
    ensures stores(redirect(s,oldest(f).unwrap(),end),f,end),
    decreases f,
{
    if let Forest::Node{id,children,siblings} = f {
        oldest_in_forest(*siblings);
        let at = oldest(f).unwrap();
        let updated = redirect(s,at,end);
        contains_records(s,*children,None);
        assert forall |j:I| #[trigger] ids(*children).contains(j) implies s.contains_key(j) && updated.contains_key(j) && updated[j] == s[j] by {
            assert(j != at);
        }
        local(s,updated,*children,None);
        if *siblings is Empty {
            assert(at == id);
            assert(updated[id].prev == end);
            assert(updated[id].first == s[id].first && updated[id].last == s[id].last);
        } else {
            assert(at == oldest(*siblings).unwrap());
            assert(ids(*siblings).contains(at));
            assert(at != id);
            splice(s,*siblings,old,end);
            assert(stores(updated,*siblings,end));
            assert(updated.contains_key(id) && updated[id] == s[id]);
        }
        assert(updated.contains_key(id));
        assert(updated[id].prev == head(*siblings,end)) by {
            assert(s[id].prev == head(*siblings,old));
            if let Forest::Node{id:next,..} = *siblings {
                assert(head(*siblings,old) == Some(next));
                assert(head(*siblings,end) == Some(next));
            }
        }
        assert(updated[id].first == oldest(*children));
        assert(updated[id].last == head(*children,None));
        assert(stores(updated,*children,None));
        assert(stores(updated,*siblings,end));
        assert(stores(updated,f,end));
    }
}

pub struct State<I,V> { pub cursor:Option<I>, pub nodes:Store<I,V> }

pub open spec fn pop<I,V>(s:State<I,V>, id:I) -> State<I,V> {
    let r = s.nodes[id];
    let rest = s.nodes.remove(id);
    match r.first {
        None => State {cursor:r.prev,nodes:rest},
        Some(first) => State {cursor:r.last,nodes:redirect(rest,first,r.prev)},
    }
}

pub open spec fn safe_pop<I,V>(s:State<I,V>, id:I) -> bool {
    &&& s.cursor == Some(id)
    &&& s.nodes.contains_key(id)
    &&& match s.nodes[id].first {
        Some(first) => first != id && s.nodes.contains_key(first),
        None => true,
    }
}

// A successful replay certifies the cursor at every step and the validity of
// both arena accesses (removal and the optional continuation splice).
pub open spec fn replay<I,V>(s:State<I,V>, plan:Seq<I>) -> Option<State<I,V>>
    decreases plan.len(),
{
    if plan.len() == 0 { Some(s) }
    else if safe_pop(s,plan.first()) { replay(pop(s,plan.first()),plan.drop_first()) }
    else { None }
}

proof fn replay_append<I,V>(s:State<I,V>, a:Seq<I>, b:Seq<I>, mid:State<I,V>)
    requires replay(s,a) == Some(mid),
    ensures replay(s,a+b) == replay(mid,b),
    decreases a.len(),
{
    if a.len() > 0 {
        assert((a+b).first() == a.first());
        assert((a+b).drop_first() =~= a.drop_first() + b);
        replay_append(pop(s,a.first()),a.drop_first(),b,mid);
    }
}

pub proof fn forest_replays<I,V>(s:Store<I,V>, f:Forest<I>, end:Option<I>)
    requires proper(f), stores(s,f,end),
    ensures replay(State{nodes:s,cursor:head(f,end)}, order(f))
        == Some(State{nodes:erase(s,ids(f)),cursor:end}),
    decreases f,
{
    if let Forest::Node{id,children,siblings} = f {
        let after = head(*siblings,end);
        let initial = State{nodes:s,cursor:Some(id)};
        let rest = s.remove(id);
        contains_records(s,*children,None);
        contains_records(s,*siblings,end);
        oldest_in_forest(*children);
        local(s,rest,*children,None);
        local(s,rest,*siblings,end);
        let next = pop(initial,id);
        if !(*children is Empty) {
            splice(rest,*children,None,after);
        }
        assert(safe_pop(initial,id));
        assert(stores(next.nodes,*children,after));
        assert(next.cursor == head(*children,after));
        forest_replays(next.nodes,*children,after);
        let after_children = erase(next.nodes,ids(*children));
        assert forall |j:I| #[trigger] ids(*siblings).contains(j) implies
            s.contains_key(j) && after_children.contains_key(j) && after_children[j] == s[j] by {
            assert(j != id && !ids(*children).contains(j));
        }
        local(s,after_children,*siblings,end);
        let mid = State{nodes:after_children,cursor:after};
        forest_replays(after_children,*siblings,end);
        replay_append(next,order(*children),order(*siblings),mid);
        assert(order(f).first() == id);
        assert(order(f).drop_first() =~= order(*children) + order(*siblings));
        assert(erase(after_children,ids(*siblings)) =~= erase(s,ids(f)));
    } else {
        assert(erase(s,ids(f)) =~= s);
    }
}

pub open spec fn detached<I>(id:I, children:Forest<I>) -> Forest<I> {
    Forest::Node{id,children:Box::new(children),siblings:Box::new(Forest::Empty)}
}

pub open spec fn valid_detachment<I, V>(arena: Store<I, V>, id: I, children: Forest<I>) -> bool {
    let forest = detached(id, children);
    proper(forest) && stores(arena, forest, None)
}

/// The owned single-payload path has no descendant or sibling continuation.
pub proof fn detached_leaf_needs_only_one_removal<I, V>(arena: Store<I, V>, id: I)
    requires arena.contains_key(id), arena[id].first.is_none(), arena[id].prev.is_none(),
    ensures replay(State { cursor: Some(id), nodes: arena }, seq![id])
        == Some(State { cursor: None, nodes: arena.remove(id) }),
{
    let before = State { cursor: Some(id), nodes: arena };
    let after = State { cursor: None, nodes: arena.remove(id) };
    let plan = seq![id];
    assert(safe_pop(before, plan.first()));
    assert(plan.drop_first().len() == 0);
    assert(pop(before, id) == after);
    reveal_with_fuel(replay, 2);
}
}

verus! {
    type Positions<I> = (Option<I>, Option<I>);

    closed spec fn removal_records<I>(links: Map<I, links::Links<I>>) -> Store<I, Positions<I>> {
        Map::new(links.dom(), |id: I| Record {
            prev: links[id].previous,
            first: links[id].first,
            last: links[id].last,
            payload: (links[id].parent, links[id].next),
        })
    }

    closed spec fn surviving_links<I>(records: Store<I, Positions<I>>) -> Map<I, links::Links<I>> {
        Map::new(records.dom(), |id: I| links::Links {
            parent: records[id].payload.0,
            previous: records[id].prev,
            next: records[id].payload.1,
            first: records[id].first,
            last: records[id].last,
        })
    }

    /// Combine the root splice used by `detach` with the reverse removal walk's
    /// exact output map. The caller's forest must enumerate the detached ranks.
    proof fn retired_branch_preserves_preorder<I: Copy>(
        before: Map<I, links::Links<I>>, parent: I, node: I,
        interval: spec_fn(I) -> (nat, nat), depth: spec_fn(I) -> nat,
        children: Forest<I>, after: Store<I, Positions<I>>,
    )
        requires
            links::preorder::valid(links::preorder::order(before, interval, depth)),
            links::coherence::coherent(before), links::coherence::child(before, parent, node),
            ids(detached(node, children)) == before.dom().filter(|id: I|
                links::preorder::order(before, interval, depth).inside(node, id)),
            after == erase(removal_records(links::set_gap(
                links::edited(before, node, links::Edit::Position(None, None, None)),
                parent, before[node].previous, before[node].next, None)), ids(detached(node, children))),
        ensures links::preorder::valid(links::preorder::order(surviving_links(after), interval, depth)),
            links::coherence::coherent(surviving_links(after)),
    {
        let prior = links::preorder::order(before, interval, depth);
        let edit = links::Edit::Position(None, None, None);
        let at = before[node];
        let spliced = links::set_gap(links::edited(before, node, edit), parent, at.previous, at.next, None);
        links::edit_keeps_keys(before, node, edit);
        links::set_gap_keeps_keys(links::edited(before, node, edit), parent, at.previous, at.next, None);
        let remaining = links::preorder::without_branch(before, prior, parent, node);
        assert(remaining.dom() =~= after.dom());
        assert(surviving_links(after) =~= remaining);
        links::coherence::branch_gap_from_links(before, prior, parent, node);
        links::preorder::remove_branch(before, parent, node, interval, depth);
        links::coherence::retired_branch_keeps_coherent(before, prior, parent, node);
    }

    /// Run the physical reverse retirement on the already-spliced root.
    fn retire_branch<I: Copy, A: kernel::DetachedNodes<Id=I, Payload=Positions<I>>>(
        arena: &mut A, parent: I, node: I,
        prior: Ghost<Map<I, links::Links<I>>>, interval: Ghost<spec_fn(I) -> (nat, nat)>,
        depth: Ghost<spec_fn(I) -> nat>,
    ) -> (complete: bool)
        requires
            links::preorder::valid(links::preorder::order(prior@, interval@, depth@)),
            links::coherence::coherent(prior@), links::coherence::child(prior@, parent, node),
            old(arena).records() == removal_records(links::coherence::spliced(
                prior@, parent, node, prior@[node].previous, prior@[node].next, false)),
        ensures complete,
            links::preorder::valid(links::preorder::order(surviving_links(final(arena).records()), interval@, depth@)),
            links::coherence::coherent(surviving_links(final(arena).records())),
        no_unwind
    {
        let children = certify_deletion_forest(prior, interval, depth, parent, node);
        let complete = kernel::remove_detached(arena, node, children);
        proof {
            retired_branch_preserves_preorder(prior@, parent, node, interval@, depth@, children@, arena.records());
        }
        complete
    }

}

verus! {
    use crate::prepare_frame::Order;

    spec fn reverse_rank<I>(before: Order<I>, id: I) -> (nat, nat) {
        let r = (before.interval)(id);
        (r.1, (r.1 - r.0) as nat)
    }

    spec fn earlier<I>(before: Order<I>, earlier: I, later: I) -> bool {
        let a = reverse_rank(before, earlier);
        let b = reverse_rank(before, later);
        a.0 < b.0 || a.0 == b.0 && a.1 < b.1
    }

    spec fn physical_forest<I>(links: Map<I, links::Links<I>>, before: Order<I>, node: I) -> Forest<I>
        decreases reverse_rank(before, node).0, reverse_rank(before, node).1,
    {
        let (last, previous) = (links[node].last, links[node].previous);
        Forest::Node { id: node,
            children: Box::new(match last {
                Some(child) if earlier(before, child, node) => physical_forest(links, before, child),
                _ => Forest::Empty,
            }),
            siblings: Box::new(match previous {
                Some(prev) if earlier(before, prev, node) => physical_forest(links, before, prev),
                _ => Forest::Empty,
            }),
        }
    }

    spec fn reverse_from<I>(links: Map<I, links::Links<I>>, before: Order<I>, node: Option<I>) -> Forest<I> {
        match node { Some(node) => physical_forest(links, before, node), None => Forest::Empty }
    }

    proof fn previous_and_last_are_earlier<I>(links: Map<I, links::Links<I>>, before: Order<I>, node: I)
        requires links::coherence::coherent(links), links.contains_key(node), before.ordered(),
            before == links::preorder::order(links, before.interval, before.depth),
        ensures
            links[node].previous.is_some() ==> earlier(before, links[node].previous.unwrap(), node),
            links[node].last.is_some() ==> earlier(before, links[node].last.unwrap(), node),
    {
        assert(links::coherence::coherent_at(links, node));
        assert((before.live)(node));
        before.node_facts(node);
        if let Some(prev) = links[node].previous {
            assert(links[prev].next == Some(node) && (before.live)(prev));
            before.node_facts(prev);
            assert((before.interval)(prev).1 <= (before.interval)(node).0);
        }
        if let Some(child) = links[node].last {
            assert((before.live)(child) && (before.parent)(child) == Some(node));
            assert(before.child(node, child));
            assert(reverse_rank(before, child).0 <= reverse_rank(before, node).0);
        }
    }

    proof fn unfold_physical_forest<I>(links: Map<I, links::Links<I>>, before: Order<I>, node: I)
        requires links[node].previous.is_some() ==> earlier(before, links[node].previous.unwrap(), node),
            links[node].last.is_some() ==> earlier(before, links[node].last.unwrap(), node),
        ensures physical_forest(links, before, node) == (Forest::Node { id: node,
            children: Box::new(reverse_from(links, before, links[node].last)),
            siblings: Box::new(reverse_from(links, before, links[node].previous)),
        }),
    {
        reveal_with_fuel(physical_forest, 1);
    }

    proof fn physical_forest_stores<I>(links: Map<I, links::Links<I>>, before: Order<I>, node: I)
        requires links::coherence::coherent(links), links.contains_key(node), before.ordered(),
            before == links::preorder::order(links, before.interval, before.depth),
        ensures ({
            let forest = physical_forest(links, before, node);
            &&& proper(forest)
            &&& stores(removal_records(links), forest, None)
            &&& links[node].parent.is_some() ==>
                oldest(forest) == links[links[node].parent.unwrap()].first
            &&& forall |id: I| #[trigger] ids(forest).contains(id) ==> {
                &&& (before.live)(id)
                &&& (before.interval)(id).1 <= (before.interval)(node).1
                &&& match links[node].parent {
                    Some(owner) => before.inside(owner, id) && (before.interval)(owner).0 < (before.interval)(id).0,
                    None => before.inside(node, id),
                }
            }
        }),
        decreases reverse_rank(before, node).0, reverse_rank(before, node).1,
    {
        let forest = physical_forest(links, before, node);
        let at = links[node];
        assert(links::coherence::coherent_at(links, node));
        previous_and_last_are_earlier(links, before, node);
        unfold_physical_forest(links, before, node);
        assert((before.live)(node));
        before.node_facts(node);
        let children = reverse_from(links, before, at.last);
        let siblings = reverse_from(links, before, at.previous);
        assert(forest == Forest::Node { id: node, children: Box::new(children), siblings: Box::new(siblings) });
        if let Some(child) = at.last {
            physical_forest_stores(links, before, child);
            assert(links[child].parent == Some(node) && oldest(children) == at.first);
            assert(head(children, None) == Some(child));
        }
        if let Some(prev) = at.previous {
            physical_forest_stores(links, before, prev);
            assert(links[prev].parent == at.parent);
            before.node_facts(prev);
            assert((before.interval)(prev).1 <= (before.interval)(node).0);
            assert(head(siblings,None) == Some(prev));
            assert(oldest(forest) == oldest(siblings));
        } else if let Some(owner) = at.parent {
            assert(links[owner].first == Some(node));
        }
        assert forall |id: I| #[trigger] ids(children).contains(id) implies
            before.inside(node, id) && (before.interval)(node).0 < (before.interval)(id).0 by {
            assert(at.last.is_some());
        }
        assert forall |id: I| #[trigger] ids(siblings).contains(id) implies
            (before.interval)(id).1 <= (before.interval)(node).0 by {
            assert(at.previous.is_some());
        }
        assert(ids(children).disjoint(ids(siblings)));
        assert(!ids(children).contains(node) && !ids(siblings).contains(node));
        assert(proper(children) && proper(siblings));
        reveal_with_fuel(proper, 2);
        assert(proper(forest));
        assert(stores(removal_records(links), children, None) && stores(removal_records(links), siblings, None));
        assert(removal_records(links).contains_key(node));
        assert(removal_records(links)[node].prev == head(siblings, None));
        assert(removal_records(links)[node].first == oldest(children));
        assert(removal_records(links)[node].last == head(children, None));
        reveal_with_fuel(stores, 2);
        assert(stores(removal_records(links), forest, None));
        assert forall |id: I| #[trigger] ids(forest).contains(id) implies {
            &&& (before.live)(id)
            &&& (before.interval)(id).1 <= (before.interval)(node).1
            &&& match at.parent {
                Some(owner) => before.inside(owner, id) && (before.interval)(owner).0 < (before.interval)(id).0,
                None => before.inside(node, id),
            }
        } by {
            if let Some(owner) = at.parent {
                assert((before.parent)(node) == Some(owner));
                assert(before.child(owner, node));
            }
        }
    }

    /// Following later siblings terminates at the actual parent's last child.
    /// Each reciprocal previous link includes the earlier forest in that tail.
    proof fn child_forest_reaches_tail<I>(links: Map<I, links::Links<I>>, before: Order<I>,
        owner: I, child: I, id: I,
    )
        requires links::coherence::coherent(links), before.ordered(), (before.live)(owner),
            before == links::preorder::order(links, before.interval, before.depth),
            before.child(owner, child), ids(physical_forest(links, before, child)).contains(id),
        ensures ids(reverse_from(links, before, links[owner].last)).contains(id),
        decreases ((before.interval)(owner).1 - (before.interval)(child).1) as nat,
    {
        assert(links::coherence::coherent_at(links, child));
        before.node_facts(child);
        if let Some(next) = links[child].next {
            assert(before.child(owner, next) && links[next].previous == Some(child));
            assert((before.interval)(child).1 <= (before.interval)(next).0);
            previous_and_last_are_earlier(links, before, next);
            unfold_physical_forest(links, before, next);
            assert(ids(physical_forest(links, before, next)).contains(id));
            child_forest_reaches_tail(links, before, owner, next, id);
        } else {
            assert(links[owner].last == Some(child));
        }
    }

    proof fn child_covers_inside<I>(before: Order<I>, root: I, id: I)
        requires before.ordered(), before.closed_subtrees(), (before.live)(root),
            id != root, before.inside(root, id),
        ensures exists |child: I| #[trigger] before.child(root, child) && before.inside(child, id),
        decreases (before.depth)(id),
    {
        assert((before.live)(id));
        assert((before.parent)(id).is_some());
        let parent = (before.parent)(id).unwrap();
        assert(before.child(parent, id) && before.inside(root, parent));
        if parent == root {
            assert(before.inside(id, id));
            assert(before.child(root, id));
        } else {
            child_covers_inside(before, root, parent);
            let child = choose |child: I| #[trigger] before.child(root, child) && before.inside(child, parent);
            assert(before.inside(child, id));
        }
    }

    proof fn child_rank_is_earlier<I>(before: Order<I>, parent: I, child: I)
        requires before.child(parent, child),
        ensures earlier(before, child, parent),
    {
        let upper = (before.interval)(parent);
        let lower = (before.interval)(child);
        assert(upper.0 < lower.0 < lower.1 <= upper.1);
    }

    proof fn descendants_appear_in_children<I>(links: Map<I, links::Links<I>>, before: Order<I>,
        node: I, id: I,
    )
        requires links::coherence::coherent(links), before.ordered(), before.closed_subtrees(), (before.live)(node),
            before == links::preorder::order(links, before.interval, before.depth),
            id != node, before.inside(node, id),
        ensures ids(reverse_from(links, before, links[node].last)).contains(id),
        decreases reverse_rank(before, node).0, reverse_rank(before, node).1,
    {
        child_covers_inside(before, node, id);
        let child = choose |child: I| #[trigger] before.child(node, child) && before.inside(child, id);
        if child != id {
            child_rank_is_earlier(before, node, child);
            descendants_appear_in_children(links, before, child, id);
        }
        previous_and_last_are_earlier(links, before, child);
        unfold_physical_forest(links, before, child);
        assert(ids(physical_forest(links, before, child)).contains(id));
        child_forest_reaches_tail(links, before, node, child, id);
    }

    spec fn children_from_links<I>(links: Map<I, links::Links<I>>, before: Order<I>, node: I) -> Forest<I> {
        reverse_from(links, before, links[node].last)
    }

    proof fn known_children<I>(links: Map<I, links::Links<I>>, before: Order<I>, node: I)
        requires links::coherence::coherent(links), links.contains_key(node), before.ordered(),
            before == links::preorder::order(links, before.interval, before.depth),
        ensures ({
            let children = children_from_links(links, before, node);
            &&& proper(children) && stores(removal_records(links), children, None)
            &&& oldest(children) == links[node].first && head(children, None) == links[node].last
            &&& forall |id: I| #[trigger] ids(children).contains(id) ==> before.inside(node, id) && id != node
        }),
    {
        let at = links[node];
        let children = children_from_links(links, before, node);
        assert(links::coherence::coherent_at(links, node));
        if let Some(last) = at.last {
            physical_forest_stores(links, before, last);
            previous_and_last_are_earlier(links, before, last);
            unfold_physical_forest(links, before, last);
            assert(links[last].parent == Some(node));
        } else {
            assert(at.first.is_none());
        }
        assert forall |id: I| #[trigger] ids(children).contains(id) implies before.inside(node, id) && id != node by {
            assert(at.last.is_some());
        }
    }

    proof fn forest_has_exact_descendants<I>(links: Map<I, links::Links<I>>, before: Order<I>, node: I)
        requires links::coherence::coherent(links), links.contains_key(node), before.ordered(), before.closed_subtrees(),
            before == links::preorder::order(links, before.interval, before.depth),
        ensures ids(detached(node, children_from_links(links, before, node))) ==
            links.dom().filter(|id: I| before.inside(node, id)),
    {
        known_children(links, before, node);
        before.node_facts(node);
        assert(before.inside(node, node));
        let forest = detached(node, children_from_links(links, before, node));
        let population = links.dom().filter(|id: I| before.inside(node, id));
        assert forall |id: I| #[trigger] population.contains(id) implies ids(forest).contains(id) by {
            if id != node {
                descendants_appear_in_children(links, before, node, id);
            }
        }
        assert forall |id: I| #[trigger] ids(forest).contains(id) implies population.contains(id) by {
            if id != node {
                reveal_with_fuel(ids, 2);
                assert(ids(children_from_links(links, before, node)).contains(id));
                assert(before.inside(node, id));
            }
            assert((before.live)(id) && links.contains_key(id));
        }
        assert(ids(forest) =~= population);
    }

    proof fn root_splice_leaves_descendants<I: Copy>(links: Map<I, links::Links<I>>, before: Order<I>, parent: I, node: I)
        requires links::coherence::coherent(links), links::coherence::child(links, parent, node), before.ordered(),
            before == links::preorder::order(links, before.interval, before.depth),
        ensures ({
            let at = links[node];
            let spliced = links::coherence::spliced(links, parent, node, at.previous, at.next, false);
            &&& spliced.contains_key(node)
            &&& spliced[node] == (links::Links { parent: None, previous: None, next: None, ..at })
            &&& forall |id: I| #[trigger] before.inside(node, id) && id != node ==> {
                &&& spliced.contains_key(id)
                &&& spliced[id] == links[id]
            }
        }),
    {
        let at = links[node];
        let spliced = links::coherence::spliced(links, parent, node, at.previous, at.next, false);
        assert(links::coherence::coherent_at(links, node));
        links::coherence::branch_gap_from_links(links, before, parent, node);
        links::coherence::splice_fields(links, parent, node, at.previous, at.next, false);
        assert((before.live)(node) && (before.parent)(node) == Some(parent));
        assert(before.child(parent, node));
        before.node_facts(node);
        if let Some(prev) = at.previous {
            assert((before.live)(prev) && (before.sibling)(prev) == Some(node));
            before.node_facts(prev);
            assert((before.interval)(prev).1 <= (before.interval)(node).0);
        }
        if let Some(next) = at.next {
            assert((before.interval)(node).1 <= (before.interval)(next).0);
        }
        assert forall |id: I| #[trigger] before.inside(node, id) && id != node implies
            spliced.contains_key(id) && spliced[id] == links[id] by {
            assert(id != parent && Some(id) != at.previous && Some(id) != at.next);
        }
    }

    /// Construct the reverse child forest from live endpoint and sibling links.
    /// The actual root splice leaves every record read by that forest intact.
    proof fn build_detached_forest<I: Copy>(links: Map<I, links::Links<I>>, before: Order<I>, parent: I, node: I)
        requires links::coherence::coherent(links), links::coherence::child(links, parent, node),
            links::preorder::valid(before),
            before == links::preorder::order(links, before.interval, before.depth),
        ensures ({
            let children = children_from_links(links, before, node);
            let at = links[node];
            let spliced = links::coherence::spliced(links, parent, node, at.previous, at.next, false);
            &&& valid_detachment(removal_records(spliced), node, children)
            &&& ids(detached(node, children)) == links.dom().filter(|id: I| before.inside(node, id))
        }),
    {
        let at = links[node];
        let spliced = links::coherence::spliced(links, parent, node, at.previous, at.next, false);
        let children = children_from_links(links, before, node);
        known_children(links, before, node);
        root_splice_leaves_descendants(links, before, parent, node);
        assert forall |id: I| #[trigger] ids(children).contains(id) implies
            removal_records(links).contains_key(id) && removal_records(spliced).contains_key(id)
                && removal_records(links)[id] == removal_records(spliced)[id] by {
            assert(before.inside(node, id) && id != node);
            assert(spliced.contains_key(id) && spliced[id] == links[id]);
        }
        local(removal_records(links), removal_records(spliced), children, None);
        assert(proper(children) && !ids(children).contains(node));
        reveal_with_fuel(proper, 2);
        reveal_with_fuel(stores, 2);
        assert(valid_detachment(removal_records(spliced), node, children));
        forest_has_exact_descendants(links, before, node);
    }

    fn certify_deletion_forest<I: Copy>(
        prior: Ghost<Map<I, links::Links<I>>>, interval: Ghost<spec_fn(I) -> (nat, nat)>,
        depth: Ghost<spec_fn(I) -> nat>, parent: I, node: I,
    ) -> (children: Ghost<Forest<I>>)
        requires links::coherence::coherent(prior@), links::coherence::child(prior@, parent, node),
            links::preorder::valid(links::preorder::order(prior@, interval@, depth@)),
        ensures ({
            let before = links::preorder::order(prior@, interval@, depth@);
            let at = prior@[node];
            let spliced = links::coherence::spliced(prior@, parent, node, at.previous, at.next, false);
            &&& valid_detachment(removal_records(spliced), node, children@)
            &&& ids(detached(node, children@)) == prior@.dom().filter(|id: I| before.inside(node, id))
        }),
        no_unwind
    {
        let before = Ghost(links::preorder::order(prior@, interval@, depth@));
        proof { build_detached_forest(prior@, before@, parent, node); }
        Ghost(children_from_links(prior@, before@, node))
    }
}
