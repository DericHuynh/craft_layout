//! The move guard's exact parent walk, derived from physical reciprocal links.
use super::*;
use crate::prepare_frame::Order;
use crate::owned_guard::{MoveParents, TreeError, ancestor_at, complete_path, validate_ancestry};

verus! {

pub(in crate::removal) open spec fn parent_column<I>(links: Map<I, Links<I>>) -> Map<I, Option<I>> {
    Map::new(links.dom(), |id: I| links[id].parent)
}

spec fn ascend<I>(links: Map<I, Links<I>>, depth: spec_fn(I) -> nat, current: I) -> Seq<I>
    decreases depth(current),
{
    match links[current].parent {
        Some(parent) if links.contains_key(current) && links.contains_key(parent) && depth(parent) < depth(current)
            => seq![current] + ascend(links, depth, parent),
        _ => seq![current],
    }
}

proof fn path_members<I>(path: Seq<I>, tail: Seq<I>, head: I)
    requires path == seq![head] + tail,
    ensures forall |id: I| #[trigger] path.contains(id) == (id == head || tail.contains(id)),
        path.to_set() == tail.to_set().insert(head),
{
    assert forall |id: I| #[trigger] path.contains(id) == (id == head || tail.contains(id)) by {
        if path.contains(id) {
            let i = choose |i: int| 0 <= i < path.len() && path[i] == id;
            if i > 0 { assert(tail[i - 1] == id); }
        } else if id == head {
            assert(path[0] == id);
        } else if tail.contains(id) {
            let i = choose |i: int| 0 <= i < tail.len() && tail[i] == id;
            assert(path[i + 1] == id);
        }
    }
    assert(path.to_set() =~= tail.to_set().insert(head));
}

proof fn complete_trace<I>(links: Map<I, Links<I>>, depth: spec_fn(I) -> nat, current: I)
    requires ranked_parents(links, depth), links.contains_key(current),
    ensures ({
        let path = ascend(links, depth, current);
        &&& 0 < path.len() && path[0] == current
        &&& path.len() == path.to_set().len()
        &&& path.to_set().subset_of(links.dom())
        &&& forall |id: I| #[trigger] path.contains(id) ==> depth(id) <= depth(current)
        &&& forall |i: int| 0 <= i < path.len() ==> {
            let id = #[trigger] path[i];
            &&& parent_column(links).contains_key(id)
            &&& parent_column(links)[id] == ancestor_at(path, i + 1)
        }
    }),
    decreases depth(current),
{
    let path = ascend(links, depth, current);
    assert(ranked_parents(links, depth));
    if let Some(parent) = links[current].parent {
        assert(links.contains_key(parent) && depth(parent) < depth(current));
        let tail = ascend(links, depth, parent);
        reveal_with_fuel(ascend, 1);
        assert(path == seq![current] + tail);
        complete_trace(links, depth, parent);
        path_members(path, tail, current);
        assert(!tail.contains(current));
        assert(!tail.to_set().contains(current));
        vstd::set::lemma_set_insert_len(tail.to_set(), current);
        assert(path.len() == path.to_set().len());
        assert(path.to_set().subset_of(links.dom()));
        assert forall |id: I| #[trigger] path.contains(id) implies depth(id) <= depth(current) by {
            if id != current { assert(tail.contains(id)); }
        }
        assert forall |i: int| 0 <= i < path.len() implies {
            let id = #[trigger] path[i];
            &&& parent_column(links).contains_key(id)
            &&& parent_column(links)[id] == ancestor_at(path, i + 1)
        } by {
            if i == 0 {
                assert(path[i + 1] == tail[0]);
            } else {
                assert(path[i] == tail[i - 1]);
                assert(parent_column(links)[tail[i - 1]] == ancestor_at(tail, i));
                if i < tail.len() { assert(path[i + 1] == tail[i]); }
            }
        }
    } else {
        assert(path == seq![current]);
        path_members(path, Seq::empty(), current);
        assert(path.to_set() =~= Set::empty().insert(current));
        vstd::set::lemma_set_insert_len(Set::empty(), current);
        assert forall |i: int| 0 <= i < path.len() implies {
            let id = #[trigger] path[i];
            &&& parent_column(links).contains_key(id)
            &&& parent_column(links)[id] == ancestor_at(path, i + 1)
        } by { assert(path[i] == current && i == 0); }
    }
}

proof fn visited_iff_ancestor<I>(links: Map<I, Links<I>>, depth: spec_fn(I) -> nat, current: I, moving: I)
    requires ranked_parents(links, depth), links.contains_key(current),
    ensures ascend(links, depth, current).contains(moving) == in_branch(links, depth, moving, current),
    decreases depth(current),
{
    if let Some(parent) = links[current].parent {
        assert(links.contains_key(parent) && depth(parent) < depth(current));
        let tail = ascend(links, depth, parent);
        reveal_with_fuel(ascend, 1);
        path_members(ascend(links, depth, current), tail, current);
        visited_iff_ancestor(links, depth, parent, moving);
    } else {
        path_members(ascend(links, depth, current), Seq::empty(), current);
    }
}

fn witnessed_path<I: Copy>(links: Ghost<Map<I, Links<I>>>, depth: Ghost<spec_fn(I) -> nat>, parent: I, live: usize)
    -> (path: Ghost<Seq<I>>)
    requires ranked_parents(links@, depth@), links@.contains_key(parent), links@.dom().len() <= live,
    ensures path@ == ascend(links@, depth@, parent), complete_path(parent_column(links@), path@, parent, live),
    no_unwind
{
    proof {
        complete_trace(links@, depth@, parent);
        let trace = ascend(links@, depth@, parent);
        vstd::set_lib::lemma_len_subset(trace.to_set(), links@.dom());
    }
    Ghost(ascend(links@, depth@, parent))
}

/// Apply the actual checked ancestry walk to its physical parent projection.
/// Under finite ranks it rejects exactly a move into the moved subtree.
fn validate_ranked_move<A: MoveParents>(store: &A, parent: A::Id, moving: A::Id, live: usize,
    links: Ghost<Map<A::Id, Links<A::Id>>>, depth: Ghost<spec_fn(A::Id) -> nat>,
) -> (result: Result<(), TreeError>)
    requires store.links() == parent_column(links@), ranked_parents(links@, depth@),
        links@.contains_key(parent), links@.dom().len() <= live,
    ensures result == if in_branch(links@, depth@, moving, parent) { Err(TreeError::WouldCreateCycle) } else { Ok(()) },
    no_unwind
{
    let path = witnessed_path(links, depth, parent, live);
    proof { visited_iff_ancestor(links@, depth@, parent, moving); }
    validate_ancestry(store, parent, moving, live, path)
}

/// Physical parent ancestry and preorder containment describe the same
/// subtree once its bounded traversal has been certified.
proof fn ancestry_is_interval<I>(links: Map<I, Links<I>>, before: Order<I>, root: I, id: I)
    requires before.ordered(), before.closed_subtrees(), (before.live)(root), (before.live)(id),
        before == preorder::order(links, before.interval, before.depth),
    ensures in_branch(links, before.depth, root, id) == before.inside(root, id),
    decreases (before.depth)(id),
{
    before.node_facts(id);
    if id != root {
        if let Some(owner) = (before.parent)(id) {
            assert(before.child(owner, id) && (before.live)(owner));
            assert(links[id].parent == Some(owner));
            ancestry_is_interval(links, before, root, owner);
            if before.inside(root, id) {
                assert(before.inside(root, owner));
            } else if before.inside(root, owner) {
                assert(before.inside(root, id));
            }
        } else {
            assert(!before.inside(root, id));
        }
    }
}

proof fn ordered_parent_ranks<I>(links: Map<I, Links<I>>, before: Order<I>)
    requires before.ordered(), before == preorder::order(links, before.interval, before.depth),
    ensures ranked_parents(links, before.depth),
{
    assert forall |id: I| #[trigger] links.contains_key(id) implies match links[id].parent {
        Some(parent) => links.contains_key(parent) && (before.depth)(parent) < (before.depth)(id),
        None => true,
    } by { assert((before.live)(id)); }
}

pub(super) fn ordered_path<I: Copy>(parent: I, moving: I, live: usize,
    links: Ghost<Map<I, Links<I>>>, before: Ghost<Order<I>>,
) -> (path: Ghost<Seq<I>>)
    requires links@.dom().len() <= live,
        before@ == preorder::order(links@, before@.interval, before@.depth),
        before@.ordered(), before@.closed_subtrees(), (before@.live)(moving), (before@.live)(parent),
    ensures complete_path(parent_column(links@), path@, parent, live),
        path@.contains(moving) == before@.inside(moving, parent),
    no_unwind
{
    proof {
        ordered_parent_ranks(links@, before@);
        ancestry_is_interval(links@, before@, moving, parent);
        visited_iff_ancestor(links@, before@.depth, parent, moving);
    }
    witnessed_path(links, Ghost(before@.depth), parent, live)
}

fn validate_ordered_move<A: MoveParents>(store: &A, parent: A::Id, moving: A::Id, live: usize,
    links: Ghost<Map<A::Id, Links<A::Id>>>, before: Ghost<Order<A::Id>>,
) -> (result: Result<(), TreeError>)
    requires store.links() == parent_column(links@), links@.dom().len() <= live,
        before@ == preorder::order(links@, before@.interval, before@.depth),
        before@.ordered(), before@.closed_subtrees(), (before@.live)(moving), (before@.live)(parent),
    ensures result == if before@.inside(moving, parent) { Err(TreeError::WouldCreateCycle) } else { Ok(()) },
    no_unwind
{
    proof {
        ordered_parent_ranks(links@, before@);
        ancestry_is_interval(links@, before@, moving, parent);
    }
    validate_ranked_move(store, parent, moving, live, links, Ghost(before@.depth))
}

}
