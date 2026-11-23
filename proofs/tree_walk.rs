//! Exact successor for both child-first and pruned traversal.
use vstd::prelude::*;

#[path = "../src/tree_walk.rs"]
mod kernel;

verus! {

/// The ordered ancestor chain starts at the current node and ends at the
/// requested subtree root. The root's outside sibling is never followed.
pub open spec fn after<I>(path: Seq<(I, Option<I>)>, position: int) -> Option<I>
    decreases path.len() - position,
{
    if position < 0 || position + 1 >= path.len() { None }
    else if path[position].1.is_some() { path[position].1 }
    else { after(path, position + 1) }
}

pub open spec fn successor<I>(path: Seq<(I, Option<I>)>, descend: bool, first: Option<I>) -> Option<I> {
    if descend && first.is_some() { first } else { after(path, 0) }
}

pub open spec fn child_link<I, F: Fn(I) -> Option<I>>(first: F, node: I, descend: bool, child: Option<I>) -> bool {
    descend ==> call_requires(first, (node,)) &&
        forall |result: Option<I>| #[trigger] call_ensures(first, (node,), result) ==> result == child
}

pub open spec fn ancestor_links<I, S: Fn(I) -> Option<I>, P: Fn(I) -> Option<I>, R: Fn(I) -> bool>(
    path: Seq<(I, Option<I>)>, sibling: S, parent: P, at_root: R,
) -> bool {
    &&& forall |i:int| 0 <= i < path.len() ==> #[trigger] call_requires(at_root, (path[i].0,))
    &&& forall |i:int, result:bool| 0 <= i < path.len() &&
        #[trigger] call_ensures(at_root, (path[i].0,), result) ==> result == (i + 1 == path.len())
    &&& forall |i:int| 0 <= i && i + 1 < path.len() ==> #[trigger] call_requires(sibling, (path[i].0,))
    &&& forall |i:int, result:Option<I>| 0 <= i && i + 1 < path.len() &&
        #[trigger] call_ensures(sibling, (path[i].0,), result) ==> result == path[i].1
    &&& forall |i:int| 0 <= i && i + 1 < path.len() && path[i].1.is_none() ==>
        #[trigger] call_requires(parent, (path[i].0,))
    &&& forall |i:int, result:Option<I>| 0 <= i && i + 1 < path.len() && path[i].1.is_none() &&
        #[trigger] call_ensures(parent, (path[i].0,), result) ==> result == Some(path[i + 1].0)
}

proof fn link_facts<I, S: Fn(I) -> Option<I>, P: Fn(I) -> Option<I>, R: Fn(I) -> bool>(
    path: Seq<(I, Option<I>)>, sibling: S, parent: P, at_root: R, i: int,
)
    requires 0 <= i < path.len(), ancestor_links(path, sibling, parent, at_root),
    ensures
        call_requires(at_root, (path[i].0,)),
        forall |r: bool| #[trigger] call_ensures(at_root, (path[i].0,), r) ==> r == (i + 1 == path.len()),
        i + 1 < path.len() ==> call_requires(sibling, (path[i].0,)),
        forall |r: Option<I>| i + 1 < path.len() && #[trigger] call_ensures(sibling, (path[i].0,), r)
            ==> r == path[i].1,
        i + 1 < path.len() && path[i].1.is_none() ==> call_requires(parent, (path[i].0,)),
        forall |r: Option<I>| i + 1 < path.len() && path[i].1.is_none() &&
            #[trigger] call_ensures(parent, (path[i].0,), r) ==> r == Some(path[i + 1].0),
{}

fn start() -> (position: Ghost<int>)
    ensures position@ == 0,
{ Ghost(0) }

fn advance(position: Ghost<int>) -> (following: Ghost<int>)
    ensures following@ == position@ + 1,
{ Ghost(position@ + 1) }

/// In an ordered tree, the following sibling starts at this subtree's end.
/// If there is no sibling, the child and parent subtrees end at the same index.
pub open spec fn preorder_chain(path: Seq<(nat, Option<nat>)>, end: spec_fn(nat) -> nat) -> bool {
    forall |i:int| 0 <= i && i + 1 < path.len() ==> {
        let pos = (#[trigger] path[i]).0;
        let enclosing_end = end(path[i + 1].0);
        &&& end(pos) <= enclosing_end
        &&& path[i].1 == if end(pos) < enclosing_end { Some(end(pos)) } else { None }
    }
}

proof fn climbs_to_subtree_end(path: Seq<(nat, Option<nat>)>, end: spec_fn(nat) -> nat, i: int)
    requires 0 <= i < path.len(), preorder_chain(path, end),
    ensures
        end(path[i].0) <= end(path.last().0),
        after(path, i) == if end(path[i].0) < end(path.last().0) { Some(end(path[i].0)) } else { None },
    decreases path.len() - i,
{
    if i + 1 < path.len() {
        climbs_to_subtree_end(path, end, i + 1);
        assert(end(path[i].0) <= end(path[i + 1].0));
    } else {
        assert(path[i] == path.last());
    }
}

/// Link traversal with pruning is equivalent to jumping to the end of the
/// current half-open preorder range. The last node in the chain bounds it.
pub proof fn successor_in_preorder(
    path: Seq<(nat, Option<nat>)>, end: spec_fn(nat) -> nat, descend: bool, child: Option<nat>,
)
    requires
        path.len() > 0, preorder_chain(path, end), path[0].0 < end(path[0].0),
        child == if path[0].0 + 1 < end(path[0].0) { Some(path[0].0 + 1) } else { None },
    ensures successor(path, descend, child) == if descend && path[0].0 + 1 < end(path[0].0) {
        Some(path[0].0 + 1)
    } else if end(path[0].0) < end(path.last().0) {
        Some(end(path[0].0))
    } else {
        None
    },
{
    climbs_to_subtree_end(path, end, 0);
}

}
