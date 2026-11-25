//! Exact successor for both child-first and pruned traversal.
use vstd::prelude::*;

#[path = "../src/tree_walk.rs"]
pub(crate) mod kernel;

#[path = "../src/free_placement.rs"]
pub(crate) mod free_placement;

#[path = "free_placement_order.rs"]
pub(crate) mod free_placement_order;

use kernel::{AttachmentError, LinkModel};

verus! {

type ParentDepth<I> = spec_fn(I) -> nat;

pub(crate) open spec fn decreasing_parent_depth<L: LinkModel + ?Sized>(
    links: &L, depth: spec_fn(L::Id) -> nat,
) -> bool {
    forall |node: L::Id| #[trigger] links.live(node) ==> match links.parent(node) {
        Some(parent) => links.live(parent) && depth(parent) < depth(node),
        None => true,
    }
}

pub(crate) open spec fn reaches_root<L: LinkModel + ?Sized>(
    links: &L, root: L::Id, node: L::Id, depth: spec_fn(L::Id) -> nat,
) -> bool
    decreases depth(node),
{
    if node == root {
        true
    } else if let Some(parent) = links.parent(node) {
        depth(parent) < depth(node) && reaches_root(links, root, parent, depth)
    } else {
        false
    }
}

pub(crate) open spec fn attachment<L: LinkModel + ?Sized>(
    links: &L, root: L::Id, child: L::Id, depth: spec_fn(L::Id) -> nat,
) -> Result<L::Id, AttachmentError> {
    if child == root {
        Err(AttachmentError::Root)
    } else if let Some(parent) = links.parent(child) {
        if reaches_root(links, root, parent, depth) {
            Ok(parent)
        } else {
            Err(AttachmentError::Detached)
        }
    } else {
        Err(AttachmentError::Detached)
    }
}

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
    first_or_after(path, if descend { first } else { None })
}

pub open spec fn first_or_after<I>(path: Seq<(I, Option<I>)>, first: Option<I>) -> Option<I> {
    if first.is_some() { first } else { after(path, 0) }
}

pub(crate) open spec fn ancestor_links<L: LinkModel + ?Sized>(
    links: &L, root: L::Id, path: Seq<(L::Id, Option<L::Id>)>,
) -> bool {
    forall |i: int| 0 <= i < path.len() ==> {
        let node = (#[trigger] path[i]).0;
        &&& links.live(node)
        &&& (node == root) == (i + 1 == path.len())
        &&& i + 1 < path.len() ==> links.sibling(node) == path[i].1
            && (path[i].1.is_none() ==> links.parent(node) == Some(path[i + 1].0))
    }
}

proof fn link_facts<L: LinkModel + ?Sized>(
    links: &L, root: L::Id, path: Seq<(L::Id, Option<L::Id>)>, i: int,
)
    requires 0 <= i < path.len(), ancestor_links(links, root, path),
    ensures
        links.live(path[i].0),
        (path[i].0 == root) == (i + 1 == path.len()),
        i + 1 < path.len() ==> links.sibling(path[i].0) == path[i].1,
        i + 1 < path.len() && path[i].1.is_none() ==> links.parent(path[i].0) == Some(path[i + 1].0),
{}

/// Depth ranks the live parent links within the requested subtree. The root's
/// parent and sibling are outside the walk.
pub(crate) open spec fn bounded_parents<L: LinkModel + ?Sized>(
    links: &L, root: L::Id, inside: spec_fn(L::Id) -> bool, depth: spec_fn(L::Id) -> nat,
) -> bool {
    forall |node: L::Id| #[trigger] inside(node) ==> {
        &&& links.live(node)
        &&& node != root ==> match links.parent(node) {
            Some(parent) => inside(parent) && depth(parent) < depth(node),
            None => false,
        }
    }
}

pub(crate) open spec fn ancestor_path<L: LinkModel + ?Sized>(
    links: &L, root: L::Id, node: L::Id, fuel: nat,
) -> Seq<(L::Id, Option<L::Id>)>
    decreases fuel,
{
    if node == root || fuel == 0 { seq![(node, None)] }
    else if let Some(parent) = links.parent(node) {
        seq![(node, links.sibling(node))] + ancestor_path(links, root, parent, (fuel - 1) as nat)
    } else { seq![(node, None)] }
}

/// A consistent finite subtree supplies the chain required by the executable
/// successor. The rank proof is erased and does not add a runtime walk.
pub(crate) proof fn build_ancestor_path<L: LinkModel + ?Sized>(
    links: &L, root: L::Id, node: L::Id, inside: spec_fn(L::Id) -> bool,
    depth: spec_fn(L::Id) -> nat, fuel: nat,
)
    requires inside(node), bounded_parents(links, root, inside, depth), depth(node) <= fuel,
    ensures ({
        let path = ancestor_path(links, root, node, fuel);
        &&& 0 < path.len() <= fuel + 1
        &&& path[0].0 == node
        &&& ancestor_links(links, root, path)
        &&& forall |i: int| 0 <= i < path.len() ==> inside((#[trigger] path[i]).0)
        &&& forall |i: int| 0 <= i && i + 1 < path.len() ==>
            links.parent((#[trigger] path[i]).0) == Some(path[i + 1].0)
    }),
    decreases fuel,
{
    let path = ancestor_path(links, root, node, fuel);
    assert(links.live(node));
    if node == root {
        assert(path =~= seq![(node, None)]);
    } else {
        let parent = links.parent(node).unwrap();
        assert(links.parent(node) == Some(parent));
        assert(inside(parent) && depth(parent) < depth(node));
        let tail = ancestor_path(links, root, parent, (fuel - 1) as nat);
        build_ancestor_path(links, root, parent, inside, depth, (fuel - 1) as nat);
        assert(path =~= seq![(node, links.sibling(node))] + tail);
        assert forall |i: int| 0 <= i < path.len() implies inside((#[trigger] path[i]).0) by {
            if i == 0 { assert(path[i].0 == node); }
            else { assert(path[i] == tail[i - 1]); }
        }
        assert forall |i: int| 0 <= i && i + 1 < path.len() implies
            links.parent((#[trigger] path[i]).0) == Some(path[i + 1].0) by {
            if i == 0 { assert(path[1] == tail[0]); }
            else { assert(path[i] == tail[i - 1]); assert(path[i + 1] == tail[i]); }
        }
        assert forall |i: int| 0 <= i < path.len() implies {
            let id = (#[trigger] path[i]).0;
            &&& links.live(id)
            &&& (id == root) == (i + 1 == path.len())
            &&& i + 1 < path.len() ==> links.sibling(id) == path[i].1
                && (path[i].1.is_none() ==> links.parent(id) == Some(path[i + 1].0))
        } by {
            if i > 0 {
                assert(path[i] == tail[i - 1]);
                if i + 1 < path.len() { assert(path[i + 1] == tail[i]); }
                link_facts(links, root, tail, i - 1);
            } else {
                assert(path[1] == tail[0]);
            }
        }
    }
}

fn start() -> (position: Ghost<int>)
    ensures position@ == 0,
    no_unwind
{ Ghost(0) }

fn advance(position: Ghost<int>) -> (following: Ghost<int>)
    ensures following@ == position@ + 1,
    no_unwind
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
