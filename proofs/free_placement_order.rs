//! Preorder progress of the links used by free-placement preflight.
use super::{after, ancestor_links, bounded_parents, decreasing_parent_depth};
use super::free_placement::PreflightModel;
use crate::prepare_frame::Order;
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(I)]
pub(crate) struct PreflightOrder<I> {
    pub contains: spec_fn(I) -> bool,
    pub depth: spec_fn(I) -> nat,
    pub rank: spec_fn(I) -> nat,
    pub end: spec_fn(I) -> nat,
    pub limit: nat,
}

impl<I> PreflightOrder<I> {
    pub(crate) open spec fn from_order(order: Order<I>, root: I) -> Self {
        Self {
            contains: |node: I| order.inside(root, node),
            depth: order.depth,
            rank: |node: I| (order.interval)(node).0,
            end: |node: I| (order.interval)(node).1,
            limit: (order.interval)(root).1,
        }
    }

    pub(crate) open spec fn inside(self, node: I) -> bool { (self.contains)(node) }
    pub(crate) open spec fn level(self, node: I) -> nat { (self.depth)(node) }
    pub(crate) open spec fn start(self, node: I) -> nat { (self.rank)(node) }
    pub(crate) open spec fn stop(self, node: I) -> nat { (self.end)(node) }
}

pub(crate) open spec fn remaining<I>(order: PreflightOrder<I>, next: Option<I>) -> int {
    match next { Some(node) => order.limit - order.start(node), None => 0 }
}

/// Descendants occupy nested half-open ranges and disjoint siblings occupy
/// ordered ranges. Only the subtree root's own following sibling lies outside.
pub(crate) open spec fn node_order<L: PreflightModel + ?Sized>(
    tree: &L, root: L::Id, order: PreflightOrder<L::Id>, node: L::Id,
) -> bool {
    &&& tree.live(node)
    &&& order.start(root) <= order.start(node) < order.stop(node) <= order.limit
    &&& match tree.first(node) {
        Some(child) => order.inside(child) && order.start(node) < order.start(child) < order.limit && child != root,
        None => true,
    }
    &&& node != root ==> match tree.sibling(node) {
        Some(sibling) => order.inside(sibling) && order.stop(node) <= order.start(sibling) < order.limit && sibling != root,
        None => true,
    }
    &&& node != root ==> match tree.parent(node) {
        Some(parent) => order.inside(parent) && order.stop(node) <= order.stop(parent),
        None => false,
    }
}

pub(crate) open spec fn ordered_links<L: PreflightModel + ?Sized>(
    tree: &L, root: L::Id, order: PreflightOrder<L::Id>,
) -> bool {
    forall |node: L::Id| #[trigger] order.inside(node) ==> node_order(tree, root, order, node)
}

pub(crate) open spec fn preflight_links<L: PreflightModel + ?Sized>(tree: &L, order: Order<L::Id>) -> bool {
    forall |node: L::Id| {
        &&& #[trigger] tree.live(node) == (order.live)(node)
        &&& (order.live)(node) ==> {
            &&& tree.first(node) == (order.first)(node)
            &&& tree.sibling(node) == (order.sibling)(node)
            &&& tree.parent(node) == (order.parent)(node)
        }
    }
}

pub(crate) proof fn subtree_preflight_order<L: PreflightModel + ?Sized>(tree: &L, target: L::Id, order: Order<L::Id>)
    requires order.ordered(), order.closed_subtrees(), (order.live)(target), preflight_links(tree, order),
    ensures
        tree.live(target),
        decreasing_parent_depth(tree, order.depth),
        PreflightOrder::from_order(order, target).inside(target),
        ordered_links(tree, target, PreflightOrder::from_order(order, target)),
        bounded_parents(tree, target, PreflightOrder::from_order(order, target).contains, order.depth),
{
    let witness = PreflightOrder::from_order(order, target);
    order.node_facts(target);
    assert forall |node: L::Id| #[trigger] tree.live(node) implies match tree.parent(node) {
        Some(parent) => tree.live(parent) && (order.depth)(parent) < (order.depth)(node),
        None => true,
    } by { order.node_facts(node); }
    assert forall |node: L::Id| #[trigger] witness.inside(node) implies node_order(tree, target, witness, node) by {
        assert(order.inside(target, node));
        order.node_facts(node);
    }
    assert forall |node: L::Id| #[trigger] witness.inside(node) implies {
        &&& tree.live(node)
        &&& node != target ==> match tree.parent(node) {
            Some(parent) => witness.inside(parent) && (order.depth)(parent) < (order.depth)(node),
            None => false,
        }
    } by { assert(order.inside(target, node)); }
}

pub(crate) proof fn order_facts<L: PreflightModel + ?Sized>(
    tree: &L, root: L::Id, order: PreflightOrder<L::Id>, node: L::Id,
)
    requires ordered_links(tree, root, order), order.inside(node),
    ensures node_order(tree, root, order, node),
{}

/// Reusing the real successor's ancestor path gives an exact lower bound on
/// any jump after the current node. Each climb covers a containing range.
pub(crate) proof fn forward_from_ancestor<L: PreflightModel + ?Sized>(
    tree: &L, root: L::Id, order: PreflightOrder<L::Id>, path: Seq<(L::Id, Option<L::Id>)>, i: int,
)
    requires
        0 <= i < path.len(), ordered_links(tree, root, order), ancestor_links(tree, root, path),
        forall |j: int| 0 <= j < path.len() ==> order.inside((#[trigger] path[j]).0),
        forall |j: int| 0 <= j && j + 1 < path.len() ==>
            tree.parent((#[trigger] path[j]).0) == Some(path[j + 1].0),
    ensures match after(path, i) {
        Some(following) => order.inside(following) && order.stop(path[i].0) <= order.start(following) < order.limit,
        None => true,
    },
    decreases path.len() - i,
{
    if i + 1 < path.len() {
        let node = path[i].0;
        order_facts(tree, root, order, node);
        assert(node != root);
        if path[i].1.is_some() {
            assert(tree.sibling(node) == path[i].1);
        } else {
            assert(tree.parent(node) == Some(path[i + 1].0));
            forward_from_ancestor(tree, root, order, path, i + 1);
        }
    }
}

}
