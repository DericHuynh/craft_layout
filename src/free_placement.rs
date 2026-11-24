//! Non-mutating eligibility checks for independent subtree placement.
#![allow(unexpected_cfgs)]

#[cfg(not(verus_keep_ghost))]
use crate::solve::SOLVED;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::SOLVED;
#[cfg(not(verus_keep_ghost))]
use super::placement_walk::wrap_reads_ready;
#[cfg(verus_keep_ghost)]
use crate::placement_walk::wrap_reads_ready;
#[cfg(not(verus_keep_ghost))]
use crate::tree_walk::{self, AncestorLinks, LinkModel};
#[cfg(verus_keep_ghost)]
use super::{ParentDepth, after, ancestor_links, ancestor_path, bounded_parents, build_ancestor_path, decreasing_parent_depth, kernel as tree_walk};
#[cfg(verus_keep_ghost)]
use super::free_placement_order::{PreflightOrder, forward_from_ancestor, ordered_links, order_facts, remaining};
#[cfg(verus_keep_ghost)]
use super::kernel::{AncestorLinks, LinkModel};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Reason why a subtree cannot be repositioned independently.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum FreePlacementError {
    /// The root takes its rectangle from the layout window.
    Root,
    /// The node's parent chain ends outside the active tree.
    Detached,
    /// The node or one of its ancestors is disabled.
    Disabled,
    /// The parent positions this node as an in-flow child.
    InFlow,
    /// The target or a visible descendant lacks a sizing value required for placement.
    Unsolved,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct PreflightStyle<A> {
    pub disabled: bool,
    pub free: bool,
    pub free_children: bool,
    pub wrap_cross_axis: Option<A>,
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait PreflightModel: LinkModel {
    type Axis: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait PreflightModel: LinkModel {
    type Axis: Copy;

    spec fn first(&self, node: Self::Id) -> Option<Self::Id>;
}
}

/// Read the existing styles, links and slot states without publishing output.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait PreflightHost: PreflightModel + AncestorLinks {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires self.live(node), no_unwind
    ))]
    fn style(&self, node: Self::Id) -> PreflightStyle<Self::Axis>;

    #[cfg_attr(verus_keep_ghost, verus_spec(first =>
        requires self.live(node),
        ensures first == self.first(node), first.is_some() ==> self.live(first.unwrap()),
        no_unwind
    ))]
    fn first_child(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(requires self.live(node), no_unwind))]
    fn finals(&self, node: Self::Id) -> [u32; 2];

    /// Resolve each declaration and indicate whether its size is flexible.
    #[cfg_attr(verus_keep_ghost, verus_spec(requires self.live(node), no_unwind))]
    fn flex_declarations(&self, node: Self::Id, axis: Self::Axis) -> [Option<bool>; 3];

    #[cfg_attr(verus_keep_ghost, verus_spec(requires self.live(node), no_unwind))]
    fn declared_states(&self, node: Self::Id, axis: Self::Axis) -> [u32; 3];
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(first =>
    requires tree.live(root), tree.live(node), decreasing_parent_depth(tree, depth@),
    ensures first.is_ok() ==> tree.live(first.unwrap()) && tree.parent(node) == Some(first.unwrap()),
    no_unwind
))]
fn eligible_parent<L: PreflightHost + ?Sized>(
    tree: &L, root: L::Id, node: L::Id,
    #[cfg(verus_keep_ghost)] depth: Ghost<ParentDepth<L::Id>>,
) -> Result<L::Id, FreePlacementError> {
    if tree.same(node, root) { return Err(FreePlacementError::Root); }
    let Some(parent) = tree.enclosing(node) else { return Err(FreePlacementError::Detached) };
    let style = tree.style(node);
    if style.disabled { return Err(FreePlacementError::Disabled); }

    // Custom adapters can hide a subtree by disabling only its ancestor.
    let mut ancestor = parent;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.live(ancestor), tree.live(parent), tree.parent(node) == Some(parent),
            decreasing_parent_depth(tree, depth@),
        decreases depth@(ancestor),
    ))]
    loop {
        if tree.style(ancestor).disabled { return Err(FreePlacementError::Disabled); }
        if tree.same(ancestor, root) { break; }
        let Some(enclosing) = tree.enclosing(ancestor) else { return Err(FreePlacementError::Detached) };
        #[cfg(verus_keep_ghost)]
        proof! { assert(depth@(enclosing) < depth@(ancestor)); }
        ancestor = enclosing;
    }
    if !style.free && !tree.style(parent).free_children { return Err(FreePlacementError::InFlow); }
    Ok(parent)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires order@.inside(node), ordered_links(tree, root, order@),
    no_unwind
))]
fn check_wrap<L: PreflightHost + ?Sized>(
    tree: &L, node: L::Id, cross: L::Axis,
    #[cfg(verus_keep_ghost)] root: L::Id,
    #[cfg(verus_keep_ghost)] order: Ghost<PreflightOrder<L::Id>>,
) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { order_facts(tree, root, order@, node); }
    let mut next = tree.first_child(node);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant ordered_links(tree, root, order@),
            next.is_some() ==> order@.inside(next.unwrap()) && next.unwrap() != root,
        decreases remaining(order@, next),
    ))]
    while let Some(child) = next {
        #[cfg(verus_keep_ghost)]
        proof! { order_facts(tree, root, order@, child); }
        next = tree.following(child);
        let style = tree.style(child);
        if !style.disabled && !tree.style(child).free {
            let [regular, min, max] = tree.flex_declarations(child, cross);
            let needed = [!matches!(regular, Some(true)), matches!(min, Some(false)), matches!(max, Some(false))];
            if !wrap_reads_ready(needed, tree.declared_states(child, cross)) { return false; }
        }
    }
    true
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(following =>
    requires order@.inside(node), ordered_links(tree, root, order@),
        bounded_parents(tree, root, order@.contains, order@.depth),
    ensures following.is_some() ==> order@.inside(following.unwrap()),
        remaining(order@, following) < remaining(order@, Some(node)),
    no_unwind
))]
fn successor<L: PreflightHost + ?Sized>(
    tree: &L, root: L::Id, node: L::Id, descend: bool,
    #[cfg(verus_keep_ghost)] order: Ghost<PreflightOrder<L::Id>>,
) -> Option<L::Id> {
    #[cfg(verus_keep_ghost)]
    proof! { order_facts(tree, root, order@, node); }
    #[cfg(verus_keep_ghost)]
    let path = preflight_path(tree, root, node, order);
    let child = if descend { tree.first_child(node) } else { None };
    tree_walk::next(tree, root, node, child, #[cfg(verus_keep_ghost)] path)
}

/// Check all visible descendants before any output callback can receive a write.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires tree.live(root), tree.live(node), decreasing_parent_depth(tree, order@.depth),
        order@.inside(node), ordered_links(tree, node, order@),
        bounded_parents(tree, node, order@.contains, order@.depth),
    ensures result.is_ok() ==> tree.live(result.unwrap()) && tree.parent(node) == Some(result.unwrap()),
    no_unwind
))]
pub(crate) fn preflight<L: PreflightHost + ?Sized>(
    tree: &L, root: L::Id, node: L::Id,
    #[cfg(verus_keep_ghost)] order: Ghost<PreflightOrder<L::Id>>,
) -> Result<L::Id, FreePlacementError> {
    #[cfg(verus_keep_ghost)]
    let depth = preflight_depth(order);
    let parent = match eligible_parent(tree, root, node, #[cfg(verus_keep_ghost)] depth) {
        Ok(parent) => parent,
        Err(error) => return Err(error),
    };
    let mut next = Some(node);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant next.is_some() ==> order@.inside(next.unwrap()),
            ordered_links(tree, node, order@), bounded_parents(tree, node, order@.contains, order@.depth),
            tree.live(parent), tree.parent(node) == Some(parent),
        decreases remaining(order@, next),
    ))]
    while let Some(item) = next {
        #[cfg(verus_keep_ghost)]
        proof! { order_facts(tree, node, order@, item); }
        let style = tree.style(item);
        let visible = !style.disabled;
        if visible {
            let [width, height] = tree.finals(item);
            if width != SOLVED || height != SOLVED { return Err(FreePlacementError::Unsolved); }
            if let Some(cross) = style.wrap_cross_axis {
                if !check_wrap(tree, item, cross, #[cfg(verus_keep_ghost)] node, #[cfg(verus_keep_ghost)] order) {
                    return Err(FreePlacementError::Unsolved);
                }
            }
        }
        next = successor(tree, node, item, visible, #[cfg(verus_keep_ghost)] order);
    }
    Ok(parent)
}

#[cfg(verus_keep_ghost)]
verus! {

fn preflight_depth<I>(order: Ghost<PreflightOrder<I>>) -> (depth: Ghost<ParentDepth<I>>)
    ensures depth@ == order@.depth,
    no_unwind
{ Ghost(order@.depth) }

fn preflight_path<L: PreflightModel + ?Sized>(
    tree: &L, root: L::Id, node: L::Id, order: Ghost<PreflightOrder<L::Id>>,
) -> (path: Ghost<Seq<(L::Id, Option<L::Id>)>>)
    requires order@.inside(node), ordered_links(tree, root, order@),
        bounded_parents(tree, root, order@.contains, order@.depth),
    ensures path@.len() > 0, path@[0].0 == node, ancestor_links(tree, root, path@),
        match after(path@, 0) {
            Some(following) => order@.inside(following) && order@.stop(node) <= order@.start(following) < order@.limit,
            None => true,
        },
    no_unwind
{
    proof! {
        build_ancestor_path(tree, root, node, order@.contains, order@.depth, order@.level(node));
        forward_from_ancestor(tree, root, order@, ancestor_path(tree, root, node, order@.level(node)), 0);
    }
    Ghost(ancestor_path(tree, root, node, order@.level(node)))
}

}
