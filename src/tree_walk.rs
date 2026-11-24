//! Bounded preorder successor over the host's tree links.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(not(verus_keep_ghost))]
pub(crate) trait LinkModel {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) trait LinkModel {
        type Id: Copy;

        spec fn live(&self, node: Self::Id) -> bool;
        spec fn sibling(&self, node: Self::Id) -> Option<Self::Id>;
        spec fn parent(&self, node: Self::Id) -> Option<Self::Id>;
    }
}

/// Read-only ancestor links in the direction the caller is visiting siblings.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait AncestorLinks: LinkModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.live(node),
        ensures result == self.sibling(node),
            result.is_some() ==> self.live(result.unwrap()),
        no_unwind
    ))]
    fn following(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.live(node),
        ensures result == self.parent(node),
            result.is_some() ==> self.live(result.unwrap()),
        no_unwind
    ))]
    fn enclosing(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures result == (node == root),
        no_unwind
    ))]
    fn same(&self, node: Self::Id, root: Self::Id) -> bool;
}

/// Reason why a node cannot be registered as a newly attached child.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum AttachmentError {
    /// The layout root has no parent to notify.
    Root,
    /// The node's parent chain ends outside the active tree.
    Detached,
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires links.live(root), links.live(child), decreasing_parent_depth(links, depth@),
    ensures result == attachment(links, root, child, depth@),
        result.is_ok() ==> links.live(result.unwrap()),
    no_unwind
))]
fn attachment_parent<L: AncestorLinks + ?Sized>(
    links: &L,
    root: L::Id,
    child: L::Id,
    #[cfg(verus_keep_ghost)] depth: Ghost<ParentDepth<L::Id>>,
) -> Result<L::Id, AttachmentError> {
    if links.same(child, root) {
        return Err(AttachmentError::Root);
    }
    let Some(parent) = links.enclosing(child) else {
        return Err(AttachmentError::Detached);
    };
    let mut ancestor = parent;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            links.live(ancestor), links.live(parent), links.live(root),
            child != root, links.parent(child) == Some(parent),
            decreasing_parent_depth(links, depth@),
            reaches_root(links, root, ancestor, depth@)
                == reaches_root(links, root, parent, depth@),
        decreases depth@(ancestor),
    ))]
    loop {
        if links.same(ancestor, root) {
            return Ok(parent);
        }
        let Some(enclosing) = links.enclosing(ancestor) else {
            #[cfg(verus_keep_ghost)]
            proof! { reveal(reaches_root); }
            return Err(AttachmentError::Detached);
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(depth@(enclosing) < depth@(ancestor));
            reveal(reaches_root);
        }
        ancestor = enclosing;
    }
}

/// A supplied child has already passed the caller's descent condition.
/// Otherwise climb only as far as the requested subtree root.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        child.is_some() ==> links.live(child.unwrap()),
        child.is_none() ==> path@.len() > 0 && path@[0].0 == node && ancestor_links(links, root, path@),
    ensures result == first_or_after(path@, child),
        result.is_some() ==> links.live(result.unwrap()),
    no_unwind
))]
pub(crate) fn next<L: AncestorLinks + ?Sized>(
    links: &L,
    root: L::Id,
    mut node: L::Id,
    child: Option<L::Id>,
    #[cfg(verus_keep_ghost)] path: Ghost<Seq<(L::Id, Option<L::Id>)>>,
) -> Option<L::Id> {
    if let Some(first_child) = child {
        return Some(first_child);
    }

    #[cfg(verus_keep_ghost)]
    let mut position = start();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= position@ < path@.len(),
            node == path@[position@].0,
            ancestor_links(links, root, path@),
            child.is_none(),
            after(path@, position@) == after(path@, 0),
        decreases path@.len() - position@,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { link_facts(links, root, path@, position@); }
        if links.same(node, root) {
            return None;
        }
        if let Some(next_sibling) = links.following(node) {
            return Some(next_sibling);
        }
        node = links.enclosing(node)?;
        #[cfg(verus_keep_ghost)]
        {
            position = advance(position);
        }
    }
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
struct Forward<'a, T: ?Sized>(&'a T);

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
impl<T: crate::TreeAdapter + ?Sized> LinkModel for Forward<'_, T> {
    type Id = T::NodeId;
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
impl<T: crate::TreeAdapter + ?Sized> AncestorLinks for Forward<'_, T> {
    #[inline(always)]
    fn following(&self, node: Self::Id) -> Option<Self::Id> { self.0.next_sibling(node) }

    #[inline(always)]
    fn enclosing(&self, node: Self::Id) -> Option<Self::Id> { self.0.parent(node) }

    #[inline(always)]
    fn same(&self, node: Self::Id, root: Self::Id) -> bool { node == root }
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
#[inline(always)]
pub(crate) fn next_forward<T: crate::TreeAdapter + ?Sized>(
    tree: &T, root: T::NodeId, node: T::NodeId, child: Option<T::NodeId>,
) -> Option<T::NodeId> {
    next(&Forward(tree), root, node, child)
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
#[inline]
pub(crate) fn registered_parent<T: crate::TreeAdapter + ?Sized>(
    tree: &T, root: T::NodeId, child: T::NodeId,
) -> Result<T::NodeId, AttachmentError> {
    attachment_parent(&Forward(tree), root, child)
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
impl<T> LinkModel for crate::LayoutTree<T> {
    type Id = crate::layout_tree::NodeKey;
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
impl<T> AncestorLinks for crate::LayoutTree<T> {
    #[inline(always)]
    fn following(&self, node: Self::Id) -> Option<Self::Id> {
        self.nodes.get(node).and_then(|entry| entry.prev_sibling)
    }

    #[inline(always)]
    fn enclosing(&self, node: Self::Id) -> Option<Self::Id> {
        self.nodes.get(node).and_then(|entry| entry.parent)
    }

    #[inline(always)]
    fn same(&self, node: Self::Id, root: Self::Id) -> bool { node == root }
}
