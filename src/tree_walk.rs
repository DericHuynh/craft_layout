//! Bounded preorder successor over the host's tree links.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Visit the first child if requested. Otherwise climb only as far as the
/// subtree root while looking for the next sibling.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        path@.len() > 0, path@[0].0 == node,
        child_link(first, node, descend, child@),
        ancestor_links(path@, sibling, parent, at_root),
    ensures result == successor(path@, descend, child@),
))]
pub(crate) fn next<I: Copy, F: Fn(I) -> Option<I>, S: Fn(I) -> Option<I>, P: Fn(I) -> Option<I>, R: Fn(I) -> bool>(
    mut node: I,
    descend: bool,
    first: F,
    sibling: S,
    parent: P,
    at_root: R,
    #[cfg(verus_keep_ghost)] path: Ghost<Seq<(I, Option<I>)>>,
    #[cfg(verus_keep_ghost)] child: Ghost<Option<I>>,
) -> Option<I> {
    let first_child = if descend { first(node) } else { None };
    if let Some(first_child) = first_child {
        return Some(first_child);
    }

    #[cfg(verus_keep_ghost)]
    let mut position = start();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= position@ < path@.len(),
            node == path@[position@].0,
            ancestor_links(path@, sibling, parent, at_root),
            (!descend || child@.is_none()),
            after(path@, position@) == after(path@, 0),
        decreases path@.len() - position@,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        proof! { link_facts(path@, sibling, parent, at_root, position@); }
        if at_root(node) {
            return None;
        }
        if let Some(next_sibling) = sibling(node) {
            return Some(next_sibling);
        }
        node = parent(node)?;
        #[cfg(verus_keep_ghost)]
        {
            position = advance(position);
        }
    }
}
