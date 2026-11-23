//! A previously measured, fixed-size branch may be saved as a unit.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub enum CachedBranch {
    Reject,
    Hidden,
    Ready,
}

#[cfg(verus_keep_ghost)]
verus! {
fn model_child<I>(tree: Ghost<Branch<I>>, cursor: Ghost<int>) -> (child: Ghost<Branch<I>>)
    ensures child@ == tree@.children[cursor@],
    no_unwind
{
    Ghost(tree@.children[cursor@])
}

fn first_cursor() -> (cursor: Ghost<int>)
    ensures cursor@ == 0,
    no_unwind
{
    Ghost(0int)
}

fn advance(cursor: Ghost<int>) -> (next: Ghost<int>)
    ensures next@ == cursor@ + 1,
    no_unwind
{
    Ghost(cursor@ + 1)
}

pub trait CacheModel {
    type Id: Copy;
    spec fn links(&self) -> Map<Self::Id, Links<Self::Id>>;
    spec fn seen(&self) -> Seq<Self::Id>;
}
}

#[cfg(not(verus_keep_ghost))]
pub trait CacheModel {
    type Id: Copy;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait BranchCache: CacheModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(status =>
        requires self.links().contains_key(node),
        ensures status == self.links()[node].status,
        no_unwind
    ))]
    fn status(&self, node: Self::Id) -> CachedBranch;

    #[cfg_attr(verus_keep_ghost, verus_spec(child =>
        requires self.links().contains_key(node),
        ensures child == self.links()[node].first,
        no_unwind
    ))]
    fn first(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(sibling =>
        requires self.links().contains_key(node),
        ensures sibling == self.links()[node].next,
        no_unwind
    ))]
    fn next(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).links().contains_key(node),
        ensures final(self).links() == old(self).links(),
            final(self).seen() == old(self).seen().push(node),
        no_unwind
    ))]
    fn include(&mut self, node: Self::Id);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).links().contains_key(node),
        ensures final(self).links().dom() == old(self).links().dom(),
        no_unwind
    ))]
    fn dirty_children(&mut self, node: Self::Id);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(ok =>
    requires rooted(old(cache).links(), tree@), tree@.id == node,
    ensures
        ok ==> all_ready(tree@),
        ready_within(tree@, depth as nat) ==> ok,
        final(cache).links().dom() == old(cache).links().dom(),
        ok ==> final(cache).links() == old(cache).links()
            && final(cache).seen() == old(cache).seen() + visible(tree@),
    decreases depth,
    no_unwind
))]
pub fn check_branch<C: BranchCache>(
    cache: &mut C,
    node: C::Id,
    depth: u8,
    #[cfg(verus_keep_ghost)] tree: Ghost<Branch<C::Id>>,
) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { if ready_within(tree@, depth as nat) { ready_depth_facts(tree@, depth as nat); } }
    if depth == 0 { return false; }
    #[cfg(verus_keep_ghost)]
    proof! {
        root_facts(cache.links(),tree@);
        empty_prefix(tree@.children);
    }
    match cache.status(node) {
        CachedBranch::Reject => return false,
        CachedBranch::Hidden => return true,
        CachedBranch::Ready => {}
    }
    cache.include(node);
    let mut next = cache.first(node);
    #[cfg(verus_keep_ghost)]
    let mut cursor = first_cursor();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            depth > 0,
            cache.links() == old(cache).links(), cache.links().contains_key(node),
            tree@.status is Ready,
            0 <= cursor@ <= tree@.children.len(),
            rooted_children(cache.links(), tree@.children, cursor@),
            next == at(tree@.children, cursor@),
            ready_prefix(tree@.children, cursor@ as nat),
            cache.seen() == old(cache).seen().push(node) + visible_prefix(tree@.children, cursor@ as nat),
        ensures
            cache.links() == old(cache).links(),
            cursor@ == tree@.children.len(),
            ready_prefix(tree@.children, tree@.children.len()),
            cache.seen() == old(cache).seen().push(node) + visible_prefix(tree@.children, tree@.children.len()),
        decreases tree@.children.len() - cursor@,
    ))]
    while let Some(child) = next {
        #[cfg(verus_keep_ghost)]
        proof! {
            sibling_cursor(tree@.children,cursor@);
            assert(cursor@ < tree@.children.len());
            assert(tree@.children[cursor@].id == child);
            child_facts(cache.links(),tree@.children,cursor@);
        }
        next = cache.next(child);
        #[cfg(verus_keep_ghost)]
        let subtree = model_child(tree, cursor);
        if !check_branch(cache, child, depth - 1, #[cfg(verus_keep_ghost)] subtree) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(old(cache).links().dom().contains(node));
                assert(cache.links().dom().contains(node));
                assert(cache.links().contains_key(node));
                if ready_within(tree@, depth as nat) {
                    child_within(tree@, depth as nat, cursor@);
                    assert(false);
                }
            }
            cache.dirty_children(node);
            return false;
        }
        #[cfg(verus_keep_ghost)]
        {
            let following = advance(cursor);
            proof! {
                accept_child(tree@.children, cursor@);
                assert(next == at(tree@.children, following@));
                assert(cache.seen() =~= old(cache).seen().push(node) + visible_prefix(tree@.children, following@ as nat));
            }
            cursor = following;
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        sibling_cursor(tree@.children,cursor@);
        assert(cursor@ == tree@.children.len());
        assert(all_ready(tree@));
        assert(cache.seen() =~= old(cache).seen() + visible(tree@));
    }
    true
}
