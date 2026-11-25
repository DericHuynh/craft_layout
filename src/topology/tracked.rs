//! Reconcile a retained snapshot against live children in preorder.
#![allow(unexpected_cfgs)]

use crate::{vec_memory::VecMemory, work_stack::{WorkStack, work_stack}};
#[cfg(verus_keep_ghost)]
use crate::structural::kernel::{ChildCursor, StructuralChange, parent_change};
#[cfg(not(verus_keep_ghost))]
use crate::structural_changes::{ChildCursor, StructuralChange, parent_change};
#[cfg(verus_keep_ghost)]
use super::kernel as state;
#[cfg(not(verus_keep_ghost))]
use super::state;
use state::{PriorNode, PriorStyle};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct Frame<I> {
    pub node: I,
    pub index: Option<usize>,
    pub end: usize,
    pub cursor: ChildCursor,
}

impl<I> Frame<I> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures final(self).node == old(self).node, final(self).index == old(self).index,
            final(self).end == old(self).end,
        no_unwind
    ))]
    fn advance_child(&mut self, child: Option<usize>, nodes: &[PriorNode<I>]) -> Option<()> {
        let following = state::following_child(nodes, self.cursor.expected, self.end)?;
        self.cursor = self.cursor.observe(child, following);
        Some(())
    }
}

pub(crate) type Start<I> = (Frame<I>, Option<I>);

#[cfg(not(verus_keep_ghost))]
pub(crate) trait Model {
    type Id: Copy;
    type Style: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) struct Links<I> {
    pub spans: Map<I, (nat, nat)>,
    pub parents: Map<I, Option<I>>,
}

impl<I> Links<I> {
    pub(crate) open spec fn live(self, id: I) -> bool { self.spans.contains_key(id) }

    pub(crate) open spec fn start(self, id: I) -> nat { self.spans[id].0 }

    pub(crate) open spec fn end(self, id: I) -> nat { self.spans[id].1 }

    pub(crate) open spec fn valid(self, root: I) -> bool {
        self.live(root) && forall |id: I| #[trigger] self.live(id) ==>
            self.start(root) <= self.start(id) < self.end(id) <= self.end(root)
    }

    pub(crate) open spec fn child(self, parent: I, child: I) -> bool {
        &&& self.live(parent) && self.live(child)
        &&& self.parents[child] == Some(parent)
        &&& self.start(parent) < self.start(child) < self.end(child) <= self.end(parent)
    }

    pub(crate) open spec fn at_child(self, parent: I, next: Option<I>, position: nat) -> bool {
        match next {
            Some(child) => self.child(parent, child) && self.start(child) == position,
            None => position == self.end(parent),
        }
    }
}

pub(crate) trait Model {
    type Id: Copy;
    type Style: Copy;
    spec fn links(&self) -> Links<Self::Id>;
    spec fn disabled(style: Self::Style) -> bool;
    spec fn style(&self, node: Self::Id) -> Self::Style;
}

pub(crate) open spec fn ancestry<I>(links: Links<I>, stack: Seq<Frame<I>>, frame: Frame<I>) -> bool {
    forall |i: int| 0 <= i < stack.len() ==> links.child(
        (#[trigger] stack[i]).node,
        if i + 1 == stack.len() { frame.node } else { stack[i + 1].node },
    )
}

proof fn suspend<I>(links: Links<I>, stack: Seq<Frame<I>>, frame: Frame<I>, child: Frame<I>)
    requires ancestry(links, stack, frame), links.child(frame.node, child.node),
    ensures ancestry(links, stack.push(frame), child),
{
    let deeper = stack.push(frame);
    assert forall |i: int| 0 <= i < deeper.len() implies links.child(
        (#[trigger] deeper[i]).node,
        if i + 1 == deeper.len() { child.node } else { deeper[i + 1].node },
    ) by {
        if i == stack.len() {
            assert(deeper[i].node == frame.node);
        } else {
            assert(deeper[i] == stack[i]);
            if i + 1 < stack.len() { assert(deeper[i + 1] == stack[i + 1]); }
            else { assert(deeper[i + 1] == frame); }
        }
    }
}

proof fn resume<I>(links: Links<I>, stack: Seq<Frame<I>>, child: Frame<I>)
    requires stack.len() > 0, ancestry(links, stack, child),
    ensures links.child(stack.last().node, child.node), ancestry(links, stack.drop_last(), stack.last()),
{
    let shorter = stack.drop_last();
    let enclosing = stack.last();
    assert(enclosing == stack[stack.len() - 1]);
    assert forall |i: int| 0 <= i < shorter.len() implies links.child(
        (#[trigger] shorter[i]).node,
        if i + 1 == shorter.len() { enclosing.node } else { shorter[i + 1].node },
    ) by {
        assert(shorter[i] == stack[i]);
        if i + 1 < shorter.len() { assert(shorter[i + 1] == stack[i + 1]); }
    }
}

fn stack_prefix<I: Copy, const N: usize>(stack: &WorkStack<Frame<I>, N>) -> (saved: Ghost<Seq<Frame<I>>>)
    ensures saved@ == stack.items(),
    no_unwind
{
    Ghost(stack.items())
}

fn position_after<A: Model>(access: &A, first: A::Id) -> (position: Ghost<nat>)
    ensures position@ == access.links().start(first) + 1,
    no_unwind
{
    Ghost(access.links().start(first) + 1)
}

fn step(position: Ghost<nat>) -> (next: Ghost<nat>)
    ensures next@ == position@ + 1,
    no_unwind
{
    Ghost(position@ + 1)
}
}

/// Host record edits leave the enabled preorder and live IDs stable.
/// A rejected cache observation requests untracked reconciliation.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: Model {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires self.links().live(node),
        no_unwind
    ))]
    fn ticket(&self, node: Self::Id) -> u64;

    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (live == prior), no_unwind))]
    fn same_id(&self, live: Self::Id, prior: Self::Id) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.links().live(node),
        ensures *result == self.style(node),
            Self::disabled(*result) ==> self.links().end(node) == self.links().start(node) + 1,
        no_unwind
    ))]
    fn read_style(&self, node: Self::Id) -> &Self::Style;

    #[cfg_attr(verus_keep_ghost, verus_spec(disabled => ensures disabled == Self::disabled(*style), no_unwind))]
    fn is_disabled(&self, style: &Self::Style) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(same =>
        ensures same ==> Self::disabled(*live) == Self::disabled(*prior),
        no_unwind
    ))]
    fn same_style(&self, live: &Self::Style, prior: &Self::Style) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(first =>
        requires self.links().live(node), !Self::disabled(self.style(node)),
        ensures self.links().at_child(node, first, self.links().start(node) + 1),
        no_unwind
    ))]
    fn first(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).links() == old(self).links(), no_unwind
    ))]
    fn invalidate_snapshot(&mut self);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).links().live(node),
        ensures final(self).links() == old(self).links(),
        no_unwind
    ))]
    fn remember_style_if_current(&mut self, node: Self::Id);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).links().live(node),
        ensures final(self).links() == old(self).links(),
        no_unwind
    ))]
    fn register_style_change(&mut self, node: Self::Id, prior: &Self::Style);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).links().live(node), mark is Subtree || mark is Moved,
        ensures final(self).links() == old(self).links(),
        no_unwind
    ))]
    fn mark_parent_change(&mut self, node: Self::Id, mark: StructuralChange);

    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires self.links().child(parent, child),
        ensures self.links().at_child(parent, next, self.links().end(child)),
        no_unwind
    ))]
    fn following(
        &self, child: Self::Id,
        #[cfg(verus_keep_ghost)] parent: Self::Id,
    ) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).links().live(node),
        ensures final(self).links() == old(self).links(),
        no_unwind
    ))]
    fn mark_children_changed(&mut self, node: Self::Id);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(access).links().live(node),
    ensures final(access).links() == old(access).links(),
        if let Some((frame, child)) = result {
            frame.node == node
                && final(access).links().at_child(node, child, final(access).links().start(node) + 1)
        } else { true },
    no_unwind
))]
fn enter<A: Access>(
    access: &mut A, node: A::Id, old_parent: Option<usize>, nodes: &[PriorNode<A::Id>],
    styles: &[PriorStyle<A::Style>], first_ticket: u64,
) -> Option<Start<A::Id>> {
    let (mut index, mut prior_parent, mut reusable) = (None, None, false);
    if let Some((i, row)) = state::ticket_row(nodes, first_ticket, access.ticket(node)) {
        if access.same_id(node, row.id) {
            index = Some(i);
            prior_parent = Some(row.parent);
            let old = &state::style_row(nodes, styles, i)?.params;
            let live = access.read_style(node);
            let was_disabled = access.is_disabled(old);
            let changed = !access.same_style(live, old);
            if changed {
                if was_disabled != access.is_disabled(live) {
                    access.invalidate_snapshot();
                }
                access.remember_style_if_current(node);
                access.register_style_change(node, old);
            }
            reusable = !was_disabled && !changed;
        }
    }
    let mark = parent_change(prior_parent, old_parent, reusable);
    if matches!(mark, StructuralChange::Subtree | StructuralChange::Moved) {
        access.mark_parent_change(node, mark);
    }
    let disabled = access.is_disabled(access.read_style(node));
    let (expected, end, first) = if disabled {
        (0, 0, None)
    } else {
        let (expected, end) = state::child_range(nodes, index)?;
        (expected, end, access.first(node))
    };
    Some((Frame { node, index, end, cursor: ChildCursor { expected, changed: false } }, first))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires access.links().live(child),
    ensures result == Some(true) ==> access.links().end(child) == access.links().start(child) + 1,
    no_unwind
))]
fn unchanged_leaf<A: Access>(
    access: &A, child: A::Id, expected: usize, prior: &PriorNode<A::Id>, ticket: u64,
    nodes: &[PriorNode<A::Id>], styles: &[PriorStyle<A::Style>],
) -> Option<bool> {
    if access.ticket(child) != ticket || !access.same_id(child, prior.id) { return Some(false); }
    let old = &state::style_row(nodes, styles, expected)?.params;
    let live = access.read_style(child);
    if !access.same_style(live, old) { return Some(false); }
    Some(access.is_disabled(old) || access.first(child).is_none())
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(access).links().live(frame.node),
    ensures final(access).links() == old(access).links(),
    no_unwind
))]
fn finish<A: Access>(access: &mut A, frame: Frame<A::Id>) {
    if frame.cursor.needs_invalidation(frame.end) {
        access.mark_children_changed(frame.node);
    }
}

/// Visit the live preorder, skipping structurally verified leaf rows. Only
/// snapshot indices and values are inspected, so a stale ID is never read
/// through the host. The stack contains only currently suspended ancestors.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(access).links().valid(root), old(stack).valid(), old(stack).items().len() == 0,
    ensures final(access).links() == old(access).links(), final(stack).valid(),
        result.is_some() ==> final(stack).items().len() == 0,
    no_unwind
))]
fn track<A: Access, M: VecMemory, const N: usize>(
    access: &mut A, root: A::Id, old_parent: Option<usize>, nodes: &[PriorNode<A::Id>],
    styles: &[PriorStyle<A::Style>], first_ticket: u64, stack: &mut WorkStack<Frame<A::Id>, N>,
) -> Option<()> {
    let (mut frame, mut next) = enter(access, root, old_parent, nodes, styles, first_ticket)?;
    #[cfg(verus_keep_ghost)]
    let mut position = position_after(access, root);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            access.links() == old(access).links(), access.links().valid(root),
            access.links().live(frame.node), access.links().at_child(frame.node, next, position@),
            position@ <= access.links().end(root), stack.valid(),
            ancestry(access.links(), stack.items(), frame),
            if stack.items().len() == 0 { frame.node == root } else { stack.items()[0].node == root },
        decreases access.links().end(root) - position@, stack.items().len(),
    ))]
    loop {
        if let Some(child) = next {
            let expected = frame.cursor.expected;
            if let Some((entry, ticket)) = state::expected_leaf(nodes, expected, frame.end, frame.cursor.changed, first_ticket)? {
                if unchanged_leaf(access, child, expected, entry, ticket, nodes, styles)? {
                    frame.cursor = frame.cursor.observe(Some(expected), Some(entry.end));
                    next = access.following(
                        child,
                        #[cfg(verus_keep_ghost)]
                        frame.node,
                    );
                    #[cfg(verus_keep_ghost)]
                    { position = step(position); }
                    continue;
                }
            }
            let (branch, first) = enter(access, child, frame.index, nodes, styles, first_ticket)?;
            if first.is_some() {
                #[cfg(verus_keep_ghost)]
                let before = stack_prefix(stack);
                stack.push::<M>(frame);
                #[cfg(verus_keep_ghost)]
                proof! { suspend(access.links(), before@, frame, branch); }
                frame = branch;
                next = first;
            } else {
                finish(access, branch);
                frame.advance_child(branch.index, nodes)?;
                next = access.following(
                    child,
                    #[cfg(verus_keep_ghost)]
                    frame.node,
                );
            }
            #[cfg(verus_keep_ghost)]
            { position = step(position); }
        } else {
            finish(access, frame);
            #[cfg(verus_keep_ghost)]
            let before = stack_prefix(stack);
            let Some(mut enclosing) = stack.pop() else { return Some(()); };
            #[cfg(verus_keep_ghost)]
            proof! { resume(access.links(), before@, frame); }
            enclosing.advance_child(frame.index, nodes)?;
            next = access.following(
                frame.node,
                #[cfg(verus_keep_ghost)]
                enclosing.node,
            );
            frame = enclosing;
        }
    }
}

/// Each traversal begins with an empty logical stack, even when an earlier
/// traversal left initialized spill entries behind.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(access).links().valid(root),
    ensures final(access).links() == old(access).links(),
    no_unwind
))]
pub(crate) fn track_reusing<A: Access, M: VecMemory>(
    access: &mut A, root: A::Id, old_parent: Option<usize>, nodes: &[PriorNode<A::Id>],
    styles: &[PriorStyle<A::Style>], first_ticket: u64, spill: &mut Vec<Frame<A::Id>>,
) -> Option<()> {
    let mut stack = work_stack::<_, 8, M>(M::take(spill));
    let result = track::<_, M, 8>(access, root, old_parent, nodes, styles, first_ticket, &mut stack);
    *spill = stack.into_spill();
    result
}
