//! Scan a fixed-size branch before preserving its measured records.
#![allow(unexpected_cfgs)]
use crate::{declarations::{X, Y}, prepare_nodes::Records};
#[cfg(not(verus_keep_ghost))]
use crate::{incremental::SubtreeCounts, region_policy, solve::cycle_rules};
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, prepare_frame::Order, prepare_nodes::live, regions::SubtreeCounts,
    sizing_pass, structural_plan::policy as region_policy};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use cycle_rules::{Kind, SOLVED};

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub enum CachedBranch {
    Reject,
    Hidden,
    Ready,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn status<T: Records + ?Sized>(tree: &T, node: T::Id) -> CachedBranch {
    let record = tree.layout_record(node);
    if !(record.structural_change is Clean) || (record.flags.0 & (cycle_rules::CYCLE_X | cycle_rules::CYCLE_Y)) != 0 {
        CachedBranch::Reject
    } else if tree.layout_params(node).disabled {
        CachedBranch::Hidden
    } else if cycle_rules::read_state(record.flags.0, cycle_rules::slot_index(0, Kind::Final) as u32) == SOLVED
        && cycle_rules::read_state(record.flags.0, cycle_rules::slot_index(1, Kind::Final) as u32) == SOLVED {
        CachedBranch::Ready
    } else { CachedBranch::Reject }
}

pub(crate) open spec fn marks<T: Records + ?Sized>(tree: &T) -> (spec_fn(T::Id) -> CachedBranch) {
    |node: T::Id| status(tree, node)
}

/// The scan covered each ordinary sibling link. A hidden node ends descent.
pub(crate) closed spec fn physical<I>(order: Order<I>, marks: spec_fn(I) -> CachedBranch, branch: Branch<I>) -> bool
    decreases branch,
{
    &&& (order.live)(branch.id)
    &&& branch.status == marks(branch.id)
    &&& match branch.status {
        CachedBranch::Reject => false,
        CachedBranch::Hidden => branch.children.len() == 0,
        CachedBranch::Ready => {
            let children = branch.children;
            let first = (order.first)(branch.id);
            if children.len() == 0 { first.is_none() } else {
                &&& first == Some(children[0].id)
                &&& (order.sibling)(children.last().id).is_none()
                &&& forall |i: int| 0 <= i < children.len() ==> {
                    let child = #[trigger] children[i];
                    &&& order.child(branch.id, child.id)
                    &&& physical(order, marks, child)
                }
                &&& forall |i: int| 0 <= i && i + 1 < children.len() ==>
                    #[trigger] (order.sibling)(children[i].id) == Some(children[i + 1].id)
            }
        },
    }
}

spec fn prefix<I>(order: Order<I>, marks: spec_fn(I) -> CachedBranch, parent: I, children: Seq<Branch<I>>, next: Option<I>) -> bool {
    if children.len() == 0 { next == (order.first)(parent) } else {
        &&& (order.first)(parent) == Some(children[0].id)
        &&& (order.sibling)(children.last().id) == next
        &&& forall |i: int| 0 <= i < children.len() ==> {
            let child = #[trigger] children[i];
            &&& order.child(parent, child.id)
            &&& physical(order, marks, child)
        }
        &&& forall |i: int| 0 <= i && i + 1 < children.len() ==>
            #[trigger] (order.sibling)(children[i].id) == Some(children[i + 1].id)
    }
}

pub(crate) open spec fn records_unchanged<T: Records + ?Sized>(before: &T, after: &T) -> bool {
    &&& before.order() == after.order()
    &&& forall |node: T::Id| #[trigger] after.layout_record(node) == before.layout_record(node)
    &&& forall |node: T::Id| #[trigger] after.layout_params(node) == before.layout_params(node)
}

proof fn same_evidence<T: Records + ?Sized>(before: &T, after: &T, branch: Branch<T::Id>)
    requires records_unchanged(before, after), physical(before.order(), marks(before), branch),
    ensures physical(after.order(), marks(after), branch),
{
    assert(marks(before) =~= marks(after));
}

proof fn extend<I>(order: Order<I>, marks: spec_fn(I) -> CachedBranch,
    parent: I, children: Seq<Branch<I>>, child: Branch<I>)
    requires prefix(order, marks, parent, children, Some(child.id)), physical(order, marks, child), order.child(parent, child.id),
    ensures prefix(order, marks, parent, children.push(child), (order.sibling)(child.id)),
{
    let rows = children.push(child);
    assert(rows.last() == child);
    if children.len() == 0 { assert(rows[0] == child); }
    else { assert(rows[0] == children[0]); }
    assert forall |i: int| 0 <= i < rows.len() implies {
        let child = #[trigger] rows[i];
        &&& order.child(parent, child.id)
        &&& physical(order, marks, child)
    } by {
        if i < children.len() { assert(rows[i] == children[i]); }
        else { assert(rows[i] == child); }
    }
    assert forall |i: int| 0 <= i && i + 1 < rows.len() implies
        #[trigger] (order.sibling)(rows[i].id) == Some(rows[i + 1].id) by {
        assert(rows[i] == children[i]);
        if i + 1 == children.len() {
            assert(rows[i] == children.last() && rows[i + 1] == child);
            assert((order.sibling)(children.last().id) == Some(child.id));
        } else {
            assert(rows[i + 1] == children[i + 1]);
            assert((order.sibling)(children[i].id) == Some(children[i + 1].id));
        }
    }
}

proof fn complete<I>(order: Order<I>, marks: spec_fn(I) -> CachedBranch, parent: I, children: Seq<Branch<I>>)
    requires (order.live)(parent), marks(parent) is Ready, prefix(order, marks, parent, children, None),
    ensures physical(order, marks, Branch { id: parent, status: CachedBranch::Ready, children }),
{
    reveal(physical);
}

proof fn hidden<I>(order: Order<I>, marks: spec_fn(I) -> CachedBranch, node: I)
    requires (order.live)(node), marks(node) is Hidden,
    ensures physical(order, marks, Branch { id: node, status: CachedBranch::Hidden, children: Seq::empty() }),
{
    reveal(physical);
}

fn empty_children<I>() -> (children: Ghost<Seq<Branch<I>>>)
    ensures children@ == Seq::<Branch<I>>::empty(), no_unwind
{
    Ghost(Seq::empty())
}

fn push_child<I>(children: Ghost<Seq<Branch<I>>>, child: Ghost<Option<Branch<I>>>) -> (out: Ghost<Seq<Branch<I>>>)
    requires child@.is_some(), ensures out@ == children@.push(child@.unwrap()), no_unwind
{
    Ghost(children@.push(child@.unwrap()))
}

fn evidence<I: Copy>(node: I, state: CachedBranch, children: Ghost<Seq<Branch<I>>>) -> (out: Ghost<Option<Branch<I>>>)
    ensures out@ == Some(Branch { id: node, status: state, children: children@ }), no_unwind
{
    Ghost(Some(Branch { id: node, status: state, children: children@ }))
}

fn rejected<I>() -> (out: Ghost<Option<Branch<I>>>)
    ensures out@.is_none(), no_unwind
{
    Ghost(None)
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Checked<I> {
    ready: bool,
    #[cfg(verus_keep_ghost)]
    pub(crate) evidence: Ghost<Option<Branch<I>>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out.ready == ready, out.evidence == proof, no_unwind))]
fn checked<I>(ready: bool, #[cfg(verus_keep_ghost)] proof: Ghost<Option<Branch<I>>>) -> Checked<I> {
    Checked {
        ready,
        #[cfg(verus_keep_ghost)]
        evidence: proof,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires live(tree, node),
    ensures out == status(tree, node),
    no_unwind
))]
fn branch_status<T: Records + ?Sized>(tree: &T, node: T::Id) -> CachedBranch {
    let data = tree.record(node);
    if !region_policy::clean_branch_root(data.structural_change, data.flags.has_cycle()) { return CachedBranch::Reject; }
    if tree.params(node).disabled { return CachedBranch::Hidden; }
    if data.flags.check_state(X, Kind::Final) == SOLVED && data.flags.check_state(Y, Kind::Final) == SOLVED {
        CachedBranch::Ready
    } else { CachedBranch::Reject }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
        forall |id: T::Id| #[trigger] final(tree).layout_params(id) == old(tree).layout_params(id),
        out.ready ==> records_unchanged(old(tree), final(tree))
            && out.evidence@.is_some() && out.evidence@.unwrap().id == node
            && physical(old(tree).order(), marks(old(tree)), out.evidence@.unwrap())
            && physical(final(tree).order(), marks(final(tree)), out.evidence@.unwrap()),
    decreases depth,
    no_unwind
))]
fn scan<T: Records + ?Sized>(tree: &mut T, node: T::Id, depth: u8, counts: &mut SubtreeCounts) -> Checked<T::Id> {
    if depth == 0 { return checked(false, #[cfg(verus_keep_ghost)] rejected()); }
    match branch_status(tree, node) {
        CachedBranch::Reject => return checked(false, #[cfg(verus_keep_ghost)] rejected()),
        CachedBranch::Hidden => {
            #[cfg(verus_keep_ghost)]
            proof! { hidden(tree.order(), marks(tree), node); }
            return checked(true, #[cfg(verus_keep_ghost)] evidence(node, CachedBranch::Hidden, empty_children()));
        }
        CachedBranch::Ready => {}
    }
    counts.include(tree.record(node).flags);
    let mut next = tree.first(node);
    #[cfg(verus_keep_ghost)]
    let mut children = empty_children();
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(node); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant records_unchanged(old(tree), tree), depth > 0, live(tree, node), tree.order().ordered(),
            status(old(tree), node) is Ready, prefix(old(tree).order(), marks(old(tree)), node, children@, next),
            next.is_some() ==> tree.order().child(node, next.unwrap()),
        decreases sizing_pass::remaining(tree.order(), node, next),
    ))]
    loop {
        let Some(child) = next else {
            #[cfg(verus_keep_ghost)]
            proof! {
                complete(old(tree).order(), marks(old(tree)), node, children@);
                same_evidence(old(tree), tree, Branch { id: node, status: CachedBranch::Ready, children: children@ });
            }
            return checked(true, #[cfg(verus_keep_ghost)] evidence(node, CachedBranch::Ready, children));
        };
        #[cfg(verus_keep_ghost)]
        proof! { tree.order().node_facts(child); }
        let result = scan(tree, child, depth - 1, counts);
        if !result.ready {
            tree.edit(node).mark_children_changed();
            return checked(false, #[cfg(verus_keep_ghost)] rejected());
        }
        next = tree.sibling(child);
        #[cfg(verus_keep_ghost)]
        {
            proof! {
                let evidence = result.evidence@.unwrap();
                assert(physical(tree.order(), marks(tree), evidence));
                assert(records_unchanged(tree, old(tree)));
                same_evidence(tree, old(tree), evidence);
                extend(old(tree).order(), marks(old(tree)), node, children@, evidence);
            }
            children = push_child(children, result.evidence);
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(), result.is_some() ==> records_unchanged(old(tree), final(tree))
        && exists |branch: Branch<T::Id>| branch.id == node && #[trigger] physical(old(tree).order(), marks(old(tree)), branch),
    no_unwind
))]
pub(crate) fn counts<T: Records + ?Sized>(tree: &mut T, node: T::Id) -> Option<(u32, usize, bool)> {
    let mut counts = SubtreeCounts::empty();
    let checked = scan(tree, node, 24, &mut counts);
    if checked.ready {
        #[cfg(verus_keep_ghost)]
        proof! {
            let branch = checked.evidence@.unwrap();
            assert(branch.id == node && physical(old(tree).order(), marks(old(tree)), branch));
        }
        Some((counts.nodes, counts.blocks, counts.has_flow))
    } else { None }
}
