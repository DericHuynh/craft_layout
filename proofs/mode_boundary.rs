//! Boundaries for layout modes that consume a parent's shared state.
use vstd::prelude::*;
use super::{regions, structural_plan::{decisions, policy, Forest, Layout}};
use super::{block_schedule as block, wrap_schedule as wrap};

verus! {

/// A child that must rebuild its region and shares live flow metrics with
/// its parent. The child list here is the one the planner walks after the edit.
pub open spec fn flow_child_changed(children: Forest, in_flow: spec_fn(int) -> bool, i: int) -> bool
    decreases children,
{
    match children {
        Forest::Empty => false,
        Forest::Node { rest, .. } => {
            let plan = decisions(children).0;
            (in_flow)(i) && (plan->Node_direct || plan->Node_raise)
                || flow_child_changed(*rest, in_flow, i + 1)
        },
    }
}

/// Connect the planner's per-child facts to the live adapter sibling list.
/// `flow_parent` is the Block or Wrap classification of their parent.
pub open spec fn samples_attachment(children: Forest, in_flow: spec_fn(int) -> bool,
    i: int, flow_parent: bool) -> bool
    decreases children,
{
    match children {
        Forest::Empty => true,
        Forest::Node { facts, rest, .. } =>
            facts.in_parent_flow == policy::attached_flow_child((in_flow)(i), flow_parent)
                && samples_attachment(*rest, in_flow, i + 1, flow_parent),
    }
}

proof fn selected_flow_child_notifies_parent(children: Forest, in_flow: spec_fn(int) -> bool, i: int)
    requires flow_child_changed(children, in_flow, i), samples_attachment(children, in_flow, i, true),
    ensures decisions(children).1.affects_parent,
    decreases children,
{
    match children {
        Forest::Empty => {},
        Forest::Node { facts, rest, .. } => {
            let (plan, requests) = decisions(children);
            if (in_flow)(i) && (plan->Node_direct || plan->Node_raise) {
                assert(facts.informs_parent(plan->Node_raise));
                assert(requests.affects_parent);
            } else {
                selected_flow_child_notifies_parent(*rest, in_flow, i + 1);
            }
        },
    }
}

/// This uses the same live Block/Wrap attachment test as `plan_subtree` and
/// the region sizing entry guard. A selected attached child is covered by
/// the parent's region and cannot start a separate regional sizing walk.
pub proof fn changed_flow_child_rebuilds_the_parent(tree: Forest, in_flow: spec_fn(int) -> bool,
    start: nat, prior: Seq<regions::Interval>)
    requires tree is Node, tree->Node_facts.enabled, tree->Node_facts.layout is FlowOrGrid,
        flow_child_changed(*tree->Node_children, in_flow, 0),
        samples_attachment(*tree->Node_children, in_flow, 0, true),
    ensures ({
        let plan = decisions(tree).0;
        let end = start + 1 + regions::length(*plan->Node_children);
        &&& plan is Node
        &&& plan->Node_direct || plan->Node_raise
        &&& regions::collect(plan, start, prior) ==
                prior.push((start, end)) + regions::planned(*plan->Node_siblings, end).regions
    }),
{
    let kids = *tree->Node_children;
    selected_flow_child_notifies_parent(kids, in_flow, 0);
    let plan = decisions(tree).0;
    let end = start + 1 + regions::length(*plan->Node_children);
    assert(plan is Node);
    assert(plan->Node_direct || plan->Node_raise);
    regions::rollback_preserves_other_regions(plan, start, prior);
    assert(prior + regions::planned(plan, start).regions =~=
        prior.push((start, end)) + regions::planned(*plan->Node_siblings, end).regions);
}

pub open spec fn block_request_owner(request: block::kernel::Request<int>) -> int {
    match request { block::kernel::Request::Height(id) | block::kernel::Request::Margins(id) => id }
}

/// A retained Block producer issues neither the height nor the margin
/// summary request for a separately measured, free-positioned child.
pub proof fn free_child_is_outside_block_flow(children: Seq<block::Child<int>>, child: int, count: nat)
    requires count <= children.len(),
        forall |i:int| 0 <= i < count && (#[trigger] children[i]).id == child ==> !children[i].in_flow,
    ensures forall |i:int| 0 <= i < block::block_inputs(children,count).len() ==>
        block_request_owner(#[trigger] block::block_inputs(children,count)[i]) != child,
    decreases count,
{
    if count > 0 {
        let end = count - 1;
        let row = children[end];
        let prev = block::block_inputs(children,end as nat);
        let reads = block::block_inputs(children,count);
        free_child_is_outside_block_flow(children,child,end as nat);
        assert forall |i:int| 0 <= i < reads.len() implies block_request_owner(#[trigger] reads[i]) != child by {
            if i < prev.len() { assert(reads[i] == prev[i]); }
            else {
                assert(row.in_flow);
                assert(block_request_owner(reads[i]) == row.id);
            }
        }
    }
}

pub open spec fn wrap_request_child(request: wrap::kernel::Request<int>) -> Option<int> {
    match request {
        wrap::kernel::Request::ParentMainFinal | wrap::kernel::Request::ParentShare => None,
        wrap::kernel::Request::MainFinal(id) | wrap::kernel::Request::MainDeclaration(id, _)
            | wrap::kernel::Request::CrossDeclaration(id, _) => Some(id),
    }
}

proof fn wrap_declarations_stay_on_the_child(id: int, p: wrap::kernel::Producer, flags: &[bool;3], n: nat)
    requires n <= 3,
    ensures forall |i:int| 0 <= i < wrap::declarations(id,p,flags,n).len() ==>
        wrap_request_child(#[trigger] wrap::declarations(id,p,flags,n)[i]) == Some(id),
    decreases n,
{
    if n > 0 {
        let prior = wrap::declarations(id,p,flags,(n-1) as nat);
        let all = wrap::declarations(id,p,flags,n);
        wrap_declarations_stay_on_the_child(id,p,flags,(n-1) as nat);
        assert forall |i:int| 0 <= i < all.len() implies wrap_request_child(#[trigger] all[i]) == Some(id) by {
            if i < prior.len() { assert(all[i] == prior[i]); }
            else { assert(all[i] == wrap::declaration(id,p,(n-1) as usize)); }
        }
    }
}

/// Neither the Wrap share nor cross-flow producer reads any declaration of
/// a free-positioned child. Requests for the parent's own slots are separate.
pub proof fn free_child_is_outside_wrap_flow(children: Seq<wrap::Child<int>>, child: int,
    p: wrap::kernel::Producer, count: nat,
)
    requires count <= children.len(),
        forall |i:int| 0 <= i < count && (#[trigger] children[i]).id == child ==> !children[i].in_flow,
    ensures forall |i:int| 0 <= i < wrap::child_requests(children,p,count).len() ==>
        wrap_request_child(#[trigger] wrap::child_requests(children,p,count)[i]) != Some(child),
    decreases count,
{
    if count > 0 {
        let end = count-1;
        let row = children[end];
        let prev = wrap::child_requests(children,p,end as nat);
        let reads = wrap::child_requests(children,p,count);
        free_child_is_outside_wrap_flow(children,child,p,end as nat);
        wrap_declarations_stay_on_the_child(row.id,p,&row.share,3);
        wrap_declarations_stay_on_the_child(row.id,p,&row.cross,3);
        assert forall |i:int| 0 <= i < reads.len() implies wrap_request_child(#[trigger] reads[i]) != Some(child) by {
            if i < prev.len() { assert(reads[i] == prev[i]); }
            else {
                let slots = wrap::row_requests(row,p);
                let j = i - prev.len();
                assert(reads[i] == slots[j] && row.in_flow);
                assert(wrap_request_child(slots[j]) == Some(row.id));
            }
        }
    }
}

}
