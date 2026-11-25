//! The solver's per-node root visit order includes the flow-producing slots.
use vstd::prelude::*;
use super::cycles::dfs::{project, project_append, requests, Region};
#[path = "../src/root_requests.rs"]
pub(crate) mod kernel;
use kernel::visit_sizing_roots;

verus! {

pub open spec fn extra(slot: Option<int>) -> Seq<int> {
    match slot { Some(i) => seq![i], None => Seq::empty() }
}

pub struct NodeRequests {
    pub node: int,
    pub x: int,
    pub y: int,
    pub block_flow: Option<int>,
    pub wrap_share: Option<int>,
}

impl NodeRequests {
    pub open spec fn order(self) -> Seq<int> {
        seq![self.x, self.y] + extra(self.block_flow) + extra(self.wrap_share)
    }

    pub open spec fn owned_by(self, owner: spec_fn(int) -> int) -> bool {
        forall |i:int| 0 <= i < self.order().len() ==> owner(#[trigger] self.order()[i]) == self.node
    }
}

// Use the same inlined root visits as solve_subtree. Requests for slots already
// initialized by preparation have no Begin/Finish events in the DFS model.
pub fn canonical_requests(x: int, y:int, flow: Option<int>, share: Option<int>) -> (out: Vec<int>)
    ensures out@ == seq![x,y] + extra(flow) + extra(share),
{
    let mut out = Vec::new();
    visit_sizing_roots!(
        x, y;
        axis => { out.push(axis); };
        flow.is_some() => { out.push(flow.unwrap()); };
        share.is_some() => { out.push(share.unwrap()); }
    );
    out
}

pub open spec fn walk(nodes: Seq<NodeRequests>) -> Seq<int>
    decreases nodes.len(),
{
    if nodes.len() == 0 { Seq::empty() }
    else { nodes.first().order() + walk(nodes.drop_first()) }
}

pub open spec fn region_nodes(nodes: Seq<NodeRequests>, inside: Region) -> Seq<NodeRequests>
    decreases nodes.len(),
{
    if nodes.len() == 0 { Seq::empty() } else {
        let rest = region_nodes(nodes.drop_first(),inside);
        if inside(nodes.first().node) { seq![nodes.first()] + rest } else { rest }
    }
}

proof fn lift_append(a: Seq<int>, b: Seq<int>)
    ensures requests(a+b) == requests(a) + requests(b),
{
    assert(requests(a+b) =~= requests(a) + requests(b));
}

proof fn projection_homogeneous(keys: Seq<int>, inside: Region, include: bool)
    requires forall |i:int| 0 <= i < keys.len() ==> inside(#[trigger] keys[i]) == include,
    ensures project(requests(keys),inside) == if include { requests(keys) } else { Seq::empty() },
    decreases keys.len(),
{
    if keys.len() > 0 {
        assert(requests(keys).drop_first() =~= requests(keys.drop_first()));
        assert forall |i:int| 0 <= i < keys.drop_first().len() implies inside(#[trigger] keys.drop_first()[i]) == include by {
            assert(keys.drop_first()[i] == keys[i+1]);
        }
        assert(requests(keys).first().key() == keys[0]);
        projection_homogeneous(keys.drop_first(),inside,include);
        assert(seq![requests(keys).first()] + requests(keys).drop_first() =~= requests(keys));
    }
}

/// Ordinary, Block and Wrap nodes retain their same intra-node entry order,
/// including when a measurement region begins between two such nodes.
pub proof fn canonical_order_projects(nodes: Seq<NodeRequests>, inside: Region, owner: spec_fn(int) -> int)
    requires forall |i:int| 0 <= i < nodes.len() ==> (#[trigger] nodes[i]).owned_by(owner),
    ensures project(requests(walk(nodes)),|k:int|inside(owner(k))) ==
        requests(walk(region_nodes(nodes,inside))),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let head = nodes.first();
        let tail = nodes.drop_first();
        let retained = region_nodes(tail,inside);
        let scope = |k:int| inside(owner(k));
        assert(head == nodes[0]);
        assert forall |i:int| 0 <= i < tail.len() implies (#[trigger] tail[i]).owned_by(owner) by {
            assert(tail[i] == nodes[i+1]);
        }
        canonical_order_projects(tail,inside,owner);
        assert forall |i:int| 0 <= i < head.order().len() implies scope(#[trigger] head.order()[i]) == inside(head.node) by {};
        projection_homogeneous(head.order(),scope,inside(head.node));
        lift_append(head.order(),walk(tail));
        project_append(requests(head.order()),requests(walk(tail)),scope);
        if inside(head.node) {
            assert((seq![head] + retained).drop_first() =~= retained);
            lift_append(head.order(),walk(retained));
        }
    } else { assert(requests(walk(nodes)) =~= Seq::empty()); }
}

}
