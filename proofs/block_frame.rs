//! Connect ordered Block dependency requests and exported summaries to a
//! canonical regional measurement below a pre-seeded fixed Free parent.
use vstd::prelude::*;
use super::block_flow::{self, kernel::{BlockItem, BlockMargins, ScalarModel}};
use super::block_schedule::{self, Child, kernel::Request};
use super::cycles::{Storage, arguments, boundary::{FreeBoundary, free_boundary_directions}};
use super::replay_view::{Replay, rebuilt_producers_match_the_document};
use super::structural_plan::SubtreeCut;
use super::{Eval, Key, Rule, Value};

verus! {

pub struct ChildBox<F: Copy> {
    pub row: Child<int>,
    pub top: F,
    pub bottom: F,
    pub can_adjoin: bool,
    pub children_empty: bool,
}

#[verifier::reject_recursive_types(F)]
pub struct Block<F: ScalarModel> {
    pub owner: int,
    pub children: Seq<ChildBox<F>>,
    pub final_y: spec_fn(int) -> int,
    pub flow_y: spec_fn(int) -> int,
    pub height_bits: spec_fn(Seq<u32>) -> F,
    pub summary_bits: spec_fn(Seq<u32>) -> Option<BlockMargins<F>>,
    pub is_zero: spec_fn(F) -> bool,
    pub collapse_top: bool,
    pub collapse_bottom: bool,
}

impl<F: ScalarModel> Block<F> {
    pub open spec fn rows(self) -> Seq<Child<int>> {
        Seq::new(self.children.len(), |i:int| self.children[i].row)
    }

    pub open spec fn key_for(self, request: Request<int>) -> int {
        match request {
            Request::Height(child) => (self.final_y)(child),
            Request::Margins(child) => (self.flow_y)(child),
        }
    }

    pub open spec fn inputs_through(self, count:nat) -> Seq<int> {
        let schedule = block_schedule::block_inputs(self.rows(),count);
        Seq::new(schedule.len(), |i:int| self.key_for(schedule[i]))
    }

    pub open spec fn inputs(self) -> Seq<int> { self.inputs_through(self.children.len()) }

    pub open spec fn item(self, child: ChildBox<F>, values: Storage) -> BlockItem<F> {
        let id = child.row.id;
        let height = (self.height_bits)(values[(self.final_y)(id)]);
        let nested = if child.row.block {
            (self.summary_bits)(values[(self.flow_y)(id)])
        } else { None };
        block_flow::item_from_edges(child.top,child.bottom,height,
            child.can_adjoin && (self.is_zero)(height),child.children_empty,nested)
    }

    pub open spec fn visible_items(self, values: Storage, count: nat) -> Seq<BlockItem<F>>
        decreases count,
    {
        if count == 0 { Seq::empty() }
        else {
            let prefix = self.visible_items(values,(count-1) as nat);
            let child = self.children[count-1];
            if child.row.in_flow { prefix.push(self.item(child,values)) } else { prefix }
        }
    }

    pub open spec fn finish(self, values: Storage) -> (F, BlockMargins<F>) {
        block_flow::finish(block_flow::replay(self.visible_items(values,self.children.len()),
            self.collapse_top,self.collapse_bottom))
    }

    pub open spec fn coordinate(self, values: Storage, i: int) -> F {
        let earlier = self.visible_items(values,i as nat);
        block_flow::push(block_flow::replay(earlier,self.collapse_top,self.collapse_bottom),
            self.item(self.children[i],values)).1
    }

    pub open spec fn belongs_to_region(self, cut: SubtreeCut, r:Replay) -> bool {
        &&& cut.valid()
        &&& cut.inside.contains(self.owner)
        &&& forall|k:int| #[trigger] (r.nodes)(k) == cut.inside.contains(k)
        &&& forall|i:int| 0<=i<self.children.len() ==> ({
            let id=(#[trigger] self.children[i]).row.id;
            (cut.parent)(id)==Some(self.owner)
                && (r.owner)((self.final_y)(id))==id && (r.owner)((self.flow_y)(id))==id
        })
    }
}

// A Flow Finish is one logical value with two observations: its height and
// the optional outgoing margin group. Index allocation is erased from words;
// margin_storage.rs proves the one-based write and reindexing operations.
pub open spec fn flow_value<F: ScalarModel>(block: Block<F>, values: Storage, publishes: bool,
    implicit: spec_fn(BlockMargins<F>)->bool, encode: spec_fn(F,Option<BlockMargins<F>>)->Seq<u32>) -> Seq<u32>
{
    let result = block.finish(values);
    encode(result.0, if publishes && !implicit(result.1) { Some(result.1) } else { None })
}

proof fn every_observed_child_is_requested<F:ScalarModel>(block:Block<F>, i:int, count:nat)
    requires 0<=i<count<=block.children.len(), block.children[i].row.in_flow,
    ensures block.inputs_through(count).contains((block.final_y)(block.children[i].row.id)),
        block.children[i].row.block ==> block.inputs_through(count).contains((block.flow_y)(block.children[i].row.id)),
    decreases count,
{
    let rows=block.rows();
    let c=rows[count-1];
    let prior=block_schedule::block_inputs(rows,(count-1) as nat);
    let schedule=block_schedule::block_inputs(rows,count);
    assert(schedule == prior+block_schedule::child_inputs(c));
    if i == count-1 {
        assert(c == block.children[i].row);
        assert(schedule[prior.len() as int] == Request::Height(c.id));
        assert(block.inputs_through(count)[prior.len() as int] == (block.final_y)(c.id));
        if c.block {
            assert(schedule[prior.len() as int+1] == Request::Margins(c.id));
            assert(block.inputs_through(count)[prior.len() as int+1] == (block.flow_y)(c.id));
        }
    } else {
        every_observed_child_is_requested(block,i,(count-1) as nat);
        assert(block.inputs_through(count).take(prior.len() as int) =~= block.inputs_through((count-1) as nat)) by {
            assert forall |j:int| 0<=j<prior.len() implies
                schedule[j] == #[trigger] prior[j] by {};
        }
    }
}

proof fn shared_flow_arguments_give_same_items<F:ScalarModel>(block:Block<F>, left:Storage, right:Storage, count:nat)
    requires count<=block.children.len(), arguments(block.inputs(),left)==arguments(block.inputs(),right),
    ensures block.visible_items(left,count)==block.visible_items(right,count),
    decreases count,
{
    if count>0 {
        shared_flow_arguments_give_same_items(block,left,right,(count-1) as nat);
        let c=block.children[count-1];
        if c.row.in_flow {
            every_observed_child_is_requested(block,count-1,block.children.len());
            let y=(block.final_y)(c.row.id);
            let asks=block.inputs();
            let at=choose |j:int| 0<=j<asks.len() && asks[j]==y;
            assert(arguments(asks,left)[at] == arguments(asks,right)[at]);
            assert(left[y] == right[y]);
            if c.row.block {
                let flow=(block.flow_y)(c.row.id);
                let at=choose |j:int| 0<=j<asks.len() && asks[j]==flow;
                assert(arguments(asks,left)[at] == arguments(asks,right)[at]);
                assert(left[flow] == right[flow]);
            }
        }
    }
}

/// The recorded request list suffices to evaluate Flow, including provisionally
/// absent nested summaries. The arena never participates in the logical value.
pub proof fn flow_finish_reads_only_requested_children<F:ScalarModel>(block:Block<F>, left:Storage, right:Storage,
    publishes:bool, implicit:spec_fn(BlockMargins<F>)->bool, encode:spec_fn(F,Option<BlockMargins<F>>)->Seq<u32>)
    requires arguments(block.inputs(),left)==arguments(block.inputs(),right),
    ensures flow_value(block,left,publishes,implicit,encode)==flow_value(block,right,publishes,implicit,encode),
{
    shared_flow_arguments_give_same_items(block,left,right,block.children.len());
}

/// A fixed Free parent can expose only its pre-seeded Final slots to the
/// rebuilt region. The internal graph may contain Block Flow cycles.
pub proof fn fixed_free_parent_closes_block_region(r:Replay, b:FreeBoundary)
    requires b.describes(r.edges), r.owner==b.owner,
        forall|node:int| #[trigger] (r.nodes)(node) == b.included(node),
        super::cycles::dfs::bounded(r.document(),r.edges,r.n),
        forall|i:int| 0<=i<r.visits.len() ==> (#[trigger] r.visits[i]).owned_by(r.owner),
        forall|k:int| #[trigger] b.ready(k) ==> r.pinned(k),
        forall|k:int| #[trigger] r.inside(k) ==>
            (r.initial_state)(k)==(r.regional_state)(k)
                && r.initial.contains_key(k) && r.cached.contains_key(k) && r.initial[k]==r.cached[k],
        forall|k:int| #[trigger] r.pinned(k) ==>
            r.initial.contains_key(k) && r.cached.contains_key(k) && r.initial[k]==r.cached[k],
    ensures r.closed(),
{
    free_boundary_directions(b,r.edges);
    assert forall|k:int| r.inside(k) == #[trigger] b.inside(k) by {};
}

proof fn same_child_box<F:ScalarModel>(r:Replay, cut:SubtreeCut, block:Block<F>, i:int)
    requires r.closed(), block.belongs_to_region(cut,r),
        0<=i<block.children.len(),
    ensures block.item(block.children[i],r.full_sizing()) == block.item(block.children[i],r.rebuilt_sizing()),
{
    let child=block.children[i];
    let id=child.row.id;
    assert((cut.parent)(id)==Some(block.owner));
    assert(cut.inside.contains(id));
    assert((r.nodes)(id));
    rebuilt_producers_match_the_document(r,(block.final_y)(id));
    if child.row.block { rebuilt_producers_match_the_document(r,(block.flow_y)(id)); }
}

proof fn same_items<F:ScalarModel>(r:Replay, cut:SubtreeCut, block:Block<F>, count:nat)
    requires r.closed(), block.belongs_to_region(cut,r), count<=block.children.len(),
    ensures block.visible_items(r.full_sizing(),count) == block.visible_items(r.rebuilt_sizing(),count),
    decreases count,
{
    if count > 0 {
        same_items(r,cut,block,(count-1) as nat);
        if block.children[count-1].row.in_flow { same_child_box(r,cut,block,count-1); }
    }
}

/// Equality includes retained summaries, independent of which arena index was
/// assigned. Applying the same placement rule includes both Y coordinates and
/// the adapter's unchanged inputs for X, origin and pixel snapping.
pub proof fn block_frame_matches_full<F:ScalarModel>(r:Replay, cut:SubtreeCut, block:Block<F>, i:int,
    publishes:bool, implicit:spec_fn(BlockMargins<F>)->bool, encode:spec_fn(F,Option<BlockMargins<F>>)->Seq<u32>,
    eval:Eval,key:Key,rule:Rule, frame:Seq<Value>, encode_position:spec_fn(F,BlockItem<F>)->Seq<Value>,
)
    requires r.closed(), block.belongs_to_region(cut,r),
        0<=i<block.children.len(), block.children[i].row.in_flow,
        (r.edges)((block.flow_y)(block.owner))==block.inputs(),
        (r.owner)((block.flow_y)(block.owner)) == block.owner,
    ensures ({
        let full=r.full_sizing();
        let regional=r.rebuilt_sizing();
        let measured=(block.flow_y)(block.owner);
        &&& full[measured]==regional[measured]
        &&& (block.summary_bits)(full[measured])==(block.summary_bits)(regional[measured])
        &&& block.finish(full)==block.finish(regional)
        &&& flow_value(block,full,publishes,implicit,encode)==flow_value(block,regional,publishes,implicit,encode)
        &&& block.coordinate(full,i)==block.coordinate(regional,i)
        &&& (eval.place)(key,rule,frame+encode_position(block.coordinate(full,i),block.item(block.children[i],full)))
            == (eval.place)(key,rule,frame+encode_position(block.coordinate(regional,i),block.item(block.children[i],regional)))
    }),
{
    assert((r.nodes)(block.owner));
    rebuilt_producers_match_the_document(r,(block.flow_y)(block.owner));
    same_items(r,cut,block,block.children.len());
    same_items(r,cut,block,i as nat);
    same_child_box(r,cut,block,i);
}

}
