//! The ordinary stack's EvenShare producer and its ordered Fill budget.
use vstd::prelude::*;
use super::cycles::{Storage, arguments};
use super::replay_view::{Replay, rebuilt_producers_match_the_document};
use super::wrap_schedule::{self, Child, kernel::{Producer, Request}};

#[path = "../src/fill_collection.rs"]
pub mod kernel;
use kernel::{FillCollection, NumericModel};

verus! {

pub open spec fn fresh<F:NumericModel>(budget:F) -> FillCollection<F> {
    FillCollection { budget, weight:F::zero_bits(), worst:None }
}

pub open spec fn charge<F:NumericModel>(state:FillCollection<F>,cost:F) -> FillCollection<F> {
    FillCollection { budget:F::charge(state.budget,cost), ..state }
}

pub open spec fn add_weight<F:NumericModel>(state:FillCollection<F>,weight:F) -> FillCollection<F> {
    FillCollection { weight:F::sum(state.weight,weight), ..state }
}

pub open spec fn record_worst<F:NumericModel>(state:FillCollection<F>,weight:F) -> FillCollection<F> {
    FillCollection { worst:Some(F::max_weight(state.worst,weight)), ..state }
}

pub open spec fn finish<F:NumericModel>(state:FillCollection<F>) -> (F,F,Option<F>) {
    (F::clamp_nonnegative(state.budget),state.weight,state.worst)
}

pub struct Bounds<F> {
    pub content: Option<F>,
    pub min: Option<F>,
    pub max: Option<F>,
    pub capped_by_content: bool,
    pub weight: F,
}

pub struct ChildShare<F> {
    pub row: Child<int>,
    pub start: F,
    pub end: F,
    pub weight: F,
    pub max_is_fill: bool,
}

pub struct Bundle<F:NumericModel> {
    pub totals: FillCollection<F>,
    pub bounds: Seq<Bounds<F>>,
}

#[verifier::reject_recursive_types(F)]
pub struct Stack<F:NumericModel> {
    pub parent: int,
    pub children: Seq<ChildShare<F>>,
    pub final_on_main: spec_fn(int)->int,
    pub declaration: spec_fn(int,usize)->int,
    pub read: spec_fn(Seq<u32>)->F,
    // Includes the parent's padding and total spacing (locally known).
    pub initial_budget: spec_fn(F)->F,
}

impl<F:NumericModel> Stack<F> {
    pub open spec fn rows(self)->Seq<Child<int>> {
        Seq::new(self.children.len(),|i:int| self.children[i].row)
    }

    pub open spec fn key(self,req:Request<int>)->int {
        match req {
            Request::ParentMainFinal => (self.final_on_main)(self.parent),
            Request::MainFinal(child) => (self.final_on_main)(child),
            Request::MainDeclaration(child,kind) => (self.declaration)(child,kind),
            _ => arbitrary(),
        }
    }

    pub open spec fn events(self,count:nat)->Seq<Request<int>> {
        seq![wrap_schedule::own::<int>(Producer::Share)]
            + wrap_schedule::child_requests(self.rows(),Producer::Share,count)
    }

    pub open spec fn reads(self,count:nat)->Seq<int> {
        let req=self.events(count);
        Seq::new(req.len(),|i:int|self.key(req[i]))
    }

    pub open spec fn declared(self,row:Child<int>,kind:usize,cache:Storage)->Option<F> {
        if row.share[kind as int] { Some((self.read)(cache[(self.declaration)(row.id,kind)])) }
        else { None }
    }

    pub open spec fn bounds(self,child:ChildShare<F>,cache:Storage)->Bounds<F> {
        let content=self.declared(child.row,0,cache);
        Bounds {
            content,
            min:self.declared(child.row,1,cache), max:self.declared(child.row,2,cache),
            capped_by_content:content.is_some() && child.max_is_fill, weight:child.weight,
        }
    }

    pub open spec fn collection(self,cache:Storage,count:nat)->Bundle<F>
        decreases count,
    {
        if count==0 {
            let size=(self.read)(cache[(self.final_on_main)(self.parent)]);
            Bundle { totals:fresh((self.initial_budget)(size)), bounds:Seq::empty() }
        } else {
            let prior=self.collection(cache,(count-1) as nat);
            let child=self.children[count-1];
            if !child.row.in_flow { prior } else {
                let totals=charge(prior.totals,F::sum(child.start,child.end));
                if child.row.has_fill {
                    let bounds=self.bounds(child,cache);
                    let totals=add_weight(totals,bounds.weight);
                    if kernel::has_constraint(bounds.content,bounds.min,bounds.max) {
                        Bundle { totals, bounds:prior.bounds.push(bounds) }
                    } else {
                        Bundle { totals:record_worst(totals,bounds.weight), bounds:prior.bounds }
                    }
                } else {
                    let size=(self.read)(cache[(self.final_on_main)(child.row.id)]);
                    Bundle { totals:charge(totals,size), bounds:prior.bounds }
                }
            }
        }
    }
}

proof fn declaration_is_in_request<I>(row:Child<I>,i:usize,n:nat)
    requires i<n<=3, row.share[i as int],
    ensures wrap_schedule::declarations(row.id,Producer::Share,&row.share,n)
        .contains(Request::MainDeclaration(row.id,i)),
    decreases n,
{
    let previous=wrap_schedule::declarations(row.id,Producer::Share,&row.share,(n-1) as nat);
    let all=wrap_schedule::declarations(row.id,Producer::Share,&row.share,n);
    if i as int==n-1 {
        assert(all[previous.len() as int]==Request::MainDeclaration(row.id,i));
    } else {
        declaration_is_in_request(row,i,(n-1) as nat);
        assert(all.take(previous.len() as int) =~= previous);
    }
}

proof fn row_observation_is_requested<F:NumericModel>(stack:Stack<F>,i:int,count:nat,req:Request<int>)
    requires 0<=i<count<=stack.children.len(),
        wrap_schedule::row_requests(stack.children[i].row,Producer::Share).contains(req),
    ensures stack.reads(count).contains(stack.key(req)),
    decreases count,
{
    let before=stack.events((count-1) as nat);
    let after=stack.events(count);
    let last=stack.rows()[count-1];
    wrap_schedule::extend_children(seq![wrap_schedule::own::<int>(Producer::Share)],stack.rows(),Producer::Share,(count-1) as nat);
    assert(after==before+wrap_schedule::row_requests(last,Producer::Share));
    if i==count-1 {
        let reads=wrap_schedule::row_requests(last,Producer::Share);
        assert(last==stack.children[i].row);
        let j=choose |j:int| 0<=j<reads.len() && reads[j]==req;
        assert(after[before.len()+j]==req);
        assert(stack.reads(count)[before.len()+j]==stack.key(req));
    } else {
        row_observation_is_requested(stack,i,(count-1) as nat,req);
        assert(stack.reads(count).take(before.len() as int) =~= stack.reads((count-1) as nat));
    }
}

proof fn requested_word_agrees(keys:Seq<int>,left:Storage,right:Storage,key:int)
    requires keys.contains(key), arguments(keys,left)==arguments(keys,right),
    ensures left[key]==right[key],
{
    let i=choose |i:int| 0<=i<keys.len() && keys[i]==key;
    assert(arguments(keys,left)[i]==arguments(keys,right)[i]);
}

/// The ordinary stack consumes exactly the slot values selected by the shared
/// Share traversal. Equal ordered arguments give the identical rounding
/// sequence, constraint order, and unconstrained-weight summary at Finish.
pub proof fn ordered_inputs_determine_bundle<F:NumericModel>(stack:Stack<F>,left:Storage,right:Storage,count:nat)
    requires count<=stack.children.len(),
        arguments(stack.reads(stack.children.len()),left)==arguments(stack.reads(stack.children.len()),right),
    ensures stack.collection(left,count)==stack.collection(right,count),
    decreases count,
{
    let full=stack.children.len();
    let keys=stack.reads(full);
    if count==0 {
        let key=(stack.final_on_main)(stack.parent);
        assert(stack.events(full)[0]==Request::ParentMainFinal);
        assert(keys[0]==key);
        requested_word_agrees(keys,left,right,key);
    } else {
        ordered_inputs_determine_bundle(stack,left,right,(count-1) as nat);
        let child=stack.children[count-1];
        let row=child.row;
        if row.in_flow {
            if row.has_fill {
                assert forall |k:usize| k<3 implies #[trigger] stack.declared(row,k,left)==stack.declared(row,k,right) by {
                    if row.share[k as int] {
                        let r=Request::MainDeclaration(row.id,k);
                        declaration_is_in_request(row,k,3);
                        row_observation_is_requested(stack,count-1,full,r);
                        requested_word_agrees(keys,left,right,stack.key(r));
                    }
                }
                assert(stack.bounds(child,left)==stack.bounds(child,right));
            } else {
                let r=Request::MainFinal(row.id);
                assert(wrap_schedule::row_requests(row,Producer::Share)[0]==r);
                row_observation_is_requested(stack,count-1,full,r);
                requested_word_agrees(keys,left,right,stack.key(r));
            }
        }
    }
}

pub open spec fn share<F:NumericModel>(stack:Stack<F>,snapshot:Storage,
    distribute:spec_fn(Seq<Bounds<F>>,F,F,Option<F>)->F) -> F
{
    let data=stack.collection(snapshot,stack.children.len());
    let (budget,weight,worst)=finish(data.totals);
    distribute(data.bounds,budget,weight,worst)
}

pub proof fn ordered_inputs_determine_even_share<F:NumericModel>(stack:Stack<F>,left:Storage,right:Storage,
    distribute:spec_fn(Seq<Bounds<F>>,F,F,Option<F>)->F)
    requires arguments(stack.reads(stack.children.len()),left)==arguments(stack.reads(stack.children.len()),right),
    ensures share(stack,left,distribute)==share(stack,right,distribute),
{
    ordered_inputs_determine_bundle(stack,left,right,stack.children.len());
}

/// An ordinary child consumes the EvenShare scalar and its own weight. There
/// are no child line words. The usual main-axis final slot then applies its
/// bounds. Internal cycles can read a provisional zero before that share is
/// finalized, and canonical replay preserves the same provisional reads.
pub proof fn closed_stack_share_matches_document<F:NumericModel>(r:Replay,stack:Stack<F>,producer:int,
    weight:F,target:spec_fn(F,F)->F)
    requires r.closed(), r.inside(producer), (r.edges)(producer)==stack.reads(stack.children.len()),
    ensures ({
        let full=r.full_sizing(); let region=r.rebuilt_sizing();
        &&& full.contains_key(producer) && region.contains_key(producer)
        &&& full[producer]==region[producer]
        &&& target((stack.read)(full[producer]),weight)==target((stack.read)(region[producer]),weight)
    }),
{
    rebuilt_producers_match_the_document(r,producer);
}

}
