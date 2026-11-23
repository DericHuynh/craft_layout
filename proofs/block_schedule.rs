//! The block-only dependency graph reads each in-flow child's height before its
//! nested margin summary. Root requests use the ordinary X/Y order plus Flow Y.
use vstd::prelude::*;

#[path = "../src/block_schedule.rs"]
pub mod kernel;
use kernel::Request;

verus! {

pub struct Child<I> {
    pub id: I,
    pub in_flow: bool,
    pub block: bool,
}

pub open spec fn child_at<I>(list: Seq<Child<I>>, index: nat) -> Option<I> {
    if index < list.len() { Some(list[index as int].id) } else { None }
}

pub open spec fn unique<I>(list: Seq<Child<I>>) -> bool {
    forall |i:int,j:int| 0 <= i < j < list.len() ==> (#[trigger] list[i]).id != (#[trigger] list[j]).id
}

pub open spec fn id_index<I>(list: Seq<Child<I>>, id: I) -> nat {
    choose |index:nat| index < list.len() && (#[trigger] list[index as int]).id == id
}

pub proof fn locate<I>(list: Seq<Child<I>>, index: nat, id: I)
    requires unique(list), child_at(list,index) == Some(id),
    ensures id_index(list,id) == index, index < list.len(),
{
    let other = id_index(list,id);
    assert(list[index as int].id == id);
    assert(list[other as int].id == id);
}

pub fn begin_scan() -> (cursor: Ghost<nat>)
    ensures cursor@ == 0,
{
    Ghost(0nat)
}

pub fn step_scan(cursor: Ghost<nat>) -> (next: Ghost<nat>)
    ensures next@ == cursor@ + 1,
{
    Ghost(cursor@+1)
}

pub open spec fn child_inputs<I>(child: Child<I>) -> Seq<Request<I>> {
    if !child.in_flow { Seq::empty() }
    else if child.block { seq![Request::Height(child.id),Request::Margins(child.id)] }
    else { seq![Request::Height(child.id)] }
}

pub open spec fn block_inputs<I>(list: Seq<Child<I>>, count: nat) -> Seq<Request<I>>
    decreases count,
{
    if count == 0 { Seq::empty() }
    else { block_inputs(list,(count-1) as nat) + child_inputs(list[count-1]) }
}

pub proof fn append_child<I>(base: Seq<Request<I>>, list: Seq<Child<I>>, index: nat)
    requires index < list.len(),
    ensures ({
        let prior = base + block_inputs(list,index);
        let complete = base + block_inputs(list,index+1);
        let c = list[index as int];
        &&& !c.in_flow ==> complete == prior
        &&& c.in_flow && !c.block ==> complete == prior.push(Request::Height(c.id))
        &&& c.in_flow && c.block ==> complete == prior.push(Request::Height(c.id)).push(Request::Margins(c.id))
    }),
{
    let c = list[index as int];
    let prior = base + block_inputs(list,index);
    let next = child_inputs(c);
    let complete = base + block_inputs(list,index+1);
    assert(complete =~= prior + next);
    if !c.in_flow {
        assert(prior + next =~= prior);
    } else if c.block {
        assert(prior + next =~= prior.push(Request::Height(c.id)).push(Request::Margins(c.id)));
    } else {
        assert(prior + next =~= prior.push(Request::Height(c.id)));
    }
}

pub enum Sizing { Missing, Auto, Intrinsic, Flexible, Fixed }

pub open spec fn resolves(size: Sizing, horizontal: bool, regular: bool, context: Option<bool>) -> Sizing {
    match size {
        Sizing::Auto => if kernel::inline_auto(horizontal,regular,context.is_some()) {
            Sizing::Flexible
        } else { Sizing::Intrinsic },
        Sizing::Flexible if kernel::flex_uses_content_height(!horizontal,true,context==Some(true)) =>
            if regular { Sizing::Intrinsic } else { Sizing::Missing },
        x => x,
    }
}

pub open spec fn child_context(block: bool, vertical: Sizing, inherited: Option<bool>, free: bool) -> Option<bool> {
    kernel::in_flow_parent(if block { Some(kernel::auto_content_height(
        vertical is Auto || vertical is Intrinsic, vertical is Flexible, inherited==Some(true)))
    } else { None },free)
}

/// A block exports the same height context as its resolved declaration. Flex
/// bounds under auto height are ignored, so those declarations stop requesting
/// the parent's unresolved vertical final slot.
pub proof fn auto_height_breaks_vertical_dependency(
    vertical: Sizing, inherited: Option<bool>, free: bool,
)
    ensures
        child_context(true,vertical,inherited,free) == if free {
            None
        } else { Some(resolves(vertical,false,true,inherited) is Intrinsic) },
        resolves(Sizing::Flexible,false,true,Some(true)) is Intrinsic,
        resolves(Sizing::Flexible,false,false,Some(true)) is Missing,
        resolves(Sizing::Auto,true,true,Some(false)) is Flexible,
        resolves(Sizing::Auto,true,false,Some(false)) is Intrinsic,
{
    match vertical {
        Sizing::Missing | Sizing::Auto | Sizing::Intrinsic | Sizing::Flexible | Sizing::Fixed => {},
    }
}

pub open spec fn contexts(ancestors: Seq<(bool,Sizing,bool)>) -> Option<bool>
    decreases ancestors.len(),
{
    if ancestors.len() == 0 { None }
    else {
        let (block,vertical,free) = ancestors.last();
        child_context(block,vertical,contexts(ancestors.drop_last()),free)
    }
}

/// Descendants get the same inherited height context after a rebuild starting
/// at an identical non-flow boundary. Each record describes the next edge's
/// parent layout and child eligibility.
pub proof fn equivalent_prefix_resolves_identically(full:Seq<(bool,Sizing,bool)>, partial:Seq<(bool,Sizing,bool)>)
    requires full == partial,
    ensures contexts(full) == contexts(partial),
{
}


/// An auto-height starting block propagates the context through any number of
/// in-flow Block descendants whose Y declaration is auto, intrinsic or flex.
/// Consequently a flex regular declaration becomes intrinsic and each flex
/// bound is absent throughout that inherited context.
pub proof fn auto_height_propagates_down_the_block_chain(ancestors: Seq<(bool,Sizing,bool)>)
    requires ancestors.len()>0, ancestors.first().1 is Auto || ancestors.first().1 is Intrinsic,
        forall |i:int| 0<=i<ancestors.len() ==> ({
            let entry=#[trigger] ancestors[i];
            entry.0 && !entry.2 && (entry.1 is Auto || entry.1 is Intrinsic || entry.1 is Flexible)
        }),
    ensures contexts(ancestors)==Some(true),
    decreases ancestors.len(),
{
    let first=ancestors.first();
    let last=ancestors.last();
    assert(first==ancestors[0] && last==ancestors[ancestors.len()-1]);
    if ancestors.len()==1 {
        assert(first==last);
    } else {
        let prefix=ancestors.drop_last();
        assert(prefix.first()==first);
        assert forall|i:int| 0<=i<prefix.len() implies ({
            let entry=#[trigger] prefix[i];
            entry.0 && !entry.2 && (entry.1 is Auto || entry.1 is Intrinsic || entry.1 is Flexible)
        }) by { assert(prefix[i]==ancestors[i]); }
        auto_height_propagates_down_the_block_chain(prefix);
    }
}

}
