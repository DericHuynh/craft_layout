//! Ordered inputs shared by stack and wrap Fill shares and wrapping line extents.
use vstd::prelude::*;
use super::wrap_lines;

#[path = "../src/wrap_schedule.rs"]
pub mod kernel;
use kernel::{Producer,Request};

verus! {

pub struct Child<I> {
    pub id:I,
    pub in_flow:bool,
    pub has_fill:bool,
    pub share:[bool;3],
    pub cross:[bool;3],
}

pub open spec fn child_at<I>(children:Seq<Child<I>>,i:nat) -> Option<I> {
    if i<children.len() {Some(children[i as int].id)} else {None}
}

pub open spec fn distinct<I>(children:Seq<Child<I>>) -> bool {
    forall |i:int,j:int| 0<=i<j<children.len() ==> (#[trigger] children[i]).id!=(#[trigger] children[j]).id
}
pub open spec fn member<I>(children:Seq<Child<I>>,id:I) -> bool {
    exists |i:nat| i<children.len() && #[trigger] child_at(children,i)==Some(id)
}
pub open spec fn index<I>(children:Seq<Child<I>>,id:I) -> nat {
    choose |i:nat| i<children.len() && #[trigger] child_at(children,i)==Some(id)
}
pub open spec fn current<I>(children: Seq<Child<I>>, id:I) -> Child<I> {
    children[index(children,id) as int]
}
pub open spec fn selected<I>(child:Child<I>,producer:Producer) -> [bool;3] {
    if producer is Share {child.share} else {child.cross}
}
pub proof fn locate<I>(children:Seq<Child<I>>,i:nat,id:I)
    requires i<=children.len(), distinct(children), child_at(children,i)==Some(id),
    ensures member(children,id), index(children,id)==i, i<children.len(),
{
    assert(exists |j:nat| j<children.len() && child_at(children,j)==Some(id));
    let j=index(children,id);
    assert(children[i as int].id==children[j as int].id);
}

pub open spec fn own<I>(producer:Producer) -> Request<I> {
    match producer {
        Producer::Share=>Request::ParentMainFinal,
        Producer::Cross=>Request::ParentShare,
    }
}
pub open spec fn declaration<I>(id:I, producer:Producer, i:usize) -> Request<I> {
    match producer {
        Producer::Share=>Request::MainDeclaration(id,i),
        Producer::Cross=>Request::CrossDeclaration(id,i),
    }
}

pub open spec fn declarations<I>(id:I,producer:Producer,flags:&[bool;3],i:nat) -> Seq<Request<I>>
    decreases i,
{
    if i==0 {Seq::empty()} else {
        let prefix=declarations(id,producer,flags,(i-1) as nat);
        if flags[i-1] {prefix.push(declaration(id,producer,(i-1) as usize))} else {prefix}
    }
}

pub proof fn extend_declarations<I>(before:Seq<Request<I>>,child:I,producer:Producer,flags:&[bool;3],i:nat)
    requires i<3,
    ensures ({
        let previous=before+declarations(child,producer,flags,i);
        let next=before+declarations(child,producer,flags,i+1);
        if flags[i as int] {next==previous.push(declaration(child,producer,i as usize))} else {next==previous}
    }),
{
    if flags[i as int] {
        assert(before+declarations(child,producer,flags,i+1) =~=
            (before+declarations(child,producer,flags,i)).push(declaration(child,producer,i as usize)));
    }
}

pub open spec fn row_requests<I>(c:Child<I>,producer:Producer) -> Seq<Request<I>> {
    if !c.in_flow {Seq::empty()} else {
        match producer {
            Producer::Cross=>seq![Request::MainFinal(c.id)]+declarations(c.id,producer,&c.cross,3),
            Producer::Share if c.has_fill=>declarations(c.id,producer,&c.share,3),
            Producer::Share=>seq![Request::MainFinal(c.id)],
        }
    }
}

pub open spec fn child_requests<I>(children:Seq<Child<I>>,producer:Producer,n:nat) -> Seq<Request<I>>
    decreases n,
{
    if n==0 {Seq::empty()} else {
        child_requests(children,producer,(n-1) as nat)+row_requests(children[n-1],producer)
    }
}

pub proof fn extend_children<I>(before:Seq<Request<I>>,children:Seq<Child<I>>,producer:Producer,i:nat)
    requires i<children.len(),
    ensures before+child_requests(children,producer,i+1)
        == (before+child_requests(children,producer,i))+row_requests(children[i as int],producer),
{
    assert(before + child_requests(children,producer,i+1) =~=
        (before+child_requests(children,producer,i))+row_requests(children[i as int],producer));
}

}
