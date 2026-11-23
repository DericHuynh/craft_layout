//! Canonical readiness used when the structural planner keeps a parent.
use vstd::prelude::*;
use super::cycles::kernel::{IN_PROGRESS, SOLVED};
use super::cycles::dfs::{self, Edges, Region, Search, Task};
use super::production_schedule::{self as roots, NodeRequests};
use super::replay_prefix::{self as prefix, RootPrefix};
use super::dependencies::{self, Edge, Part};
use super::structural_plan::{Facts, Layout, SubtreeCut};

verus! {

spec fn pending(s:Search, key:int) -> bool {
    ||| (s.state)(key) == SOLVED
    ||| exists |i:int| 0<=i<s.todo.len() && s.todo[i]==Task::Finish(key)
    ||| (s.state)(key) != IN_PROGRESS &&
        exists |i:int| 0<=i<s.todo.len() && s.todo[i]==Task::Visit(key)
}

proof fn pending_after_step(s:Search, edges:Edges, seed:spec_fn(int)->Seq<u32>, key:int)
    requires s.todo.len()>0, pending(s,key),
    ensures pending(dfs::step(s,edges,seed,None).next,key),
{
    let task = s.todo.first();
    let target = task.key();
    let advance = dfs::step(s,edges,seed,None).next;
    let entered = task is Visit && dfs::fresh(s,target);
    let count = if entered { edges(target).len()+1 } else { 0 };
    assert(task == s.todo[0]);
    assert forall |i:int| 1<=i<s.todo.len() implies #[trigger] advance.todo[count+i-1]==s.todo[i] by {
        if entered { assert(dfs::requests(edges(target)).len()==edges(target).len()); }
        assert(s.todo.drop_first()[i-1]==s.todo[i]);
    }
    if (s.state)(key)==SOLVED || task==Task::Finish(key) {
        assert((advance.state)(key)==SOLVED);
    } else if entered && target==key {
        assert(advance.todo[count-1]==Task::Finish(key));
        assert(count-1<advance.todo.len());
    } else if exists |i:int| 0<=i<s.todo.len() && s.todo[i]==Task::Finish(key) {
        let i = choose |i:int| 0<=i<s.todo.len() && s.todo[i]==Task::Finish(key);
        assert(i>0);
        assert(0<=count+i-1<advance.todo.len());
        assert(advance.todo[count+i-1]==Task::Finish(key));
    } else {
        let i = choose |i:int| 0<=i<s.todo.len() && s.todo[i]==Task::Visit(key);
        assert((s.state)(key)!=IN_PROGRESS && (s.state)(key)!=SOLVED);
        if i==0 { assert(entered && target==key); }
        assert(0<=count+i-1<advance.todo.len());
        assert(advance.todo[count+i-1]==Task::Visit(key));
        assert((advance.state)(key)!=IN_PROGRESS);
    }
}

proof fn pending_at_exhaustion(s:Search, edges:Edges, seed:spec_fn(int)->Seq<u32>, gas:nat, key:int)
    requires pending(s,key), prefix::stop(s,edges,seed,gas).search.todo.len()==0,
    ensures (prefix::stop(s,edges,seed,gas).search.state)(key)==SOLVED,
    decreases gas,
{
    if s.todo.len()>0 {
        assert(gas>0);
        let next = dfs::step(s,edges,seed,None).next;
        pending_after_step(s,edges,seed,key);
        pending_at_exhaustion(next,edges,seed,(gas-1) as nat,key);
    }
}

proof fn finals_are_in_the_root_walk(nodes:Seq<NodeRequests>, i:int)
    requires 0<=i<nodes.len(),
    ensures roots::walk(nodes).contains(nodes[i].x) && roots::walk(nodes).contains(nodes[i].y),
    decreases nodes.len(),
{
    let walk = roots::walk(nodes);
    let first = nodes.first().order();
    if i>0 {
        let tail = nodes.drop_first();
        assert(tail[i-1]==nodes[i]);
        finals_are_in_the_root_walk(tail,i-1);
        let rest = roots::walk(tail);
        let x = choose |j:int| 0<=j<rest.len() && rest[j]==nodes[i].x;
        let y = choose |j:int| 0<=j<rest.len() && rest[j]==nodes[i].y;
        assert(walk[first.len()+x]==nodes[i].x && walk[first.len()+y]==nodes[i].y);
    } else {
        assert(walk[0]==nodes[0].x && walk[1]==nodes[0].y);
    }
}

/// A parent that precedes the edited subtree in the canonical visit list has
/// committed both Finals at that cut. This also covers pre-seeded Finals that
/// returned from their request without emitting a Finish event.
pub proof fn parent_finals_are_settled(cut:RootPrefix, i:int)
    requires cut.in_order(), 0<=i<cut.split,
        (cut.document.initial_state)(cut.before()[i].x)!=IN_PROGRESS,
        (cut.document.initial_state)(cut.before()[i].y)!=IN_PROGRESS,
    ensures (cut.settled().search.state)(cut.before()[i].x)==SOLVED,
        (cut.settled().search.state)(cut.before()[i].y)==SOLVED,
{
    let doc = cut.document;
    let start = cut.prefix_search();
    let walk = roots::walk(cut.before());
    let node = cut.before()[i];
    finals_are_in_the_root_walk(cut.before(),i);
    let x = choose |j:int| 0<=j<walk.len() && walk[j]==node.x;
    let y = choose |j:int| 0<=j<walk.len() && walk[j]==node.y;
    assert(start.todo[x]==Task::Visit(node.x) && start.todo[y]==Task::Visit(node.y));
    prefix::document_factors_at_a_root_cut(cut,doc.cached);
    pending_at_exhaustion(start,doc.edges,doc.provisional,doc.gas(),node.x);
    pending_at_exhaustion(start,doc.edges,doc.provisional,doc.gas(),node.y);
}

proof fn earlier_roots_do_not_start_the_region(s:Search, edges:Edges, seed:spec_fn(int)->Seq<u32>,
    gas:nat, inside:Region,
)
    requires
        forall |i:int| 0<=i<s.todo.len() ==> !inside((#[trigger] s.todo[i]).key()),
        forall |k:int,j:int| !inside(k) && 0<=j<edges(k).len() ==> !inside(#[trigger] edges(k)[j]),
    ensures ({
        let events = prefix::stop(s,edges,seed,gas).events;
        forall |i:int| 0<=i<events.len() ==> !inside((#[trigger] events[i]).target())
    }),
    decreases gas,
{
    if s.todo.len()>0 && gas>0 {
        let task = s.todo.first();
        let key = task.key();
        assert(task==s.todo[0] && !inside(key));
        let begin = task is Visit && dfs::fresh(s,key);
        let step = dfs::step(s,edges,seed,None);
        let count = if begin { edges(key).len()+1 } else { 0 };
        assert forall |i:int| 0<=i<step.next.todo.len() implies !inside((#[trigger] step.next.todo[i]).key()) by {
            if i<count {
                if i<edges(key).len() {
                    assert(step.next.todo[i]==Task::Visit(edges(key)[i]));
                } else { assert(step.next.todo[i]==Task::Finish(key)); }
            } else {
                assert(step.next.todo[i]==s.todo[i-count+1]);
            }
        }
        let left = (gas-1) as nat;
        earlier_roots_do_not_start_the_region(step.next,edges,seed,left,inside);
        let rest = prefix::stop(step.next,edges,seed,left).events;
        let now = prefix::stop(s,edges,seed,gas).events;
        if let Some(event) = step.event {
            assert(event.target()==key);
            assert forall |i:int| 0<=i<now.len() implies !inside((#[trigger] now[i]).target()) by {
                if i>0 { assert(now[i]==rest[i-1]); }
            }
        }
    }
}

pub proof fn independent_prefix_leaves_the_region_fresh(cut:RootPrefix)
    requires
        forall |i:int| 0<=i<cut.prefix_search().todo.len() ==>
            !cut.document.inside((#[trigger] cut.prefix_search().todo[i]).key()),
        forall |k:int,j:int| !cut.document.inside(k) && 0<=j<(cut.document.edges)(k).len() ==>
            !cut.document.inside(#[trigger] (cut.document.edges)(k)[j]),
    ensures cut.untouched_region(),
{
    let d = cut.document;
    earlier_roots_do_not_start_the_region(cut.prefix_search(),d.edges,d.provisional,d.gas(),|k:int|d.inside(k));
}

proof fn root_walk_belongs_to_outside_nodes(nodes:Seq<NodeRequests>, owner:spec_fn(int)->int, inside:Region)
    requires forall |i:int| 0<=i<nodes.len() ==> ({
        let node = #[trigger] nodes[i];
        node.owned_by(owner) && !inside(node.node)
    }),
    ensures forall |j:int| 0<=j<roots::walk(nodes).len() ==> !inside(owner(#[trigger] roots::walk(nodes)[j])),
    decreases nodes.len(),
{
    if nodes.len()>0 {
        let first = nodes.first();
        let rest = nodes.drop_first();
        assert(first==nodes[0]);
        assert forall |i:int| 0<=i<rest.len() implies ({
            let node = #[trigger] rest[i];
            node.owned_by(owner) && !inside(node.node)
        }) by { assert(rest[i]==nodes[i+1]); }
        root_walk_belongs_to_outside_nodes(rest,owner,inside);
        let here = first.order();
        let later = roots::walk(rest);
        assert forall |i:int| 0<=i<roots::walk(nodes).len() implies !inside(owner(#[trigger] roots::walk(nodes)[i])) by {
            if i<here.len() {
                assert(roots::walk(nodes)[i]==here[i]);
                assert(owner(here[i])==first.node);
            } else { assert(roots::walk(nodes)[i]==later[i-here.len()]); }
        }
    }
}

/// A prefix before the region's first node cannot evaluate anything inside it
/// when every dependency leaving a prefix owner stays in the exterior.
pub proof fn independent_preceding_visits_leave_region_fresh(cut:RootPrefix)
    requires
        forall |i:int| 0<=i<cut.before().len() ==> ({
            let node = #[trigger] cut.before()[i];
            node.owned_by(cut.document.owner) && !(cut.document.nodes)(node.node)
        }),
        forall |k:int,j:int| !cut.document.inside(k) && 0<=j<(cut.document.edges)(k).len() ==>
            !cut.document.inside(#[trigger] (cut.document.edges)(k)[j]),
    ensures cut.untouched_region(),
{
    let doc = cut.document;
    let before = cut.before();
    let walk = roots::walk(before);
    root_walk_belongs_to_outside_nodes(before,doc.owner,doc.nodes);
    assert forall |i:int| 0<=i<cut.prefix_search().todo.len() implies
        !doc.inside((#[trigger] cut.prefix_search().todo[i]).key()) by {
        assert(cut.prefix_search().todo[i]==Task::Visit(walk[i]));
    }
    independent_prefix_leaves_the_region_fresh(cut);
}

/// At an independent Free parent, the refresh scan rules out child-dependent
/// declarations. The parent's Finals can themselves depend on its ancestors.
/// The parent still occurs before the region in the canonical root walk.
pub struct FreeParent {
    pub tree:SubtreeCut,
    pub location:int,
    pub facts:Facts,
    pub parts:spec_fn(int)->Part,
    pub relationship:spec_fn(int,int)->Edge,
}

impl FreeParent {
    pub open spec fn supported(self, cut:RootPrefix) -> bool {
        let d = cut.document;
        let p = cut.before()[self.location];
        &&& cut.in_order() && 0<=self.location<cut.split
        &&& (d.initial_state)(p.x)!=IN_PROGRESS && (d.initial_state)(p.y)!=IN_PROGRESS
        &&& self.facts.layout is Free && self.facts.refreshes()
        &&& self.tree.valid() && (self.tree.parent)(self.tree.root)==Some(p.node)
        &&& !self.tree.inside.contains(p.node)
        &&& forall |node:int| (#[trigger] (d.nodes)(node)) == self.tree.inside.contains(node)
        &&& forall |k:int| #[trigger] (d.owner)(k)==p.node && (self.parts)(k) is Final ==> k==p.x || k==p.y
        &&& forall |i:int| 0<=i<cut.before().len() ==> ({
            let item = #[trigger] cut.before()[i];
            item.owned_by(d.owner) && !(d.nodes)(item.node)
        })
        &&& forall |k:int,j:int| 0<=j<(d.edges)(k).len() && d.inside(k)!=d.inside(#[trigger] (d.edges)(k)[j]) ==> ({
            let input = (d.edges)(k)[j];
            let link = (self.relationship)(k,input);
            let kind = (self.parts)(k);
            &&& self.tree.relates((d.owner)(k),(d.owner)(input),link)
            &&& dependencies::full_read(kind,(self.parts)(input),link)
            &&& !link.stack_axis
            &&& (d.owner)(k)==p.node && kind is Declared && kind->Declared_0.reads_children()
                ==> self.facts.reads_children
        })
    }
}

pub proof fn refreshed_free_parent_supplies_its_finals(cut:RootPrefix, boundary:FreeParent)
    requires boundary.supported(cut),
    ensures cut.untouched_region(), ({
        let d = cut.document;
        let flags = cut.settled().search.state;
        forall |k:int,j:int| 0<=j<(d.edges)(k).len() ==> ({
            let input = #[trigger] (d.edges)(k)[j];
            &&& !d.inside(k) ==> !d.inside(input)
            &&& d.inside(k) && !d.inside(input) ==> flags(input)==SOLVED
        })
    }),
{
    let d = cut.document;
    let p = cut.before()[boundary.location];
    parent_finals_are_settled(cut,boundary.location);
    assert(forall |k:int,j:int| 0<=j<(d.edges)(k).len() ==> ({
        let input = #[trigger] (d.edges)(k)[j];
        &&& !d.inside(k) ==> !d.inside(input)
        &&& d.inside(k) && !d.inside(input) ==> input==p.x || input==p.y
    })) by {
        assert forall |k:int,j:int| 0<=j<(d.edges)(k).len() implies ({
            let input = #[trigger] (d.edges)(k)[j];
            &&& !d.inside(k) ==> !d.inside(input)
            &&& d.inside(k) && !d.inside(input) ==> input==p.x || input==p.y
        }) by {
            let input = (d.edges)(k)[j];
            if d.inside(k)!=d.inside(input) {
                let link = (boundary.relationship)(k,input);
                let reader = (boundary.parts)(k);
                let provider = (boundary.parts)(input);
                let a = (d.owner)(k);
                let b = (d.owner)(input);
                assert(dependencies::full_read(reader,provider,link));
                assert(!link.stack_axis);
                assert(boundary.tree.relates(a,b,link));
                if d.inside(k) {
                    assert(link.source is Parent);
                    assert(a==boundary.tree.root && b==p.node);
                    assert(provider is Final);
                } else {
                    assert(link.source is Child);
                    assert(b==boundary.tree.root && a==p.node);
                    assert(reader is Declared && reader->Declared_0.reads_children());
                    assert(boundary.facts.reads_children);
                }
            }
        }
    }
    independent_preceding_visits_leave_region_fresh(cut);
}

}
