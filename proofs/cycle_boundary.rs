//! Replay an ordinary dirty subtree below a fixed-pixel Free parent.
use super::{Event, Storage, Compute, replay, kernel};
use super::dfs::*;
use crate::dependencies::{self, Part, Edge, Source};
use crate::{Eval, Key, Rule, Value, Geometry, Work, valid_route, writes, requested_work_is_executed};
use crate::placement::{PathEdge, PlacementWork};
use crate::structural_plan::SubtreeCut;
use crate::retained_view::Outputs;
use vstd::prelude::*;

verus! {

/// The ordinary branch of solve_subtree requests the two Final slots in
/// this order. Extra Wrap and Block root requests are outside this fragment.
/// Already-ready slots can be included as no-op requests.
pub open spec fn local_roots(node:int, finals:spec_fn(int,bool)->int) -> Seq<int> {
    let order = kernel::canonical_axes(false,true);
    seq![finals(node,order[0]), finals(node,order[1])]
}

pub open spec fn document_roots(nodes:Seq<int>, finals:spec_fn(int,bool)->int) -> Seq<int>
    decreases nodes.len(),
{
    if nodes.len()==0 { Seq::empty() }
    else { local_roots(nodes.first(),finals)+document_roots(nodes.drop_first(),finals) }
}

proof fn requests_append(a:Seq<int>,b:Seq<int>)
    ensures requests(a+b) == requests(a)+requests(b),
{
    assert(requests(a+b) =~= requests(a)+requests(b));
}

proof fn two_roots_project(
    node:int, inside:Region, finals:spec_fn(int,bool)->int, owner:spec_fn(int)->int,
)
    requires owner(finals(node,false)) == node && owner(finals(node,true)) == node,
    ensures project(requests(local_roots(node,finals)),|k:int|inside(owner(k))) ==
        (if inside(node) { requests(local_roots(node,finals)) } else { Seq::<Task>::empty() }),
{
    let roots = requests(local_roots(node,finals));
    assert(roots =~= seq![Task::Visit(finals(node,false)),Task::Visit(finals(node,true))]);
    assert(roots.drop_first() =~= seq![roots[1]]);
    assert(roots.drop_first().drop_first() =~= Seq::<Task>::empty());
    reveal_with_fuel(project,3);
}

pub open spec fn region_nodes(nodes: Seq<int>, inside: Region) -> Seq<int>
    decreases nodes.len(),
{
    if nodes.len() == 0 { Seq::empty() } else {
        let next = region_nodes(nodes.drop_first(),inside);
        if inside(nodes.first()) { seq![nodes.first()] + next } else { next }
    }
}

/// Restricting document preorder to the region preserves the canonical X/Y
/// sequence at each included node, whether it is an ancestor or a leaf.
pub proof fn region_roots(
    nodes:Seq<int>, finals:spec_fn(int,bool)->int, owner:spec_fn(int)->int, inside:Region,
)
    requires forall|i:int| 0<=i<nodes.len() ==> ({
        let this=#[trigger] nodes[i];
        owner(finals(this,false))==this && owner(finals(this,true))==this
    }),
    ensures project(requests(document_roots(nodes,finals)),|k:int|inside(owner(k))) ==
        requests(document_roots(region_nodes(nodes,inside),finals)),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let head = nodes.first();
        let tail = nodes.drop_first();
        assert(nodes[0] == head);
        assert forall|i:int| 0<=i<tail.len() implies ({
            let this=#[trigger] tail[i];
            owner(finals(this,false))==this && owner(finals(this,true))==this
        }) by { assert(tail[i]==nodes[i+1]); }
        region_roots(tail,finals,owner,inside);
        two_roots_project(head,inside,finals,owner);
        let a = local_roots(head,finals);
        let b = document_roots(tail,finals);
        requests_append(a,b);
        super::dfs::project_append(requests(a),requests(b),|k:int|inside(owner(k)));
        if inside(head) {
            let rest = region_nodes(tail,inside);
            assert((seq![head] + rest).first() == head);
            assert((seq![head] + rest).drop_first() =~= rest);
            requests_append(a,document_roots(rest,finals));
        }
    } else { assert(requests(document_roots(nodes,finals)) =~= Seq::<Task>::empty()); }
}

/// Along a subtree cut every cross-node slot request follows the root-parent
/// edge. A fixed Free parent exposes pre-seeded Final slots and cannot request
/// measurements inside the region.
pub struct FreeBoundary {
    pub cut: SubtreeCut,
    pub parent: int,
    pub owner: spec_fn(int) -> int,
    pub part: spec_fn(int) -> Part,
    pub near: spec_fn(int,int) -> Edge,
}

impl FreeBoundary {
    pub open spec fn included(self, node:int) -> bool { self.cut.inside.contains(node) }
    pub open spec fn inside(self, k:int) -> bool { self.included((self.owner)(k)) }
    pub open spec fn ready(self, k:int) -> bool { (self.owner)(k)==self.parent && (self.part)(k) is Final }

    pub open spec fn describes(self, edges:Edges) -> bool {
        &&& self.cut.valid() && !self.included(self.parent)
        &&& (self.cut.parent)(self.cut.root) == Some(self.parent)
        &&& forall|k:int,j:int| 0<=j<edges(k).len() && self.inside(k)!=self.inside(#[trigger] edges(k)[j]) ==> ({
            let d=edges(k)[j];
            let near=(self.near)(k,d);
            &&& self.cut.relates((self.owner)(k),(self.owner)(d),near)
            &&& dependencies::full_read((self.part)(k),(self.part)(d),near)
            &&& !near.stack_axis && !near.grid_main
            &&& (self.owner)(k) == self.parent && (self.part)(k) is Declared ==> (self.part)(k)->Declared_0 is Constant
        })
    }

    pub open spec fn links(self,edges:Edges) -> bool {
        forall|k:int,j:int| 0<=j<edges(k).len() ==> ({
            let d=#[trigger] edges(k)[j];
            &&& self.inside(k) && !self.inside(d) ==> self.ready(d)
            &&& !self.inside(k) ==> !self.inside(d)
        })
    }
}

pub proof fn free_boundary_directions(b:FreeBoundary,edges:Edges)
    requires b.describes(edges),
    ensures b.links(edges),
{
    assert forall|k:int,j:int| 0<=j<edges(k).len() implies ({
        let d=#[trigger] edges(k)[j];
        &&& b.inside(k) && !b.inside(d) ==> b.ready(d)
        &&& !b.inside(k) ==> !b.inside(d)
    }) by {
        let d=edges(k)[j];
        if b.inside(k)!=b.inside(d) {
            let near=(b.near)(k,d);
            let k_node = (b.owner)(k);
            let d_node = (b.owner)(d);
            assert(dependencies::full_read((b.part)(k),(b.part)(d),near));
            if b.inside(k) {
                assert(near.source is Parent);
                assert((b.cut.parent)(k_node) == Some(d_node));
                assert(k_node == b.cut.root);
                if let Part::Declared(form)=(b.part)(k) {
                    dependencies::declaration_sources(form,false);
                }
            } else {
                assert(near.source is Child);
                assert((b.cut.parent)(d_node) == Some(k_node));
                assert(d_node == b.cut.root);
                assert(k_node == b.parent);
            }
        }
    }
}

pub(crate) proof fn ready_nodes_are_not_rewritten(
    s:Search, edges:Edges, initial:spec_fn(int)->Seq<u32>, ready:Region, gas:nat,
)
    requires
        forall|k:int| #[trigger] ready(k) ==> (s.state)(k)==kernel::SOLVED,
        forall|i:int| 0<=i<s.todo.len() && (#[trigger] s.todo[i]) is Finish ==> !ready(s.todo[i].key()),
    ensures ({
        let events=drive(s,edges,initial,None,|_:int|true,gas).0;
        forall|i:int| 0<=i<events.len() ==> ({
            let event=#[trigger] events[i];
            &&& !ready(event.target())
            &&& event is Finish ==> event.inputs()==edges(event.target())
        })
    }),
    decreases gas,
{
    if gas>0 && s.todo.len()>0 {
        let t=s.todo.first();
        let k=t.key();
        let it=step(s,edges,initial,None);
        if ready(k) {
            assert(t==s.todo[0]);
            assert(it.event.is_none());
            assert(it.next.state==s.state);
        }
        assert forall|i:int| 0<=i<it.next.todo.len() && (#[trigger] it.next.todo[i]) is Finish
            implies !ready(it.next.todo[i].key()) by {
            if t is Visit && fresh(s,k) {
                let count=edges(k).len();
                if i<count {
                    assert(it.next.todo[i]==Task::Visit(edges(k)[i]));
                } else if i==count {
                    assert(it.next.todo[i]==Task::Finish(k));
                } else {
                    assert(it.next.todo[i]==s.todo[i-count]);
                }
            } else {
                assert(it.next.todo[i]==s.todo[i+1]);
            }
        }
        let restgas=(gas-1) as nat;
        ready_nodes_are_not_rewritten(it.next,edges,initial,ready,restgas);
        if let Some(e)=it.event {
            let rest=drive(it.next,edges,initial,None,|_:int|true,restgas).0;
            let events=drive(s,edges,initial,None,|_:int|true,gas).0;
            assert(!ready(e.target()) && (e is Finish ==> e.inputs()==edges(e.target())));
            assert forall|i:int| 0<=i<events.len() implies ({
                let event=#[trigger] events[i];
                &&& !ready(event.target())
                &&& event is Finish ==> event.inputs()==edges(event.target())
            }) by {
                if i>0 { assert(events[i]==rest[i-1]); }
                else { assert(events[i]==e); }
            }
        }
    }
}

pub(crate) proof fn ready_value_is_retained(events:Seq<Event>, a:Storage, eval:Compute, k:int)
    requires a.contains_key(k),
        forall|i:int| 0<=i<events.len() ==> (#[trigger] events[i]).target()!=k,
    ensures replay(events,a,eval).contains_key(k), replay(events,a,eval)[k]==a[k],
    decreases events.len(),
{
    if events.len()>0 {
        let prefix=events.drop_last();
        assert forall|i:int| 0<=i<prefix.len() implies (#[trigger] prefix[i]).target()!=k by {
            assert(prefix[i]==events[i]);
        }
        ready_value_is_retained(prefix,a,eval,k);
        assert(events.last()==events[events.len()-1]);
    }
}

/// A fixed-width/height pixel parent's ready Final slots keep their seeded
/// bits even if other DFS calls run before the region reads those slots.
pub proof fn ready_parent_closes_boundary(events:Seq<Event>, b:FreeBoundary, edges:Edges,
    a:Storage, cached:Storage, eval:Compute)
    requires b.links(edges),
        forall|k:int| #[trigger] b.ready(k) ==> a.contains_key(k) && cached.contains_key(k) && a[k]==cached[k],
        forall|i:int| 0<=i<events.len() ==> ({
            let e=#[trigger] events[i];
            &&& !b.ready(e.target())
            &&& e is Finish ==> e.inputs()==edges(e.target())
        }),
    ensures boundary_cache(events,a,cached,|k:int|b.inside(k),eval),
    decreases events.len(),
{
    if events.len()>0 {
        let prefix=events.drop_last();
        assert forall|i:int| 0<=i<prefix.len() implies ({
            let e=#[trigger] prefix[i];
            &&& !b.ready(e.target())
            &&& e is Finish ==> e.inputs()==edges(e.target())
        }) by { assert(prefix[i]==events[i]); }
        ready_parent_closes_boundary(prefix,b,edges,a,cached,eval);
        let e=events.last(); let reads=e.inputs();
        assert(e==events[events.len()-1]);
        if b.inside(e.target()) && e is Finish {
            assert(reads==edges(e.target()));
            assert forall|j:int| 0<=j<reads.len() && !b.inside(#[trigger] reads[j]) implies
                replay(prefix,a,eval).contains_key(reads[j]) && cached.contains_key(reads[j])
                    && replay(prefix,a,eval)[reads[j]]==cached[reads[j]] by {
                let k=reads[j];
                assert(b.ready(k));
                assert forall|i:int| 0<=i<prefix.len() implies (#[trigger] prefix[i]).target()!=k by {};
                ready_value_is_retained(prefix,a,eval,k);
            }
        }
    }
}

pub struct Replay {
    pub topology:FreeBoundary,
    pub edges:Edges,
    pub nodes:Seq<int>,
    pub finals:spec_fn(int,bool)->int,
    pub n:nat,
    pub defaults:spec_fn(int)->Seq<u32>,
    pub eval:Compute,
    pub full_state:spec_fn(int)->u32,
    pub region_state:spec_fn(int)->u32,
    pub clean:Storage,
    pub cached:Storage,
}

impl Replay {
    pub open spec fn full(self)->Search {
        Search {todo:requests(document_roots(self.nodes,self.finals)),state:self.full_state}
    }
    pub open spec fn region(self)->Search {
        let inside = |node:int| self.topology.included(node);
        Search {
            todo: requests(document_roots(region_nodes(self.nodes,inside),self.finals)),
            state: self.region_state,
        }
    }
    pub open spec fn fuel(self)->nat { self.full().todo.len()+budget(self.full(),self.edges,self.n) }
    pub open spec fn full_events(self)->Seq<Event> {
        drive(self.full(),self.edges,self.defaults,None,|_:int|true,self.fuel()).0
    }
    pub open spec fn region_events(self)->Seq<Event> {
        let inside=|k:int|self.topology.inside(k);
        drive(self.region(),self.edges,self.defaults,Some(inside),inside,self.fuel()).0
    }
    pub open spec fn full_sizes(self)->Storage { replay(self.full_events(),self.clean,self.eval) }
    pub open spec fn regional_sizes(self)->Storage { replay(self.region_events(),self.cached,self.eval) }

    /// A freshly prepared ordinary region uses the same initial states and
    /// provisional values as the document solve.
    /// The fixed parent's seeded Final bits form the only incoming data.
    pub open spec fn prepared(self)->bool {
        let b=self.topology;
        &&& b.describes(self.edges)
        &&& bounded(self.full(),self.edges,self.n)
        &&& self.nodes.no_duplicates() && self.nodes.contains(b.cut.root)
        &&& forall|i:int| 0<=i<self.nodes.len() ==> ({
            let node=#[trigger] self.nodes[i];
            (b.owner)((self.finals)(node,false))==node && (b.owner)((self.finals)(node,true))==node
        })
        &&& forall|k:int| #[trigger] b.inside(k) ==> (self.full_state)(k)==(self.region_state)(k)
            && ((self.full_state)(k)==kernel::SOLVED || (self.full_state)(k)==kernel::UNSOLVED)
            && self.clean.contains_key(k) && self.cached.contains_key(k) && self.clean[k]==self.cached[k]
            && ((self.full_state)(k)==kernel::UNSOLVED ==> self.clean[k]==(self.defaults)(k))
        &&& forall|k:int| #[trigger] b.ready(k) ==> (self.full_state)(k)==kernel::SOLVED
            && self.clean.contains_key(k) && self.cached.contains_key(k) && self.clean[k]==self.cached[k]
    }
}

pub proof fn free_parent_subtree_replays(r:Replay, k:int)
    requires r.prepared(), r.topology.inside(k),
    ensures
        r.region_events()==visible(r.full_events(),|i:int|r.topology.inside(i)),
        r.full_sizes().contains_key(k) && r.regional_sizes().contains_key(k)
            && r.full_sizes()[k]==r.regional_sizes()[k],
{
    let b=r.topology;
    let inside=|k:int|b.inside(k);
    let ready=|k:int|b.ready(k);
    free_boundary_directions(b,r.edges);
    assert(isolated(r.full(),r.edges,inside));
    let included = |node:int| b.included(node);
    region_roots(r.nodes,r.finals,b.owner,included);
    assert(inside =~= |k:int| included((b.owner)(k)));
    assert(r.region().todo==project(r.full().todo,inside));
    ready_nodes_are_not_rewritten(r.full(),r.edges,r.defaults,ready,r.fuel());
    ready_parent_closes_boundary(r.full_events(),b,r.edges,r.clean,r.cached,r.eval);
    finite_region_rebuilds_full_values(document_roots(r.nodes,r.finals),inside,r.edges,r.n,
        r.full_state,r.region_state,r.defaults,r.clean,r.cached,r.eval,k);
}

/// The solver writes a rebuilt leaf after its parent frame is positioned. The
/// ordered placement inputs include that frame, viewport and pixel-scale data.
/// Once those frame arguments agree, regional replay supplies the same values
/// for the leaf's two dimensions and any other local measured inputs.
pub open spec fn placed_leaf(
    eval:Eval, key:Key, rule:Rule, frame:Seq<Value>, local:Seq<int>, sizes:Storage,
) -> Geometry {
    let dimensions=Seq::new(local.len(), |i:int| Value::Words(sizes[local[i]]));
    (eval.place)(key,rule,frame+dimensions)
}

pub proof fn cyclic_leaf_publishes_full_geometry(
    r:Replay, eval:Eval, key:Key, rule:Rule, frame:Seq<Value>, local:Seq<int>, host:Outputs,
    path:Seq<PathEdge>,
)
    requires
        r.prepared(), key.phase is Placement,
        valid_route(Work::Place { path, root_force:false, mark:PlacementWork::Subtree }),
        forall|i:int| 0<=i<local.len() ==> r.topology.inside(#[trigger] local[i]),
    ensures ({
        let work=Work::Place { path, root_force:false, mark:PlacementWork::Subtree };
        let full=Map::<Key,Geometry>::empty().insert(key,placed_leaf(eval,key,rule,frame,local,r.full_sizes()));
        let region=host.insert(key,placed_leaf(eval,key,rule,frame,local,r.regional_sizes()));
        &&& writes(work) && full.contains_key(key) && region.contains_key(key)
        &&& full[key] == region[key]
        &&& forall|other:Key| other!=key ==> #[trigger] region.contains_key(other)==host.contains_key(other)
            && (host.contains_key(other) ==> region[other]==host[other])
    }),
{
    requested_work_is_executed(Work::Place { path, root_force:false, mark:PlacementWork::Subtree });
    assert forall|i:int| 0<=i<local.len() implies
        r.full_sizes()[#[trigger] local[i]]==r.regional_sizes()[local[i]] by {
        free_parent_subtree_replays(r,local[i]);
    }
    assert(Seq::new(local.len(),|i:int|Value::Words(r.full_sizes()[local[i]]))
        =~= Seq::new(local.len(),|i:int|Value::Words(r.regional_sizes()[local[i]])));
}
}
