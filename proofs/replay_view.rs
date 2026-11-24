//! Mixed-mode cyclic sizing and its published view.
//!
//! A producer's result includes the words it writes for later readers, such
//! as a grid assignment or wrapping line metric. A reader names the producer
//! whose provisional or final words it consumes. Expanding the region must
//! therefore preserve both the ordered visits and the word source of a read.
use vstd::prelude::*;
use super::*;
use super::cycles::{Event, Storage, Compute, replay};
use super::cycles::boundary::{ready_nodes_are_not_rewritten, ready_value_is_retained};
use super::cycles::dfs::{self, Edges, Region, Search};
use super::production_schedule as roots;

verus! {

pub struct Replay {
    pub visits: Seq<roots::NodeRequests>,
    pub owner: spec_fn(int) -> int,
    pub nodes: Region,
    pub edges: Edges,
    pub n: nat,
    pub initial_state: spec_fn(int) -> u32,
    pub regional_state: spec_fn(int) -> u32,
    pub provisional: spec_fn(int) -> Seq<u32>,
    pub initial: Storage,
    pub cached: Storage,
    pub eval: Compute,
}

impl Replay {
    pub open spec fn inside(self, slot: int) -> bool { (self.nodes)((self.owner)(slot)) }

    pub open spec fn pinned(self, slot: int) -> bool {
        !self.inside(slot) && (self.initial_state)(slot) == cycles::kernel::SOLVED
    }

    pub open spec fn document(self) -> Search {
        Search { todo:dfs::requests(roots::walk(self.visits)), state:self.initial_state }
    }

    pub open spec fn region(self) -> Search {
        Search {
            todo:dfs::requests(roots::walk(roots::region_nodes(self.visits,self.nodes))),
            state:self.regional_state,
        }
    }

    pub open spec fn gas(self) -> nat { self.document().todo.len() + dfs::budget(self.document(),self.edges,self.n) }

    pub open spec fn full_events(self) -> Seq<Event> {
        dfs::drive(self.document(),self.edges,self.provisional,None,|_:int| true,self.gas()).0
    }

    pub open spec fn rebuilt_events(self) -> Seq<Event> {
        let region = |k:int| self.inside(k);
        dfs::drive(self.region(),self.edges,self.provisional,Some(region),region,self.gas()).0
    }

    pub open spec fn full_sizing(self) -> Storage { replay(self.full_events(),self.initial,self.eval) }
    pub open spec fn rebuilt_sizing(self) -> Storage { replay(self.rebuilt_events(),self.cached,self.eval) }

    /// Pinned producers can be read from within the region. No outside
    /// dispatch can open a slot owned by the region. These conditions concern
    /// preparation and graph edges, independently of the final result.
    pub open spec fn scheduled(self) -> bool {
        &&& dfs::bounded(self.document(),self.edges,self.n)
        &&& forall |i:int| 0 <= i < self.visits.len() ==> (#[trigger] self.visits[i]).owned_by(self.owner)
        &&& forall |k:int,j:int| 0 <= j < (self.edges)(k).len() ==> ({
            let dep = #[trigger] (self.edges)(k)[j];
            &&& !self.inside(k) && self.inside(dep) ==> (self.initial_state)(k) == cycles::kernel::SOLVED
            &&& self.inside(k) && !self.inside(dep) ==> self.pinned(dep)
        })
        &&& forall |k:int| #[trigger] self.inside(k)
            ==> (self.initial_state)(k) == (self.regional_state)(k) && self.initial.contains_key(k)
        &&& forall |k:int| #[trigger] self.pinned(k) ==> self.initial.contains_key(k)
    }

    pub open spec fn closed(self) -> bool {
        &&& self.scheduled()
        &&& forall |k:int| #[trigger] self.inside(k) ==> self.cached.contains_key(k) && self.initial[k] == self.cached[k]
        &&& forall |k:int| #[trigger] self.pinned(k) ==> ({
            &&& self.initial.contains_key(k) && self.cached.contains_key(k)
            &&& self.initial[k] == self.cached[k]
        })
    }
}

pub(crate) proof fn reads_pinned_values(r: Replay, events: Seq<Event>)
    requires r.closed(),
        forall |i:int| 0 <= i < events.len() ==> ({
            let e = #[trigger] events[i];
            &&& !r.pinned(e.target())
            &&& e is Finish ==> e.inputs() == (r.edges)(e.target())
        }),
    ensures dfs::boundary_cache(events,r.initial,r.cached,|k:int| r.inside(k),r.eval),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        assert forall |i:int| 0 <= i < prefix.len() implies ({
            let e = #[trigger] prefix[i];
            &&& !r.pinned(e.target())
            &&& e is Finish ==> e.inputs() == (r.edges)(e.target())
        }) by { assert(prefix[i] == events[i]); }
        reads_pinned_values(r,prefix);
        let last = events.last();
        let reads = last.inputs();
        assert(last == events[events.len()-1]);
        if r.inside(last.target()) {
            assert forall |j:int| 0 <= j < reads.len() && !r.inside(#[trigger] reads[j]) implies ({
                let value = replay(prefix,r.initial,r.eval);
                &&& value.contains_key(reads[j]) && r.cached.contains_key(reads[j])
                &&& value[reads[j]] == r.cached[reads[j]]
            }) by {
                assert(last is Finish);
                assert(reads == (r.edges)(last.target()));
                let input = reads[j];
                assert(r.pinned(input));
                assert forall |i:int| 0 <= i < prefix.len() implies (#[trigger] prefix[i]).target() != input by {};
                ready_value_is_retained(prefix,r.initial,r.eval,input);
            }
        }
    }
}

pub(crate) proof fn match_region_events(r: Replay)
    requires r.closed(),
    ensures r.rebuilt_events() == dfs::visible(r.full_events(),|s:int|r.inside(s)),
{
    let inside = |s:int| r.inside(s);
    roots::canonical_order_projects(r.visits,r.nodes,r.owner);
    assert(inside =~= |k:int| (r.nodes)((r.owner)(k)));
    assert(r.region().todo == dfs::project(r.document().todo,inside));
    assert(dfs::isolated(r.document(),r.edges,inside));
    dfs::finite_region_from_roots(roots::walk(r.visits),inside,r.edges,r.n,r.initial_state,r.regional_state,r.provisional);
    dfs::visibility_is_event_filter(r.document(),r.edges,r.provisional,inside,r.gas());
}

/// Replaying a closed region rebuilds the complete producer bundles. The
/// proof includes explicitly requested Flow and share slots in both walks.
pub proof fn rebuilt_producers_match_the_document(r: Replay, k:int)
    requires r.closed(), r.inside(k),
    ensures
        r.rebuilt_events() == dfs::visible(r.full_events(),|s:int| r.inside(s)),
        r.rebuilt_sizing().contains_key(k) && r.full_sizing().contains_key(k),
        r.rebuilt_sizing()[k] == r.full_sizing()[k],
{
    let inside = |s:int| r.inside(s);
    roots::canonical_order_projects(r.visits,r.nodes,r.owner);
    assert(inside =~= |k:int| (r.nodes)((r.owner)(k)));
    assert(r.region().todo == dfs::project(r.document().todo,inside));
    assert(dfs::isolated(r.document(),r.edges,inside));
    ready_nodes_are_not_rewritten(r.document(),r.edges,r.provisional,|s:int| r.pinned(s),r.gas());
    reads_pinned_values(r,r.full_events());
    dfs::finite_region_rebuilds_full_values(roots::walk(r.visits),inside,r.edges,r.n,r.initial_state,r.regional_state,
        r.provisional,r.initial,r.cached,r.eval,k);
}

/// Geometry can select any word from a producer, including any cell or line
/// metric. Earlier placement outputs can include the unrounded parent frame,
/// its snapped origin, or a prior sibling's cursor for shared positioning.
pub struct ReadWord { pub producer: int, pub word: int }
pub struct PlaceNode {
    pub key: Key,
    pub inputs: Seq<ReadWord>,
    pub local: Seq<int>,
    pub earlier: Seq<Key>,
}

pub struct Placement {
    pub output: Geometry,
    pub frame: Seq<u32>,
}

pub type Draw = spec_fn(Key, Seq<int>, Seq<u32>, Seq<Placement>) -> Placement;

pub struct PlacedRecord {
    pub local: Seq<int>,
    pub measured: Seq<u32>,
    pub inherited: Seq<Placement>,
    pub result: Placement,
}

pub type Placements = Map<Key, PlacedRecord>;

pub open spec fn words(source: Storage, node: PlaceNode) -> Seq<u32> {
    Seq::new(node.inputs.len(), |i:int| {
        let r = node.inputs[i];
        source[r.producer][r.word]
    })
}

pub open spec fn place_frame(nodes: Seq<PlaceNode>, source: Storage, draw: Draw) -> Placements
    decreases nodes.len(),
{
    if nodes.len() == 0 { Map::empty() } else {
        let prior = place_frame(nodes.drop_last(),source,draw);
        let node = nodes.last();
        let inherited = Seq::new(node.earlier.len(), |i:int| prior[node.earlier[i]].result);
        let measured = words(source,node);
        let result = draw(node.key,node.local,measured,inherited);
        prior.insert(node.key,PlacedRecord { local:node.local, measured, inherited, result })
    }
}

pub open spec fn ordered_view(nodes: Seq<PlaceNode>, placed: Placements) -> Seq<(Key, Geometry)> {
    Seq::new(nodes.len(), |i:int| (nodes[i].key, placed[nodes[i].key].result.output))
}

/// Placement compares all the words it can actually read, including producer
/// side state and the inherited results of earlier placement steps.
pub proof fn same_words_give_same_placement(nodes: Seq<PlaceNode>, a: Storage, b: Storage, draw: Draw)
    requires forall |i: int, j: int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len() ==> {
        let read = #[trigger] nodes[i].inputs[j];
        a[read.producer][read.word] == b[read.producer][read.word]
    },
    ensures place_frame(nodes, a, draw) == place_frame(nodes, b, draw),
    decreases nodes.len(),
{
    if nodes.len() != 0 {
        let prior = nodes.drop_last();
        assert forall |i: int, j: int| 0 <= i < prior.len() && 0 <= j < prior[i].inputs.len() implies {
            let read = #[trigger] prior[i].inputs[j];
            a[read.producer][read.word] == b[read.producer][read.word]
        } by { assert(prior[i] == nodes[i]); }
        same_words_give_same_placement(prior, a, b, draw);
        let last = nodes.last();
        assert(last == nodes[nodes.len() - 1]);
        assert(words(a, last) =~= words(b, last));
    }
}

/// The same producer reads and placement rule sequence lead to the same
/// absolute and local geometry throughout the region, including children
/// placed from an already published parent frame.
pub proof fn rebuilt_region_publishes_the_document_view(r: Replay, nodes: Seq<PlaceNode>, draw: Draw)
    requires r.closed(),
        forall |i:int,j:int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len()
            ==> r.inside((#[trigger] nodes[i].inputs[j]).producer),
    ensures place_frame(nodes,r.rebuilt_sizing(),draw) == place_frame(nodes,r.full_sizing(),draw),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let prefix = nodes.drop_last();
        let last = nodes.last();
        assert(last == nodes[nodes.len()-1]);
        assert forall |i:int,j:int| 0 <= i < prefix.len() && 0 <= j < prefix[i].inputs.len()
            implies r.inside((#[trigger] prefix[i].inputs[j]).producer) by { assert(prefix[i] == nodes[i]); }
        rebuilt_region_publishes_the_document_view(r,prefix,draw);
        assert(words(r.rebuilt_sizing(),last) =~= words(r.full_sizing(),last)) by {
            assert forall |i:int| 0 <= i < last.inputs.len() implies
                words(r.rebuilt_sizing(),last)[i] == words(r.full_sizing(),last)[i] by {
                assert(r.inside(last.inputs[i].producer));
                rebuilt_producers_match_the_document(r,last.inputs[i].producer);
            }
        }
    }
}

}
