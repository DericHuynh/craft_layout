//! Wrap side state in the ordered DFS trace. Share and Flow own separate
//! producer bundles. Beginning either producer gives its consumers canonical
//! provisional words regardless of values left by an earlier layout.
use vstd::prelude::*;
use super::cycles::{Storage, Compute, kernel as slot_state};
use super::cycles::dfs::*;
use super::cycles::boundary::{FreeBoundary, free_boundary_directions};
use super::{production_schedule, replay_view};
use super::wrap_metrics::{Words, other, stamp, read_word, stamp_preserves_other_words};
use super::wrap_metrics::kernel::Metric;
use super::wrap_metrics::kernel as words;
use super::wrap_schedule::{self, Child, kernel::{Producer, Request}};

verus! {

pub enum Mode { Scalar, Share, Cross }

pub enum View {
    /// The ordinary slot value, including the provisional value on a back edge.
    Value,
    /// A child's word in the share or cross-extent producer named by the input.
    Metric(int),
    /// A child's saved start in the line partition owned by EvenShare.
    Start(int),
}

/// Multiple logical observations can come from one ordered DFS request.
pub struct Read { pub key:int, pub views:Seq<View> }

pub struct Wrap {
    pub parent:int,
    pub children:Seq<Child<int>>,
    pub share:int,
    pub cross:int,
    pub main_final:spec_fn(int)->int,
    pub main_declaration:spec_fn(int,usize)->int,
    pub cross_declaration:spec_fn(int,usize)->int,
}

impl Wrap {
    pub open spec fn requested(self, request:Request<int>) -> Read {
        match request {
            Request::ParentMainFinal => Read {key:(self.main_final)(self.parent), views:seq![View::Value]},
            Request::ParentShare => Read {
                key:self.share,
                views:Seq::new(self.children.len(),|i:int|View::Start(i)),
            },
            Request::MainFinal(child) => Read {key:(self.main_final)(child),views:seq![View::Value]},
            Request::MainDeclaration(child,i) => Read {key:(self.main_declaration)(child,i),views:seq![View::Value]},
            Request::CrossDeclaration(child,i) => Read {key:(self.cross_declaration)(child,i),views:seq![View::Value]},
        }
    }

    pub open spec fn reads(self, producer:Producer) -> Seq<Read> {
        let requests=seq![wrap_schedule::own(producer)] +
            wrap_schedule::child_requests(self.children,producer,self.children.len());
        Seq::new(requests.len(),|i:int|self.requested(requests[i]))
    }

    pub open spec fn child_metric(self, channel:Metric, index:int) -> Read {
        Read {
            key:match channel {Metric::Share=>self.share,Metric::Cross=>self.cross},
            views:seq![View::Metric(index)],
        }
    }

    /// The share root exports line starts and shares. Flow consumes those
    /// starts from exactly one parent request, then exports cross extents.
    pub open spec fn installed(self, program:Program) -> bool {
        &&& (program.mode)(self.share) is Share
        &&& (program.mode)(self.cross) is Cross
        &&& (program.children)(self.share) == Seq::new(self.children.len(),|i:int|self.children[i].id)
        &&& (program.children)(self.cross) == (program.children)(self.share)
        &&& (program.inputs)(self.share) == self.reads(Producer::Share)
        &&& (program.inputs)(self.cross) == self.reads(Producer::Cross)
    }
}

/// The actual producers use scan_line to get each maximal sibling run. Share
/// may skip publishing bits for a run without Fill, but still records its next
/// boundary. Cross publishes an extent for every run.
pub struct LineEffect {
    pub rows: Seq<(int,bool)>,
    pub next: Option<int>,
    pub value: Option<u32>,
}

pub struct Program {
    pub mode: spec_fn(int)->Mode,
    pub children: spec_fn(int)->Seq<int>,
    pub inputs: spec_fn(int)->Seq<Read>,
    pub scalar: spec_fn(int,Seq<Seq<u32>>)->u32,
    pub lines: spec_fn(int,Seq<Seq<u32>>)->Seq<LineEffect>,
}

pub open spec fn zero_words(children:Seq<int>) -> Map<int,Words> {
    Map::new(children.to_set(), |_:int| (words::INITIAL_WORDS[0],words::INITIAL_WORDS[1]))
}

pub open spec fn publish(lines:Seq<LineEffect>, cache:Map<int,Words>, metric:Metric) -> Map<int,Words>
    decreases lines.len(),
{
    if lines.len()==0 {cache} else {
        let previous=publish(lines.drop_last(),cache,metric);
        let last=lines.last();
        match last.value {
            Some(bits) => stamp(last.rows,last.rows.len(),previous,metric,bits),
            None => previous,
        }
    }
}

pub open spec fn marked(lines:Seq<LineEffect>, children:Seq<int>, i:int) -> bool {
    exists |line:int| 0<=line<lines.len() && (#[trigger] lines[line]).next==Some(children[i])
}

pub open spec fn owns_all_writes(lines:Seq<LineEffect>,children:Seq<int>) -> bool {
    forall |i:int,j:int| 0<=i<lines.len() && 0<=j<lines[i].rows.len() ==>
        children.contains((#[trigger] lines[i].rows[j]).0)
}

pub open spec fn ready_words(cache:Map<int,Words>,children:Seq<int>) -> bool {
    forall |id:int| #[trigger] children.contains(id) ==> cache.contains_key(id)
}

pub open spec fn agrees_on_channel(a:Map<int,Words>,b:Map<int,Words>,children:Seq<int>,channel:Metric) -> bool {
    forall |id:int| #[trigger] children.contains(id) ==> read_word(a[id],channel)==read_word(b[id],channel)
}

/// Late writes in a cyclic DFS finish affect only that phase's own words.
/// Comparing the logical producer bundle against physical storage therefore
/// does not require equal words from the other phase at any time.
proof fn publish_preserves_channels(
    lines:Seq<LineEffect>, children:Seq<int>, channel:Metric, cache:Map<int,Words>, reference:Map<int,Words>,
)
    requires owns_all_writes(lines,children), ready_words(cache,children), ready_words(reference,children),
        agrees_on_channel(cache,reference,children,channel),
    ensures ({
        let a=publish(lines,cache,channel);
        let b=publish(lines,reference,channel);
        &&& ready_words(a,children) && ready_words(b,children)
        &&& agrees_on_channel(a,b,children,channel)
        &&& agrees_on_channel(a,cache,children,other(channel))
    }),
    decreases lines.len(),
{
    if lines.len()>0 {
        let prefix=lines.drop_last();
        assert forall |i:int,j:int| 0<=i<prefix.len() && 0<=j<prefix[i].rows.len() implies
            children.contains((#[trigger] prefix[i].rows[j]).0) by {assert(prefix[i]==lines[i]);}
        publish_preserves_channels(prefix,children,channel,cache,reference);
        let a=publish(prefix,cache,channel);
        let b=publish(prefix,reference,channel);
        let last=lines.last();
        assert(last==lines[lines.len()-1]);
        if let Some(bits)=last.value {
            let run=last.rows;
            assert forall |j:int| 0<=j<run.len() implies ({
                let id=(#[trigger] run[j]).0;
                &&& a.contains_key(id) && b.contains_key(id)
            }) by { assert(children.contains(run[j].0)); }
            assert forall |id:int| #[trigger] children.contains(id) implies ({
                let af=publish(lines,cache,channel);
                let bf=publish(lines,reference,channel);
                &&& af.contains_key(id) && bf.contains_key(id)
                &&& read_word(af[id],channel)==read_word(bf[id],channel)
                &&& read_word(af[id],other(channel))==read_word(cache[id],other(channel))
            }) by {
                stamp_preserves_other_words(run,run.len(),a,channel,bits,id);
                stamp_preserves_other_words(run,run.len(),b,channel,bits,id);
            }
        }
    }
}

pub open spec fn reset_words(cache:Map<int,Words>,children:Seq<int>) -> Map<int,Words> {
    Map::new(cache.dom().union(children.to_set()), |id:int|
        if children.contains(id) {(words::INITIAL_WORDS[0],words::INITIAL_WORDS[1])} else {cache[id]})
}

pub proof fn two_producers_publish_from_prepared_words(
    share:Seq<LineEffect>, cross:Seq<LineEffect>, children:Seq<int>, old:Map<int,Words>,
)
    requires owns_all_writes(share,children), owns_all_writes(cross,children),
    ensures ({
        let reset=reset_words(old,children);
        let share_bundle=publish(share,zero_words(children),Metric::Share);
        let cross_bundle=publish(cross,zero_words(children),Metric::Cross);
        let share_then_cross=publish(cross,publish(share,reset,Metric::Share),Metric::Cross);
        let cross_then_share=publish(share,publish(cross,reset,Metric::Cross),Metric::Share);
        &&& agrees_on_channel(share_then_cross,share_bundle,children,Metric::Share)
        &&& agrees_on_channel(cross_then_share,share_bundle,children,Metric::Share)
        &&& agrees_on_channel(share_then_cross,cross_bundle,children,Metric::Cross)
        &&& agrees_on_channel(cross_then_share,cross_bundle,children,Metric::Cross)
    }),
{
    let reset=reset_words(old,children);
    let zero=zero_words(children);
    let s=publish(share,reset,Metric::Share);
    let c=publish(cross,reset,Metric::Cross);
    publish_preserves_channels(share,children,Metric::Share,reset,zero);
    publish_preserves_channels(cross,children,Metric::Cross,reset,zero);
    publish_preserves_channels(share,children,Metric::Share,c,zero);
    publish_preserves_channels(cross,children,Metric::Cross,s,zero);
}

pub open spec fn encode(ready:bool, value:u32, metrics:Seq<u32>, starts:Seq<u32>) -> Seq<u32> {
    seq![value,if ready {1u32} else {0u32}]+metrics+starts
}

impl Program {
    pub open spec fn project(self, key:int, bundle:Seq<u32>, view:View) -> u32 {
        match view {
            View::Value => bundle[0],
            View::Metric(i) => {
                let channel = if (self.mode)(key) is Share {Metric::Share} else {Metric::Cross};
                match words::ready_metric(bundle[1]==1,channel) {
                    Some(_) => bundle[2+i],
                    None => 0,
                }
            },
            View::Start(i) => if bundle[1]==1 {bundle[2+(self.children)(key).len()+i]} else {0},
        }
    }

    pub open spec fn operands(self,key:int,dependencies:Seq<Seq<u32>>) -> Seq<Seq<u32>> {
        let input = (self.inputs)(key);
        Seq::new(input.len(),|i:int| Seq::new(input[i].views.len(),|j:int|
            self.project(input[i].key,dependencies[i],input[i].views[j])))
    }

    pub open spec fn computed(self,key:int,dependencies:Seq<Seq<u32>>) -> Seq<u32> {
        let operands=self.operands(key,dependencies);
        let result= (self.scalar)(key,operands);
        let mode=(self.mode)(key);
        let children=(self.children)(key);
        let lines=(self.lines)(key,operands);
        match mode {
            Mode::Scalar => encode(true,result,Seq::empty(),Seq::empty()),
            Mode::Share | Mode::Cross => {
                let channel=if mode is Share {Metric::Share} else {Metric::Cross};
                let metrics=publish(lines,zero_words(children),channel);
                let values=Seq::new(children.len(),|i:int| read_word(metrics[children[i]],channel));
                let starts=if mode is Share {
                    Seq::new(children.len(),|i:int| if marked(lines,children,i) {1u32} else {0u32})
                } else {Seq::empty()};
                encode(true,result,values,starts)
            },
        }
    }

    /// The ordinary value has the slot's fresh provisional bits. Breaks and
    /// metrics have zero-length logical projections until the producer finishes.
    pub open spec fn provisional(self,key:int,value:u32) -> Seq<u32> {
        let primary=if (self.mode)(key) is Scalar {value} else {slot_state::provisional_bits(false)};
        encode(false,primary,Seq::empty(),Seq::empty())
    }

    pub open spec fn edges(self) -> Edges {
        |key:int| Seq::new((self.inputs)(key).len(),|i:int| (self.inputs)(key)[i].key)
    }
    pub open spec fn eval(self) -> Compute {
        |key:int,deps:Seq<Seq<u32>>| self.computed(key,deps)
    }

    pub open spec fn accepts_view(self,key:int,view:View) -> bool {
        match view {
            View::Value => true,
            View::Metric(i) => !((self.mode)(key) is Scalar) && 0<=i<(self.children)(key).len(),
            View::Start(i) => (self.mode)(key) is Share && 0<=i<(self.children)(key).len(),
        }
    }
}

pub proof fn unfinished_producer_reads_zero(p:Program,key:int,bits:u32,view:View)
    ensures
        p.project(key,p.provisional(key,bits),view) ==
            if view is Value && (p.mode)(key) is Scalar {bits} else {0u32},
{
    assert(p.provisional(key,bits)[0]==if (p.mode)(key) is Scalar {bits} else {0u32});
    assert(p.provisional(key,bits)[1]==0u32);
}

/// Register a complete span of a producer's ordered child list. The write to
/// either channel follows the actual production writer's exact stamping
/// contract. No state from the other channel is read to produce this bundle.
pub proof fn completed_producer_projects_its_own_bits(p:Program,key:int,dependencies:Seq<Seq<u32>>,i:int)
    requires !((p.mode)(key) is Scalar), 0<=i<(p.children)(key).len(),
    ensures ({
        let mode=(p.mode)(key);
        let children=(p.children)(key);
        let channel=if mode is Share {Metric::Share} else {Metric::Cross};
        let args=p.operands(key,dependencies);
        let lines=(p.lines)(key,args);
        let bundle=p.computed(key,dependencies);
        &&& p.project(key,bundle,View::Metric(i))==read_word(publish(lines,zero_words(children),channel)[children[i]],channel)
        &&& mode is Share ==> p.project(key,bundle,View::Start(i))==if marked(lines,children,i) {1u32} else {0u32}
    }),
{
    assert(p.computed(key,dependencies)[1]==1u32);
}

pub proof fn producers_and_consumers_name_one_channel(w:Wrap,p:Program,index:int)
    requires w.installed(p), 0<=index<w.children.len(),
    ensures ({
        let share=w.child_metric(Metric::Share,index);
        let cross=w.child_metric(Metric::Cross,index);
        let flow_inputs=(p.inputs)(w.cross);
        &&& share.key!=cross.key
        &&& p.accepts_view(share.key,share.views[0])
        &&& p.accepts_view(cross.key,cross.views[0])
        &&& flow_inputs[0].key==share.key
        &&& flow_inputs[0].views[index]==View::Start(index)
        &&& p.accepts_view(share.key,flow_inputs[0].views[index])
    }),
{
    let requests=seq![wrap_schedule::own(Producer::Cross)] +
        wrap_schedule::child_requests(w.children,Producer::Cross,w.children.len());
    assert(requests[0]==Request::ParentShare);
}

pub open spec fn installed(program:Program,key:int,ready:bool,seed_bits:u32,pending_bits:u32) -> Seq<u32> {
    if ready {encode(true,seed_bits,Seq::empty(),Seq::empty())}
    else {program.provisional(key,pending_bits)}
}

pub open spec fn scope(n:nat, inside:Region) -> Set<int>
    decreases n,
{
    if n==0 {Set::empty()} else {
        let cached=scope((n-1) as nat,inside);
        if inside(n-1) {cached.insert(n-1)} else {cached}
    }
}

proof fn in_scope(n:nat,inside:Region,key:int)
    ensures scope(n,inside).contains(key)==(0<=key<n && inside(key)),
    decreases n,
{
    if n>0 {in_scope((n-1) as nat,inside,key);}
}

/// Only the fresh slots published by preparation are seeded. Wrap producers
/// start Unsolved with empty line starts and zero side words. Entirely
/// unrelated stale cached values can remain outside the region.
pub open spec fn prepare(
    program:Program, inside:Region, n:nat, ready:Region,
    seed_bits:spec_fn(int)->u32, pending:spec_fn(int)->u32, previous:Storage,
) -> Storage {
    Map::new(
        scope(n,inside).union(previous.dom()),
        |key:int| if 0<=key<n && inside(key) {
            installed(program,key,ready(key),seed_bits(key),pending(key))
        } else {previous[key]},
    )
}

pub struct WrapReplay {
    pub program:Program,
    pub visits:Seq<production_schedule::NodeRequests>,
    pub owner:spec_fn(int)->int,
    pub nodes:Region,
    pub n:nat,
    pub seed_ready:Region,
    pub seed_bits:spec_fn(int)->u32,
    pub pending:spec_fn(int)->u32,
    pub full_stale:Storage,
    pub regional_stale:Storage,
}

impl WrapReplay {
    pub open spec fn inside(self,key:int) -> bool { (self.nodes)((self.owner)(key)) }

    pub open spec fn state(self,key:int) -> u32 {
        if 0<=key<self.n && (self.seed_ready)(key) {slot_state::SOLVED} else {slot_state::UNSOLVED}
    }
    pub open spec fn defaults(self) -> spec_fn(int)->Seq<u32> {
        |key:int| self.program.provisional(key,(self.pending)(key))
    }
    pub open spec fn full_initial(self) -> Storage {
        prepare(self.program,|_:int|true,self.n,self.seed_ready,self.seed_bits,self.pending,self.full_stale)
    }
    pub open spec fn region_initial(self) -> Storage {
        // A pre-seeded boundary reads its current pixel declaration, just as
        // the already-solved full parent does. Other outside values are unused.
        prepare(self.program,|key:int| self.inside(key) || (self.seed_ready)(key),
            self.n,self.seed_ready,self.seed_bits,self.pending,self.regional_stale)
    }
    pub open spec fn replay(self) -> replay_view::Replay {
        replay_view::Replay {
            visits:self.visits, owner:self.owner, nodes:self.nodes, edges:self.program.edges(), n:self.n,
            initial_state:|key:int|self.state(key), regional_state:|key:int|self.state(key),
            provisional:self.defaults(),
            initial:self.full_initial(), cached:self.region_initial(), eval:self.program.eval(),
        }
    }
    pub open spec fn well_prepared(self) -> bool {
        let r=self.replay();
        let edges=self.program.edges();
        &&& bounded(r.document(),edges,self.n)
        &&& forall |i:int| 0<=i<self.visits.len() ==> (#[trigger] self.visits[i]).owned_by(self.owner)
        &&& forall |key:int| #[trigger] self.inside(key) ==> 0<=key<self.n
        &&& forall |key:int| #[trigger] (self.seed_ready)(key) ==> (self.program.mode)(key) is Scalar
        &&& forall |key:int,j:int| 0<=j<edges(key).len() ==> ({
            let dep=#[trigger] edges(key)[j];
            &&& !self.inside(key) && self.inside(dep) ==> self.state(key)==slot_state::SOLVED
            &&& self.inside(key) && !self.inside(dep) ==> self.state(dep)==slot_state::SOLVED
        })
    }
}

pub proof fn wrap_preparation_closes_replay(w:WrapReplay)
    requires w.well_prepared(),
    ensures w.replay().closed(),
{
    let r=w.replay();
    assert forall |k:int| #[trigger] r.inside(k) implies ({
        &&& (r.initial_state)(k) == (r.regional_state)(k)
        &&& r.initial.contains_key(k) && r.cached.contains_key(k)
        &&& r.initial[k] == r.cached[k]
    }) by {
        assert(w.inside(k));
        in_scope(w.n,|_:int|true,k);
        in_scope(w.n,|key:int| w.inside(key) || (w.seed_ready)(key),k);
    }
    assert forall |k:int| #[trigger] r.pinned(k) implies ({
        &&& r.initial.contains_key(k) && r.cached.contains_key(k)
        &&& r.initial[k] == r.cached[k]
    }) by {
        assert(0<=k<w.n && (w.seed_ready)(k));
        in_scope(w.n,|_:int|true,k);
        in_scope(w.n,|key:int| w.inside(key) || (w.seed_ready)(key),k);
    }
}

/// Along this concrete subtree boundary the only imports are the fixed Free
/// parent's ready Final slots. No unfinished parent can enter the region.
pub proof fn fixed_free_parent_wrap_region(w:WrapReplay, boundary:FreeBoundary)
    requires boundary.describes(w.program.edges()), w.owner==boundary.owner,
        forall |node:int| #[trigger] (w.nodes)(node)==boundary.included(node),
        forall |key:int| #[trigger] boundary.ready(key) ==> 0<=key<w.n && (w.seed_ready)(key),
        bounded(w.replay().document(),w.program.edges(),w.n),
        forall |i:int| 0<=i<w.visits.len() ==> (#[trigger] w.visits[i]).owned_by(w.owner),
        forall |key:int| #[trigger] w.inside(key) ==> 0<=key<w.n,
        forall |key:int| #[trigger] (w.seed_ready)(key) ==> (w.program.mode)(key) is Scalar,
    ensures w.well_prepared(), w.replay().closed(),
{
    free_boundary_directions(boundary,w.program.edges());
    assert forall |key:int| #[trigger] w.inside(key)==boundary.inside(key) by {};
    wrap_preparation_closes_replay(w);
}

/// A freshly measured region with no unfinished external dependency retains
/// arbitrary internal cycles. All Wrap views, including the markers used in
/// placement, match after regional and document-order replay. No equality
/// premise is imposed on prior cache words, intermediate line decisions,
/// or on the computed geometry.
pub proof fn closed_wrap_region_replays(w:WrapReplay,key:int,view:View)
    requires w.well_prepared(), w.inside(key), w.program.accepts_view(key,view),
    ensures ({
        let r=w.replay();
        let a=r.full_sizing();
        let b=r.rebuilt_sizing();
        &&& r.rebuilt_events()==visible(r.full_events(),|key:int|r.inside(key))
        &&& a.contains_key(key) && b.contains_key(key)
        &&& a[key]==b[key]
        &&& w.program.project(key,a[key],view)==w.program.project(key,b[key],view)
    }),
{
    wrap_preparation_closes_replay(w);
    replay_view::rebuilt_producers_match_the_document(w.replay(),key);
}

pub proof fn wrapping_region_publishes_same_geometry(w:WrapReplay, nodes:Seq<replay_view::PlaceNode>, draw:replay_view::Draw)
    requires w.well_prepared(),
        forall |i:int,j:int| 0<=i<nodes.len() && 0<=j<nodes[i].inputs.len()
            ==> w.inside((#[trigger] nodes[i].inputs[j]).producer),
    ensures replay_view::place_frame(nodes,w.replay().rebuilt_sizing(),draw)
        == replay_view::place_frame(nodes,w.replay().full_sizing(),draw),
{
    wrap_preparation_closes_replay(w);
    replay_view::rebuilt_region_publishes_the_document_view(w.replay(),nodes,draw);
}

}
