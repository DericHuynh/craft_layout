//! Primitive placement inputs that survive the native partial-placement guards.
use vstd::prelude::*;
use super::*;
use super::cycles::Storage;
use super::placement::{self, kernel as marks, PathEdge, PlacementWork};
use super::replay_view::{self, PlaceNode, Placements, ReadWord, Draw, Replay};
use super::replay_publication;
use super::retained_view::Outputs;

verus! {

pub enum Mode { Free, Stack, Wrap, Block, Grid }

/// All ambient inputs read by positioning and output rounding. A window
/// change affects clamping, and a scale change affects output and origins.
pub struct Ambient {
    pub viewport: Seq<u32>,
    pub pixel_scale: Option<u32>,
}

pub open spec fn scale_dirty(previous: Option<u32>, edits: Seq<Option<u32>>) -> bool
    decreases edits.len(),
{
    if edits.len()==0 { false } else {
        let prior=edits.drop_last();
        let old=if prior.len()==0 { previous } else { prior.last() };
        marks::update_scale_dirty(scale_dirty(previous,prior),old != edits.last())
    }
}

/// Setting the scale several times in one batch never hides a change. A
/// positive finite scale's ordinary comparison is exact on its bits.
pub proof fn unchanged_scale_gate_keeps_bits(previous:Option<u32>, edits:Seq<Option<u32>>)
    ensures !scale_dirty(previous,edits) ==>
        (if edits.len()==0 { previous } else { edits.last() }) == previous,
    decreases edits.len(),
{
    if edits.len()>0 { unchanged_scale_gate_keeps_bits(previous,edits.drop_last()); }
}

pub proof fn dispatch_partial_keeps_ambient(previous:Ambient,current:Ambient,structural:bool,
    needs_topology:bool, edits:Seq<Option<u32>>, retains:bool)
    requires current.pixel_scale == (if edits.len()==0 {previous.pixel_scale} else {edits.last()}),
        retains, marks::partial_placement(structural,needs_topology,
            current.viewport==previous.viewport,scale_dirty(previous.pixel_scale,edits)),
    ensures previous==current, structural, !needs_topology,
{
    unchanged_scale_gate_keeps_bits(previous.pixel_scale,edits);
}

/// Per-child inputs of coupled positioning. Free placement reads no row from
/// this group. Stack and Wrap use sibling extents and margins, Block uses
/// heights and collapsed margins, and Grid uses its track and cell outputs.
pub struct Contribution {
    pub child: Key,
    pub free: bool,
    pub declarations: Seq<int>,
    pub producers: Seq<ReadWord>,
}

pub struct ChildFacts {
    pub placement: PlacementWork,
    pub affects_parent: bool,
}

/// The path edge stores the exact summary produced by the child loop.
/// Visible and disabled roster changes are conservatively structural.
pub struct GroupStep {
    pub edge: PathEdge,
    pub before: Seq<Contribution>,
    pub after: Seq<Contribution>,
    pub facts: Seq<ChildFacts>,
}

impl GroupStep {
    #[verifier::opaque]
    pub closed spec fn explained(self) -> bool {
        &&& self.edge.children.len()==self.facts.len()==self.after.len()
        &&& !self.edge.children_changed ==> self.before.len()==self.after.len()
        &&& forall |i:int| 0<=i<self.after.len() ==> ({
            let current=#[trigger] self.after[i];
            let prior=self.before[i];
            let child=self.facts[i];
            &&& self.edge.children[i] == (child.placement,
                marks::coupled_child_changed(self.edge.coupled,child.affects_parent,current.free))
            &&& !self.edge.children_changed ==> {
                &&& prior.child==current.child
                &&& prior.free==current.free
                &&& !current.free && prior!=current ==> child.affects_parent
            }
        })
    }
}

pub open spec fn flow_children(rows:Seq<Contribution>)->Seq<Contribution>
    decreases rows.len(),
{
    if rows.len()==0 { Seq::empty() } else {
        let prefix=flow_children(rows.drop_last());
        if rows.last().free { prefix } else { prefix.push(rows.last()) }
    }
}

proof fn same_in_flow_list(before:Seq<Contribution>,after:Seq<Contribution>)
    requires before.len()==after.len(),
        forall |i:int| 0<=i<after.len() ==> ({
            let row=#[trigger] after[i];
            before[i].free==row.free && (!row.free ==> before[i]==row)
        }),
    ensures flow_children(before)==flow_children(after),
    decreases after.len(),
{
    if after.len()>0 {
        let a=before.drop_last(); let b=after.drop_last();
        assert forall |i:int| 0<=i<b.len() implies ({
            let row=#[trigger] b[i];
            a[i].free==row.free && (!row.free ==> a[i]==row)
        }) by { assert(a[i]==before[i] && b[i]==after[i]); }
        assert(before.last()==before[before.len()-1] && after.last()==after[after.len()-1]);
        same_in_flow_list(a,b);
    }
}

/// Any changed in-flow contribution below a coupled parent forces a rewrite
/// of the parent subtree. Clean free siblings supply no such input.
pub proof fn skipped_parent_keeps_flow_group(s:GroupStep)
    requires s.explained(), s.edge.coupled, !s.edge.parent_mark().writes(false),
    ensures flow_children(s.before)==flow_children(s.after),
{
    reveal(GroupStep::explained);
    placement::lemma_parent_fold(s.edge.previous,s.edge.children_changed,s.edge.coupled,s.edge.children,false);
    assert(!s.edge.children_changed && !placement::any_coupled_size_change(s.edge.children));
    assert forall |i:int| 0<=i<s.after.len() implies ({
        let row=#[trigger] s.after[i];
        s.before[i].free==row.free && (!row.free ==> s.before[i]==row)
    }) by {
        if !s.after[i].free && s.before[i]!=s.after[i] {
            assert(s.facts[i].affects_parent);
            assert(s.edge.children[i].1);
            assert(placement::any_coupled_size_change(s.edge.children));
        }
    }
    same_in_flow_list(s.before,s.after);
}

/// Valid paths ensure the child's partial callback cannot be skipped under a
/// parent that rewrites its subtree. This holds independently of the actual
/// numerical placement rule.
pub proof fn skip_propagates_to_parent(child:Work,parent:Work,edge:PathEdge)
    requires child is Place, parent is Place,
        child->Place_path == parent->Place_path.push(edge),
        edge.parent_mark()==parent->Place_mark,
        child->Place_root_force==parent->Place_root_force,
        valid_route(child), !requested(child),
    ensures !requested(parent), !edge.parent_mark().writes(false),
{
    let pp=parent->Place_path;
    let cp=child->Place_path;
    assert(cp.last()==edge);
    assert(cp[pp.len() as int]==edge);
    if edge.parent_mark().writes(false) { assert(placement::ancestor_writes(cp)); }
    if placement::ancestor_writes(pp) {
        let i=choose |i:int| 0<=i<pp.len() && (#[trigger] pp[i]).parent_mark() is Subtree;
        assert(pp[i]==cp[i]);
        assert(placement::ancestor_writes(cp));
    }
}

pub struct NodeSource {
    pub key: Key,
    pub parent: Option<Key>,
    pub mode: Mode,
    pub free: bool,
    pub declaration: Seq<int>,
    pub parent_context: Seq<int>,
    pub own_reads: Seq<ReadWord>,
    pub siblings: Seq<Contribution>,
}

pub open spec fn sibling_declarations(rows:Seq<Contribution>)->Seq<int>
    decreases rows.len(),
{
    if rows.len()==0 { Seq::empty() } else {
        sibling_declarations(rows.drop_last()) + rows.last().declarations
    }
}

pub open spec fn sibling_producers(rows:Seq<Contribution>)->Seq<ReadWord>
    decreases rows.len(),
{
    if rows.len()==0 { Seq::empty() } else {
        sibling_producers(rows.drop_last()) + rows.last().producers
    }
}

impl NodeSource {
    pub open spec fn reads_siblings(self)->bool {
        self.parent.is_some() && !(self.mode is Free) && !self.free
    }

    #[verifier::opaque]
    pub closed spec fn description(self, ambient:Ambient)->PlaceNode {
        let flow=if self.reads_siblings() { flow_children(self.siblings) } else { Seq::<Contribution>::empty() };
        let viewport=Seq::new(ambient.viewport.len(),|i:int| ambient.viewport[i] as int);
        let scale=match ambient.pixel_scale { Some(bits)=>seq![bits as int], None=>Seq::empty() };
        let earlier=match self.parent { Some(parent)=>seq![parent], None=>Seq::empty() };
        PlaceNode {
            key:self.key,
            inputs:self.own_reads+sibling_producers(flow),
            local:self.declaration+self.parent_context+viewport+scale+sibling_declarations(flow),
            earlier,
        }
    }

    pub open spec fn direct_same(self,other:NodeSource)->bool {
        self.key==other.key && self.parent==other.parent && self.mode==other.mode
            && self.free==other.free && self.declaration==other.declaration
            && self.parent_context==other.parent_context && self.own_reads==other.own_reads
    }
}

pub proof fn dropped_writes_keep_placement_recipe(before:NodeSource,after:NodeSource,ambient:Ambient,
    child:Work,parent:Work,group:GroupStep)
    requires
        before.direct_same(after), !requested(child),
        after.reads_siblings() ==> ({
            &&& group.explained()
            &&& group.edge.coupled
            &&& group.before==before.siblings && group.after==after.siblings
            &&& child is Place && parent is Place && valid_route(child)
            &&& child->Place_path==parent->Place_path.push(group.edge)
            &&& group.edge.parent_mark()==parent->Place_mark
            &&& child->Place_root_force==parent->Place_root_force
        }),
    ensures before.description(ambient)==after.description(ambient),
{
    reveal(NodeSource::description);
    if after.reads_siblings() {
        skip_propagates_to_parent(child,parent,group.edge);
        skipped_parent_keeps_flow_group(group);
    }
}


#[verifier::opaque]
pub closed spec fn descriptions(nodes:Seq<NodeSource>, ambient:Ambient)->Seq<PlaceNode> {
    Seq::new(nodes.len(),|i:int| nodes[i].description(ambient))
}

proof fn description_at(nodes:Seq<NodeSource>,ambient:Ambient,i:int)
    requires 0<=i<nodes.len(),
    ensures descriptions(nodes,ambient)[i]==nodes[i].description(ambient),
        descriptions(nodes,ambient)[i].key==nodes[i].key,
        descriptions(nodes,ambient)[i].earlier
            ==match nodes[i].parent { Some(p)=>seq![p], None=>Seq::<Key>::empty() },
{
    reveal(descriptions);
    reveal(NodeSource::description);
}

proof fn descriptions_len(nodes:Seq<NodeSource>,ambient:Ambient)
    ensures descriptions(nodes,ambient).len()==nodes.len(),
{
    reveal(descriptions);
}

#[verifier::opaque]
pub closed spec fn documented(nodes:Seq<NodeSource>,key:Key) -> bool {
    exists |i:int| 0<=i<nodes.len() && (#[trigger] nodes[i]).key==key
}

#[verifier::opaque]
pub closed spec fn lookup(nodes:Seq<NodeSource>,key:Key)->int {
    choose |i:int| 0<=i<nodes.len() && (#[trigger] nodes[i]).key==key
}

proof fn known_node_index(nodes:Seq<NodeSource>,key:Key)
    requires documented(nodes,key),
    ensures 0<=lookup(nodes,key)<nodes.len(),nodes[lookup(nodes,key)].key==key,
{
    reveal(documented);
    reveal(lookup);
}

#[verifier::opaque]
pub closed spec fn ordered_nodes(nodes:Seq<NodeSource>)->bool {
    source_keys_unique(nodes) && parents_precede_children(nodes)
}

#[verifier::opaque]
closed spec fn source_keys_unique(nodes:Seq<NodeSource>)->bool {
    forall|i:int,j:int| 0<=i<j<nodes.len() ==> (#[trigger] nodes[i]).key!=(#[trigger] nodes[j]).key
}

#[verifier::opaque]
closed spec fn parents_precede_children(nodes:Seq<NodeSource>)->bool {
    forall|i:int| 0<=i<nodes.len() && (#[trigger] nodes[i]).parent.is_some() ==>
        exists |j:int| 0<=j<i && (#[trigger] nodes[j]).key==nodes[i].parent.unwrap()
}

#[verifier::opaque]
closed spec fn unique_keys(nodes:Seq<PlaceNode>)->bool {
    forall |i:int,j:int| 0<=i<j<nodes.len()
        ==> (#[trigger] nodes[i]).key!=(#[trigger] nodes[j]).key
}

proof fn descriptions_have_unique_keys(nodes:Seq<NodeSource>,ambient:Ambient)
    requires ordered_nodes(nodes),
    ensures unique_keys(descriptions(nodes,ambient)),
{
    reveal(ordered_nodes);
    reveal(source_keys_unique);
    reveal(unique_keys);
    let desc=descriptions(nodes,ambient);
    descriptions_len(nodes,ambient);
    assert forall |i:int,j:int| 0<=i<j<desc.len()
        implies (#[trigger] desc[i]).key!=(#[trigger] desc[j]).key by {
        description_at(nodes,ambient,i);
        description_at(nodes,ambient,j);
        assert(nodes[i].key!=nodes[j].key);
    }
}

proof fn description_prefix(desc:Seq<PlaceNode>)
    requires desc.len()>0, unique_keys(desc),
    ensures unique_keys(desc.drop_last()),
{
    reveal(unique_keys);
    let prefix=desc.drop_last();
    assert forall |i:int,j:int| 0<=i<j<prefix.len() implies
        (#[trigger] prefix[i]).key!=(#[trigger] prefix[j]).key by {
        assert(prefix[i]==desc[i] && prefix[j]==desc[j]);
    }
}

proof fn place_record_at(desc:Seq<PlaceNode>,sizing:Storage,draw:Draw,i:int,parent:Option<int>)
    requires unique_keys(desc),0<=i<desc.len(),
        match parent {
            Some(p)=>0<=p<i && desc[i].earlier==seq![desc[p].key],
            None=>desc[i].earlier==Seq::<Key>::empty(),
        },
    ensures ({
        let node=desc[i];
        let all=replay_view::place_frame(desc,sizing,draw);
        let row=all[node.key];
        &&& all.contains_key(node.key)
        &&& row.local==node.local
        &&& row.measured==replay_view::words(sizing,node)
        &&& row.inherited==match parent {
            Some(p)=>seq![all[desc[p].key].result],
            None=>Seq::<replay_view::Placement>::empty(),
        }
        &&& row.result==draw(node.key,row.local,row.measured,row.inherited)
    }),
    decreases desc.len(),
{
    reveal(unique_keys);
    let prefix=desc.drop_last();
    let prior=replay_view::place_frame(prefix,sizing,draw);
    let all=replay_view::place_frame(desc,sizing,draw);
    let last=desc.last();
    let node=desc[i];
    assert(last==desc[desc.len()-1]);
    if let Some(p)=parent {
        assert(desc[p].key!=last.key);
        assert(prefix[p]==desc[p]);
        assert(all[desc[p].key]==prior[desc[p].key]);
    }
    if i<desc.len()-1 {
        description_prefix(desc);
        assert(node==prefix[i]);
        place_record_at(prefix,sizing,draw,i,parent);
        assert(node.key!=last.key);
        assert(all[node.key]==prior[node.key]);
    } else if let Some(p)=parent {
        assert(all[node.key].inherited =~= seq![all[desc[p].key].result]);
    } else {
        assert(all[node.key].inherited =~= Seq::<replay_view::Placement>::empty());
    }
}

/// Facts supplied by edit classification and the already-verified sizing
/// boundary. They describe only primitive declarations and producer words.
/// No Raw, snapped, local, or absolute output equivalence is a prerequisite.
pub struct PlacementDelta {
    pub before:Seq<NodeSource>,
    pub after:Seq<NodeSource>,
    pub before_sizing:Storage,
    pub after_sizing:Storage,
    pub ambient:Ambient,
    pub plan:spec_fn(Key)->Work,
    pub claimed:spec_fn(Key)->PlacementWork,
    pub group:spec_fn(Key)->GroupStep,
}

impl PlacementDelta {
    pub open spec fn before_placement(self,draw:Draw)->Placements {
        replay_view::place_frame(descriptions(self.before,self.ambient),self.before_sizing,draw)
    }
    pub open spec fn after_placement(self,draw:Draw)->Placements {
        replay_view::place_frame(descriptions(self.after,self.ambient),self.after_sizing,draw)
    }
    #[verifier::opaque]
    pub closed spec fn marks_cover_primitives(self)->bool {
        &&& ordered_nodes(self.before) && ordered_nodes(self.after)
        &&& forall|i:int|0<=i<self.after.len() ==> #[trigger] self.mark_at(i)
    }

    #[verifier::opaque]
    pub closed spec fn mark_at(self,i:int)->bool {
        self.direct_mark_at(i) && self.route_at(i)
    }

    #[verifier::opaque]
    pub closed spec fn direct_mark_at(self,i:int)->bool {
        let cur=self.after[i];
        let old=self.before[lookup(self.before,cur.key)];
        let work=(self.plan)(cur.key);
        &&& work is Place
        // An inherited force covers descendants of an edited frame. A
        // changed local rule outside that set requires a direct mark.
        &&& (!documented(self.before,cur.key) || !old.direct_same(cur))
            ==> requested(work) || (self.claimed)(cur.key) is Subtree
        &&& (self.claimed)(cur.key) is Subtree ==> work->Place_mark is Subtree
    }

    #[verifier::opaque]
    pub closed spec fn route_at(self,i:int)->bool {
        let cur=self.after[i];
        let old=self.before[lookup(self.before,cur.key)];
        let work=(self.plan)(cur.key);
        &&& work is Place && valid_route(work)
        &&& match cur.parent {
            None => true,
            Some(parent) => {
                let group=(self.group)(cur.key);
                let p=(self.plan)(parent);
                &&& p is Place
                &&& work->Place_path==p->Place_path.push(group.edge)
                &&& group.edge.parent_mark()==p->Place_mark
                &&& work->Place_root_force==p->Place_root_force
                &&& cur.reads_siblings() ==> group.explained() && group.edge.coupled
                    && group.before==old.siblings && group.after==cur.siblings
            },
        }
    }

    #[verifier::opaque]
    pub closed spec fn primitive_edits_covered(self)->bool {
        &&& self.marks_cover_primitives()
        &&& forall|i:int|0<=i<self.after.len() ==> #[trigger] self.skip_words_match(i)
    }

    #[verifier::opaque]
    pub closed spec fn skip_words_match(self,i:int)->bool {
        let cur=self.after[i];
        !requested((self.plan)(cur.key)) ==>
            replay_view::words(self.before_sizing,cur.description(self.ambient))
                ==replay_view::words(self.after_sizing,cur.description(self.ambient))
    }

    #[verifier::opaque]
    pub closed spec fn skipped_reads_are_retained(self,edit:replay_retained::Edit)->bool {
        forall|i:int|0<=i<self.after.len() ==> #[trigger] self.reads_retained_at(edit,i)
    }

    #[verifier::opaque]
    pub closed spec fn reads_retained_at(self,edit:replay_retained::Edit,i:int)->bool {
        let cur=self.after[i];
        let node=cur.description(self.ambient);
        !requested((self.plan)(cur.key)) ==>
            forall|j:int|0<=j<node.inputs.len()
                ==> edit.outside((#[trigger] node.inputs[j]).producer)
    }
}

proof fn retained_reads_are_equal(edit:replay_retained::Edit,node:PlaceNode)
    requires edit.same_shell(), forall |j:int|0<=j<node.inputs.len()
        ==> edit.outside((#[trigger] node.inputs[j]).producer),
    ensures replay_view::words(edit.old.full_sizing(),node)==replay_view::words(edit.new.full_sizing(),node),
{
    let before=replay_view::words(edit.old.full_sizing(),node);
    let after=replay_view::words(edit.new.full_sizing(),node);
    assert(before =~= after) by {
        assert forall |j:int|0<=j<node.inputs.len() implies before[j]==after[j] by {
            let source=node.inputs[j].producer;
            assert(edit.outside(source));
            replay_retained::cached_complement_matches_the_new_document(edit,source);
        };
    };
}

proof fn retained_reads_at(d:PlacementDelta,edit:replay_retained::Edit,i:int)
    requires d.reads_retained_at(edit,i),edit.same_shell(),
        d.before_sizing==edit.old.full_sizing(),d.after_sizing==edit.new.full_sizing(),
    ensures d.skip_words_match(i),
{
    reveal(PlacementDelta::reads_retained_at);
    reveal(PlacementDelta::skip_words_match);
    if !requested((d.plan)(d.after[i].key)) {
        retained_reads_are_equal(edit,d.after[i].description(d.ambient));
    }
}

pub proof fn retained_cut_preserves_skipped_placement_inputs(d:PlacementDelta,edit:replay_retained::Edit)
    requires d.marks_cover_primitives(),d.skipped_reads_are_retained(edit),edit.same_shell(),
        d.before_sizing==edit.old.full_sizing(),d.after_sizing==edit.new.full_sizing(),
    ensures d.primitive_edits_covered(),
{
    reveal(PlacementDelta::primitive_edits_covered);
    reveal(PlacementDelta::skipped_reads_are_retained);
    assert forall |i:int|0<=i<d.after.len() implies #[trigger] d.skip_words_match(i) by {
        retained_reads_at(d,edit,i);
    };
}

proof fn ordered_parent_index(nodes:Seq<NodeSource>,i:int,p:Key) -> (j:int)
    requires ordered_nodes(nodes),0<=i<nodes.len(),nodes[i].parent==Some(p),
    ensures 0<=j<i,nodes[j].key==p,
{
    reveal(ordered_nodes);
    reveal(parents_precede_children);
    choose |j:int|0<=j<i && (#[trigger] nodes[j]).key==p
}

proof fn direct_registration_forces_writes(work:Work,mark:PlacementWork,old_exists:bool,same_rule:bool)
    requires work is Place,
        (!old_exists || !same_rule) ==> requested(work) || mark is Subtree,
        mark is Subtree ==> work->Place_mark is Subtree,
        !requested(work),
    ensures old_exists && same_rule,
{
    assert(!(work->Place_mark is Subtree));
    assert(!(mark is Subtree));
}

proof fn match_skipped_node(d:PlacementDelta,i:int)
    requires d.direct_mark_at(i),0<=i<d.after.len(),!requested((d.plan)(d.after[i].key)),
    ensures ({
        let cur=d.after[i];
        let old_idx=lookup(d.before,cur.key);
        0<=old_idx<d.before.len() && d.before[old_idx].direct_same(cur)
    }),
{
    reveal(PlacementDelta::direct_mark_at);
    let cur=d.after[i];
    let old_idx=lookup(d.before,cur.key);
    let old=d.before[old_idx];
    let work=(d.plan)(cur.key);
    direct_registration_forces_writes(work,(d.claimed)(cur.key),documented(d.before,cur.key),old.direct_same(cur));
    known_node_index(d.before,cur.key);
}

proof fn skipped_rule_keeps_inputs(d:PlacementDelta,i:int,old_idx:int)
    requires d.route_at(i),0<=i<d.after.len(),0<=old_idx<d.before.len(),
        old_idx==lookup(d.before,d.after[i].key),d.before[old_idx].direct_same(d.after[i]),
        !requested((d.plan)(d.after[i].key)),
    ensures d.before[old_idx].description(d.ambient)==d.after[i].description(d.ambient),
{
    reveal(PlacementDelta::route_at);
    let cur=d.after[i];
    let work=(d.plan)(cur.key);
    let group=(d.group)(cur.key);
    let parent=match cur.parent { Some(k)=>(d.plan)(k), None=>Work::Size{recompute:false} };
    dropped_writes_keep_placement_recipe(d.before[old_idx],cur,d.ambient,work,parent,group);
}

proof fn parent_is_also_skipped(d:PlacementDelta,i:int,p:Key)
    requires d.route_at(i),d.after[i].parent==Some(p),!requested((d.plan)(d.after[i].key)),
    ensures !requested((d.plan)(p)),
{
    reveal(PlacementDelta::route_at);
    let key=d.after[i].key;
    skip_propagates_to_parent((d.plan)(key),(d.plan)(p),(d.group)(key).edge);
}

proof fn skipped_parent_indices(d:PlacementDelta,i:int,old_idx:int)
    -> (parent:Option<(int,int)>)
    requires d.route_at(i),0<=i<d.after.len(),0<=old_idx<d.before.len(),
        d.before[old_idx].parent==d.after[i].parent,
        ordered_nodes(d.before),ordered_nodes(d.after),!requested((d.plan)(d.after[i].key)),
    ensures match parent {
        Some((k,j))=> {
            &&& 0<=k<old_idx && 0<=j<i
            &&& d.after[i].parent==Some(d.after[j].key)
            &&& d.before[old_idx].parent==Some(d.before[k].key)
            &&& d.after[j].key==d.before[k].key
            &&& !requested((d.plan)(d.after[j].key))
        },
        None=>d.before[old_idx].parent.is_none() && d.after[i].parent.is_none(),
    },
{
    if let Some(p)=d.after[i].parent {
        parent_is_also_skipped(d,i,p);
        let j=ordered_parent_index(d.after,i,p);
        let k=ordered_parent_index(d.before,old_idx,p);
        Some((k,j))
    } else {
        None
    }
}

proof fn skipped_recipe_facts(d:PlacementDelta,i:int)
    requires d.primitive_edits_covered(),0<=i<d.after.len(),
    ensures d.direct_mark_at(i),d.route_at(i),d.skip_words_match(i),
        ordered_nodes(d.before),ordered_nodes(d.after),
{
    reveal(PlacementDelta::primitive_edits_covered);
    reveal(PlacementDelta::marks_cover_primitives);
    assert(d.mark_at(i));
    assert(d.skip_words_match(i));
    reveal(PlacementDelta::mark_at);
}

/// Starting with raw declarations, ordered producer reads, and plan marks,
/// reconstruct inherited frames in parent-before-child order.
pub proof fn clean_nodes_retain_their_raw_frames(d:PlacementDelta,draw:Draw,i:int)
    requires d.primitive_edits_covered(),0<=i<d.after.len(),!requested((d.plan)(d.after[i].key)),
    ensures ({
        let key=d.after[i].key;
        let before=d.before_placement(draw);
        let after=d.after_placement(draw);
        &&& before.contains_key(key) && after.contains_key(key)
        &&& replay_publication::local_input_matches(before[key],after[key])
        &&& before[key].result==after[key].result
    }),
    decreases i,
{
    skipped_recipe_facts(d,i);
    match_skipped_node(d,i);
    let old_idx=lookup(d.before,d.after[i].key);
    skipped_rule_keeps_inputs(d,i,old_idx);
    let parent=skipped_parent_indices(d,i,old_idx);
    reveal(PlacementDelta::skip_words_match);
    let old_nodes=descriptions(d.before,d.ambient);
    let new_nodes=descriptions(d.after,d.ambient);
    descriptions_have_unique_keys(d.before,d.ambient);
    descriptions_have_unique_keys(d.after,d.ambient);
    descriptions_len(d.before,d.ambient);
    descriptions_len(d.after,d.ambient);
    description_at(d.before,d.ambient,old_idx);
    description_at(d.after,d.ambient,i);
    let key=d.after[i].key;
    let node=new_nodes[i];
    assert(old_nodes[old_idx]==node && node.key==key);
    let before=d.before_placement(draw);
    let after=d.after_placement(draw);
    if let Some((k,j))=parent {
        description_at(d.before,d.ambient,k);
        description_at(d.after,d.ambient,j);
        let parent_key=d.after[j].key;
        assert(old_nodes[k].key==parent_key && new_nodes[j].key==parent_key);
        assert(node.earlier==seq![parent_key]);
        place_record_at(old_nodes,d.before_sizing,draw,old_idx,Some(k));
        place_record_at(new_nodes,d.after_sizing,draw,i,Some(j));
        clean_nodes_retain_their_raw_frames(d,draw,j);
        assert(before[parent_key].result==after[parent_key].result);
        assert(before[key].inherited==after[key].inherited);
    } else {
        place_record_at(old_nodes,d.before_sizing,draw,old_idx,None);
        place_record_at(new_nodes,d.after_sizing,draw,i,None);
    }
    assert(before[key].local==node.local && after[key].local==node.local);
    assert(before[key].measured==after[key].measured);
    assert(before[key].inherited==after[key].inherited);
    assert(replay_publication::local_input_matches(before[key],after[key]));
    assert(before[key].result==after[key].result);
}

/// Placement-only edits keep all solved producer words. A skipped rectangle
/// therefore keeps its inputs and inherited frame, including the parent's
/// unrounded edges and snapped origin.
pub proof fn placement_only_keeps_skipped_rectangles(d: PlacementDelta, draw: Draw)
    requires d.marks_cover_primitives(), d.before_sizing == d.after_sizing,
    ensures forall|i: int| 0 <= i < d.after.len() && !requested((d.plan)((#[trigger] d.after[i]).key))
        ==> {
            let key = d.after[i].key;
            let before = d.before_placement(draw);
            let after = d.after_placement(draw);
            &&& before.contains_key(key) && after.contains_key(key)
            &&& before[key].result == after[key].result
        },
{
    reveal(PlacementDelta::primitive_edits_covered);
    reveal(PlacementDelta::skip_words_match);
    assert(d.primitive_edits_covered());
    assert forall|i: int| 0 <= i < d.after.len() && !requested((d.plan)((#[trigger] d.after[i]).key))
        implies {
            let key = d.after[i].key;
            let before = d.before_placement(draw);
            let after = d.after_placement(draw);
            &&& before.contains_key(key) && after.contains_key(key)
            &&& before[key].result == after[key].result
        } by {
        clean_nodes_retain_their_raw_frames(d, draw, i);
    };
}

proof fn ordered_placement_is_covered(d:PlacementDelta,draw:Draw)
    requires d.primitive_edits_covered(),
    ensures ({
        let nodes=descriptions(d.after,d.ambient);
        let prior=d.before_placement(draw);
        &&& unique_keys(nodes)
        &&& replay_publication::sound(prior,draw)
        &&& forall|i:int|0<=i<nodes.len() ==> ({
            let key=(#[trigger] nodes[i]).key;
            &&& valid_route((d.plan)(key))
            &&& !requested((d.plan)(key)) ==> prior.contains_key(key)
                && replay_publication::local_input_matches(prior[key],d.after_placement(draw)[key])
        })
    }),
{
    let nodes=descriptions(d.after,d.ambient);
    let prior=d.before_placement(draw);
    reveal(PlacementDelta::primitive_edits_covered);
    reveal(PlacementDelta::marks_cover_primitives);
    descriptions_have_unique_keys(d.after,d.ambient);
    descriptions_len(d.after,d.ambient);
    replay_publication::canonical_records_are_sound(descriptions(d.before,d.ambient),d.before_sizing,draw);
    assert forall|i:int|0<=i<nodes.len() implies ({
        let key=(#[trigger] nodes[i]).key;
        &&& valid_route((d.plan)(key))
        &&& !requested((d.plan)(key)) ==> prior.contains_key(key)
            && replay_publication::local_input_matches(prior[key],d.after_placement(draw)[key])
    }) by {
        assert(d.mark_at(i));
        reveal(PlacementDelta::mark_at);
        reveal(PlacementDelta::route_at);
        description_at(d.after,d.ambient,i);
        if !requested((d.plan)(nodes[i].key)) { clean_nodes_retain_their_raw_frames(d,draw,i); }
    }
}

pub proof fn covered_structural_placement_matches_full(d:PlacementDelta,history:Seq<Replay>,draw:Draw,host:Outputs)
    requires d.primitive_edits_covered(), replay_history::supported(history), history.len()>0,
        d.after_sizing==history.last().full_sizing(),
        replay_publication::retained_outputs_are_sound(d.before_placement(draw),host),
        forall|i:int,j:int|0<=i<d.after.len() && 0<=j<d.after[i].description(d.ambient).inputs.len()
            ==> 0<=(#[trigger] d.after[i].description(d.ambient).inputs[j]).producer<history.last().n,
    ensures ({
        let nodes=descriptions(d.after,d.ambient);
        let after=replay_publication::commit(nodes,replay_history::measured(history),draw,d.plan,host);
        retained_view::emitted_view(Seq::new(nodes.len(),|i:int|nodes[i].key),after)
            == replay_view::ordered_view(nodes,d.after_placement(draw))
    }),
{
    let nodes=descriptions(d.after,d.ambient);
    let prior=d.before_placement(draw);
    descriptions_len(d.after,d.ambient);
    assert forall |i:int,j:int|0<=i<nodes.len() && 0<=j<nodes[i].inputs.len()
        implies 0<=(#[trigger] nodes[i].inputs[j]).producer<history.last().n by {
        description_at(d.after,d.ambient,i);
    }
    ordered_placement_is_covered(d,draw);
    reveal(unique_keys);
    replay_publication::mixed_history_can_skip_unchanged_output(history,nodes,draw,d.plan,prior,host);
}

/// Combine the retained sizing complement with the placement mark fold.
/// The placement coverage condition names producers, without supplying
/// equality of their values, inherited frames, or published rectangles.
pub proof fn retained_cut_publishes_the_full_placement(
    d:PlacementDelta,history:Seq<Replay>,draw:Draw,host:Outputs,
)
    requires
        d.marks_cover_primitives(), replay_history::supported(history), history.len()>1,
        d.before_sizing==history.drop_last().last().full_sizing(),
        d.after_sizing==history.last().full_sizing(),
        d.skipped_reads_are_retained(replay_history::transition(history.drop_last().last(),history.last())),
        replay_publication::retained_outputs_are_sound(d.before_placement(draw),host),
        forall |i:int,j:int|0<=i<d.after.len() && 0<=j<d.after[i].description(d.ambient).inputs.len()
            ==> 0<=(#[trigger] d.after[i].description(d.ambient).inputs[j]).producer<history.last().n,
    ensures ({
        let nodes=descriptions(d.after,d.ambient);
        let after=replay_publication::commit(nodes,replay_history::measured(history),draw,d.plan,host);
        retained_view::emitted_view(Seq::new(nodes.len(),|i:int|nodes[i].key),after)
            == replay_view::ordered_view(nodes,d.after_placement(draw))
    }),
{
    let previous=history.drop_last().last();
    let edit=replay_history::transition(previous,history.last());
    assert(edit.old.full_sizing()==previous.full_sizing());
    retained_cut_preserves_skipped_placement_inputs(d,edit);
    covered_structural_placement_matches_full(d,history,draw,host);
}


}
