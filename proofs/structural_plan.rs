//! Decide when a structural edit must cross a parent boundary.
use vstd::prelude::*;
use super::{regions, regional_frame, invalidation, Key, Cache, Step, Eval, build, sound, coherent, dependencies::{self, Edge, Part, rules::Form}};
use super::structural::kernel as structural_changes;
use structural_changes::StructuralChange;

#[path = "../src/region_policy.rs"]
pub(crate) mod policy;

verus! {

pub enum Layout {
    Free,
    Stack { share_ready: bool, flexible_child: bool },
    FlowOrGrid,
}

/// Facts sampled by the production planner. `reads_children` is the scan
/// over the node's six declarations, using the resolved dependency form.
pub struct Facts {
    pub change: StructuralChange,
    pub enabled: bool,
    pub layout: Layout,
    pub solved: bool,
    pub cyclic: bool,
    pub reads_children: bool,
    pub block_item: bool,
    pub in_parent_flow: bool,
}

impl Facts {
    pub open spec fn refreshes(self) -> bool {
        policy::can_refresh(self.block_item, self.solved, self.reads_children)
        && match self.layout {
            Layout::Free => true,
            Layout::Stack { share_ready, flexible_child } => !share_ready && !flexible_child,
            Layout::FlowOrGrid => false,
        }
    }

    pub open spec fn promotes(self, changed_child: bool, nested_region: bool) -> bool {
        let changed = changed_child || self.change is Children;
        !policy::starts_region(self.change) && self.enabled
            && match policy::after_children(changed,self.cyclic,nested_region) {
                policy::AfterChildren::Keep => false,
                policy::AfterChildren::Refresh => !self.refreshes(),
                policy::AfterChildren::Rebuild => true,
            }
    }

    pub open spec fn informs_parent(self, promoted: bool) -> bool {
        policy::starts_region(self.change) ||
            promoted && policy::affects_parent(self.cyclic, self.reads_children, self.block_item, self.in_parent_flow)
    }
}

/// A refreshed parent has no final or declared dependency on a child. Stack
/// shares are absent, and the guard excludes flow/grid side effects.
pub proof fn refreshed_parent_has_no_dependency_on_changed_child(facts: Facts, parent: Part, child: Part, e: Edge)
    requires facts.refreshes(), e.source is Child,
        parent is Declared ==> (parent->Declared_0.reads_children() ==> facts.reads_children),
        parent is Share ==> match facts.layout {
            Layout::Free => false,
            Layout::Stack { share_ready, .. } => share_ready,
            Layout::FlowOrGrid => true,
        },
    ensures !dependencies::full_read(parent, child, e),
{
    assert(!facts.reads_children);
}

/// Available space in a stack changes with the sibling gaps only on its
/// main axis and for in-flow fractional or Fill declarations.
pub proof fn refreshed_stack_has_no_affected_declaration(facts: Facts, enabled: bool, in_flow: bool, main: bool, decl: Form)
    requires facts.refreshes(), facts.layout is Stack,
        (main && policy::stack_reads_child_list(enabled,in_flow, decl is Fraction || decl is Fill))
                ==> facts.layout->Stack_flexible_child,
    ensures enabled && in_flow && main ==> !(decl is Fraction || decl is Fill),
{}

pub enum Forest {
    Empty,
    Node { facts: Facts, children: Box<Forest>, rest: Box<Forest> },
}

pub struct Requests {
    pub affects_parent: bool,
    pub has_regions: bool,
}

pub open spec fn decisions(tree: Forest) -> (regions::Forest, Requests)
    decreases tree,
{
    match tree {
        Forest::Empty => (regions::Forest::Empty, Requests { affects_parent:false, has_regions:false }),
        Forest::Node { facts, children, rest } => {
            let tail = decisions(*rest);
            let (inside, requests) = if facts.enabled || policy::starts_region(facts.change) {
                decisions(*children)
            } else {
                (regions::Forest::Empty, Requests { affects_parent:false, has_regions:false })
            };
            let direct = policy::starts_region(facts.change);
            let raise = facts.promotes(requests.affects_parent, requests.has_regions);
            let informs = facts.informs_parent(raise);
            let regions = regions::Forest::Node { direct, raise, children: Box::new(inside), siblings: Box::new(tail.0) };
            (regions, Requests {
                affects_parent: informs || tail.1.affects_parent,
                has_regions: direct || raise || requests.has_regions || tail.1.has_regions,
            })
        },
    }
}

/// A finite adapter forest produces the same global region partition whether
/// a node is selected before visiting children or replaces tentative regions.
/// The child return value records actual propagation, distinct from whether
/// there is work deeper in the branch. Cyclic promotion uses both.
pub proof fn planner_emits_partition(tree: Forest, start: nat, pos: nat, prior: Seq<regions::Interval>)
    ensures ({
        let (forest, requests) = decisions(tree);
        let plan = regions::planned(forest,start);
        &&& regions::collect(forest,start,prior) == prior + plan.regions
        &&& regions::ordered(plan.regions,start,start + regions::length(forest))
        &&& requests.has_regions == (plan.regions.len() > 0)
        &&& regions::required(forest,start,pos) ==> regions::measured(plan,pos)
    }),
    decreases tree,
{
    let (forest, requests) = decisions(tree);
    let plan = regions::planned(forest,start);
    regions::rollback_preserves_other_regions(forest,start,prior);
    regions::complete_partition(forest,start,pos);
    match tree {
        Forest::Empty => {
            assert(!requests.has_regions);
            assert(plan.regions.len() == 0);
        },
        Forest::Node { facts, children, rest } => {
            let take_children = facts.enabled || policy::starts_region(facts.change);
            let children_forest = if take_children { decisions(*children).0 } else { regions::Forest::Empty };
            let child_requests = take_children && decisions(*children).1.has_regions;
            let end = start + 1 + regions::length(children_forest);
            let kids = regions::planned(children_forest,start + 1);
            let tail = regions::planned(decisions(*rest).0,end);
            planner_emits_partition(*rest,end,pos,prior);
            assert(decisions(*rest).1.has_regions == (tail.regions.len() > 0));
            if take_children {
                planner_emits_partition(*children,start + 1,pos,prior);
            }
            assert(child_requests == (kids.regions.len() > 0));
            assert(plan.regions.len()
                == tail.regions.len() + if forest->Node_direct || forest->Node_raise { 1 } else { kids.regions.len() });
            assert(requests.has_regions == (plan.regions.len() > 0));
        },
    }
}

pub proof fn a_refreshed_boundary_stops_sizing_propagation(facts: Facts, child: bool, nested: bool)
    requires facts.refreshes(), !facts.cyclic, !policy::starts_region(facts.change),
    ensures !facts.promotes(child,nested), !facts.informs_parent(facts.promotes(child,nested)),
{}

pub proof fn cyclic_boundary_accounts_for_nested_work(facts: Facts, child: bool, nested: bool)
    requires facts.cyclic, facts.enabled, child || nested || facts.change is Children,
    ensures policy::starts_region(facts.change) || facts.promotes(child,nested),
        facts.informs_parent(facts.promotes(child,nested)),
{}

pub proof fn movement_and_local_changes_start_regions(change: StructuralChange)
    ensures policy::starts_region(change) == (change is Moved || change is Subtree),
{}

pub proof fn a_clean_branch_gate_excludes_dirty_or_cyclic_nodes(change: StructuralChange, cyclic: bool)
    ensures policy::clean_branch_root(change,cyclic) == (change is Clean && !cyclic),
{}


/// Immediate-parent and immediate-child relationships are determined by the
/// adapter's own links. A subtree rooted at `root` contains every child of
/// each included node. Its only missing parent is the parent of `root`.
pub struct SubtreeCut {
    pub root: int,
    pub inside: Set<int>,
    pub parent: spec_fn(int) -> Option<int>,
}

impl SubtreeCut {
    pub open spec fn valid(self) -> bool {
        &&& self.inside.contains(self.root)
        &&& forall |i:int| match #[trigger] (self.parent)(i) {
            Some(p) => (self.inside.contains(p) ==> self.inside.contains(i))
                && (i != self.root && self.inside.contains(i) ==> self.inside.contains(p)),
            None => true,
        }
    }

    pub open spec fn relates(self, reader: int, input: int, edge: Edge) -> bool {
        match edge.source {
            dependencies::Source::SameNode => reader == input,
            dependencies::Source::Parent => (self.parent)(reader) == Some(input),
            dependencies::Source::Child => (self.parent)(input) == Some(reader),
            dependencies::Source::Elsewhere => true,
        }
    }
}

pub open spec fn boundary_slot(slot: Part) -> bool {
    slot is Final || slot is Declared && slot->Declared_0 is Constant
}

/// Explicit finite pixels without bounds expose only their Regular and Final
/// slots to the surrounding non-flow graph. A local share can read the
/// boundary Final, but is itself private to the subtree.
pub proof fn fixed_pixel_boundary_is_closed(cut: SubtreeCut, reader: int, input: int, r: Part, s: Part, edge: Edge)
    requires cut.valid(), cut.relates(reader,input,edge), dependencies::full_read(r,s,edge),
        reader == cut.root ==> boundary_slot(r) || r is Share,
        input == cut.root ==> (boundary_slot(s) || s is Share) && !edge.child_has_fill,
    ensures
        cut.inside.contains(reader) ==> cut.inside.contains(input),
        !cut.inside.contains(reader) && cut.inside.contains(input)
            ==> input == cut.root && edge.source is Child && boundary_slot(s),
{
    if cut.inside.contains(reader) && !cut.inside.contains(input) {
        match edge.source {
            dependencies::Source::Parent => {
                assert((cut.parent)(reader) == Some(input));
                assert(reader == cut.root);
            },
            _ => {},
        }
    }
    if !cut.inside.contains(reader) && cut.inside.contains(input) {
        match edge.source {
            dependencies::Source::Child => {
                assert((cut.parent)(input) == Some(reader));
                assert(input == cut.root);
            },
            _ => {},
        }
    }
}


/// Relate measurement keys to the adapter's immediate-neighbor links. An
/// explicit pixel root has only regular/final declarations and optional local
/// stack share work. Other layout-specific side state has its own proof.
pub struct BranchGraph {
    pub cut: SubtreeCut,
    pub owner: spec_fn(Key) -> int,
    pub part: spec_fn(Key) -> Part,
    pub edge: spec_fn(Key, Key) -> Edge,
}

impl BranchGraph {
    pub open spec fn stable(self) -> ISet<Key> {
        ISet::new(|k:Key| k.phase is Measurement && self.cut.inside.contains((self.owner)(k)))
    }

    pub open spec fn input(self, reader: Key, producer: Key) -> bool {
        let r = (self.owner)(reader);
        let s = (self.owner)(producer);
        let e = (self.edge)(reader,producer);
        let p = (self.part)(reader);
        let q = (self.part)(producer);
        &&& producer.phase is Measurement
        &&& self.cut.relates(r,s,e)
        &&& dependencies::full_read(p,q,e)
        &&& r == self.cut.root ==> boundary_slot(p) || p is Share
        &&& s == self.cut.root ==> (boundary_slot(q) || q is Share) && !e.child_has_fill
    }
}

pub open spec fn stable_branch_source(steps: Seq<Step>, old: Cache, branch: BranchGraph) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 { true } else {
        let step = steps.last();
        &&& stable_branch_source(steps.drop_last(),old,branch)
        &&& branch.stable().contains(step.key) ==> ({
            &&& old.contains_key(step.key)
            &&& step.rule == old[step.key].rule
            &&& forall |i:int| 0 <= i < step.rule.reads.len()
                ==> branch.input(step.key,#[trigger] step.rule.reads[i])
        })
    }
}

/// The fixed pixel cut closes the prerequisites of even deeply nested cached
/// slots. Equality follows for every slot regardless of which are recomputed.
pub proof fn fixed_branch_keeps_every_sizing_value(
    steps: Seq<Step>, old: Cache, branch: BranchGraph, eval: Eval, k: Key,
)
    requires branch.cut.valid(), stable_branch_source(steps,old,branch),
        invalidation::well_formed(steps), sound(old,eval), coherent(old),
    ensures regional_frame::stable_rules(steps,old,branch.stable()),
        branch.stable().contains(k) && invalidation::trace_keys(steps).contains(k) ==> {
            &&& build(steps,old,eval,false)[k].value == old[k].value
            &&& build(steps,old,eval,true)[k].value == old[k].value
        },
    decreases steps.len(),
{
    if steps.len() > 0 {
        fixed_branch_keeps_every_sizing_value(steps.drop_last(),old,branch,eval,k);
        let step = steps.last();
        if branch.stable().contains(step.key) {
            assert forall |i:int| 0 <= i < step.rule.reads.len()
                implies #[trigger] branch.stable().contains(step.rule.reads[i]) by {
                let read = step.rule.reads[i];
                let r = (branch.owner)(step.key);
                let s = (branch.owner)(read);
                fixed_pixel_boundary_is_closed(branch.cut,r,s,(branch.part)(step.key),
                    (branch.part)(read),(branch.edge)(step.key,read));
            }
        }
    }
    regional_frame::unchanged_rules_keep_their_values(steps,old,eval,branch.stable(),false);
    regional_frame::unchanged_rules_keep_their_values(steps,old,eval,branch.stable(),true);
}

}
