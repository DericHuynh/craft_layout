//! From structural measurement regions and stable boundary inputs to view coverage.
use super::*;
use super::invalidation::{well_formed, trace_keys};
use super::regions::{Forest, measured, planned, required, complete_partition};
use super::retained_view::{Coverage, Frames, after, same_view_after_edits, valid_frames};

verus! {

/// `owner` maps each phase of a node incarnation to its current preorder position.
/// `retained` identifies measurements reused inside a selected region, e.g. a
/// pixel leaf. Affected placement keys include writes forced through an ancestor.
pub struct Schedule {
    pub tree: Forest,
    pub owner: spec_fn(Key) -> nat,
    pub retained: Set<Key>,
    pub placed: Set<Key>,
}

impl Schedule {
    pub open spec fn run(self, k: Key) -> bool {
        if k.phase is Placement { self.placed.contains(k) }
        else { measured(planned(self.tree, 0), (self.owner)(k)) && !self.retained.contains(k) }
    }
    pub open spec fn direct(self, k: Key) -> bool {
        if k.phase is Placement { self.placed.contains(k) }
        else { required(self.tree, 0, (self.owner)(k)) && !self.retained.contains(k) }
    }
}

/// Local rule changes have been registered. Each value crossing from a rebuilt
/// producer into a skipped reader is already known to have the same bits. The
/// interiors of the retained subtrees need no per-step input equality premise.
pub open spec fn valid_boundary(steps: Seq<Step>, s: Schedule, old: Cache, eval: Eval) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 { true } else {
        let step = steps.last();
        let prefix = steps.drop_last();
        let prior = build(prefix,old,eval,false);
        &&& valid_boundary(prefix,s,old,eval)
        &&& writes(step.work) == s.run(step.key)
        &&& !old.contains_key(step.key) || old[step.key].rule != step.rule ==> s.direct(step.key)
        &&& !s.run(step.key) ==> forall |i:int| 0 <= i < step.rule.reads.len() ==> {
            let k = #[trigger] step.rule.reads[i];
            s.run(k) ==> old.contains_key(k) && old[k].value == prior[k].value
        }
    }
}

pub proof fn regions_cover_reads(steps: Seq<Step>, s: Schedule, old: Cache, eval: Eval)
    requires well_formed(steps), valid_boundary(steps,s,old,eval), sound(old,eval), coherent(old),
    ensures covered(steps,old,eval), build(steps,old,eval,false).dom() == trace_keys(steps),
        forall |k:Key| #[trigger] trace_keys(steps).contains(k) && !s.run(k) ==> (
            old.contains_key(k) && build(steps,old,eval,false)[k].value == old[k].value),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let step = steps.last();
        let prefix = steps.drop_last();
        let prior = build(prefix,old,eval,false);
        regions_cover_reads(prefix,s,old,eval);
        complete_partition(s.tree,0,(s.owner)(step.key));
        if !s.run(step.key) {
            assert(!s.direct(step.key));
            assert(old.contains_key(step.key));
            assert(old[step.key].rule == step.rule);
            assert(args(step.rule,prior) =~= args(step.rule,old)) by {
                assert forall |i:int| 0 <= i < step.rule.reads.len() implies
                    #[trigger] prior[step.rule.reads[i]].value == old[step.rule.reads[i]].value by {
                    let k = step.rule.reads[i];
                    assert(trace_keys(prefix).contains(k));
                }
            }
        }
        assert(build(steps,old,eval,false).dom() =~= trace_keys(steps));
    }
}

/// A region may recompute an unchanged rule, such as a fixed pixel Final.
/// Protecting it and its prerequisites establishes an unchanged crossing
/// without comparing new geometry or assuming equality of evaluated results.
pub open spec fn stable_rules(steps: Seq<Step>, old: Cache, stable: ISet<Key>) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 { true } else {
        let last = steps.last();
        &&& stable_rules(steps.drop_last(),old,stable)
        &&& stable.contains(last.key) ==> ({
            &&& old.contains_key(last.key)
            &&& last.rule == old[last.key].rule
            &&& forall |i:int| 0 <= i < last.rule.reads.len()
                ==> #[trigger] stable.contains(last.rule.reads[i])
        })
    }
}

/// Every crossing into retained sizing or placement either comes from other
/// retained work or is protected by unchanged rules and their prerequisites.
pub open spec fn dependency_cut(steps: Seq<Step>, s: Schedule, old: Cache, stable: ISet<Key>) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 { true } else {
        let step = steps.last();
        &&& dependency_cut(steps.drop_last(),s,old,stable)
        &&& writes(step.work) == s.run(step.key)
        &&& !old.contains_key(step.key) || old[step.key].rule != step.rule ==> s.direct(step.key)
        &&& !s.run(step.key) ==> forall |i:int| 0 <= i < step.rule.reads.len() ==> ({
            let k = #[trigger] step.rule.reads[i];
            s.run(k) ==> stable.contains(k)
        })
    }
}

pub proof fn unchanged_rules_keep_their_values(
    steps: Seq<Step>, old: Cache, eval: Eval, stable: ISet<Key>, full: bool,
)
    requires well_formed(steps), stable_rules(steps,old,stable), sound(old,eval), coherent(old),
    ensures build(steps,old,eval,full).dom() == trace_keys(steps),
        forall |k:Key| #[trigger] trace_keys(steps).contains(k) && stable.contains(k)
            ==> old.contains_key(k) && build(steps,old,eval,full)[k].value == old[k].value,
    decreases steps.len(),
{
    if steps.len() > 0 {
        let step = steps.last();
        let prefix = steps.drop_last();
        unchanged_rules_keep_their_values(prefix,old,eval,stable,full);
        let prior = build(prefix,old,eval,full);
        if stable.contains(step.key) {
            assert(args(step.rule,prior) =~= args(step.rule,old)) by {
                assert forall |i:int| 0 <= i < step.rule.reads.len() implies
                    #[trigger] prior[step.rule.reads[i]].value == old[step.rule.reads[i]].value by {
                    let k = step.rule.reads[i];
                    assert(stable.contains(k));
                    assert(trace_keys(prefix).contains(k));
                }
            }
            assert(build(steps,old,eval,full)[step.key].value == old[step.key].value);
        }
        assert(build(steps,old,eval,full).dom() =~= trace_keys(steps));
        assert forall |k:Key| #[trigger] trace_keys(steps).contains(k) && stable.contains(k)
            implies old.contains_key(k) && build(steps,old,eval,full)[k].value == old[k].value by {
            if k != step.key { assert(trace_keys(prefix).contains(k)); }
        }
    }
}

pub proof fn unchanged_rules_discharge_boundary(steps: Seq<Step>, s: Schedule, old: Cache, eval: Eval, stable: ISet<Key>)
    requires well_formed(steps), dependency_cut(steps,s,old,stable), stable_rules(steps,old,stable),
        sound(old,eval), coherent(old),
    ensures valid_boundary(steps,s,old,eval),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let step = steps.last();
        let prefix = steps.drop_last();
        unchanged_rules_discharge_boundary(prefix,s,old,eval,stable);
        unchanged_rules_keep_their_values(prefix,old,eval,stable,false);
        let prior = build(prefix,old,eval,false);
        if !s.run(step.key) {
            assert forall |i:int| 0 <= i < step.rule.reads.len() implies ({
                let k = #[trigger] step.rule.reads[i];
                s.run(k) ==> old.contains_key(k) && old[k].value == prior[k].value
            }) by {
                assert(trace_keys(prefix).contains(step.rule.reads[i]));
            }
        }
    }
}

/// Compose a structural pass after any previous valid history, including a
/// change-aware numeric pass. Fresh full placement and retained output agree
/// in the document order of the new tree.
pub proof fn next_structural_frame(previous: Frames, sizes: Seq<Step>, root: traversal::Node, s: Schedule, eval: Eval)
    requires valid_frames(previous,eval,Coverage::UnchangedReads),
        forall |i:int| 0 <= i < sizes.len() ==> (#[trigger] sizes[i]).work is Size,
        well_formed(sizes + traversal::trace(root,Seq::empty(),false)),
        valid_boundary(sizes + traversal::trace(root,Seq::empty(),false),s,after(previous,eval).0,eval),
    ensures ({
        let steps = sizes + traversal::trace(root,Seq::empty(),false);
        let history = previous.push(steps);
        let full = retained_view::publish_frame(steps,Map::empty(),Map::empty(),eval,true);
        &&& valid_frames(history,eval,Coverage::UnchangedReads)
        &&& retained_view::emitted_view(traversal::document(root),after(history,eval).1)
            == retained_view::emitted_view(traversal::document(root),full)
    }),
{
    let steps = sizes + traversal::trace(root,Seq::empty(),false);
    same_view_after_edits(previous,eval,Coverage::UnchangedReads);
    regions_cover_reads(steps,s,after(previous,eval).0,eval);
    assert(previous.push(steps).drop_last() =~= previous);
    assert(previous.push(steps).last() == steps);
    traversal::retained_tree_matches_full(root,sizes,previous,eval,Coverage::UnchangedReads,false);
}

/// For a structural frame whose crossings are closed at unchanged rules,
/// equivalence requires no independently established boundary-value equality.
pub proof fn structural_frame_matches_at_unchanged_rules(
    previous: Frames, sizes: Seq<Step>, root: traversal::Node, s: Schedule, eval: Eval, stable: ISet<Key>,
)
    requires valid_frames(previous,eval,Coverage::UnchangedReads),
        forall |i:int| 0 <= i < sizes.len() ==> (#[trigger] sizes[i]).work is Size,
        ({
            let steps = sizes + traversal::trace(root,Seq::empty(),false);
            let cache = after(previous,eval).0;
            &&& well_formed(steps)
            &&& stable_rules(steps,cache,stable)
            &&& dependency_cut(steps,s,cache,stable)
        }),
    ensures ({
        let steps = sizes + traversal::trace(root,Seq::empty(),false);
        let history = previous.push(steps);
        let full = retained_view::publish_frame(steps,Map::empty(),Map::empty(),eval,true);
        &&& valid_frames(history,eval,Coverage::UnchangedReads)
        &&& retained_view::emitted_view(traversal::document(root),after(history,eval).1)
            == retained_view::emitted_view(traversal::document(root),full)
    }),
{
    let steps = sizes + traversal::trace(root,Seq::empty(),false);
    same_view_after_edits(previous,eval,Coverage::UnchangedReads);
    unchanged_rules_discharge_boundary(steps,s,after(previous,eval).0,eval,stable);
    next_structural_frame(previous,sizes,root,s,eval);
}

}
