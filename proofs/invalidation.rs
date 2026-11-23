//! Coverage of edits in an ordered dependency trace.
use super::*;

verus! {

pub open spec fn trace_keys(steps: Seq<Step>) -> Set<Key>
    decreases steps.len(),
{
    if steps.len() == 0 { Set::empty() }
    else { trace_keys(steps.drop_last()).insert(steps.last().key) }
}

// A key is produced once in this frame and every input is produced before its reader.
pub open spec fn well_formed(steps: Seq<Step>) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 { true }
    else {
        let prefix = steps.drop_last();
        let earlier = trace_keys(prefix);
        let step = steps.last();
        well_formed(prefix) && valid_route(step.work)
            && ((step.key.phase is Placement) == (step.work is Place))
            && !earlier.contains(step.key)
            && (forall |i: int| 0 <= i < step.rule.reads.len() ==>
                #[trigger] earlier.contains(step.rule.reads[i]))
    }
}

// Rule equality includes the ordered read keys and every local input. Replacing
// a dependency with another key counts as an edit even if its current bits agree.
pub open spec fn needs_rebuild(step: Step, old: Cache, earlier_dirty: Set<Key>) -> bool {
    !old.contains_key(step.key) || step.rule != old[step.key].rule
        || (exists |i: int| 0 <= i < step.rule.reads.len()
            && #[trigger] earlier_dirty.contains(step.rule.reads[i]))
}

pub open spec fn invalidated(steps: Seq<Step>, old: Cache) -> Set<Key>
    decreases steps.len(),
{
    if steps.len() == 0 { Set::empty() }
    else {
        let earlier = invalidated(steps.drop_last(), old);
        let step = steps.last();
        if needs_rebuild(step, old, earlier) { earlier.insert(step.key) } else { earlier }
    }
}

// Each step may conservatively do more work than the edit closure requires.
pub open spec fn rebuilds_invalidated(steps: Seq<Step>, old: Cache) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 { true }
    else {
        let prefix = steps.drop_last();
        let step = steps.last();
        rebuilds_invalidated(prefix, old)
            && (needs_rebuild(step, old, invalidated(prefix, old)) ==> requested(step.work))
    }
}

pub proof fn edits_cover_reads(steps: Seq<Step>, old: Cache, eval: Eval)
    requires well_formed(steps), rebuilds_invalidated(steps, old), sound(old, eval), coherent(old),
    ensures
        covered(steps, old, eval),
        build(steps, old, eval, false).dom() == trace_keys(steps),
        forall |key: Key| #[trigger] trace_keys(steps).contains(key)
            && !invalidated(steps, old).contains(key) ==> (
                old.contains_key(key)
                && build(steps, old, eval, false)[key].value == old[key].value
            ),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let prefix = steps.drop_last();
        edits_cover_reads(prefix, old, eval);
        let step = steps.last();
        requested_work_is_executed(step.work);
        let earlier = build(prefix, old, eval, false);
        let dirty = invalidated(prefix, old);
        let result = build(steps, old, eval, false);
        assert(result.dom() =~= trace_keys(steps));
        assert forall |i: int| 0 <= i < step.rule.reads.len() implies
            #[trigger] earlier.contains_key(step.rule.reads[i]) by {
            assert(trace_keys(prefix).contains(step.rule.reads[i]));
        }
        if !needs_rebuild(step, old, dirty) {
            let entry = old[step.key];
            assert(old.contains_key(step.key));
            assert(entry.rule == step.rule);
            assert(entry.args == args(entry.rule, old));
            assert(args(step.rule, earlier) =~= args(step.rule, old)) by {
                assert forall |i: int| 0 <= i < step.rule.reads.len() implies
                    #[trigger] earlier[step.rule.reads[i]].value == old[step.rule.reads[i]].value by {
                    let read = step.rule.reads[i];
                    assert(trace_keys(prefix).contains(read));
                    assert(!dirty.contains(read));
                }
            }
            assert(entry.value == eval.apply(step.key, entry.rule, entry.args));
            assert(result[step.key].value == entry.value);
        }
        assert forall |key: Key| #[trigger] trace_keys(steps).contains(key)
            && !invalidated(steps, old).contains(key) implies (
                old.contains_key(key) && result[key].value == old[key].value
            ) by {
            if key != step.key {
                assert(trace_keys(prefix).contains(key));
            }
        }
    }
}

}
