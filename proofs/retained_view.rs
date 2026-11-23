//! The host retains old rectangles and receives only the writes made by placement.
use super::*;
use super::invalidation::{edits_cover_reads, rebuilds_invalidated, well_formed};

verus! {

pub type Outputs = Map<Key, Geometry>;

pub open spec fn published(cache: Cache, outputs: Outputs) -> bool {
    forall |k: Key| cache.contains_key(k) && (#[trigger] cache[k]).value is Rects ==> {
        &&& outputs.contains_key(k)
        &&& outputs[k] == cache[k].value->Rects_0
    }
}

pub open spec fn emitted_view(order: Seq<Key>, outputs: Outputs) -> Seq<(Key, Geometry)> {
    Seq::new(order.len(), |i: int| (order[i], outputs[order[i]]))
}

// Physical host storage starts with the previous outputs. Skipping a write is
// observable here. Entries outside the new visible order may remain in storage.
pub open spec fn publish_frame(steps: Seq<Step>, initial: Outputs, old: Cache, eval: Eval, full: bool) -> Outputs
    decreases steps.len(),
{
    if steps.len() == 0 { initial }
    else {
        let prior = publish_frame(steps.drop_last(), initial, old, eval, full);
        let step = steps.last();
        let value = build(steps, old, eval, full)[step.key].value;
        if step.work is Place && (full || writes(step.work)) && value is Rects {
            prior.insert(step.key, value->Rects_0)
        } else { prior }
    }
}

proof fn writes_publish_current_geometry(steps: Seq<Step>, initial: Outputs, old: Cache, eval: Eval)
    requires
        sound(old, eval), covered(steps, old, eval), well_formed(steps),
        published(old, initial),
    ensures
        published(build(steps, old, eval, false), publish_frame(steps, initial, old, eval, false)),
        published(build(steps, Map::empty(), eval, true), publish_frame(steps, Map::empty(), Map::empty(), eval, true)),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let prefix = steps.drop_last();
        writes_publish_current_geometry(prefix, initial, old, eval);
        incremental_matches_full(prefix, old, eval);
        incremental_matches_full(steps, old, eval);
        let step = steps.last();
        let result = build(steps, old, eval, false);
        let prior = build(prefix, old, eval, false);
        let outputs = publish_frame(steps, initial, old, eval, false);
        let full = publish_frame(steps, Map::empty(), Map::empty(), eval, true);
        assert forall |k: Key| result.contains_key(k) && (#[trigger] result[k]).value is Rects implies {
            &&& outputs.contains_key(k)
            &&& outputs[k] == result[k].value->Rects_0
            &&& full.contains_key(k)
            &&& full[k] == result[k].value->Rects_0
        } by {
            if k != step.key {
                assert(prior.contains_key(k));
                assert(prior[k] == result[k]);
            } else if !writes(step.work) {
                assert(old.contains_key(k));
                assert(initial[k] == old[k].value->Rects_0);
                skipped_key_retains_output(prefix, initial, old, eval, k);
            }
        }
    }
}

// No earlier step in a well-formed trace is allowed to overwrite this key.
proof fn skipped_key_retains_output(steps: Seq<Step>, initial: Outputs, old: Cache, eval: Eval, k: Key)
    requires !build(steps, old, eval, false).contains_key(k),
    ensures
        publish_frame(steps, initial, old, eval, false).contains_key(k) == initial.contains_key(k),
        initial.contains_key(k) ==> publish_frame(steps, initial, old, eval, false)[k] == initial[k],
    decreases steps.len(),
{
    if steps.len() > 0 { skipped_key_retains_output(steps.drop_last(), initial, old, eval, k); }
}

// Document order comes from the current trace, including the placement steps
// skipped in this pass. There is no caller-supplied list of keys to compare.
pub open spec fn visible_keys(steps: Seq<Step>) -> Seq<Key>
    decreases steps.len(),
{
    if steps.len() == 0 { Seq::empty() }
    else {
        let prior = visible_keys(steps.drop_last());
        let step = steps.last();
        if step.work is Place { prior.push(step.key) } else { prior }
    }
}

proof fn visible_keys_have_geometry(steps: Seq<Step>, old: Cache, eval: Eval)
    requires sound(old, eval), covered(steps, old, eval), well_formed(steps),
    ensures has_rects(visible_keys(steps), build(steps, old, eval, false)),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let prefix = steps.drop_last();
        let step = steps.last();
        visible_keys_have_geometry(prefix, old, eval);
        incremental_matches_full(steps, old, eval);
        let order = visible_keys(steps);
        let result = build(steps, old, eval, false);
        assert forall |i: int| 0 <= i < order.len() implies {
            &&& #[trigger] result.contains_key(order[i])
            &&& result[order[i]].value is Rects
        } by {
            if i < visible_keys(prefix).len() {
                assert(order[i] == visible_keys(prefix)[i]);
                assert(build(prefix, old, eval, false).contains_key(order[i]));
            }
        }
    }
}

pub type Frames = Seq<Seq<Step>>;

// Start each independent full build with empty output storage. Only incremental
// evaluation carries the host buffer and the dependency cache between frames.
pub open spec fn after(frames: Frames, eval: Eval) -> (Cache, Outputs)
    decreases frames.len(),
{
    if frames.len() == 0 { (Map::empty(), Map::empty()) }
    else {
        let steps = frames.last();
        let (cache, host) = after(frames.drop_last(), eval);
        (build(steps, cache, eval, false), publish_frame(steps, host, cache, eval, false))
    }
}

pub enum Coverage {
    // Rebuild every transitive reader of an edited rule.
    DirtyClosure,
    // Stop propagation when the actual ordered inputs to a skipped step agree.
    UnchangedReads,
}

pub open spec fn valid_frames(frames: Frames, eval: Eval, coverage: Coverage) -> bool
    decreases frames.len(),
{
    if frames.len() == 0 { true }
    else {
        let steps = frames.last();
        let old = after(frames.drop_last(), eval).0;
        valid_frames(frames.drop_last(), eval, coverage)
        && well_formed(steps)
        && match coverage {
            Coverage::DirtyClosure => rebuilds_invalidated(steps, old),
            Coverage::UnchangedReads => covered(steps, old, eval),
        }
    }
}

// Holds for every finite prefix of edits, including an initial build from empty,
// and compares the retained host output with a newly populated host buffer.
pub proof fn same_view_after_edits(frames: Frames, eval: Eval, coverage: Coverage)
    requires valid_frames(frames, eval, coverage),
    ensures
        sound(after(frames, eval).0, eval),
        coherent(after(frames, eval).0),
        published(after(frames, eval).0, after(frames, eval).1),
        frames.len() > 0 ==> {
            let steps = frames.last();
            let full = publish_frame(steps, Map::empty(), Map::empty(), eval, true);
            emitted_view(visible_keys(steps), after(frames, eval).1) == emitted_view(visible_keys(steps), full)
        },
    decreases frames.len(),
{
    if frames.len() > 0 {
        let prefix = frames.drop_last();
        let (old, host) = after(prefix, eval);
        let steps = frames.last();
        let order = visible_keys(steps);
        same_view_after_edits(prefix, eval, coverage);
        if coverage is DirtyClosure {
            edits_cover_reads(steps, old, eval);
        }
        incremental_matches_full(steps, old, eval);
        visible_keys_have_geometry(steps, old, eval);
        writes_publish_current_geometry(steps, host, old, eval);
        let (cache, outputs) = after(frames, eval);
        let full = publish_frame(steps, Map::empty(), Map::empty(), eval, true);
        assert forall |i: int| 0 <= i < order.len() implies
            #[trigger] outputs[order[i]] == full[order[i]] by {
            let k = order[i];
            assert(cache.contains_key(k));
            assert(cache[k].value is Rects);
        }
        assert(emitted_view(order, outputs) =~= emitted_view(order, full));
    }
}

}
