//! Compose a change-aware sizing queue with the full placement used for numeric edits.
use super::*;
use super::invalidation::{trace_keys, well_formed};
use super::retained_view::{after, Coverage, emitted_view, Frames, publish_frame, same_view_after_edits, valid_frames, visible_keys};
use super::traversal::{document, Node, placement_keys_follow_document};

verus! {

pub open spec fn frame(previous: Frames, f: queue_view::Frame, seeds: Set<int>, root: Node, eval: Eval) -> Seq<Step> {
    let sizes = queue_view::trace(f, after(previous,eval).0, seeds, eval, f.keys.len());
    sizes + traversal::trace(root, Seq::empty(), true)
}

proof fn keys_in_cache(steps: Seq<Step>, old: Cache, eval: Eval)
    ensures build(steps,old,eval,false).dom() == trace_keys(steps),
    decreases steps.len(),
{
    if steps.len() > 0 {
        keys_in_cache(steps.drop_last(),old,eval);
        assert(build(steps,old,eval,false).dom() =~= trace_keys(steps));
    }
}

proof fn force_suffix(prefix: Seq<Step>, tail: Seq<Step>, old: Cache, eval: Eval)
    requires covered(prefix,old,eval), well_formed(prefix + tail),
        forall |i:int| 0 <= i < tail.len() ==> {
            let w = (#[trigger] tail[i]).work; w is Place && w->Place_root_force
        },
    ensures covered(prefix + tail,old,eval),
        visible_keys(prefix + tail) == visible_keys(prefix) + visible_keys(tail),
    decreases tail.len(),
{
    if tail.len() > 0 {
        let prior = prefix + tail.drop_last();
        assert((prefix + tail).drop_last() =~= prior);
        force_suffix(prefix,tail.drop_last(),old,eval);
        keys_in_cache(prior,old,eval);
        let step = tail.last();
        assert(step == tail[tail.len()-1]);
        requested_work_is_executed(step.work);
        assert((prefix + tail).last() == step);
        assert(visible_keys(prefix + tail) =~= visible_keys(prefix) + visible_keys(tail));
    } else { assert(prefix + tail =~= prefix); }
}

proof fn sizing_has_no_visible_keys(f: queue_view::Frame, old: Cache, seeds: Set<int>, eval: Eval, n: nat)
    ensures visible_keys(queue_view::trace(f,old,seeds,eval,n)) == Seq::<Key>::empty(),
    decreases n,
{
    if n > 0 {
        sizing_has_no_visible_keys(f,old,seeds,eval,(n-1) as nat);
        let steps = queue_view::trace(f,old,seeds,eval,n);
        assert(steps.drop_last() == queue_view::trace(f,old,seeds,eval,(n-1) as nat));
    }
}

/// A numeric edit can stop propagation as soon as a value compares equal.
/// A well-formed host tree and registered primitive edits suffice for this next frame:
/// the caller does not have to establish coverage of skipped work in the new frame.
pub proof fn next_numeric_frame(previous: Frames, f: queue_view::Frame, edits: Seq<dependencies::Edit>, root: Node, eval: Eval)
    requires valid_frames(previous,eval,Coverage::UnchangedReads),
        f.stable_graph(after(previous,eval).0,eval),
        forall |i:int| 0 <= i < f.keys.len() && after(previous,eval).0[f.keys[i]].rule.local != f.local[i]
            ==> #[trigger] dependencies::reader_changed(edits,i),
        well_formed(frame(previous,f,dependencies::batch_seeds(edits,f.keys.len()),root,eval)),
    ensures ({
        let steps = frame(previous,f,dependencies::batch_seeds(edits,f.keys.len()),root,eval);
        let frames = previous.push(steps);
        let fresh = publish_frame(steps,Map::empty(),Map::empty(),eval,true);
        &&& valid_frames(frames,eval,Coverage::UnchangedReads)
        &&& emitted_view(document(root),after(frames,eval).1) == emitted_view(document(root),fresh)
    }),
{
    same_view_after_edits(previous,eval,Coverage::UnchangedReads);
    let old = after(previous,eval).0;
    let seeds = dependencies::batch_seeds(edits,f.keys.len());
    let sizes = queue_view::trace(f,old,seeds,eval,f.keys.len());
    let places = traversal::trace(root,Seq::empty(),true);
    queue_view::registered_sizing_frame_matches_full(f,edits,old,eval);
    traversal::trace_force_steps(root,Seq::empty(),true);
    force_suffix(sizes,places,old,eval);
    sizing_has_no_visible_keys(f,old,seeds,eval,f.keys.len());
    placement_keys_follow_document(root,Seq::empty(),true);
    assert(visible_keys(sizes + places) =~= document(root));
    let frames = previous.push(sizes + places);
    assert(frames.drop_last() =~= previous);
    assert(frames.last() == sizes + places);
    same_view_after_edits(frames,eval,Coverage::UnchangedReads);
}
}
