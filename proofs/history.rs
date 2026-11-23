//! A mixed history beginning with empty cache and empty host output.
use super::*;
use super::invalidation::{edits_cover_reads, rebuilds_invalidated, well_formed};
use super::retained_view::{Coverage, Frames, after, emitted_view, publish_frame, same_view_after_edits, valid_frames};
use super::traversal::{Node, document};

verus! {

pub enum Build {
    Full { declarations: Seq<(Key, Rule)> },
    Numeric { sizing: queue_view::Frame, edits: Seq<dependencies::Edit> },
    Structural { sizes: Seq<Step>, schedule: regional_frame::Schedule },
}

pub struct Frame {
    pub root: Node,
    pub build: Build,
}

pub open spec fn full_sizes(declarations: Seq<(Key,Rule)>) -> Seq<Step> {
    Seq::new(declarations.len(), |i:int| Step { key:declarations[i].0, rule:declarations[i].1,
        work:Work::Size {recompute:true} })
}

impl Frame {
    pub open spec fn steps(self, prior: Frames, eval: Eval) -> Seq<Step> {
        match self.build {
            Build::Full {declarations} => full_sizes(declarations) + traversal::trace(self.root,Seq::empty(),true),
            Build::Numeric {sizing,edits} => numeric_frame::frame(prior,sizing,
                dependencies::batch_seeds(edits,sizing.keys.len()),self.root,eval),
            Build::Structural {sizes,..} => sizes + traversal::trace(self.root,Seq::empty(),false),
        }
    }

    pub open spec fn supported(self, prior: Frames, eval: Eval) -> bool {
        let old = after(prior,eval).0;
        let steps = self.steps(prior,eval);
        well_formed(steps) && match self.build {
            Build::Full {..} => true,
            Build::Numeric {sizing,edits} =>
                sizing.stable_graph(old,eval)
                && forall |i:int| 0 <= i < sizing.keys.len() && old[sizing.keys[i]].rule.local != sizing.local[i]
                    ==> #[trigger] dependencies::reader_changed(edits,i),
            Build::Structural {sizes,schedule} =>
                (forall |i:int| 0 <= i < sizes.len() ==> (#[trigger] sizes[i]).work is Size)
                && regional_frame::valid_boundary(steps,schedule,old,eval),
        }
    }
}

pub open spec fn traces(history: Seq<Frame>, eval: Eval) -> Frames
    decreases history.len(),
{
    if history.len() == 0 { Seq::empty() } else {
        let prior = traces(history.drop_last(),eval);
        prior.push(history.last().steps(prior,eval))
    }
}

pub open spec fn supported(history: Seq<Frame>, eval: Eval) -> bool
    decreases history.len(),
{
    history.len() == 0 || (supported(history.drop_last(),eval) &&
        history.last().supported(traces(history.drop_last(),eval),eval))
}

proof fn full_requests_every_change(steps: Seq<Step>, old: Cache)
    requires forall|i:int| 0 <= i < steps.len() ==> requested((#[trigger] steps[i]).work),
    ensures rebuilds_invalidated(steps,old),
    decreases steps.len(),
{
    if steps.len() > 0 {
        assert(requested(steps[steps.len()-1].work));
        full_requests_every_change(steps.drop_last(),old);
    }
}

/// Every prefix of a supported history has the fresh full view in the visible
/// order of its own final tree. Coverage of the new frame is a conclusion.
pub proof fn same_document_across_mixed_builds(history: Seq<Frame>, eval: Eval)
    requires supported(history,eval),
    ensures ({
        let frames = traces(history,eval);
        &&& frames.len() == history.len()
        &&& valid_frames(frames,eval,Coverage::UnchangedReads)
        &&& history.len() > 0 ==> {
            let fresh = publish_frame(frames.last(),Map::empty(),Map::empty(),eval,true);
            let keys = document(history.last().root);
            emitted_view(keys,after(frames,eval).1) == emitted_view(keys,fresh)
        }
    }),
    decreases history.len(),
{
    if history.len() > 0 {
        let frame = history.last();
        let prior = traces(history.drop_last(),eval);
        let steps = frame.steps(prior,eval);
        let frames = prior.push(steps);
        assert(frames.drop_last() =~= prior);
        assert(frames.last() == steps);
        same_document_across_mixed_builds(history.drop_last(),eval);
        match frame.build {
            Build::Numeric {sizing,edits} => numeric_frame::next_numeric_frame(prior,sizing,edits,frame.root,eval),
            Build::Structural {sizes,schedule} => regional_frame::next_structural_frame(prior,sizes,frame.root,schedule,eval),
            Build::Full {declarations} => {
                let old = after(prior,eval).0;
                let places = traversal::trace(frame.root,Seq::empty(),true);
                let sizes = full_sizes(declarations);
                traversal::trace_force_steps(frame.root,Seq::empty(),true);
                assert forall|i:int| 0 <= i < steps.len() implies requested((#[trigger] steps[i]).work) by {
                    if i < sizes.len() { assert(steps[i] == sizes[i]); }
                    else { assert(steps[i] == places[i-sizes.len()]); }
                }
                same_view_after_edits(prior,eval,Coverage::UnchangedReads);
                full_requests_every_change(steps,old);
                edits_cover_reads(steps,old,eval);
                traversal::retained_tree_matches_full(frame.root,sizes,prior,eval,Coverage::UnchangedReads,true);
            }
        }
    }
}

pub proof fn every_prefix_matches(history: Seq<Frame>, count: nat, eval: Eval)
    requires supported(history,eval), 0 < count <= history.len(),
    ensures ({
        let prefix = history.take(count as int);
        let frames = traces(prefix,eval);
        let keys = document(history[count-1].root);
        let fresh = publish_frame(frames.last(),Map::empty(),Map::empty(),eval,true);
        emitted_view(keys,after(frames,eval).1) == emitted_view(keys,fresh)
    }),
    decreases history.len(),
{
    if count < history.len() {
        every_prefix_matches(history.drop_last(),count,eval);
        assert(history.take(count as int) =~= history.drop_last().take(count as int));
    } else {
        assert(history.take(count as int) =~= history);
        same_document_across_mixed_builds(history,eval);
    }
}
}
