//! Use the cyclic replay theorem even when the host keeps skipped rectangles.
use vstd::prelude::*;
use super::{Key, Geometry, Work, writes, requested, valid_route, requested_work_is_executed};
use super::cycles::Storage;
use super::replay_view::{self, Draw, Replay, PlaceNode, Placements};
use super::replay_history;
use super::retained_view::{self, Outputs};

verus! {

pub open spec fn local_input_matches(a: replay_view::PlacedRecord, b: replay_view::PlacedRecord) -> bool {
    a.local == b.local && a.measured == b.measured && a.inherited == b.inherited
}

pub open spec fn sound(placements: Placements, draw: Draw) -> bool {
    forall |k:Key| #[trigger] placements.contains_key(k) ==> ({
        let item = placements[k];
        item.result == draw(k,item.local,item.measured,item.inherited)
    })
}

pub open spec fn retained_outputs_are_sound(placements:Placements, host:Outputs) -> bool {
    forall |k:Key| #[trigger] placements.contains_key(k)
        ==> host.contains_key(k) && host[k] == placements[k].result.output
}

pub open spec fn placed_keys(nodes:Seq<PlaceNode>) -> Set<Key>
    decreases nodes.len(),
{
    if nodes.len() == 0 { Set::empty() } else { placed_keys(nodes.drop_last()).insert(nodes.last().key) }
}

proof fn node_key_is_placed(nodes:Seq<PlaceNode>, i:int)
    requires 0 <= i < nodes.len(),
    ensures placed_keys(nodes).contains(nodes[i].key),
    decreases nodes.len(),
{
    if i < nodes.len()-1 {
        node_key_is_placed(nodes.drop_last(),i);
        assert(nodes.drop_last()[i] == nodes[i]);
    } else { assert(nodes.last() == nodes[i]); }
}

pub proof fn canonical_records_are_sound(nodes:Seq<PlaceNode>, source:Storage, draw:Draw)
    ensures sound(replay_view::place_frame(nodes,source,draw),draw),
        replay_view::place_frame(nodes,source,draw).dom() == placed_keys(nodes),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let before = nodes.drop_last();
        let node = nodes.last();
        canonical_records_are_sound(before,source,draw);
        assert(replay_view::place_frame(nodes,source,draw).dom() =~= placed_keys(nodes));
    } else {
        assert(placed_keys(nodes) =~= Set::empty());
    }
}

/// A retained host starts with the previous output and receives the current
/// placement callbacks. Skipping a write leaves that entry physically intact.
pub open spec fn commit(nodes:Seq<PlaceNode>, measured:Storage, draw:Draw,
    plan:spec_fn(Key) -> Work, host:Outputs) -> Outputs
    decreases nodes.len(),
{
    if nodes.len() == 0 { host } else {
        let prefix = commit(nodes.drop_last(),measured,draw,plan,host);
        let k = nodes.last().key;
        if writes(plan(k)) { prefix.insert(k,replay_view::place_frame(nodes,measured,draw)[k].result.output) }
        else { prefix }
    }
}

proof fn omitted_record_stays_unchanged(nodes:Seq<PlaceNode>, measured:Storage, draw:Draw,
    plan:spec_fn(Key) -> Work, host:Outputs, key:Key)
    requires !writes(plan(key)),
    ensures commit(nodes,measured,draw,plan,host).contains_key(key) == host.contains_key(key),
        host.contains_key(key) ==> commit(nodes,measured,draw,plan,host)[key] == host[key],
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        omitted_record_stays_unchanged(nodes.drop_last(),measured,draw,plan,host,key);
    }
}

/// Each skipped record has exactly the same local declarations, measured
/// words and inherited frames as before. Each requested write reaches the host
/// by the production placement marks. No equality of rendered bits is assumed.
pub proof fn mixed_history_can_skip_unchanged_output(
    history:Seq<Replay>, nodes:Seq<PlaceNode>, draw:Draw, plan:spec_fn(Key) -> Work,
    previous:Placements, host:Outputs,
)
    requires
        replay_history::supported(history), history.len() > 0,
        forall |i:int,j:int| 0 <= i < j < nodes.len()
            ==> (#[trigger] nodes[i]).key != (#[trigger] nodes[j]).key,
        sound(previous,draw), retained_outputs_are_sound(previous,host),
        forall |i:int,j:int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len()
            ==> 0 <= (#[trigger] nodes[i].inputs[j]).producer < history.last().n,
        forall |i:int| 0 <= i < nodes.len() ==> ({
            let k = (#[trigger] nodes[i]).key;
            let now = replay_view::place_frame(nodes,history.last().full_sizing(),draw);
            &&& valid_route(plan(k))
            &&& !requested(plan(k)) ==> previous.contains_key(k) && local_input_matches(previous[k],now[k])
        }),
    ensures ({
        let after = commit(nodes,replay_history::measured(history),draw,plan,host);
        let fresh = replay_view::place_frame(nodes,history.last().full_sizing(),draw);
        &&& retained_outputs_are_sound(fresh,after)
        &&& retained_view::emitted_view(Seq::new(nodes.len(),|i:int| nodes[i].key),after)
            == replay_view::ordered_view(nodes,fresh)
    }),
    decreases nodes.len(),
{
    let incremental = replay_history::measured(history);
    let full = history.last().full_sizing();
    let fresh = replay_view::place_frame(nodes,full,draw);
    let output = commit(nodes,incremental,draw,plan,host);
    canonical_records_are_sound(nodes,full,draw);
    replay_history::retained_history_matches_the_fresh_view(history,nodes,draw);
    if nodes.len() > 0 {
        let prefix = nodes.drop_last();
        let current = nodes.last().key;
        assert(nodes.last() == nodes[nodes.len()-1]);
        let prior = replay_view::place_frame(prefix,full,draw);
        canonical_records_are_sound(prefix,full,draw);
        assert forall |i:int,j:int| 0 <= i < prefix.len() && 0 <= j < prefix[i].inputs.len() implies
            0 <= (#[trigger] prefix[i].inputs[j]).producer < history.last().n by { assert(prefix[i] == nodes[i]); }
        assert forall |i:int,j:int| 0 <= i < j < prefix.len()
            implies (#[trigger] prefix[i]).key != (#[trigger] prefix[j]).key by {
            assert(prefix[i] == nodes[i] && prefix[j] == nodes[j]);
        }
        assert forall |i:int| 0 <= i < prefix.len() implies ({
            let k = (#[trigger] prefix[i]).key;
            &&& valid_route(plan(k))
            &&& !requested(plan(k)) ==> previous.contains_key(k) && local_input_matches(previous[k],prior[k])
        }) by {
            assert(prefix[i] == nodes[i]);
            assert(prefix[i].key != current);
        }
        mixed_history_can_skip_unchanged_output(history,prefix,draw,plan,previous,host);
        requested_work_is_executed(plan(current));
        if !writes(plan(current)) {
            omitted_record_stays_unchanged(nodes,incremental,draw,plan,host,current);
            assert(previous.contains_key(current));
            assert(host[current] == fresh[current].result.output);
        }
        assert forall |k:Key| #[trigger] fresh.contains_key(k) implies
            output.contains_key(k) && output[k] == fresh[k].result.output by {
            if k != current { assert(prior.contains_key(k)); }
        }
    }
    let order = Seq::new(nodes.len(),|i:int| nodes[i].key);
    assert(retained_view::emitted_view(order,output) =~= replay_view::ordered_view(nodes,fresh)) by {
        assert forall |i:int| 0 <= i < order.len()
            implies output[#[trigger] order[i]] == fresh[order[i]].result.output by {
            node_key_is_placed(nodes,i);
            assert(order[i] == nodes[i].key);
            assert(fresh.contains_key(order[i]));
        }
    }
}

pub struct Frame {
    pub nodes:Seq<PlaceNode>,
    pub plan:spec_fn(Key) -> Work,
}

pub open spec fn canonical(frame:Frame, sizing:Replay, draw:Draw) -> Placements {
    replay_view::place_frame(frame.nodes,sizing.full_sizing(),draw)
}

pub open spec fn planned(history:Seq<Replay>, frames:Seq<Frame>, draw:Draw) -> bool
    decreases frames.len(),
{
    &&& frames.len() == history.len()
    &&& if frames.len() == 0 { true } else {
        let f = frames.last();
        let r = history.last();
        let now = canonical(f,r,draw);
        let previous = if frames.len() > 1 {
            canonical(frames.drop_last().last(),history.drop_last().last(),draw)
        } else { Map::empty() };
        &&& planned(history.drop_last(),frames.drop_last(),draw)
        &&& forall |i:int,j:int| 0 <= i < j < f.nodes.len()
            ==> (#[trigger] f.nodes[i]).key != (#[trigger] f.nodes[j]).key
        &&& forall |i:int,j:int| 0 <= i < f.nodes.len() && 0 <= j < f.nodes[i].inputs.len()
            ==> 0 <= (#[trigger] f.nodes[i].inputs[j]).producer < r.n
        &&& forall |i:int| 0 <= i < f.nodes.len() ==> ({
            let k = (#[trigger] f.nodes[i]).key;
            &&& valid_route((f.plan)(k))
            &&& !requested((f.plan)(k)) ==> previous.contains_key(k) && local_input_matches(previous[k],now[k])
        })
    }
}

pub open spec fn publish(history:Seq<Replay>, frames:Seq<Frame>, draw:Draw) -> Outputs
    decreases frames.len(),
{
    if frames.len() == 0 { Map::empty() } else {
        let f = frames.last();
        let old = publish(history.drop_last(),frames.drop_last(),draw);
        commit(f.nodes,replay_history::measured(history),draw,f.plan,old)
    }
}

/// A normal retained host receives only requested updates. Its earlier
/// outputs are the consequence of the preceding incremental execution.
pub proof fn successive_edits_publish_the_full_view(history:Seq<Replay>, frames:Seq<Frame>, draw:Draw)
    requires replay_history::supported(history), planned(history,frames,draw), frames.len() > 0,
    ensures ({
        let f = frames.last();
        let fresh = canonical(f,history.last(),draw);
        let host = publish(history,frames,draw);
        &&& retained_outputs_are_sound(fresh,host)
        &&& retained_view::emitted_view(Seq::new(f.nodes.len(),|i:int| f.nodes[i].key),host)
            == replay_view::ordered_view(f.nodes,fresh)
    }),
    decreases frames.len(),
{
    let old_frames = frames.drop_last();
    let old_history = history.drop_last();
    let old_host = publish(old_history,old_frames,draw);
    let previous = if old_frames.len() == 0 { Map::empty() } else {
        canonical(old_frames.last(),old_history.last(),draw)
    };
    if old_frames.len() > 0 {
        successive_edits_publish_the_full_view(old_history,old_frames,draw);
        canonical_records_are_sound(old_frames.last().nodes,old_history.last().full_sizing(),draw);
    }
    let f = frames.last();
    mixed_history_can_skip_unchanged_output(history,f.nodes,draw,f.plan,previous,old_host);
}

pub proof fn every_retained_prefix_publishes_the_full_view(
    history:Seq<Replay>, frames:Seq<Frame>, count:nat, draw:Draw,
)
    requires replay_history::supported(history), planned(history,frames,draw), 0 < count <= frames.len(),
    ensures ({
        let f = frames[count-1];
        let reference = canonical(f,history[count-1],draw);
        let host = publish(history.take(count as int),frames.take(count as int),draw);
        &&& retained_outputs_are_sound(reference,host)
        &&& retained_view::emitted_view(Seq::new(f.nodes.len(),|i:int| f.nodes[i].key),host)
            == replay_view::ordered_view(f.nodes,reference)
    }),
    decreases frames.len(),
{
    if count == frames.len() {
        assert(history.take(count as int) =~= history);
        assert(frames.take(count as int) =~= frames);
        assert(history[count-1] == history.last() && frames[count-1] == frames.last());
        successive_edits_publish_the_full_view(history,frames,draw);
    } else {
        let prior_history = history.drop_last();
        let prior_frames = frames.drop_last();
        every_retained_prefix_publishes_the_full_view(prior_history,prior_frames,count,draw);
        assert(history.take(count as int) =~= prior_history.take(count as int));
        assert(frames.take(count as int) =~= prior_frames.take(count as int));
    }
}

}
