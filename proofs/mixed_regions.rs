//! Rebuild several disjoint regions without replacing the intermediate cache
//! with the fresh reference. A later region may read an earlier region's
//! finalized boundary, or a preserved boundary from the input cache.

use super::cycles::{Storage, kernel::SOLVED, boundary};
use super::cycles::dfs::{self, Region};
use super::replay_history::prepare;
use super::replay_retained::{self, Edit};
use super::replay_view::{self, Replay, PlaceNode, Draw};
use vstd::prelude::*;

verus! {

pub open spec fn with_region(frame: Replay, region: Region) -> Replay {
    Replay { nodes: region, ..frame }
}

pub open spec fn includes(frame: Replay, cuts: Seq<Region>, key: int) -> bool {
    exists |i: int| 0 <= i < cuts.len() && #[trigger] with_region(frame, cuts[i]).inside(key)
}

/// Feed each cut the state left by its predecessors. Preparation inside the
/// cut uses the new declarations. No reference execution supplies results.
pub open spec fn run(frame: Replay, cuts: Seq<Region>, prior: Storage) -> Storage
    decreases cuts.len(),
{
    if cuts.len() == 0 {
        prior
    } else {
        prepare(with_region(frame, cuts.last()), run(frame, cuts.drop_last(), prior)).rebuilt_sizing()
    }
}

pub open spec fn runnable(frame: Replay, cuts: Seq<Region>, prior: Storage) -> bool
    decreases cuts.len(),
{
    if cuts.len() == 0 {
        true
    } else {
        let prefix = cuts.drop_last();
        let cut = with_region(frame, cuts.last());
        &&& runnable(frame, prefix, prior)
        &&& cut.scheduled()
        &&& forall |key: int| #[trigger] cut.inside(key) ==> !includes(frame, prefix, key)
        &&& forall |key: int| #[trigger] cut.pinned(key) ==> ({
            &&& 0 <= key < frame.n
            &&& includes(frame, prefix, key) || prior.contains_key(key) && prior[key] == frame.initial[key]
        })
    }
}

proof fn includes_last(frame: Replay, cuts: Seq<Region>, key: int)
    requires cuts.len() > 0,
    ensures includes(frame, cuts, key) ==
        (includes(frame, cuts.drop_last(), key) || with_region(frame, cuts.last()).inside(key)),
{
    let prefix = cuts.drop_last();
    let last = with_region(frame, cuts.last());
    assert(cuts[cuts.len() - 1] == cuts.last());
    if includes(frame, cuts, key) {
        let i = choose |i: int| 0 <= i < cuts.len() && #[trigger] with_region(frame, cuts[i]).inside(key);
        if i < prefix.len() {
            assert(prefix[i] == cuts[i]);
            assert(includes(frame, prefix, key));
        }
    }
    if includes(frame, prefix, key) {
        let i = choose |i: int| 0 <= i < prefix.len() && #[trigger] with_region(frame, prefix[i]).inside(key);
        assert(prefix[i] == cuts[i]);
        assert(includes(frame, cuts, key));
    }
    if last.inside(key) { assert(includes(frame, cuts, key)); }
}

proof fn fresh_keeps_seeded_boundary(frame: Replay, key: int)
    requires (frame.initial_state)(key) == SOLVED, frame.initial.contains_key(key),
    ensures
        frame.full_sizing().contains_key(key),
        frame.full_sizing()[key] == frame.initial[key],
{
    let ready = |k: int| (frame.initial_state)(k) == SOLVED;
    boundary::ready_nodes_are_not_rewritten(frame.document(), frame.edges, frame.provisional, ready, frame.gas());
    boundary::ready_value_is_retained(frame.full_events(), frame.initial, frame.eval, key);
}

proof fn prepare_preserves_an_exterior_value(cut: Replay, prior: Storage, key: int)
    requires !cut.inside(key), prior.contains_key(key),
    ensures prepare(cut, prior).cached.contains_key(key), prepare(cut, prior).cached[key] == prior[key],
{
    assert(cut.initial.dom().union(prior.dom()).contains(key));
}

proof fn prepared_cut_is_closed(cut: Replay, prior: Storage)
    requires cut.scheduled(),
        forall |key: int| #[trigger] cut.pinned(key) ==> prior.contains_key(key) && prior[key] == cut.initial[key],
    ensures prepare(cut, prior).closed(),
{
    let prepared = prepare(cut, prior);
    assert(prepared.document() == cut.document());
    assert forall |key: int, index: int| 0 <= index < (prepared.edges)(key).len() implies ({
        let input = #[trigger] (prepared.edges)(key)[index];
        &&& !prepared.inside(key) && prepared.inside(input) ==> (prepared.initial_state)(key) == SOLVED
        &&& prepared.inside(key) && !prepared.inside(input) ==> prepared.pinned(input)
    }) by {
        let input = (prepared.edges)(key)[index];
        assert(input == (cut.edges)(key)[index]);
        assert(prepared.inside(key) == cut.inside(key));
        assert(prepared.inside(input) == cut.inside(input));
    }
    assert forall |key: int| #[trigger] prepared.inside(key) implies
        (prepared.initial_state)(key) == (prepared.regional_state)(key) && prepared.initial.contains_key(key)
        by { assert(cut.inside(key)); }
    assert forall |key: int| #[trigger] prepared.pinned(key) implies prepared.initial.contains_key(key)
        by { assert(cut.pinned(key)); }
    assert(prepared.scheduled());
    assert forall |key: int| #[trigger] prepared.inside(key) implies
        prepared.cached.contains_key(key) && prepared.cached[key] == prepared.initial[key] by {
        assert(cut.inside(key));
        assert(cut.initial.dom().union(prior.dom()).contains(key));
    }
    assert forall |key: int| #[trigger] prepared.pinned(key) implies
        prepared.cached.contains_key(key) && prepared.cached[key] == prepared.initial[key] by {
        assert(cut.pinned(key));
        prepare_preserves_an_exterior_value(cut, prior, key);
    }
}

/// Sequential passes over mixed regions write the canonical words inside
/// their union and keep each outside word from the supplied cache.
pub proof fn every_region_commits_exact_words(frame: Replay, cuts: Seq<Region>, prior: Storage, key: int)
    requires runnable(frame, cuts, prior), 0 <= key < frame.n,
        forall |k: int| 0 <= k < frame.n ==> #[trigger] prior.contains_key(k),
    ensures
        run(frame, cuts, prior).contains_key(key),
        run(frame, cuts, prior)[key] ==
            if includes(frame, cuts, key) { frame.full_sizing()[key] } else { prior[key] },
    decreases cuts.len(),
{
    if cuts.len() > 0 {
        let prefix = cuts.drop_last();
        let current = run(frame, prefix, prior);
        let cut = with_region(frame, cuts.last());
        let prepared = prepare(cut, current);
        assert(cut.scheduled());
        assert forall |k: int| #[trigger] cut.pinned(k) implies
            current.contains_key(k) && current[k] == cut.initial[k] by {
            assert(0 <= k < frame.n);
            every_region_commits_exact_words(frame, prefix, prior, k);
            if includes(frame, prefix, k) {
                fresh_keeps_seeded_boundary(frame, k);
            }
        }
        prepared_cut_is_closed(cut, current);
        includes_last(frame, cuts, key);
        assert(prepared.full_sizing() == frame.full_sizing());
        if prepared.inside(key) {
            replay_view::rebuilt_producers_match_the_document(prepared, key);
        } else {
            every_region_commits_exact_words(frame, prefix, prior, key);
            prepare_preserves_an_exterior_value(cut, current, key);
            replay_view::match_region_events(prepared);
            dfs::visible_contains_only_inside(prepared.full_events(), |slot: int| prepared.inside(slot));
            boundary::ready_value_is_retained(prepared.rebuilt_events(), prepared.cached, prepared.eval, key);
        }
    }
}

/// The retained complement comes from the preceding frame. Its equality
/// follows from its unchanged rule graph and ordered reads, not from supplying
/// a cache pre-populated with the new full-build result.
pub proof fn mixed_regions_match_fresh_sizing(edit: Edit, cuts: Seq<Region>, prior: Storage, key: int)
    requires
        edit.same_shell(), edit.live(key), runnable(edit.new, cuts, prior),
        forall |k: int| 0 <= k < edit.new.n ==> #[trigger] prior.contains_key(k),
        forall |k: int| #[trigger] edit.new.inside(k) == includes(edit.new, cuts, k),
        forall |k: int| #[trigger] edit.outside(k) ==> prior[k] == edit.old.full_sizing()[k],
    ensures
        run(edit.new, cuts, prior).contains_key(key),
        run(edit.new, cuts, prior)[key] == edit.new.full_sizing()[key],
{
    every_region_commits_exact_words(edit.new, cuts, prior, key);
    if edit.outside(key) {
        replay_retained::cached_complement_matches_the_new_document(edit, key);
    }
}

pub proof fn mixed_regions_publish_fresh_view(edit: Edit, cuts: Seq<Region>, prior: Storage, nodes: Seq<PlaceNode>, draw: Draw)
    requires
        edit.same_shell(), runnable(edit.new, cuts, prior),
        forall |k: int| 0 <= k < edit.new.n ==> #[trigger] prior.contains_key(k),
        forall |k: int| #[trigger] edit.new.inside(k) == includes(edit.new, cuts, k),
        forall |k: int| #[trigger] edit.outside(k) ==> prior[k] == edit.old.full_sizing()[k],
        forall |i: int, j: int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len()
            ==> edit.live((#[trigger] nodes[i].inputs[j]).producer),
    ensures replay_view::place_frame(nodes, run(edit.new, cuts, prior), draw)
        == replay_view::place_frame(nodes, edit.new.full_sizing(), draw),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let prefix = nodes.drop_last();
        assert forall |i: int, j: int| 0 <= i < prefix.len() && 0 <= j < prefix[i].inputs.len()
            implies edit.live((#[trigger] prefix[i].inputs[j]).producer) by {
            assert(prefix[i] == nodes[i]);
        }
        mixed_regions_publish_fresh_view(edit, cuts, prior, prefix, draw);
        let node = nodes.last();
        assert(node == nodes[nodes.len() - 1]);
        let measured = run(edit.new, cuts, prior);
        assert(replay_view::words(measured, node) =~= replay_view::words(edit.new.full_sizing(), node)) by {
            assert forall |i: int| 0 <= i < node.inputs.len() implies
                #[trigger] replay_view::words(measured, node)[i] == replay_view::words(edit.new.full_sizing(), node)[i] by {
                mixed_regions_match_fresh_sizing(edit, cuts, prior, node.inputs[i].producer);
            }
        }
    }
}

}
