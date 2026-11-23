//! Carry a replay's retained data through more than one edit without importing
//! the fresh reference result into the incremental execution.
use vstd::prelude::*;
use super::cycles::Storage;
use super::replay_view::{self, Replay, PlaceNode, Draw};
use super::replay_retained::{self, Edit};

verus! {

pub open spec fn prepare(next: Replay, old: Storage) -> Replay {
    let dom = next.initial.dom().union(old.dom());
    let live = dom.filter(|k:int| (next.inside(k) && next.initial.contains_key(k))
        || (!next.inside(k) && old.contains_key(k)));
    Replay { cached:Map::new(live, |k:int| if next.inside(k) { next.initial[k] } else { old[k] }), ..next }
}

pub proof fn previous_result_prepares_the_boundary(edit:Edit, prior:Storage)
    requires edit.same_shell(),
        forall |k:int| #[trigger] edit.outside(k)
            ==> prior.contains_key(k) && prior[k] == edit.old.full_sizing()[k],
        // Only materialized slot identities can be pinned publishers. The
        // finite range uses the union of old and new identities for this edit.
        forall |k:int| #[trigger] edit.new.pinned(k) ==> edit.live(k),
    ensures ({
        let prepared = prepare(edit.new,prior);
        let runnable = Edit { new:prepared, ..edit };
        &&& runnable.same_shell() && runnable.usable_cache()
        &&& prepared.closed()
        &&& prepared.full_sizing() == edit.new.full_sizing()
    }),
{
    let next = edit.new;
    let prepared = prepare(next,prior);
    assert(next.scheduled());
    assert forall |k:int| #[trigger] prepared.inside(k) implies
        prepared.cached.contains_key(k) && prepared.cached[k] == prepared.initial[k] by {
        assert(next.inside(k));
        assert(next.initial.contains_key(k));
        assert(next.initial.dom().union(prior.dom()).contains(k));
    }
    assert forall |k:int| #[trigger] prepared.pinned(k) implies
        prepared.cached.contains_key(k) && prepared.cached[k] == prepared.initial[k] by {
        assert(next.pinned(k));
        assert(edit.live(k));
        assert(edit.outside(k));
        assert(prior.contains_key(k));
        assert(next.initial.dom().union(prior.dom()).contains(k));
        replay_retained::cached_complement_matches_the_new_document(edit,k);
        // The new schedule begins with this producer solved. It has no
        // event and its completed document words equal its seeded words.
        let ready = |i:int| (next.initial_state)(i) == super::cycles::kernel::SOLVED;
        super::cycles::boundary::ready_nodes_are_not_rewritten(
            next.document(),next.edges,next.provisional,ready,next.gas(),
        );
        assert forall |i:int| 0 <= i < next.full_events().len() implies
            (#[trigger] next.full_events()[i]).target() != k by {};
        super::cycles::boundary::ready_value_is_retained(next.full_events(),next.initial,next.eval,k);
        assert(prepared.cached[k] == prepared.initial[k]);
    }
    let runnable = Edit {new:prepared,..edit};
    assert(prepared.document() == next.document());
    assert(prepared.full_events() == next.full_events());
    assert forall |k:int,j:int| 0 <= j < (prepared.edges)(k).len() implies ({
        let dep = #[trigger] (prepared.edges)(k)[j];
        &&& !prepared.inside(k) && prepared.inside(dep)
            ==> (prepared.initial_state)(k) == super::cycles::kernel::SOLVED
        &&& prepared.inside(k) && !prepared.inside(dep) ==> prepared.pinned(dep)
    }) by {
        let dep = (prepared.edges)(k)[j];
        assert(dep == (next.edges)(k)[j]);
        assert(prepared.inside(k) == next.inside(k));
        assert(prepared.inside(dep) == next.inside(dep));
    }
    assert forall |k:int| #[trigger] prepared.inside(k) implies
        (prepared.initial_state)(k) == (prepared.regional_state)(k) && prepared.initial.contains_key(k)
        by { assert(next.inside(k)); }
    assert forall |k:int| #[trigger] prepared.pinned(k) implies prepared.initial.contains_key(k)
        by { assert(next.pinned(k)); }
    assert(prepared.scheduled());
    assert(prepared.closed());

    assert((|k:int| runnable.shell(k)) =~= (|k:int| edit.shell(k)));
    assert forall |k:int| #[trigger] runnable.outside(k) implies ({
        &&& !runnable.old.inside(k)
        &&& (runnable.old.initial_state)(k) == (runnable.new.initial_state)(k)
        &&& runnable.old.initial.contains_key(k) && runnable.new.initial.contains_key(k)
        &&& runnable.old.initial[k] == runnable.new.initial[k]
    }) by { assert(edit.outside(k)); }
    assert forall |k:int| #[trigger] runnable.shell(k) implies ({
        &&& (runnable.old.edges)(k) == (runnable.new.edges)(k)
        &&& (runnable.old.provisional)(k) == (runnable.new.provisional)(k)
        &&& forall |args:Seq<Seq<u32>>| #[trigger] (runnable.old.eval)(k,args) == (runnable.new.eval)(k,args)
    }) by { assert(edit.shell(k)); }
    assert forall |k:int| #[trigger] runnable.old.inside(k) == runnable.new.inside(k)
        by { assert(edit.old.inside(k) == edit.new.inside(k)); }
    assert(runnable.same_shell());
    assert forall |k:int| #[trigger] runnable.outside(k) implies
        runnable.new.cached.contains_key(k) &&
            runnable.new.cached[k] == runnable.old.full_sizing()[k] by {
        assert(edit.outside(k));
        assert(!next.inside(k));
        assert(prior.contains_key(k));
        replay_retained::cached_complement_matches_the_new_document(edit,k);
        assert(next.initial.dom().union(prior.dom()).contains(k));
    }
    assert(runnable.usable_cache());
}

pub open spec fn measured(history: Seq<Replay>) -> Storage
    decreases history.len(),
{
    if history.len() == 0 { Map::empty() }
    else if history.len() == 1 { history.last().full_sizing() }
    else { prepare(history.last(), measured(history.drop_last())).rebuilt_sizing() }
}

/// The previous full execution has no region. Project it onto the current
/// edit's cut when comparing the old and new retained complement. The region
/// used for the preceding incremental execution can be entirely different.
pub open spec fn transition(previous:Replay, next:Replay) -> Edit {
    let old = Replay {
        owner:next.owner,
        nodes:next.nodes,
        regional_state:previous.initial_state,
        ..previous
    };
    Edit { old, new:next }
}

pub open spec fn supported(history: Seq<Replay>) -> bool
    decreases history.len(),
{
    if history.len() == 0 { true }
    else {
        let next = history.last();
        let prefix = history.drop_last();
        &&& next.scheduled()
        &&& forall |k:int| 0 <= k < next.n ==> #[trigger] next.initial.contains_key(k)
        &&& forall |k:int| #[trigger] next.pinned(k) ==> 0 <= k < next.n
        &&& supported(prefix)
        &&& prefix.len() > 0 ==> transition(prefix.last(),next).same_shell()
    }
}

proof fn full_preserves_materialized_slots(r:Replay, events:Seq<super::cycles::Event>, k:int)
    requires r.initial.contains_key(k),
    ensures super::cycles::replay(events,r.initial,r.eval).contains_key(k),
    decreases events.len(),
{
    if events.len() > 0 { full_preserves_materialized_slots(r,events.drop_last(),k); }
}

pub proof fn every_producer_after_edits_is_exact(history:Seq<Replay>, k:int)
    requires supported(history), history.len() > 0, 0 <= k < history.last().n,
    ensures measured(history).contains_key(k) && history.last().full_sizing().contains_key(k),
        measured(history)[k] == history.last().full_sizing()[k],
    decreases history.len(),
{
    let next = history.last();
    if history.len() == 1 { full_preserves_materialized_slots(next,next.full_events(),k); }
    else {
        let prefix = history.drop_last();
        let edit = transition(prefix.last(),next);
        let prior = measured(prefix);
        assert(edit.old.full_sizing() == prefix.last().full_sizing());
        assert forall |i:int| #[trigger] edit.outside(i) implies
            prior.contains_key(i) && prior[i] == edit.old.full_sizing()[i] by {
            every_producer_after_edits_is_exact(prefix,i);
        }
        previous_result_prepares_the_boundary(edit,prior);
        let prepared = prepare(next,prior);
        replay_retained::edited_document_producer_is_exact(Edit {new:prepared,..edit},k);
    }
}

/// The engine retains the results of earlier frames. The canonical reference
/// starts anew on this frame. Every consumer of a live slot receives the
/// reference words, so every published absolute and local rectangle agrees.
pub proof fn retained_history_matches_the_fresh_view(history:Seq<Replay>, nodes:Seq<PlaceNode>, draw:Draw)
    requires supported(history), history.len() > 0,
        forall |i:int,j:int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len()
            ==> 0 <= (#[trigger] nodes[i].inputs[j]).producer < history.last().n,
    ensures replay_view::place_frame(nodes,measured(history),draw)
        == replay_view::place_frame(nodes,history.last().full_sizing(),draw),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let prior = nodes.drop_last();
        assert forall |i:int,j:int| 0 <= i < prior.len() && 0 <= j < prior[i].inputs.len() implies
            0 <= (#[trigger] prior[i].inputs[j]).producer < history.last().n by { assert(prior[i] == nodes[i]); }
        retained_history_matches_the_fresh_view(history,prior,draw);
        let node = nodes.last();
        assert(node == nodes[nodes.len()-1]);
        let incr = measured(history);
        let full = history.last().full_sizing();
        assert(replay_view::words(incr,node) =~= replay_view::words(full,node)) by {
            assert forall |i:int| 0 <= i < node.inputs.len() implies
                replay_view::words(incr,node)[i] == replay_view::words(full,node)[i] by {
                every_producer_after_edits_is_exact(history,node.inputs[i].producer);
            }
        }
    }
}


pub proof fn every_edit_prefix_publishes_in_document_order(
    history:Seq<Replay>, count:nat, nodes:Seq<PlaceNode>, draw:Draw,
)
    requires supported(history), 0 < count <= history.len(),
        forall |i:int,j:int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len()
            ==> 0 <= (#[trigger] nodes[i].inputs[j]).producer < history[count-1].n,
    ensures ({
        let prefix = history.take(count as int);
        let incr = replay_view::place_frame(nodes,measured(prefix),draw);
        let full = replay_view::place_frame(nodes,history[count-1].full_sizing(),draw);
        replay_view::ordered_view(nodes,incr) == replay_view::ordered_view(nodes,full)
    }),
    decreases history.len(),
{
    if count < history.len() {
        every_edit_prefix_publishes_in_document_order(history.drop_last(),count,nodes,draw);
        assert(history.take(count as int) =~= history.drop_last().take(count as int));
    } else {
        assert(history.take(count as int) =~= history);
        assert(history.last() == history[count-1]);
        retained_history_matches_the_fresh_view(history,nodes,draw);
    }
}

}
