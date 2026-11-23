//! Choose an enclosing cut before starting any replay. An unresolved reader
//! cannot enter a smaller region, and a regional reader cannot pull a
//! provisional or uninitialized value from an unresolved external producer.
use vstd::prelude::*;
use super::cycles;
use super::cycles::dfs::{self, Edges};
use super::replay_prefix::{self, RootPrefix};
use super::replay_view::{self, Replay};
use super::regions::{self, Interval};

verus! {

pub struct ProducerGraph {
    pub edges: Edges,
    pub owner: spec_fn(int) -> int,
    pub state: spec_fn(int) -> u32,
    pub slots: nat,
}

impl ProducerGraph {
    pub open spec fn well_formed(self) -> bool {
        &&& forall |slot:int| !(0 <= slot < self.slots) ==> (#[trigger] (self.edges)(slot)).len() == 0
        &&& forall |slot:int,j:int| 0 <= j < (self.edges)(slot).len() ==>
            0 <= #[trigger] (self.edges)(slot)[j] < self.slots
    }

    pub open spec fn inside(self, nodes: ISet<int>, slot: int) -> bool { nodes.contains((self.owner)(slot)) }

    /// A crossing can be omitted from replay only when its exterior endpoint
    /// is ready. Both directions are needed because the first call into a
    /// cycle determines which reads observe provisional words.
    pub open spec fn allows(self, nodes: ISet<int>, reader: int, input: int) -> bool {
        let from = self.inside(nodes, reader);
        let to = self.inside(nodes, input);
        &&& !from && to ==> (self.state)(reader) == cycles::kernel::SOLVED
        &&& from && !to ==> (self.state)(input) == cycles::kernel::SOLVED
    }

    pub open spec fn closed(self, nodes: ISet<int>) -> bool {
        forall |reader:int,j:int| 0 <= j < (self.edges)(reader).len() ==>
            self.allows(nodes, reader, #[trigger] (self.edges)(reader)[j])
    }
}

/// Consecutive candidates are the proposed region and its enclosing
/// subtrees. The last includes every slot owner, so the search terminates
/// even when every proper subregion cuts a live dependency.
pub open spec fn enclosing(graph: ProducerGraph, candidates: Seq<ISet<int>>) -> bool {
    &&& candidates.len() > 0
    &&& forall |i:int| 0 <= i && i + 1 < candidates.len() ==>
        (#[trigger] candidates[i]).subset_of(candidates[i + 1])
    &&& forall |slot:int| 0 <= slot < graph.slots ==>
        candidates.last().contains(#[trigger] (graph.owner)(slot))
}

pub open spec fn first_closed(graph: ProducerGraph, candidates: Seq<ISet<int>>, from: nat) -> nat
    decreases candidates.len() - from,
{
    if from + 1 >= candidates.len() || graph.closed(candidates[from as int]) { from }
    else { first_closed(graph, candidates, from + 1) }
}

pub proof fn whole_graph_is_closed(graph: ProducerGraph, nodes: ISet<int>)
    requires graph.well_formed(), forall |slot:int| 0 <= slot < graph.slots ==>
        nodes.contains(#[trigger] (graph.owner)(slot)),
    ensures graph.closed(nodes),
{
    assert forall |reader:int,j:int| 0 <= j < (graph.edges)(reader).len() implies
        graph.allows(nodes, reader, #[trigger] (graph.edges)(reader)[j]) by {
        assert(0 <= reader < graph.slots);
        assert(0 <= (graph.edges)(reader)[j] < graph.slots);
        assert(graph.inside(nodes, reader) && graph.inside(nodes, (graph.edges)(reader)[j]));
    }
}

/// Rejection identifies a real position in an ordered dependency list and
/// the exterior slot that must be included or proved ready.
pub proof fn rejected_cut_identifies_a_crossing(graph: ProducerGraph, nodes: ISet<int>) -> (witness: (int, int, int))
    requires graph.well_formed(), !graph.closed(nodes),
    ensures ({
        let (reader, index, outside) = witness;
        let input = (graph.edges)(reader)[index];
        &&& 0 <= reader < graph.slots
        &&& 0 <= index < (graph.edges)(reader).len()
        &&& !graph.allows(nodes, reader, input)
        &&& !graph.inside(nodes, outside) && (graph.state)(outside) != cycles::kernel::SOLVED
        &&& outside == reader || outside == input
    }),
{
    let (reader, index) = choose |reader:int,index:int| 0 <= index < (graph.edges)(reader).len()
        && !graph.allows(nodes, reader, #[trigger] (graph.edges)(reader)[index]);
    let input = (graph.edges)(reader)[index];
    let outside = if graph.inside(nodes, reader) { input } else { reader };
    assert(0 <= reader < graph.slots);
    (reader, index, outside)
}

/// Compute the smallest accepted ancestor in the supplied chain. The result
/// contains every dirty owner of the original cut, and each discarded cut has
/// a real crossing that would use an unresolved exterior slot.
pub proof fn widen_before_replaying(graph: ProducerGraph, candidates: Seq<ISet<int>>, from: nat)
    requires graph.well_formed(), enclosing(graph, candidates), from < candidates.len(),
    ensures ({
        let winner = first_closed(graph, candidates, from);
        &&& from <= winner < candidates.len()
        &&& graph.closed(candidates[winner as int])
        &&& candidates[from as int].subset_of(candidates[winner as int])
        &&& forall |i:int| from <= i < winner ==> !graph.closed(#[trigger] candidates[i])
    }),
    decreases candidates.len() - from,
{
    if from + 1 == candidates.len() {
        assert(candidates[from as int] == candidates.last());
        whole_graph_is_closed(graph, candidates.last());
    } else if !graph.closed(candidates[from as int]) {
        widen_before_replaying(graph, candidates, from + 1);
        let winner = first_closed(graph, candidates, from);
        assert(candidates[from as int].subset_of(candidates[(from + 1) as int]));
        assert forall |i:int| from <= i < winner implies !graph.closed(#[trigger] candidates[i]) by {};
        assert(candidates[from as int].subset_of(candidates[winner as int]));
    }
}

impl Replay {
    pub open spec fn producer_graph(self) -> ProducerGraph {
        ProducerGraph { edges: self.edges, owner: self.owner, state: self.initial_state, slots: self.n }
    }
}

pub open spec fn ready_in_canonical_prefix(cut: RootPrefix, key: int) -> bool {
    (cut.document.initial_state)(key) == cycles::kernel::SOLVED ||
        exists |i:int| #[trigger] replay_prefix::finished_at(cut.settled().events, key, i)
}

/// The runtime facts needed for a crossing are an exact preparation fact or
/// an observed completion in a canonical prefix. This excludes old solved
/// flags by construction and leaves the cache-word agreement to preparation.
pub proof fn canonical_prefix_justifies_crossing(cut: RootPrefix, nodes: ISet<int>, reader: int, input: int)
    ensures ({
        let graph = cut.resume(cut.document.cached).producer_graph();
        let from = graph.inside(nodes, reader);
        let to = graph.inside(nodes, input);
        graph.allows(nodes, reader, input) == (
            (!from && to ==> ready_in_canonical_prefix(cut, reader)) &&
            (from && !to ==> ready_in_canonical_prefix(cut, input)))
    }),
{
    replay_prefix::canonical_ready_has_exact_origin(cut, reader);
    replay_prefix::canonical_ready_has_exact_origin(cut, input);
}

/// After widening, preparation and previously committed words discharge the
/// remaining cache premises. The chosen cut then has the same ordered slot
/// events and computed bundles as the canonical run.
pub proof fn accepted_cut_replays_the_ordered_graph(replay: Replay, cut: ISet<int>, key: int)
    requires replay.producer_graph().closed(cut),
        forall |node:int| #[trigger] (replay.nodes)(node) == cut.contains(node),
        dfs::bounded(replay.document(), replay.edges, replay.n), replay.inside(key),
        forall |i:int| 0 <= i < replay.visits.len() ==> (#[trigger] replay.visits[i]).owned_by(replay.owner),
        forall |k:int| #[trigger] replay.inside(k) ==> ({
            &&& (replay.initial_state)(k) == (replay.regional_state)(k)
            &&& replay.initial.contains_key(k) && replay.cached.contains_key(k)
            &&& replay.initial[k] == replay.cached[k]
        }),
        forall |k:int| #[trigger] replay.pinned(k) ==> ({
            &&& replay.initial.contains_key(k) && replay.cached.contains_key(k)
            &&& replay.initial[k] == replay.cached[k]
        }),
    ensures replay.closed(),
        replay.rebuilt_events() == dfs::visible(replay.full_events(), |k:int| replay.inside(k)),
        replay.rebuilt_sizing()[key] == replay.full_sizing()[key],
{
    let graph = replay.producer_graph();
    assert(graph.closed(cut));
    assert(graph.edges == replay.edges);
    assert forall |reader:int,j:int| 0 <= j < (replay.edges)(reader).len() implies
        graph.allows(cut, reader, #[trigger] (replay.edges)(reader)[j]) by {
        assert(0 <= j < (graph.edges)(reader).len());
        let dep = (graph.edges)(reader)[j];
        assert(dep == (replay.edges)(reader)[j]);
    }
    assert forall |k:int,j:int| 0 <= j < (replay.edges)(k).len() implies ({
        let d = #[trigger] (replay.edges)(k)[j];
        &&& !replay.inside(k) && replay.inside(d) ==> (replay.initial_state)(k) == cycles::kernel::SOLVED
        &&& replay.inside(k) && !replay.inside(d) ==> replay.pinned(d)
    }) by {
        let d = (replay.edges)(k)[j];
        assert(graph.allows(cut, k, d));
        assert(graph.inside(cut, k) == replay.inside(k));
        assert(graph.inside(cut, d) == replay.inside(d));
    }
    replay_view::rebuilt_producers_match_the_document(replay, key);
}

pub open spec fn separated(a: Interval, b: Interval) -> bool { a.1 <= b.0 || b.1 <= a.0 }

pub open spec fn contains_region(a: Interval, b: Interval) -> bool { a.0 <= b.0 && b.1 <= a.1 }

pub open spec fn nodes_in(range: Interval) -> ISet<int> {
    ISet::new(|node:int| range.0 <= node < range.1)
}

pub open spec fn covers(plan: Seq<Interval>, pos: nat) -> bool {
    exists |i:int| 0 <= i < plan.len() && regions::within(#[trigger] plan[i], pos)
}

/// Subtree intervals are disjoint or nested. Insert the accepted ancestor and
/// remove every covered interval in one update, preserving the other cuts.
pub open spec fn replace_covered(plan: Seq<Interval>, wider: Interval) -> Seq<Interval>
    decreases plan.len(),
{
    if plan.len() == 0 {
        seq![wider]
    } else {
        let first = plan.first();
        let tail = plan.drop_first();
        if first.1 <= wider.0 { seq![first] + replace_covered(tail, wider) }
        else if wider.1 <= first.0 { seq![wider] + plan }
        else { replace_covered(tail, wider) }
    }
}

proof fn head_membership(head: Interval, tail: Seq<Interval>, region: Interval)
    ensures (seq![head] + tail).contains(region) == (head == region || tail.contains(region)),
{
    let all = seq![head] + tail;
    if all.contains(region) {
        let i = choose |i:int| 0 <= i < all.len() && #[trigger] all[i] == region;
        if i > 0 { assert(tail[i - 1] == region); }
    }
    if tail.contains(region) {
        let i = choose |i:int| 0 <= i < tail.len() && #[trigger] tail[i] == region;
        assert(all[i + 1] == region);
    }
    assert(all[0] == head);
}

proof fn prepend_ordered(first: Interval, tail: Seq<Interval>, low: nat, high: nat)
    requires regions::ordered(tail, low, high), low <= first.0 < first.1 <= high,
        forall |i:int| 0 <= i < tail.len() ==> first.1 <= (#[trigger] tail[i]).0,
    ensures regions::ordered(seq![first] + tail, low, high),
{
    let all = seq![first] + tail;
    assert forall |i:int| 0 <= i < all.len() implies ({
        let r = #[trigger] all[i]; low <= r.0 < r.1 <= high
    }) by { if i > 0 { assert(all[i] == tail[i - 1]); } }
    assert forall |i:int,j:int| 0 <= i < j < all.len() implies
        (#[trigger] all[i]).1 <= (#[trigger] all[j]).0 by {
        assert(all[j] == tail[j - 1]);
        if i > 0 { assert(all[i] == tail[i - 1]); }
    }
}

proof fn replacement_preserves_partition(plan: Seq<Interval>, wider: Interval, low: nat, high: nat)
    requires regions::ordered(plan, low, high), low <= wider.0 < wider.1 <= high,
        forall |i:int| 0 <= i < plan.len() ==> ({
            let old = #[trigger] plan[i]; separated(old, wider) || contains_region(wider, old)
        }),
    ensures regions::ordered(replace_covered(plan, wider), low, high),
        forall |r:Interval| #[trigger] replace_covered(plan, wider).contains(r) ==
            (r == wider || plan.contains(r) && separated(r, wider)),
    decreases plan.len(),
{
    let result = replace_covered(plan, wider);
    if plan.len() == 0 {
        assert(result =~= seq![wider]);
        assert(result =~= seq![wider] + plan);
        assert forall |r:Interval| #[trigger] result.contains(r) ==
            (r == wider || plan.contains(r) && separated(r, wider)) by {
            head_membership(wider, plan, r);
            assert(!plan.contains(r));
        }
    } else {
        let first = plan[0];
        let tail = plan.drop_first();
        assert(plan =~= seq![first] + tail);
        assert(regions::ordered(tail, low, high)) by {
            assert forall |i:int| 0 <= i < tail.len() implies ({
                let r = #[trigger] tail[i]; low <= r.0 < r.1 <= high
            }) by { assert(tail[i] == plan[i + 1]); }
            assert forall |i:int,j:int| 0 <= i < j < tail.len() implies
                (#[trigger] tail[i]).1 <= (#[trigger] tail[j]).0 by {
                assert(tail[i] == plan[i + 1] && tail[j] == plan[j + 1]);
            }
        }
        assert forall |i:int| 0 <= i < tail.len() implies ({
            let r = #[trigger] tail[i]; separated(r, wider) || contains_region(wider, r)
        }) by { assert(tail[i] == plan[i + 1]); }
        if wider.1 <= first.0 {
            assert forall |i:int| 0 <= i < plan.len() implies wider.1 <= (#[trigger] plan[i]).0 by {
                if i > 0 { assert(first.1 <= plan[i].0); }
            }
            prepend_ordered(wider, plan, low, high);
            assert forall |r:Interval| #[trigger] result.contains(r) ==
                (r == wider || plan.contains(r) && separated(r, wider)) by {
                head_membership(wider, plan, r);
                if plan.contains(r) {
                    let i = choose |i:int| 0 <= i < plan.len() && #[trigger] plan[i] == r;
                    assert(wider.1 <= plan[i].0);
                }
            }
        } else {
            replacement_preserves_partition(tail, wider, low, high);
            let replaced_tail = replace_covered(tail, wider);
            if first.1 <= wider.0 {
                assert forall |i:int| 0 <= i < replaced_tail.len() implies first.1 <= (#[trigger] replaced_tail[i]).0 by {
                    let r = replaced_tail[i];
                    assert(replaced_tail.contains(r));
                    if r != wider {
                        let j = choose |j:int| 0 <= j < tail.len() && #[trigger] tail[j] == r;
                        assert(tail[j] == plan[j + 1]);
                    }
                }
                prepend_ordered(first, replaced_tail, low, high);
            }
            assert forall |r:Interval| #[trigger] result.contains(r) ==
                (r == wider || plan.contains(r) && separated(r, wider)) by {
                head_membership(first, tail, r);
                if first.1 <= wider.0 { head_membership(first, replaced_tail, r); }
            }
        }
    }
}

/// The chosen ancestor can absorb other requested regions in any position
/// of the partition. All surviving regions must satisfy the same canonical
/// edge check, using flags valid for their replay phase.
pub proof fn widening_an_ordered_partition_preserves_admissibility(
    graph: ProducerGraph, plan: Seq<Interval>, selected: int, wider: Interval, low: nat, high: nat,
)
    requires regions::ordered(plan, low, high), 0 <= selected < plan.len(),
        low <= wider.0 < wider.1 <= high, contains_region(wider, plan[selected]),
        graph.closed(nodes_in(wider)),
        forall |i:int| 0 <= i < plan.len() ==> ({
            let r = #[trigger] plan[i];
            &&& separated(r, wider) || contains_region(wider, r) || contains_region(r, wider)
            &&& separated(r, wider) ==> graph.closed(nodes_in(r))
        }),
    ensures regions::ordered(replace_covered(plan, wider), low, high),
        forall |r:Interval| #[trigger] replace_covered(plan, wider).contains(r) ==
            (r == wider || plan.contains(r) && separated(r, wider)),
        forall |r:Interval| #[trigger] replace_covered(plan, wider).contains(r) ==> graph.closed(nodes_in(r)),
        forall |pos:nat| #[trigger] covers(replace_covered(plan, wider), pos) ==
            (covers(plan, pos) || regions::within(wider, pos)),
{
    assert forall |i:int| 0 <= i < plan.len() implies ({
        let r = #[trigger] plan[i]; separated(r, wider) || contains_region(wider, r)
    }) by {
        let r = plan[i];
        if contains_region(r, wider) {
            let inner = plan[selected];
            if i < selected { assert(r.1 <= inner.0); }
            else if selected < i { assert(inner.1 <= r.0); }
            assert(i == selected);
        }
    }
    replacement_preserves_partition(plan, wider, low, high);
    assert forall |r:Interval| #[trigger] replace_covered(plan, wider).contains(r) implies
        graph.closed(nodes_in(r)) by {
        if r != wider {
            let i = choose |i:int| 0 <= i < plan.len() && #[trigger] plan[i] == r;
            assert(graph.closed(nodes_in(plan[i])));
        }
    }
    let widened = replace_covered(plan, wider);
    assert forall |pos:nat| #[trigger] covers(widened, pos) == (covers(plan, pos) || regions::within(wider, pos)) by {
        if covers(widened, pos) {
            let index = choose |i:int| 0 <= i < widened.len() && regions::within(#[trigger] widened[i], pos);
            let r = widened[index];
            assert(widened.contains(r));
            if r != wider {
                let k = choose |i:int| 0 <= i < plan.len() && #[trigger] plan[i] == r;
                assert(regions::within(plan[k], pos));
                assert(covers(plan, pos));
            }
        }
        if covers(plan, pos) && !regions::within(wider, pos) {
            let index = choose |i:int| 0 <= i < plan.len() && regions::within(#[trigger] plan[i], pos);
            let r = plan[index];
            assert(separated(r, wider));
            assert(plan.contains(r));
            assert(widened.contains(r));
            let k = choose |i:int| 0 <= i < widened.len() && #[trigger] widened[i] == r;
            assert(regions::within(widened[k], pos));
            assert(covers(widened, pos));
        } else if regions::within(wider, pos) {
            assert(widened.contains(wider));
            let k = choose |i:int| 0 <= i < widened.len() && #[trigger] widened[i] == wider;
            assert(regions::within(widened[k], pos));
            assert(covers(widened, pos));
        }
    }
}

}
