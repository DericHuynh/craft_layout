//! The old layout's retained boundary is derived from an unchanged exterior
//! program evaluated in the same canonical order before either region runs.
use vstd::prelude::*;
use super::cycles::{Compute, Event, Storage, arguments, replay, kernel::SOLVED};
use super::cycles::boundary::{ready_nodes_are_not_rewritten, ready_value_is_retained};
use super::cycles::dfs::{self, Region, Search, Task};
use super::planner_boundary::{self, FreeParent};
use super::replay_prefix::{self, RootPrefix, stop};
use super::replay_view::{self, Draw, PlaceNode};

verus! {

pub struct ExteriorPrefix {
    pub old: RootPrefix,
    pub new: RootPrefix,
    pub exterior: Region,
}

impl ExteriorPrefix {
    pub open spec fn outside(self, key: int) -> bool { (self.exterior)(key) }

    pub open spec fn same_program(self) -> bool {
        let a = self.old.document;
        let b = self.new.document;
        let scope = |k:int| self.outside(k);
        &&& self.old.in_order() && self.new.in_order()
        &&& dfs::project(self.old.prefix_search().todo, scope) == dfs::project(self.new.prefix_search().todo, scope)
        &&& ready_omissions(self.old.prefix_search(), scope)
        &&& ready_omissions(self.new.prefix_search(), scope)
        &&& forall |k:int| #[trigger] self.outside(k) ==> ({
            &&& !a.inside(k) && !b.inside(k)
            &&& (a.initial_state)(k) == (b.initial_state)(k)
            &&& a.initial.contains_key(k) && b.initial.contains_key(k) && a.initial[k] == b.initial[k]
            &&& (a.edges)(k) == (b.edges)(k)
            &&& (a.provisional)(k) == (b.provisional)(k)
            &&& forall |args:Seq<Seq<u32>>| #[trigger] (a.eval)(k,args) == (b.eval)(k,args)
        })
        &&& exterior_reads(a.edges, scope) && exterior_reads(b.edges, scope)
    }
}

/// A projected-away root can occur in either prefix if its slot is already
/// prepared and the request can only reuse its value. No other root is lost.
pub open spec fn ready_omissions(s: Search, exterior: Region) -> bool {
    forall |i:int| 0 <= i < s.todo.len() && !exterior((#[trigger] s.todo[i]).key()) ==>
        s.todo[i] is Visit && (s.state)(s.todo[i].key()) == SOLVED
}

pub open spec fn exterior_reads(edges: dfs::Edges, exterior: Region) -> bool {
    forall |k:int,j:int| exterior(k) && 0 <= j < edges(k).len() ==> exterior(#[trigger] edges(k)[j])
}

proof fn one_step_leaves_only_ready_omissions(s: Search, edges: dfs::Edges, seeds: spec_fn(int) -> Seq<u32>, scope: Region)
    requires ready_omissions(s, scope), exterior_reads(edges, scope), s.todo.len() > 0,
    ensures ready_omissions(dfs::step(s, edges, seeds, None).next, scope),
{
    let task = s.todo.first();
    let key = task.key();
    let next = dfs::step(s, edges, seeds, None).next;
    assert(task == s.todo[0]);
    assert(!scope(key) ==> task is Visit && (s.state)(key) == SOLVED);
    assert forall |i:int| 0 <= i < next.todo.len() && !scope((#[trigger] next.todo[i]).key()) implies
        next.todo[i] is Visit && (next.state)(next.todo[i].key()) == SOLVED by {
        let work = next.todo[i];
        if task is Visit && dfs::fresh(s, key) {
            assert(scope(key));
            if i < edges(key).len() {
                assert(work == Task::Visit(edges(key)[i]));
                assert(scope(edges(key)[i]));
            } else if i == edges(key).len() {
                assert(work == Task::Finish(key));
            } else {
                assert(work == s.todo[i - edges(key).len()]);
            }
        } else {
            assert(work == s.todo[i + 1]);
            if !scope(key) { assert(next.state == s.state); }
        }
    }
}

proof fn equal_exterior_run(e: ExteriorPrefix, a: Search, b: Search, ga: nat, gb: nat)
    requires e.same_program(),
        ({
            let scope = |k:int| e.outside(k);
            &&& dfs::project(a.todo, scope) == dfs::project(b.todo, scope)
            &&& ready_omissions(a, scope) && ready_omissions(b, scope)
        }),
        forall |k:int| #[trigger] e.outside(k) ==> (a.state)(k) == (b.state)(k),
        stop(a, e.old.document.edges, e.old.document.provisional, ga).search.todo.len() == 0,
        stop(b, e.new.document.edges, e.new.document.provisional, gb).search.todo.len() == 0,
    ensures ({
        let x = stop(a, e.old.document.edges, e.old.document.provisional, ga);
        let y = stop(b, e.new.document.edges, e.new.document.provisional, gb);
        &&& x.events == y.events
        &&& forall |k:int| #[trigger] e.outside(k) ==> (x.search.state)(k) == (y.search.state)(k)
    }),
    decreases ga + gb,
{
    let scope = |k:int| e.outside(k);
    let old = e.old.document;
    let new = e.new.document;
    if a.todo.len() > 0 && !scope(a.todo.first().key()) {
        assert(ga > 0);
        assert(a.todo.first() == a.todo[0]);
        let x = dfs::step(a, old.edges, old.provisional, None);
        assert(x.event.is_none() && x.next.state == a.state && x.next.todo == a.todo.drop_first());
        one_step_leaves_only_ready_omissions(a, old.edges, old.provisional, scope);
        equal_exterior_run(e, x.next, b, (ga - 1) as nat, gb);
    } else if b.todo.len() > 0 && !scope(b.todo.first().key()) {
        assert(gb > 0);
        assert(b.todo.first() == b.todo[0]);
        let y = dfs::step(b, new.edges, new.provisional, None);
        assert(y.event.is_none() && y.next.state == b.state && y.next.todo == b.todo.drop_first());
        one_step_leaves_only_ready_omissions(b, new.edges, new.provisional, scope);
        equal_exterior_run(e, a, y.next, ga, (gb - 1) as nat);
    } else if a.todo.len() > 0 {
        let task = a.todo.first();
        let key = task.key();
        let x_roots = dfs::project(a.todo, scope);
        let y_roots = dfs::project(b.todo, scope);
        let later_x = dfs::project(a.todo.drop_first(), scope);
        let later_y = dfs::project(b.todo.drop_first(), scope);
        assert(scope(key));
        assert(x_roots == seq![task] + later_x && x_roots[0] == task);
        assert(y_roots.len() > 0);
        assert(b.todo.len() > 0);
        assert(scope(b.todo.first().key()));
        assert(y_roots == seq![b.todo.first()] + later_y && y_roots[0] == b.todo.first());
        assert(b.todo.first() == task);
        assert(x_roots.drop_first() =~= later_x);
        assert(y_roots.drop_first() =~= later_y);
        assert(ga > 0 && gb > 0);
        let x = dfs::step(a, old.edges, old.provisional, None);
        let y = dfs::step(b, new.edges, new.provisional, None);
        assert(x.event == y.event);
        assert(later_x == later_y);
        if task is Visit && dfs::fresh(a, key) {
            let enter = dfs::requests((old.edges)(key)) + seq![Task::Finish(key)];
            assert(x.next.todo == enter + a.todo.drop_first() && y.next.todo == enter + b.todo.drop_first());
            dfs::project_append(enter, a.todo.drop_first(), scope);
            dfs::project_append(enter, b.todo.drop_first(), scope);
        }
        one_step_leaves_only_ready_omissions(a, old.edges, old.provisional, scope);
        one_step_leaves_only_ready_omissions(b, new.edges, new.provisional, scope);
        assert forall |k:int| #[trigger] e.outside(k) implies (x.next.state)(k) == (y.next.state)(k) by {};
        equal_exterior_run(e, x.next, y.next, (ga - 1) as nat, (gb - 1) as nat);
    } else {
        assert(b.todo.len() == 0);
    }
}

proof fn prefix_events_stay_exterior(s: Search, edges: dfs::Edges, seeds: spec_fn(int) -> Seq<u32>, scope: Region, gas: nat)
    requires ready_omissions(s, scope), exterior_reads(edges, scope),
    ensures forall |i:int| 0 <= i < stop(s, edges, seeds, gas).events.len() ==> ({
        let e = #[trigger] stop(s, edges, seeds, gas).events[i];
        &&& scope(e.target())
        &&& forall |j:int| 0 <= j < e.inputs().len() ==> scope(#[trigger] e.inputs()[j])
    }),
    decreases gas,
{
    if s.todo.len() > 0 && gas > 0 {
        let item = dfs::step(s, edges, seeds, None);
        let left = (gas - 1) as nat;
        let later = stop(item.next, edges, seeds, left).events;
        let all = stop(s, edges, seeds, gas).events;
        one_step_leaves_only_ready_omissions(s, edges, seeds, scope);
        prefix_events_stay_exterior(item.next, edges, seeds, scope, left);
        if let Some(e) = item.event {
            assert(s.todo.first() == s.todo[0]);
            assert(scope(e.target()));
            assert forall |j:int| 0 <= j < e.inputs().len() implies scope(#[trigger] e.inputs()[j]) by {
                assert(e is Finish && e.inputs() == edges(e.target()));
            }
            assert forall |i:int| 0 <= i < all.len() implies ({
                let event = #[trigger] all[i];
                &&& scope(event.target())
                &&& forall |j:int| 0 <= j < event.inputs().len() ==> scope(#[trigger] event.inputs()[j])
            }) by {
                if i == 0 { assert(all[i] == e); }
                else { assert(all[i] == later[i - 1]); }
            }
        }
    }
}

proof fn evaluate_same_exterior_events(e: ExteriorPrefix, events: Seq<Event>)
    requires e.same_program(),
        forall |i:int| 0 <= i < events.len() ==> ({
            let event = #[trigger] events[i];
            &&& e.outside(event.target())
            &&& forall |j:int| 0 <= j < event.inputs().len() ==> e.outside(#[trigger] event.inputs()[j])
        }),
    ensures ({
        let old = e.old.document;
        let new = e.new.document;
        let a = replay(events, old.initial, old.eval);
        let b = replay(events, new.initial, new.eval);
        forall |k:int| #[trigger] e.outside(k) ==> a.contains_key(k) && b.contains_key(k) && a[k] == b[k]
    }),
    decreases events.len(),
{
    if events.len() > 0 {
        let old = e.old.document;
        let new = e.new.document;
        let earlier = events.drop_last();
        let last = events.last();
        assert(last == events[events.len() - 1]);
        assert forall |i:int| 0 <= i < earlier.len() implies ({
            let event = #[trigger] earlier[i];
            &&& e.outside(event.target())
            &&& forall |j:int| 0 <= j < event.inputs().len() ==> e.outside(#[trigger] event.inputs()[j])
        }) by { assert(earlier[i] == events[i]); }
        evaluate_same_exterior_events(e, earlier);
        if let Event::Finish { key, reads } = last {
            let a = replay(earlier, old.initial, old.eval);
            let b = replay(earlier, new.initial, new.eval);
            assert(arguments(reads, a) =~= arguments(reads, b)) by {
                assert forall |i:int| 0 <= i < reads.len() implies a[#[trigger] reads[i]] == b[reads[i]] by {
                    assert(e.outside(last.inputs()[i]));
                }
            }
        }
    }
}

/// The two completed prefixes have the same exterior program and execute
/// the same exterior trace, including provisional observations on back edges.
pub proof fn stable_exterior_computes_the_same_prefix(e: ExteriorPrefix)
    requires e.same_program(),
    ensures e.old.settled().events == e.new.settled().events,
        forall |k:int| #[trigger] e.outside(k) ==> ({
            &&& (e.old.settled().search.state)(k) == (e.new.settled().search.state)(k)
            &&& e.old.prefix_words().contains_key(k) && e.new.prefix_words().contains_key(k)
            &&& e.old.prefix_words()[k] == e.new.prefix_words()[k]
        }),
{
    let a = e.old.document;
    let b = e.new.document;
    replay_prefix::document_factors_at_a_root_cut(e.old, a.cached);
    replay_prefix::document_factors_at_a_root_cut(e.new, b.cached);
    equal_exterior_run(e, e.old.prefix_search(), e.new.prefix_search(), a.gas(), b.gas());
    prefix_events_stay_exterior(e.old.prefix_search(), a.edges, a.provisional, |k:int| e.outside(k), a.gas());
    evaluate_same_exterior_events(e, e.old.settled().events);
}

/// Once ready, every later canonical request reuses that bundle, even if its
/// consumer is a newly rebuilt interior slot.
pub proof fn canonical_full_retains_every_ready_prefix_word(cut: RootPrefix, key: int)
    requires cut.in_order(), (cut.settled().search.state)(key) == SOLVED, cut.prefix_words().contains_key(key),
    ensures cut.document.full_sizing().contains_key(key), cut.document.full_sizing()[key] == cut.prefix_words()[key],
{
    replay_prefix::document_factors_at_a_root_cut(cut, cut.document.cached);
    let suffix = cut.resume(cut.document.cached);
    let start = suffix.document();
    let ready = |k:int| k == key;
    assert forall |i:int| 0 <= i < start.todo.len() implies (#[trigger] start.todo[i]) is Visit by {};
    ready_nodes_are_not_rewritten(start, suffix.edges, suffix.provisional, ready, suffix.gas());
    ready_value_is_retained(suffix.full_events(), suffix.initial, suffix.eval, key);
}

pub proof fn retained_exterior_word_is_the_current_boundary(e: ExteriorPrefix, key: int)
    requires e.same_program(), e.outside(key), (e.new.settled().search.state)(key) == SOLVED,
    ensures e.old.document.full_sizing().contains_key(key) && e.new.prefix_words().contains_key(key),
        e.old.document.full_sizing()[key] == e.new.prefix_words()[key],
{
    stable_exterior_computes_the_same_prefix(e);
    canonical_full_retains_every_ready_prefix_word(e.old, key);
}

/// Close the new regional replay using physical words retained from the old
/// full result. No equality to a newly evaluated boundary is a premise.
pub proof fn retained_old_words_close_the_new_prefix(e: ExteriorPrefix, retained: Storage)
    requires e.same_program(), e.new.untouched_region(),
        forall |i:int| 0 <= i < e.new.document.visits.len() ==>
            (#[trigger] e.new.document.visits[i]).owned_by(e.new.document.owner),
        forall |k:int| #[trigger] e.new.document.inside(k) ==> ({
            let d = e.new.document;
            &&& (d.initial_state)(k) == (d.regional_state)(k)
            &&& d.initial.contains_key(k) && retained.contains_key(k) && d.initial[k] == retained[k]
        }),
        forall |k:int,j:int| 0 <= j < (e.new.document.edges)(k).len() ==> ({
            let dep = #[trigger] (e.new.document.edges)(k)[j];
            let scope = |slot:int| e.new.document.inside(slot);
            let flags = e.new.settled().search.state;
            &&& !scope(k) && scope(dep) ==> flags(k) == SOLVED
            &&& scope(k) && !scope(dep) ==> flags(dep) == SOLVED
        }),
        forall |k:int| #[trigger] e.new.resume(retained).pinned(k) ==> ({
            &&& e.outside(k) && retained.contains_key(k)
            &&& retained[k] == e.old.document.full_sizing()[k]
        }),
    ensures e.new.resume(retained).closed(),
{
    assert forall |k:int| #[trigger] e.new.resume(retained).pinned(k) implies
        e.new.prefix_words().contains_key(k) && retained.contains_key(k) && e.new.prefix_words()[k] == retained[k] by {
        retained_exterior_word_is_the_current_boundary(e, k);
    }
    replay_prefix::retained_prefix_closes_the_suffix(e.new, retained);
}

/// Both Final bundles of an independent Free parent can be retained even
/// when they were first resolved in a canonical prefix rather than seeded.
pub proof fn refreshed_free_parent_retains_exact_finals(e: ExteriorPrefix, parent: FreeParent)
    requires e.same_program(), parent.supported(e.new),
        e.outside(e.new.before()[parent.location].x), e.outside(e.new.before()[parent.location].y),
    ensures e.new.untouched_region(), ({
        let p = e.new.before()[parent.location];
        &&& e.old.document.full_sizing().contains_key(p.x) && e.new.prefix_words().contains_key(p.x)
        &&& e.old.document.full_sizing().contains_key(p.y) && e.new.prefix_words().contains_key(p.y)
        &&& e.old.document.full_sizing()[p.x] == e.new.prefix_words()[p.x]
        &&& e.old.document.full_sizing()[p.y] == e.new.prefix_words()[p.y]
    }),
{
    planner_boundary::refreshed_free_parent_supplies_its_finals(e.new, parent);
    planner_boundary::parent_finals_are_settled(e.new, parent.location);
    let p = e.new.before()[parent.location];
    retained_exterior_word_is_the_current_boundary(e, p.x);
    retained_exterior_word_is_the_current_boundary(e, p.y);
}

/// A structural region below a refreshed Free parent can reuse the previous
/// sizing publication outside it and rebuild the same placement as full DFS.
pub proof fn refreshed_free_parent_rebuilds_the_view(
    e: ExteriorPrefix, parent: FreeParent, retained: Storage, nodes: Seq<PlaceNode>, draw: Draw,
)
    requires e.same_program(), parent.supported(e.new),
        forall |i:int| 0 <= i < e.new.document.visits.len() ==>
            (#[trigger] e.new.document.visits[i]).owned_by(e.new.document.owner),
        forall |k:int| #[trigger] e.new.document.inside(k) ==> ({
            let d = e.new.document;
            &&& (d.initial_state)(k) == (d.regional_state)(k)
            &&& d.initial.contains_key(k) && retained.contains_key(k) && d.initial[k] == retained[k]
        }),
        forall |k:int| #[trigger] e.new.resume(retained).pinned(k) ==> ({
            &&& e.outside(k) && retained.contains_key(k)
            &&& retained[k] == e.old.document.full_sizing()[k]
        }),
        forall |i:int,j:int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len() ==> ({
            let provider = (#[trigger] nodes[i].inputs[j]).producer;
            e.new.document.inside(provider) || e.new.resume(retained).pinned(provider)
        }),
    ensures e.new.resume(retained).closed(),
        replay_view::place_frame(nodes, e.new.resume(retained).rebuilt_sizing(), draw) ==
            replay_view::place_frame(nodes, e.new.document.full_sizing(), draw),
{
    planner_boundary::refreshed_free_parent_supplies_its_finals(e.new, parent);
    retained_old_words_close_the_new_prefix(e, retained);
    replay_prefix::settled_prefix_rebuilds_the_view(e.new, retained, nodes, draw);
}

}
