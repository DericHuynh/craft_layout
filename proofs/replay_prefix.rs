//! Factoring canonical DFS at a completed prefix of root requests.
//! A producer visited in the prefix can supply a ready boundary word without
//! being ready in the document's initial state.
use vstd::prelude::*;
use super::cycles::{self, Compute, Event, Storage, replay};
use super::cycles::boundary::{ready_nodes_are_not_rewritten, ready_value_is_retained};
use super::cycles::dfs::{self, Edges, Search, Task};
use super::production_schedule::{self as roots, NodeRequests};
use super::replay_view::{self, Draw, PlaceNode, Replay};

verus! {

pub struct Stopped {
    pub search: Search,
    pub events: Seq<Event>,
    pub gas: nat,
}

/// Execute the existing DFS steps while also retaining the post-step flags.
/// The suffix is held aside, so no suffix root starts in this run.
pub open spec fn stop(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, gas: nat) -> Stopped
    decreases gas,
{
    if s.todo.len() == 0 || gas == 0 {
        Stopped { search: s, events: Seq::empty(), gas }
    } else {
        let item = dfs::step(s, edges, seeds, None);
        let tail = stop(item.next, edges, seeds, (gas - 1) as nat);
        let events = match item.event { Some(e) => seq![e] + tail.events, None => tail.events };
        Stopped { search: tail.search, events, gas: tail.gas }
    }
}

proof fn stop_executes_the_same_steps(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, gas: nat)
    ensures dfs::drive(s, edges, seeds, None, |_:int| true, gas)
        == (stop(s, edges, seeds, gas).events, stop(s, edges, seeds, gas).search.todo.len() == 0),
    decreases gas,
{
    if s.todo.len() > 0 && gas > 0 {
        let item = dfs::step(s, edges, seeds, None);
        stop_executes_the_same_steps(item.next, edges, seeds, (gas - 1) as nat);
    }
}

spec fn append_tasks(s: Search, tasks: Seq<Task>) -> Search {
    Search { todo: s.todo + tasks, state: s.state }
}

proof fn step_keeps_the_later_roots(s: Search, tasks: Seq<Task>, edges: Edges, seeds: spec_fn(int) -> Seq<u32>)
    requires s.todo.len() > 0,
    ensures ({
        let before = dfs::step(s, edges, seeds, None);
        let extended = dfs::step(append_tasks(s, tasks), edges, seeds, None);
        extended.next == append_tasks(before.next, tasks) && extended.event == before.event
    }),
{
    assert((s.todo + tasks).first() == s.todo.first());
    assert((s.todo + tasks).drop_first() =~= s.todo.drop_first() + tasks);
    let k = s.todo.first().key();
    let continuation = dfs::requests(edges(k)) + seq![Task::Finish(k)];
    assert(continuation + (s.todo.drop_first() + tasks) =~=
        (continuation + s.todo.drop_first()) + tasks);
    let before = dfs::step(s, edges, seeds, None);
    let extended = dfs::step(append_tasks(s, tasks), edges, seeds, None);
    assert(extended.next.state == before.next.state);
    assert(extended.next.todo == before.next.todo + tasks);
}

proof fn resume_after_prefix(s: Search, tasks: Seq<Task>, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, gas: nat)
    requires stop(s, edges, seeds, gas).search.todo.len() == 0,
    ensures ({
        let cut = stop(s, edges, seeds, gas);
        let resumed = dfs::drive(append_tasks(cut.search, tasks), edges, seeds, None, |_:int| true, cut.gas);
        dfs::drive(append_tasks(s, tasks), edges, seeds, None, |_:int| true, gas) ==
            (cut.events + resumed.0, resumed.1)
    }),
    decreases gas,
{
    if s.todo.len() > 0 {
        assert(gas > 0);
        let item = dfs::step(s, edges, seeds, None);
        step_keeps_the_later_roots(s, tasks, edges, seeds);
        resume_after_prefix(item.next, tasks, edges, seeds, (gas - 1) as nat);
    }
}

proof fn enough_fuel_gives_one_run(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, a: nat, b: nat)
    requires dfs::drive(s, edges, seeds, None, |_:int| true, a).1,
        dfs::drive(s, edges, seeds, None, |_:int| true, b).1,
    ensures dfs::drive(s, edges, seeds, None, |_:int| true, a).0 ==
        dfs::drive(s, edges, seeds, None, |_:int| true, b).0,
    decreases a,
{
    if s.todo.len() > 0 {
        assert(a > 0 && b > 0);
        let item = dfs::step(s, edges, seeds, None);
        enough_fuel_gives_one_run(item.next, edges, seeds, (a - 1) as nat, (b - 1) as nat);
    }
}

proof fn append_node_visits(a: Seq<NodeRequests>, b: Seq<NodeRequests>)
    ensures roots::walk(a + b) == roots::walk(a) + roots::walk(b),
    decreases a.len(),
{
    if a.len() > 0 {
        assert((a + b).first() == a.first());
        assert((a + b).drop_first() =~= a.drop_first() + b);
        append_node_visits(a.drop_first(), b);
    }
}

proof fn replay_appended_events(a: Seq<Event>, b: Seq<Event>, initial: Storage, eval: Compute)
    ensures replay(a + b, initial, eval) == replay(b, replay(a, initial, eval), eval),
    decreases b.len(),
{
    if b.len() > 0 {
        assert((a + b).last() == b.last());
        assert((a + b).drop_last() =~= a + b.drop_last());
        replay_appended_events(a, b.drop_last(), initial, eval);
    }
}

proof fn visible_skips_settled_prefix(a: Seq<Event>, b: Seq<Event>, inside: dfs::Region)
    requires forall |i:int| 0 <= i < a.len() ==> !inside((#[trigger] a[i]).target()),
    ensures dfs::visible(a + b, inside) == dfs::visible(b, inside),
    decreases a.len(),
{
    if a.len() > 0 {
        let rest = a.drop_first();
        assert((a + b).first() == a[0]);
        assert((a + b).drop_first() =~= rest + b);
        assert forall |i:int| 0 <= i < rest.len() implies !inside((#[trigger] rest[i]).target()) by {
            assert(rest[i] == a[i + 1]);
        }
        visible_skips_settled_prefix(rest, b, inside);
    }
}

proof fn budget_depends_only_on_flags(a: Search, b: Search, edges: Edges, n: nat)
    requires a.state == b.state,
    ensures dfs::budget(a, edges, n) == dfs::budget(b, edges, n),
    decreases n,
{
    if n > 0 { budget_depends_only_on_flags(a, b, edges, (n - 1) as nat); }
}

proof fn prefix_keeps_untouched_flags(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, gas: nat, key: int)
    requires forall |i:int| 0 <= i < stop(s, edges, seeds, gas).events.len() ==>
        (#[trigger] stop(s, edges, seeds, gas).events[i]).target() != key,
    ensures (stop(s, edges, seeds, gas).search.state)(key) == (s.state)(key),
    decreases gas,
{
    if s.todo.len() > 0 && gas > 0 {
        let item = dfs::step(s, edges, seeds, None);
        let tail = stop(item.next, edges, seeds, (gas - 1) as nat);
        let out = stop(s, edges, seeds, gas);
        if let Some(e) = item.event {
            assert(e == out.events[0]);
            assert((item.next.state)(key) == (s.state)(key));
            assert forall |i:int| 0 <= i < tail.events.len() implies (#[trigger] tail.events[i]).target() != key by {
                assert(tail.events[i] == out.events[i + 1]);
            }
        }
        prefix_keeps_untouched_flags(item.next, edges, seeds, (gas - 1) as nat, key);
    }
}

proof fn stop_preserves_ready_slot(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, gas: nat, key: int)
    requires (s.state)(key) == cycles::kernel::SOLVED,
    ensures (stop(s, edges, seeds, gas).search.state)(key) == cycles::kernel::SOLVED,
    decreases gas,
{
    if s.todo.len() > 0 && gas > 0 {
        let item = dfs::step(s, edges, seeds, None);
        stop_preserves_ready_slot(item.next, edges, seeds, (gas - 1) as nat, key);
    }
}

spec fn waiting_finishes(s: Search) -> bool {
    forall |key:int| #[trigger] (s.state)(key) == cycles::kernel::IN_PROGRESS ==>
        exists |i:int| 0 <= i < s.todo.len() && #[trigger] s.todo[i] == Task::Finish(key)
}

proof fn stop_preserves_pending_finishes(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, gas: nat)
    requires waiting_finishes(s),
    ensures waiting_finishes(stop(s, edges, seeds, gas).search),
    decreases gas,
{
    if s.todo.len() > 0 && gas > 0 {
        let t = s.todo.first();
        let k = t.key();
        let item = dfs::step(s, edges, seeds, None);
        let next = item.next;
        assert(t == s.todo[0]);
        assert forall |key:int| #[trigger] (next.state)(key) == cycles::kernel::IN_PROGRESS implies
            exists |j:int| 0 <= j < next.todo.len() && #[trigger] next.todo[j] == Task::Finish(key) by {
            let appended = t is Visit && dfs::fresh(s, k);
            if appended && key == k {
                assert(next.todo[edges(k).len() as int] == Task::Finish(key));
            } else {
                assert((s.state)(key) == cycles::kernel::IN_PROGRESS);
                let i = choose |i:int| 0 <= i < s.todo.len() && #[trigger] s.todo[i] == Task::Finish(key);
                assert(i > 0) by {
                    if i == 0 {
                        assert(t == Task::Finish(key));
                        assert((next.state)(key) == cycles::kernel::SOLVED);
                    }
                }
                let j = if appended { i + edges(k).len() } else { i - 1 };
                assert(0 <= j < next.todo.len() && next.todo[j] == Task::Finish(key));
            }
        }
        stop_preserves_pending_finishes(next, edges, seeds, (gas - 1) as nat);
    }
}

proof fn stop_finishes_at_ready_slot(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, gas: nat, key: int, index: int)
    requires 0 <= index < stop(s, edges, seeds, gas).events.len(),
        stop(s, edges, seeds, gas).events[index] is Finish,
        stop(s, edges, seeds, gas).events[index].target() == key,
    ensures (stop(s, edges, seeds, gas).search.state)(key) == cycles::kernel::SOLVED,
    decreases gas,
{
    assert(s.todo.len() > 0 && gas > 0);
    let item = dfs::step(s, edges, seeds, None);
    let left = (gas - 1) as nat;
    let tail = stop(item.next, edges, seeds, left);
    if let Some(e) = item.event {
        if index == 0 {
            assert(e == stop(s, edges, seeds, gas).events[0]);
            stop_preserves_ready_slot(item.next, edges, seeds, left, key);
        } else {
            assert(tail.events[index - 1] == stop(s, edges, seeds, gas).events[index]);
            stop_finishes_at_ready_slot(item.next, edges, seeds, left, key, index - 1);
        }
    } else {
        stop_finishes_at_ready_slot(item.next, edges, seeds, left, key, index);
    }
}

pub open spec fn finished_at(events: Seq<Event>, key: int, index: int) -> bool {
    0 <= index < events.len() && events[index] is Finish && events[index].target() == key
}

proof fn ready_transition_has_finish(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, gas: nat, key: int)
    -> (index: int)
    requires (s.state)(key) != cycles::kernel::SOLVED,
        (stop(s, edges, seeds, gas).search.state)(key) == cycles::kernel::SOLVED,
    ensures finished_at(stop(s, edges, seeds, gas).events, key, index),
    decreases gas,
{
    assert(s.todo.len() > 0 && gas > 0);
    let item = dfs::step(s, edges, seeds, None);
    let left = (gas - 1) as nat;
    let tail = stop(item.next, edges, seeds, left);
    let events = stop(s, edges, seeds, gas).events;
    if (item.next.state)(key) == cycles::kernel::SOLVED {
        assert(item.event.is_some());
        assert(item.event.unwrap() is Finish && item.event.unwrap().target() == key);
        assert(events[0] == item.event.unwrap());
        0
    } else {
        let next = ready_transition_has_finish(item.next, edges, seeds, left, key);
        if item.event.is_some() {
            assert(events[next + 1] == tail.events[next]);
            next + 1
        } else {
            next
        }
    }
}

proof fn replay_keeps_written_slot(events: Seq<Event>, initial: Storage, eval: Compute, key: int, index: int)
    requires 0 <= index < events.len(), events[index].target() == key,
    ensures replay(events, initial, eval).contains_key(key),
    decreases events.len(),
{
    if index + 1 == events.len() {
        assert(events.last() == events[index]);
    } else {
        assert(events.drop_last()[index] == events[index]);
        replay_keeps_written_slot(events.drop_last(), initial, eval, key, index);
    }
}

pub struct RootPrefix {
    pub document: Replay,
    pub split: int,
}

impl RootPrefix {
    pub open spec fn before(self) -> Seq<NodeRequests> { self.document.visits.take(self.split) }
    pub open spec fn after(self) -> Seq<NodeRequests> { self.document.visits.skip(self.split) }

    pub open spec fn prefix_search(self) -> Search {
        Search { todo: dfs::requests(roots::walk(self.before())), state: self.document.initial_state }
    }

    pub open spec fn settled(self) -> Stopped {
        let d = self.document;
        stop(self.prefix_search(), d.edges, d.provisional, d.gas())
    }

    pub open spec fn prefix_words(self) -> Storage {
        replay(self.settled().events, self.document.initial, self.document.eval)
    }

    /// Supplying a different regional cache lets a caller phrase explicitly
    /// which committed producer bundles are present in the prepared tree.
    pub open spec fn resume(self, retained: Storage) -> Replay {
        let d = self.document;
        Replay {
            visits: self.after(), owner: d.owner, nodes: d.nodes, edges: d.edges, n: d.n,
            initial_state: self.settled().search.state, regional_state: d.regional_state,
            provisional: d.provisional, initial: self.prefix_words(), cached: retained, eval: d.eval,
        }
    }

    pub open spec fn in_order(self) -> bool {
        &&& 0 <= self.split <= self.document.visits.len()
        &&& dfs::bounded(self.document.document(), self.document.edges, self.document.n)
    }

    pub open spec fn untouched_region(self) -> bool {
        let events = self.settled().events;
        forall |i:int| 0 <= i < events.len() ==> !self.document.inside((#[trigger] events[i]).target())
    }
}

/// A cut is taken at a boundary between nodes in the actual canonical visit
/// list. The remaining roots are exactly its suffix in canonical order.
pub proof fn document_factors_at_a_root_cut(cut: RootPrefix, retained: Storage)
    requires cut.in_order(),
    ensures cut.settled().search.todo.len() == 0,
        dfs::bounded(cut.resume(retained).document(), cut.document.edges, cut.document.n),
        cut.document.full_events() == cut.settled().events + cut.resume(retained).full_events(),
        cut.document.full_sizing() == cut.resume(retained).full_sizing(),
{
    let d = cut.document;
    let start = cut.prefix_search();
    let resume = cut.resume(retained);
    let tail = resume.document().todo;
    let first = cut.before();
    let last = cut.after();
    assert(first + last =~= d.visits);
    append_node_visits(first, last);
    assert(start.todo + tail =~= d.document().todo);
    assert(append_tasks(start, tail) == d.document());
    assert(dfs::bounded(start, d.edges, d.n)) by {
        assert forall |i:int| 0 <= i < start.todo.len() implies 0 <= (#[trigger] start.todo[i]).key() < d.n by {
            assert(start.todo[i] == d.document().todo[i]);
        }
    }
    budget_depends_only_on_flags(start, d.document(), d.edges, d.n);
    assert(start.todo.len() + dfs::budget(start, d.edges, d.n) <= d.gas());
    assert forall |i:int| 0 <= i < start.todo.len() implies (#[trigger] start.todo[i]) is Visit by {};
    dfs::finite_full_dfs_finishes(start, d.edges, d.provisional, |_:int| true, d.n, d.gas());
    stop_executes_the_same_steps(start, d.edges, d.provisional, d.gas());
    let prefix = cut.settled();
    assert(prefix.search.todo.len() == 0);
    assert(append_tasks(prefix.search, tail) == resume.document());
    resume_after_prefix(start, tail, d.edges, d.provisional, d.gas());
    assert forall |i:int| 0 <= i < d.document().todo.len() implies (#[trigger] d.document().todo[i]) is Visit by {};
    dfs::finite_full_dfs_finishes(d.document(), d.edges, d.provisional, |_:int| true, d.n, d.gas());
    assert(dfs::bounded(resume.document(), d.edges, d.n)) by {
        assert forall |i:int| 0 <= i < tail.len() implies 0 <= (#[trigger] tail[i]).key() < d.n by {
            assert(tail[i] == d.document().todo[start.todo.len() + i]);
        }
    }
    assert forall |i:int| 0 <= i < tail.len() implies (#[trigger] tail[i]) is Visit by {};
    dfs::finite_full_dfs_finishes(resume.document(), d.edges, d.provisional, |_:int| true, d.n, resume.gas());
    enough_fuel_gives_one_run(resume.document(), d.edges, d.provisional, prefix.gas, resume.gas());
    replay_appended_events(prefix.events, resume.full_events(), d.initial, d.eval);
}

/// Starting with no active slot means the cut has no active slot either.
/// Every active flag minted by DFS is paired with a pending Finish task.
pub proof fn root_cut_is_quiescent(cut: RootPrefix)
    requires cut.in_order(),
        forall |key:int| #[trigger] (cut.document.initial_state)(key) != cycles::kernel::IN_PROGRESS,
    ensures cut.settled().search.todo.len() == 0,
        forall |key:int| #[trigger] (cut.settled().search.state)(key) != cycles::kernel::IN_PROGRESS,
{
    let d = cut.document;
    document_factors_at_a_root_cut(cut, d.cached);
    stop_preserves_pending_finishes(cut.prefix_search(), d.edges, d.provisional, d.gas());
}

pub proof fn settled_prefix_leaves_interior_unstarted(cut: RootPrefix, key: int)
    requires cut.untouched_region(), cut.document.inside(key), cut.document.initial.contains_key(key),
    ensures (cut.settled().search.state)(key) == (cut.document.initial_state)(key),
        cut.prefix_words().contains_key(key), cut.prefix_words()[key] == cut.document.initial[key],
{
    let d = cut.document;
    prefix_keeps_untouched_flags(cut.prefix_search(), d.edges, d.provisional, d.gas(), key);
    ready_value_is_retained(cut.settled().events, d.initial, d.eval, key);
}

/// A Finish in the prefix publishes a ready boundary input even when the
/// input was pending at the start of document sizing.
pub proof fn finished_prefix_slot_is_ready(cut: RootPrefix, key: int, index: int)
    requires 0 <= index < cut.settled().events.len(), cut.settled().events[index] is Finish,
        cut.settled().events[index].target() == key,
    ensures (cut.settled().search.state)(key) == cycles::kernel::SOLVED, cut.prefix_words().contains_key(key),
{
    let d = cut.document;
    stop_finishes_at_ready_slot(cut.prefix_search(), d.edges, d.provisional, d.gas(), key, index);
    replay_keeps_written_slot(cut.settled().events, d.initial, d.eval, key, index);
}

spec fn unique_active_finish(s: Search, key: int) -> bool {
    &&& forall |i:int| 0 <= i < s.todo.len() && #[trigger] s.todo[i] == Task::Finish(key) ==>
        (s.state)(key) == cycles::kernel::IN_PROGRESS
    &&& forall |i:int,j:int| 0 <= i < s.todo.len() && 0 <= j < s.todo.len() &&
        #[trigger] s.todo[i] == Task::Finish(key) && #[trigger] s.todo[j] == Task::Finish(key) ==> i == j
}

proof fn finish_step_keeps_unique_active(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>, key: int)
    requires s.todo.len() > 0, unique_active_finish(s,key),
    ensures unique_active_finish(dfs::step(s,edges,seeds,None).next,key),
{
    let t = s.todo[0];
    let k = t.key();
    let next = dfs::step(s,edges,seeds,None).next;
    let starts = t is Visit && dfs::fresh(s,k);
    let deps = dfs::requests(edges(k));
    let added = if starts { deps.len()+1 } else { 0 };
    assert forall |i:int| 0 <= i < next.todo.len() && #[trigger] next.todo[i] == Task::Finish(key)
        implies (next.state)(key) == cycles::kernel::IN_PROGRESS &&
            (i < added ==> i == added-1 && k == key) &&
            (i >= added ==> 1 <= i-added+1 < s.todo.len() && s.todo[i-added+1] == Task::Finish(key)) by {
        if i < added {
            if i < deps.len() { assert(next.todo[i] == deps[i] && deps[i] is Visit); }
            else { assert(next.todo[i] == Task::Finish(k)); }
        } else {
            assert(next.todo[i] == s.todo[i-added+1]);
            if t == Task::Finish(key) { assert(i-added+1 != 0 && s.todo[0] == Task::Finish(key)); }
        }
    }
    assert forall |i:int,j:int| 0 <= i < next.todo.len() && 0 <= j < next.todo.len() &&
        #[trigger] next.todo[i] == Task::Finish(key) && #[trigger] next.todo[j] == Task::Finish(key) implies i==j by {
        if i < added && j >= added {
            assert(k == key && s.todo[j-added+1] == Task::Finish(key));
        } else if j < added && i >= added {
            assert(k == key && s.todo[i-added+1] == Task::Finish(key));
        }
    }
}

proof fn stop_keeps_finished_word(s: Search, edges: Edges, seeds: spec_fn(int) -> Seq<u32>,
    gas: nat, key: int, index: int,
)
    requires unique_active_finish(s,key), finished_at(stop(s,edges,seeds,gas).events,key,index),
    ensures forall |i:int| index < i < stop(s,edges,seeds,gas).events.len() ==>
        (#[trigger] stop(s,edges,seeds,gas).events[i]).target() != key,
    decreases gas,
{
    assert(s.todo.len() > 0 && gas > 0);
    let step = dfs::step(s,edges,seeds,None);
    let left = (gas-1) as nat;
    let events = stop(s,edges,seeds,gas).events;
    let tail = stop(step.next,edges,seeds,left).events;
    finish_step_keeps_unique_active(s,edges,seeds,key);
    if let Some(e) = step.event {
        if index == 0 {
            assert(e == events[0]);
            assert((step.next.state)(key) == cycles::kernel::SOLVED);
            let ready = |k:int| k == key;
            ready_nodes_are_not_rewritten(step.next,edges,seeds,ready,left);
            stop_executes_the_same_steps(step.next,edges,seeds,left);
            assert forall |i:int| index < i < events.len() implies (#[trigger] events[i]).target() != key by {
                assert(events[i] == tail[i-1]);
            }
        } else {
            assert(events[index] == tail[index-1]);
            stop_keeps_finished_word(step.next,edges,seeds,left,key,index-1);
            assert forall |i:int| index < i < events.len() implies (#[trigger] events[i]).target() != key by {
                assert(events[i] == tail[i-1]);
            }
        }
    } else { stop_keeps_finished_word(step.next,edges,seeds,left,key,index); }
}

/// A canonical producer commits once. Later sizing roots can reuse its value
/// but cannot reopen the slot or replace its words.
pub proof fn finished_prefix_slot_has_no_later_write(cut: RootPrefix, key: int, index: int)
    requires finished_at(cut.settled().events,key,index),
    ensures forall |i:int| index < i < cut.settled().events.len() ==>
        (#[trigger] cut.settled().events[i]).target() != key,
{
    let d = cut.document;
    let start = cut.prefix_search();
    assert forall |i:int| 0 <= i < start.todo.len() implies (#[trigger] start.todo[i]) is Visit by {};
    stop_keeps_finished_word(start,d.edges,d.provisional,d.gas(),key,index);
}

/// This is the readiness test for a canonical cut. A solver can use an
/// explicit preparation witness or a Finish from the completed prefix. The
/// presence of solved bits in a previous frame supplies neither witness.
pub proof fn canonical_ready_has_exact_origin(cut: RootPrefix, key: int)
    ensures ({
        let prepared = (cut.document.initial_state)(key) == cycles::kernel::SOLVED;
        let done = exists |index:int| #[trigger] finished_at(cut.settled().events, key, index);
        let ready = (cut.settled().search.state)(key) == cycles::kernel::SOLVED;
        &&& ready == (prepared || done)
        &&& ready && (cut.document.initial.contains_key(key) || done) ==> cut.prefix_words().contains_key(key)
        &&& prepared && cut.document.initial.contains_key(key) ==> cut.prefix_words()[key] == cut.document.initial[key]
    }),
{
    let d = cut.document;
    let events = cut.settled().events;
    let start = cut.prefix_search();
    let done = exists |i:int| #[trigger] finished_at(events, key, i);
    if (d.initial_state)(key) == cycles::kernel::SOLVED {
        stop_preserves_ready_slot(start, d.edges, d.provisional, d.gas(), key);
        let ready = |k:int| k == key;
        ready_nodes_are_not_rewritten(start, d.edges, d.provisional, ready, d.gas());
        stop_executes_the_same_steps(start, d.edges, d.provisional, d.gas());
        assert(!done) by {
            if done {
                let i = choose |i:int| #[trigger] finished_at(events, key, i);
                assert(events[i].target() != key);
            }
        }
        if d.initial.contains_key(key) {
            ready_value_is_retained(events, d.initial, d.eval, key);
        }
    } else if (cut.settled().search.state)(key) == cycles::kernel::SOLVED {
        let index = ready_transition_has_finish(start, d.edges, d.provisional, d.gas(), key);
        assert(finished_at(events, key, index));
        assert(done);
        finished_prefix_slot_is_ready(cut, key, index);
    } else if done {
        let index = choose |i:int| #[trigger] finished_at(events, key, i);
        finished_prefix_slot_is_ready(cut, key, index);
    }
}

/// Establish suffix closure from the actual phase state at the cut. Interior
/// seeds still come from clean preparation. Boundary words come from the
/// executed prefix, including producers that were initially unsolved.
pub proof fn retained_prefix_closes_the_suffix(cut: RootPrefix, retained: Storage)
    requires cut.in_order(), cut.untouched_region(),
        forall |i:int| 0 <= i < cut.document.visits.len() ==>
            (#[trigger] cut.document.visits[i]).owned_by(cut.document.owner),
        forall |k:int| #[trigger] cut.document.inside(k) ==> ({
            let d = cut.document;
            &&& (d.initial_state)(k) == (d.regional_state)(k)
            &&& d.initial.contains_key(k) && retained.contains_key(k) && d.initial[k] == retained[k]
        }),
        forall |k:int,j:int| 0 <= j < (cut.document.edges)(k).len() ==> ({
            let dep = #[trigger] (cut.document.edges)(k)[j];
            let inside = |slot:int| cut.document.inside(slot);
            let state = cut.settled().search.state;
            &&& !inside(k) && inside(dep) ==> state(k) == cycles::kernel::SOLVED
            &&& inside(k) && !inside(dep) ==> state(dep) == cycles::kernel::SOLVED
        }),
        forall |k:int| #[trigger] cut.resume(retained).pinned(k) ==>
            cut.prefix_words().contains_key(k) && retained.contains_key(k) && cut.prefix_words()[k] == retained[k],
    ensures cut.resume(retained).closed(),
{
    document_factors_at_a_root_cut(cut, retained);
    let r = cut.resume(retained);
    assert forall |i:int| 0 <= i < r.visits.len() implies (#[trigger] r.visits[i]).owned_by(r.owner) by {
        assert(r.visits[i] == cut.document.visits[i + cut.split]);
    }
    assert forall |k:int| #[trigger] r.inside(k) implies ({
        &&& (r.initial_state)(k) == (r.regional_state)(k)
        &&& r.initial.contains_key(k) && r.cached.contains_key(k) && r.initial[k] == r.cached[k]
    }) by {
        assert(cut.document.inside(k));
        settled_prefix_leaves_interior_unstarted(cut, k);
    }
}

/// A closed suffix can use any committed prefix bundle, including a Grid
/// assignment first calculated by an earlier root. This theorem takes
/// closure at the cut and the retained cache as premises.
pub proof fn settled_prefix_replays_canonical_suffix(cut: RootPrefix, retained: Storage, key: int)
    requires cut.in_order(), cut.untouched_region(), cut.resume(retained).closed(), cut.document.inside(key),
    ensures cut.resume(retained).rebuilt_events() == dfs::visible(cut.document.full_events(), |k:int| cut.document.inside(k)),
        cut.resume(retained).rebuilt_sizing().contains_key(key), cut.document.full_sizing().contains_key(key),
        cut.resume(retained).rebuilt_sizing()[key] == cut.document.full_sizing()[key],
{
    document_factors_at_a_root_cut(cut, retained);
    let r = cut.resume(retained);
    let inside = |k:int| cut.document.inside(k);
    assert(inside =~= |k:int| r.inside(k));
    visible_skips_settled_prefix(cut.settled().events, r.full_events(), inside);
    replay_view::rebuilt_producers_match_the_document(r, key);
}

/// Placement may read a settled external bundle directly as well as sizing
/// slots rebuilt in the suffix. Neither execution rewrites that bundle.
pub proof fn ready_prefix_slot_is_retained(cut: RootPrefix, retained: Storage, key: int)
    requires cut.in_order(), cut.resume(retained).closed(), cut.resume(retained).pinned(key),
    ensures cut.resume(retained).rebuilt_sizing().contains_key(key), cut.document.full_sizing().contains_key(key),
        cut.resume(retained).rebuilt_sizing()[key] == cut.document.full_sizing()[key],
{
    document_factors_at_a_root_cut(cut, retained);
    let r = cut.resume(retained);
    let ready = |k:int| r.pinned(k);
    let inside = |k:int| r.inside(k);
    ready_nodes_are_not_rewritten(r.document(), r.edges, r.provisional, ready, r.gas());
    replay_view::reads_pinned_values(r, r.full_events());
    replay_view::match_region_events(r);
    ready_value_is_retained(r.full_events(), r.initial, r.eval, key);
    dfs::replay_projection(r.full_events(), r.initial, r.cached, inside, r.eval, key);
}

pub proof fn settled_prefix_rebuilds_the_view(cut: RootPrefix, retained: Storage, nodes: Seq<PlaceNode>, draw: Draw)
    requires cut.in_order(), cut.untouched_region(), cut.resume(retained).closed(),
        forall |i:int,j:int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len() ==> ({
            let producer = (#[trigger] nodes[i].inputs[j]).producer;
            cut.document.inside(producer) || cut.resume(retained).pinned(producer)
        }),
    ensures replay_view::place_frame(nodes, cut.resume(retained).rebuilt_sizing(), draw) ==
        replay_view::place_frame(nodes, cut.document.full_sizing(), draw),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let prefix = nodes.drop_last();
        let node = nodes.last();
        let rebuilt = cut.resume(retained).rebuilt_sizing();
        let full = cut.document.full_sizing();
        assert(node == nodes[nodes.len() - 1]);
        assert forall |i:int,j:int| 0 <= i < prefix.len() && 0 <= j < prefix[i].inputs.len() implies ({
            let producer = (#[trigger] prefix[i].inputs[j]).producer;
            cut.document.inside(producer) || cut.resume(retained).pinned(producer)
        }) by { assert(prefix[i] == nodes[i]); }
        settled_prefix_rebuilds_the_view(cut, retained, prefix, draw);
        assert(replay_view::words(rebuilt, node) =~= replay_view::words(full, node)) by {
            assert forall |j:int| 0 <= j < node.inputs.len() implies
                rebuilt[(#[trigger] node.inputs[j]).producer] == full[node.inputs[j].producer] by {
                let key = node.inputs[j].producer;
                if cut.document.inside(key) {
                    settled_prefix_replays_canonical_suffix(cut, retained, key);
                } else {
                    ready_prefix_slot_is_retained(cut, retained, key);
                }
            }
        }
    }
}

}
