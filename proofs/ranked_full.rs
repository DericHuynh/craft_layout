//! Connect a fresh DFS sizing run to the rank-ordered solver used by numeric edits.
use vstd::prelude::*;
use crate::cycles::{self, Compute, Event, Storage, kernel};
use crate::cycles::dfs::{self, Edges, Search, Task};
use crate::{dependencies, sizing_tape};

verus! {

pub open spec fn ranked(edges: Edges, count: nat) -> bool {
    forall |k: int, i: int| 0 <= k < count && 0 <= i < edges(k).len()
        ==> 0 <= #[trigger] edges(k)[i] < k
}

pub open spec fn fixed_point(edges: Edges, eval: Compute, values: Seq<Seq<u32>>) -> bool {
    forall |k: int| 0 <= k < values.len() ==> #[trigger] values[k] ==
        eval(k, Seq::new(edges(k).len(), |i: int| values[edges(k)[i]]))
}

// Every pending request precedes only finishes for higher-ranked ancestors.
spec fn ordered_stack(search: Search) -> bool {
    forall |i: int, j: int| 0 <= i < j < search.todo.len()
        && (#[trigger] search.todo[j]) is Finish
        ==> (#[trigger] search.todo[i]).key() < search.todo[j].key()
}

spec fn no_orphaned_slot(search: Search, count: nat) -> bool {
    forall |k: int| 0 <= k < count && #[trigger] (search.state)(k) == kernel::IN_PROGRESS
        ==> search.todo.contains(Task::Finish(k))
}

spec fn exact_settled(search: Search, words: Storage, values: Seq<Seq<u32>>) -> bool {
    forall |k: int| 0 <= k < values.len() && #[trigger] (search.state)(k) == kernel::SOLVED
        ==> words.contains_key(k) && words[k] == values[k]
}

spec fn queued_or_solved(search: Search, key: int) -> bool {
    ||| dfs::pending_or_solved(search, key)
    ||| search.todo.contains(Task::Visit(key))
}

proof fn ranked_stack_step(search: Search, edges: Edges, provisional: spec_fn(int) -> Seq<u32>, count: nat)
    requires search.todo.len() > 0, dfs::bounded(search, edges, count),
        ranked(edges, count), ordered_stack(search), no_orphaned_slot(search, count),
    ensures ordered_stack(dfs::step(search, edges, provisional, None).next),
        no_orphaned_slot(dfs::step(search, edges, provisional, None).next, count),
{
    let head = search.todo.first();
    let key = head.key();
    let next = dfs::step(search, edges, provisional, None).next;
    let deps = dfs::requests(edges(key));
    let expands = head is Visit && dfs::fresh(search, key);
    let extra = if expands { deps.len() + 1 } else { 0nat };
    assert(head == search.todo[0]);
    assert forall |i: int, j: int| 0 <= i < j < next.todo.len()
        && (#[trigger] next.todo[j]) is Finish
        implies (#[trigger] next.todo[i]).key() < next.todo[j].key() by {
        if j < extra {
            assert(j == deps.len() && next.todo[j] == Task::Finish(key));
            assert(next.todo[i] == deps[i]);
            assert(deps[i].key() == edges(key)[i]);
        } else {
            let prior_j = j-extra+1;
            assert(0 < prior_j < search.todo.len());
            assert(next.todo[j] == search.todo[prior_j]);
            if i < extra {
                assert(head.key() < search.todo[prior_j].key());
                if i == deps.len() { assert(next.todo[i] == Task::Finish(key)); }
                else {
                    assert(next.todo[i] == deps[i]);
                    assert(deps[i].key() == edges(key)[i]);
                }
                assert(next.todo[i].key() <= key);
            } else {
                assert(next.todo[i] == search.todo[i-extra+1]);
            }
        }
    }
    assert forall |k: int| 0 <= k < count && #[trigger] (next.state)(k) == kernel::IN_PROGRESS
        implies next.todo.contains(Task::Finish(k)) by {
        if expands && k == key {
            assert(next.todo[deps.len() as int] == Task::Finish(k));
        } else {
            assert((search.state)(k) == kernel::IN_PROGRESS);
            assert(search.todo.contains(Task::Finish(k)));
            let prior = choose |i: int| 0 <= i < search.todo.len() && search.todo[i] == Task::Finish(k);
            if prior == 0 { assert(head == Task::Finish(k) && (next.state)(k) == kernel::SOLVED); }
            assert(next.todo[prior - 1 + extra] == Task::Finish(k));
        }
    }
}

proof fn requested_step(search: Search, edges: Edges, provisional: spec_fn(int) -> Seq<u32>, count: nat, key: int)
    requires search.todo.len() > 0, 0 <= key < count, queued_or_solved(search, key),
        no_orphaned_slot(search, count),
    ensures queued_or_solved(dfs::step(search, edges, provisional, None).next, key),
{
    if dfs::pending_or_solved(search, key) {
        dfs::full_step_preserves_goal(search, edges, provisional, key);
    } else {
        let head = search.todo.first();
        let next = dfs::step(search, edges, provisional, None).next;
        let extra = if head is Visit && dfs::fresh(search, head.key()) { edges(head.key()).len() + 1 } else { 0nat };
        let position = choose |i: int| 0 <= i < search.todo.len() && search.todo[i] == Task::Visit(key);
        if position > 0 {
            assert(next.todo[position-1+extra] == Task::Visit(key));
        } else {
            assert(head == Task::Visit(key));
            if dfs::fresh(search, key) {
                assert(next.todo[edges(key).len() as int] == Task::Finish(key));
            } else {
                assert(kernel::enter((search.state)(key)) is Reuse
                    || kernel::enter((search.state)(key)) is BackEdge);
                assert((search.state)(key) == kernel::SOLVED || (search.state)(key) == kernel::IN_PROGRESS);
                if (search.state)(key) == kernel::IN_PROGRESS {
                    assert(search.todo.contains(Task::Finish(key)));
                    assert(false);
                }
            }
        }
    }
}

proof fn head_finish_reads_solved(search: Search, edges: Edges, count: nat)
    requires search.todo.len() > 0, search.todo.first() is Finish,
        dfs::bounded(search, edges, count), dfs::reads_available(search, edges),
        no_orphaned_slot(search, count), ordered_stack(search), ranked(edges, count),
    ensures forall |i: int| 0 <= i < edges(search.todo.first().key()).len()
        ==> (search.state)(#[trigger] edges(search.todo.first().key())[i]) == kernel::SOLVED,
{
    let head = search.todo.first();
    let key = head.key();
    assert(head == search.todo[0]);
    assert forall |i: int| 0 <= i < edges(key).len()
        implies (search.state)(#[trigger] edges(key)[i]) == kernel::SOLVED by {
        let read = edges(key)[i];
        assert(0 <= read < key);
        assert(!dfs::fresh(search, read));
        if (search.state)(read) != kernel::SOLVED {
            assert((search.state)(read) == kernel::IN_PROGRESS);
            let j = choose |j: int| 0 <= j < search.todo.len() && search.todo[j] == Task::Finish(read);
            if j == 0 { assert(read == key); }
            assert(key < search.todo[j].key());
        }
    }
}

proof fn replay_prepend(event: Event, tail: Seq<Event>, words: Storage, eval: Compute)
    ensures cycles::replay(seq![event] + tail, words, eval)
        == cycles::replay(tail, cycles::replay(seq![event], words, eval), eval),
    decreases tail.len(),
{
    if tail.len() != 0 {
        replay_prepend(event, tail.drop_last(), words, eval);
        assert((seq![event] + tail).drop_last() =~= seq![event] + tail.drop_last());
        assert((seq![event] + tail).last() == tail.last());
    } else {
        assert(seq![event] + tail =~= seq![event]);
    }
}

proof fn replay_one(event: Event, words: Storage, eval: Compute)
    ensures cycles::replay(seq![event], words, eval) == words.insert(event.target(), match event {
        Event::Begin { provisional, .. } => provisional,
        Event::Finish { key, reads } => eval(key, cycles::arguments(reads, words)),
    }),
{
    reveal_with_fuel(cycles::replay, 2);
    assert(seq![event].drop_last() =~= Seq::<Event>::empty());
    assert(seq![event].last() == event);
}

proof fn ranked_execution(
    search: Search, edges: Edges, provisional: spec_fn(int) -> Seq<u32>,
    words: Storage, eval: Compute, values: Seq<Seq<u32>>, fuel: nat, goal: int,
)
    requires
        ranked(edges, values.len()), fixed_point(edges, eval, values),
        dfs::bounded(search, edges, values.len()), dfs::active_finishes(search),
        dfs::reads_scheduled(search, edges), ordered_stack(search),
        no_orphaned_slot(search, values.len()), exact_settled(search, words, values),
        search.todo.len() + dfs::budget(search, edges, values.len()) <= fuel,
        0 <= goal < values.len(), queued_or_solved(search, goal),
    ensures ({
        let (events, done) = dfs::drive(search, edges, provisional, None, |_: int| true, fuel);
        let result = cycles::replay(events, words, eval);
        &&& done
        &&& result.contains_key(goal)
        &&& result[goal] == values[goal]
    }),
    decreases fuel,
{
    let count = values.len();
    if search.todo.len() == 0 {
        assert((search.state)(goal) == kernel::SOLVED);
        return;
    }
    let head = search.todo.first();
    let key = head.key();
    assert(head == search.todo[0]);
    let step = dfs::step(search, edges, provisional, None);
    let next_words = if step.event.is_some() {
        cycles::replay(seq![step.event.unwrap()], words, eval)
    } else { words };
    if let Some(event) = step.event { replay_one(event, words, eval); }
    ranked_stack_step(search, edges, provisional, count);
    requested_step(search, edges, provisional, count, goal);
    dfs::full_step_preserves_driver_invariants(search, edges, provisional, count);
    dfs::step_keeps_reads_scheduled(search, edges, provisional, None);
    if head is Finish {
        head_finish_reads_solved(search, edges, count);
        assert(step.event == Some(Event::Finish { key, reads: edges(key) }));
        assert(cycles::arguments(edges(key), words) =~= Seq::new(edges(key).len(), |i: int| values[edges(key)[i]])) by {
            assert forall |i: int| 0 <= i < edges(key).len()
                implies words[#[trigger] edges(key)[i]] == values[edges(key)[i]] by {
                assert(0 <= edges(key)[i] < key);
            }
        }
        assert(values[key] == eval(key, cycles::arguments(edges(key), words)));
        assert(next_words.contains_key(key) && next_words[key] == values[key]);
    }
    assert forall |k: int| 0 <= k < count && #[trigger] (step.next.state)(k) == kernel::SOLVED
        implies next_words.contains_key(k) && next_words[k] == values[k] by {
        if !(head is Finish && k == key) {
            assert((search.state)(k) == kernel::SOLVED);
            assert(words.contains_key(k) && words[k] == values[k]);
            if step.event.is_some() { assert(step.event.unwrap().target() != k); }
        }
    }
    ranked_execution(step.next, edges, provisional, next_words, eval, values, (fuel-1) as nat, goal);
    if let Some(event) = step.event {
        let tail = dfs::drive(step.next, edges, provisional, None, |_: int| true, (fuel-1) as nat).0;
        replay_prepend(event, tail, words, eval);
    }
}

/// A full traversal may request producers in any root order. Strictly lower
/// dependencies prevent a read from observing an in-progress producer.
/// Prepared words enter individually as already solved producers.
pub proof fn full_roots_match_ranked_values(
    roots: Seq<int>, state: spec_fn(int) -> u32, edges: Edges,
    provisional: spec_fn(int) -> Seq<u32>, words: Storage, eval: Compute,
    values: Seq<Seq<u32>>, goal: int,
)
    requires ranked(edges, values.len()), fixed_point(edges, eval, values),
        forall |k: int| 0 <= k < values.len() ==> #[trigger] state(k) != kernel::IN_PROGRESS,
        forall |k: int| 0 <= k < values.len() && #[trigger] state(k) == kernel::SOLVED
            ==> words.contains_key(k) && words[k] == values[k],
        forall |i: int| 0 <= i < roots.len() ==> 0 <= #[trigger] roots[i] < values.len(),
        0 <= goal < values.len(), roots.contains(goal) || state(goal) == kernel::SOLVED,
    ensures ({
        let search = Search { todo: dfs::requests(roots), state };
        let fuel = search.todo.len() + dfs::budget(search, edges, values.len());
        let (events, done) = dfs::drive(search, edges, provisional, None, |_: int| true, fuel);
        let result = cycles::replay(events, words, eval);
        &&& done
        &&& result.contains_key(goal)
        &&& result[goal] == values[goal]
    }),
{
    let search = Search { todo: dfs::requests(roots), state };
    assert forall |i: int| 0 <= i < search.todo.len() implies
        (#[trigger] search.todo[i]) == Task::Visit(roots[i]) by {}
    if roots.contains(goal) {
        let i = choose |i: int| 0 <= i < roots.len() && roots[i] == goal;
        assert(search.todo[i] == Task::Visit(goal));
    }
    ranked_execution(search, edges, provisional, words, eval, values,
        search.todo.len() + dfs::budget(search, edges, values.len()), goal);
}

pub open spec fn finish_one(edges: Edges, eval: Compute, key: int, earlier: Seq<Seq<u32>>) -> Seq<u32> {
    eval(key, Seq::new(edges(key).len(), |i: int| earlier[edges(key)[i]]))
}

spec fn ranked_values(edges: Edges, eval: Compute, count: nat) -> Seq<Seq<u32>>
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let key = count - 1;
        let earlier = ranked_values(edges, eval, key as nat);
        earlier.push(finish_one(edges, eval, key, earlier))
    }
}

proof fn ranked_values_solve_edges(edges: Edges, eval: Compute, count: nat)
    requires ranked(edges, count),
    ensures ranked_values(edges, eval, count).len() == count,
        fixed_point(edges, eval, ranked_values(edges, eval, count)),
    decreases count,
{
    if count > 0 {
        let key = count - 1;
        let prefix = ranked_values(edges, eval, key as nat);
        let all = ranked_values(edges, eval, count);
        assert(ranked(edges, key as nat));
        ranked_values_solve_edges(edges, eval, key as nat);
        assert forall |k: int| 0 <= k < count implies
            #[trigger] all[k] == finish_one(edges, eval, k, all) by {
            assert(Seq::new(edges(k).len(), |i: int| prefix[edges(k)[i]])
                =~= Seq::new(edges(k).len(), |i: int| all[edges(k)[i]])) by {
                assert forall |j: int| 0 <= j < edges(k).len()
                    implies prefix[#[trigger] edges(k)[j]] == all[edges(k)[j]] by {
                    assert(0 <= edges(k)[j] < k <= key);
                }
            }
            if k < key { assert(all[k] == prefix[k]); }
        }
    }
}

pub open spec fn queue_edges(graph: dependencies::Graph) -> Edges {
    |key: int| graph.reads[key]
}

pub open spec fn queue_finish(graph: dependencies::Graph, local: dependencies::Locals) -> Compute {
    |key: int, inputs: Seq<Seq<u32>>| (graph.eval)(key, local[key], inputs)
}

proof fn ranked_queue_values(graph: dependencies::Graph, local: dependencies::Locals, count: nat)
    ensures ranked_values(queue_edges(graph), queue_finish(graph, local), count)
        == dependencies::full_prefix(graph, local, count),
    decreases count,
{
    if count > 0 {
        let key = count - 1;
        ranked_queue_values(graph, local, key as nat);
    }
}

pub open spec fn tape_edges(order: sizing_tape::DependencyOrder) -> Edges {
    |key: int| order.reads[key]
}

pub open spec fn tape_finish(order: sizing_tape::DependencyOrder, local: sizing_tape::Inputs) -> Compute {
    |key: int, inputs: Seq<Seq<u32>>| (order.finish)(key, local[key], inputs)
}

proof fn ranked_tape_values(order: sizing_tape::DependencyOrder, local: sizing_tape::Inputs, count: nat)
    ensures ranked_values(tape_edges(order), tape_finish(order, local), count)
        == sizing_tape::fresh_prefix(order, local, count),
    decreases count,
{
    if count > 0 {
        let key = count - 1;
        ranked_tape_values(order, local, key as nat);
    }
}

pub proof fn queue_prefix_solves_edges(graph: dependencies::Graph, local: dependencies::Locals)
    requires graph.valid(),
    ensures ({
        let count = graph.reads.len();
        let values = dependencies::full_prefix(graph, local, count);
        &&& values.len() == count
        &&& ranked(queue_edges(graph), count)
        &&& fixed_point(queue_edges(graph), queue_finish(graph, local), values)
    }),
{
    let count = graph.reads.len();
    assert(ranked(queue_edges(graph), count));
    ranked_values_solve_edges(queue_edges(graph), queue_finish(graph, local), count);
    ranked_queue_values(graph, local, count);
}

pub proof fn tape_prefix_solves_edges(order: sizing_tape::DependencyOrder, local: sizing_tape::Inputs)
    requires order.ordered(),
    ensures ({
        let count = order.reads.len();
        let values = sizing_tape::fresh_prefix(order, local, count);
        &&& values.len() == count
        &&& ranked(tape_edges(order), count)
        &&& fixed_point(tape_edges(order), tape_finish(order, local), values)
    }),
{
    let count = order.reads.len();
    assert(ranked(tape_edges(order), count));
    ranked_values_solve_edges(tape_edges(order), tape_finish(order, local), count);
    ranked_tape_values(order, local, count);
}

/// An independent reference run using its canonical ordered roots and
/// initially prepared words. The producer key is its topological ordinal.
pub open spec fn full_run(
    roots: Seq<int>, state: spec_fn(int) -> u32, edges: Edges,
    provisional: spec_fn(int) -> Seq<u32>, words: Storage, eval: Compute, count: nat,
) -> Storage {
    let search = Search { todo: dfs::requests(roots), state };
    let fuel = search.todo.len() + dfs::budget(search, edges, count);
    cycles::replay(dfs::drive(search, edges, provisional, None, |_: int| true, fuel).0, words, eval)
}

pub open spec fn prepared_words(
    state: spec_fn(int) -> u32, words: Storage, recipe: Seq<Seq<u32>>,
) -> bool {
    forall |key: int| 0 <= key < recipe.len() ==> {
        &&& #[trigger] state(key) != kernel::IN_PROGRESS
        &&& state(key) == kernel::SOLVED ==> words.contains_key(key) && words[key] == recipe[key]
    }
}

/// The change-aware queue is compared with an independent DFS run, including
/// its initial preparation. The old words were computed from the old locals.
pub proof fn registered_queue_matches_full(
    graph: dependencies::Graph, prior: dependencies::Locals, current: dependencies::Locals,
    seeds: Set<int>, roots: Seq<int>, state: spec_fn(int) -> u32, words: Storage,
    provisional: spec_fn(int) -> Seq<u32>, key: int,
)
    requires
        graph.valid(), prior.len() == current.len() == graph.reads.len(),
        forall |k: int| 0 <= k < current.len() && prior[k] != current[k] ==> #[trigger] seeds.contains(k),
        prepared_words(state, words, dependencies::full_prefix(graph, current, graph.reads.len())),
        forall |i: int| 0 <= i < roots.len() ==> 0 <= #[trigger] roots[i] < graph.reads.len(),
        0 <= key < graph.reads.len(), roots.contains(key) || state(key) == kernel::SOLVED,
    ensures ({
        let count = graph.reads.len();
        let before = dependencies::full_prefix(graph, prior, count);
        let queue = dependencies::queue_prefix(graph, current, before, seeds, count);
        let full = full_run(roots, state, queue_edges(graph), provisional, words, queue_finish(graph, current), count);
        &&& queue.values.len() == count
        &&& full.contains_key(key)
        &&& queue.values[key] == full[key]
    }),
{
    let count = graph.reads.len();
    let edges = queue_edges(graph);
    let eval = queue_finish(graph, current);
    let before = dependencies::full_prefix(graph, prior, count);
    let after = dependencies::full_prefix(graph, current, count);
    queue_prefix_solves_edges(graph, prior);
    queue_prefix_solves_edges(graph, current);
    dependencies::queue_matches_full_prefix(graph, prior, current, before, seeds, count);
    full_roots_match_ranked_values(roots, state, edges, provisional, words, eval, after, key);
}

/// Replay of a complete reader closure is compared against the same fresh DFS
/// semantics as the ranked queue, including ready producer words.
pub proof fn retained_tape_matches_full(
    order: sizing_tape::DependencyOrder, prior: sizing_tape::Inputs, current: sizing_tape::Inputs,
    touched: Set<int>, roots: Seq<int>, state: spec_fn(int) -> u32, words: Storage,
    provisional: spec_fn(int) -> Seq<u32>, key: int,
)
    requires
        order.ordered(), order.closed(touched), prior.len() == current.len() == order.reads.len(),
        forall |k: int| 0 <= k < current.len() && prior[k] != current[k] ==> #[trigger] touched.contains(k),
        prepared_words(state, words, sizing_tape::fresh_prefix(order, current, order.reads.len())),
        forall |i: int| 0 <= i < roots.len() ==> 0 <= #[trigger] roots[i] < order.reads.len(),
        0 <= key < order.reads.len(), roots.contains(key) || state(key) == kernel::SOLVED,
    ensures ({
        let count = order.reads.len();
        let before = sizing_tape::fresh_prefix(order, prior, count);
        let tape = sizing_tape::replay_prefix(order, current, before, touched, count);
        let full = full_run(roots, state, tape_edges(order), provisional, words, tape_finish(order, current), count);
        &&& tape.len() == count
        &&& full.contains_key(key)
        &&& tape[key] == full[key]
    }),
{
    let count = order.reads.len();
    let edges = tape_edges(order);
    let eval = tape_finish(order, current);
    let before = sizing_tape::fresh_prefix(order, prior, count);
    let after = sizing_tape::fresh_prefix(order, current, count);
    tape_prefix_solves_edges(order, prior);
    tape_prefix_solves_edges(order, current);
    sizing_tape::replay_matches_fresh(order, prior, current, before, touched, count);
    full_roots_match_ranked_values(roots, state, edges, provisional, words, eval, after, key);
}

}
