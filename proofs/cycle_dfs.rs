//! Generate the cyclic transcript by DFS from ordered roots and adjacency.
//! Restricting to a region suppresses requests for resolved boundary slots.
//!
//! In the solver, solve_slot uses the verified enter() dispatch. A back edge
//! marks the cycle and returns with the provisional value still in its slot.
//! A numeric pass following a cycle uses the canonical full solve. Structural
//! measurement promotes a previously flagged ancestor when changed children or
//! nested sizing regions reach it. The free-parent case accepted by
//! try_refresh_independent_parent has no intrinsic or share reads from children.
//! Free-placed children also have no inbound sizing edge from their parent.
//! Calls to slots already seeded SOLVED are accounted for by ready_boundaries_emit_no_events.
//!
//! The finite-region theorem quantifies over ordered roots, edges and initial
//! slot states. For general adapters and optimized layout paths the application
//! must identify those roots and edges, show alignment of the initial states,
//! and supply a correct cached value wherever the region reads an external
//! dependency. Structural promotion of a flagged ancestor alone does not
//! establish all of these graph-cut and boundary-value conditions.
//! The theorem then derives both DFS transcripts and the equality of results.
use super::{Event, Storage, Compute, arguments, replay, kernel};
use vstd::prelude::*;

verus! {

pub enum Task { Visit(int), Finish(int) }
impl Task {
    pub open spec fn key(self) -> int {
        match self { Self::Visit(k) | Self::Finish(k) => k }
    }
}
pub type Region = spec_fn(int) -> bool;
pub type Edges = spec_fn(int) -> Seq<int>;

pub open spec fn requests(keys:Seq<int>) -> Seq<Task> {
    Seq::new(keys.len(),|i:int| Task::Visit(keys[i]))
}
pub open spec fn project(tasks:Seq<Task>, inside:Region) -> Seq<Task>
    decreases tasks.len(),
{
    if tasks.len() == 0 { Seq::empty() }
    else {
        let t = tasks.first();
        let suffix = project(tasks.drop_first(),inside);
        if inside(t.key()) { seq![t]+suffix } else { suffix }
    }
}
pub(crate) proof fn project_append(a:Seq<Task>, b:Seq<Task>, inside:Region)
    ensures project(a+b,inside) == project(a,inside)+project(b,inside),
    decreases a.len(),
{
    if a.len() > 0 {
        project_append(a.drop_first(),b,inside);
        assert((a+b).drop_first() =~= a.drop_first()+b);
        assert((a+b).first() == a.first());
    }
}
proof fn no_internal_requests(keys:Seq<int>, inside:Region)
    requires forall|i:int| 0 <= i < keys.len() ==> !inside(#[trigger] keys[i]),
    ensures project(requests(keys),inside).len() == 0,
    decreases keys.len(),
{
    if keys.len() > 0 {
        assert(requests(keys).drop_first() =~= requests(keys.drop_first()));
        assert forall|i:int| 0 <= i < keys.drop_first().len() implies
            !inside(#[trigger] keys.drop_first()[i]) by { assert(keys.drop_first()[i] == keys[i+1]); }
        no_internal_requests(keys.drop_first(),inside);
    }
}

pub struct Search {
    pub todo:Seq<Task>,
    pub state:spec_fn(int)->u32,
}
pub struct Iteration {
    pub next:Search,
    pub event:Option<Event>,
}

pub open spec fn step(s:Search, edges:Edges, initial:spec_fn(int)->Seq<u32>, restrict:Option<Region>) -> Iteration {
    let t = s.todo.first();
    let k = t.key();
    let rest = s.todo.drop_first();
    match t {
        Task::Visit(_) => {
            let action = kernel::enter((s.state)(k));
            if action is Reuse || action is BackEdge {
                Iteration { next:Search { todo:rest, state:s.state }, event:None }
            } else {
                let deps = requests(edges(k));
                let deps = match restrict { None => deps, Some(inside) => project(deps,inside) };
                Iteration {
                    next:Search { todo:deps+seq![Task::Finish(k)]+rest,
                        state:|i:int| if i == k {kernel::IN_PROGRESS} else {(s.state)(i)} },
                    event:Some(Event::Begin {key:k,provisional:initial(k)}),
                }
            }
        }
        Task::Finish(_) => Iteration {
            next:Search { todo:rest, state:|i:int| if i == k {kernel::SOLVED} else {(s.state)(i)} },
            event:Some(Event::Finish {key:k,reads:edges(k)}),
        }
    }
}

/// The Boolean indicates exhaustion of the work list. Fuel also describes every
/// finite prefix, including graphs supplied by a host that do not terminate.
pub open spec fn drive(s:Search, edges:Edges, initial:spec_fn(int)->Seq<u32>, restrict:Option<Region>,
    observe:Region, fuel:nat) -> (Seq<Event>,bool)
    decreases fuel,
{
    if s.todo.len() == 0 { (Seq::empty(),true) }
    else if fuel == 0 { (Seq::empty(),false) }
    else {
        let it = step(s,edges,initial,restrict);
        let tail = drive(it.next,edges,initial,restrict,observe,(fuel-1) as nat);
        match it.event {
            Some(event) if observe(event.target()) => (seq![event]+tail.0,tail.1),
            _ => tail,
        }
    }
}

pub open spec fn aligned(full:Search, partial:Search, inside:Region) -> bool {
    &&& partial.todo == project(full.todo,inside)
    &&& forall|i:int| #[trigger] inside(i) ==> (partial.state)(i) == (full.state)(i)
}

/// A full external request may be a ready boundary hit. When it must expand,
/// none of its dependencies may lead back into the region. This condition can
/// be checked on the full graph; cycles and arbitrary sharing inside are fine.
pub open spec fn isolated(full:Search, edges:Edges, inside:Region) -> bool {
    forall|k:int,j:int| !inside(k)
        && !(kernel::enter((full.state)(k)) is Reuse) && !(kernel::enter((full.state)(k)) is BackEdge)
        && 0 <= j < edges(k).len() ==> !inside(#[trigger] edges(k)[j])
}

pub proof fn restricted_dfs_generates_canonical_events(full:Search, partial:Search, edges:Edges,
    initial:spec_fn(int)->Seq<u32>, inside:Region, gas:nat, partial_gas:nat)
    requires
        aligned(full,partial,inside), isolated(full,edges,inside), gas <= partial_gas,
        drive(full,edges,initial,None,inside,gas).1,
    ensures
        drive(partial,edges,initial,Some(inside),inside,partial_gas).1,
        drive(partial,edges,initial,Some(inside),inside,partial_gas).0
            == drive(full,edges,initial,None,inside,gas).0,
    decreases gas,
{
    if full.todo.len() > 0 {
        let t = full.todo.first();
        let k = t.key();
        let a = step(full,edges,initial,None);
        let deps = requests(edges(k));
        let done = seq![Task::Finish(k)];
        assert(done.first() == Task::Finish(k));
        reveal_with_fuel(project,2);
        let rest = full.todo.drop_first();
        project_append(deps,done,inside);
        project_append(deps+done,rest,inside);
        assert(done.drop_first() =~= Seq::<Task>::empty());
        assert(isolated(a.next,edges,inside));
        if inside(k) {
            assert(partial.todo.first() == t);
            assert(partial.todo.drop_first() =~= project(rest,inside));
            let b = step(partial,edges,initial,Some(inside));
            assert(project(done,inside) =~= done);
            assert(a.event == b.event);
            assert(b.next.todo =~= project(a.next.todo,inside));
            assert forall|i:int| #[trigger] inside(i) implies (a.next.state)(i) == (b.next.state)(i) by {};
            assert(aligned(a.next,b.next,inside));
            restricted_dfs_generates_canonical_events(a.next,b.next,edges,initial,inside,
                (gas-1) as nat,(partial_gas-1) as nat);
        } else {
            if t is Visit && !(kernel::enter((full.state)(k)) is Reuse)
                && !(kernel::enter((full.state)(k)) is BackEdge) {
                no_internal_requests(edges(k),inside);
            }
            assert(project(done,inside) =~= Seq::<Task>::empty());
            assert(partial.todo =~= project(a.next.todo,inside));
            assert forall|i:int| #[trigger] inside(i) implies (a.next.state)(i) == (partial.state)(i) by {};
            assert(aligned(a.next,partial,inside));
            restricted_dfs_generates_canonical_events(a.next,partial,edges,initial,inside,(gas-1) as nat,partial_gas);
        }
    }
}

pub open spec fn fresh(s:Search,k:int) -> bool {
    let e = kernel::enter((s.state)(k));
    !(e is Reuse) && !(e is BackEdge)
}

/// A pending Finish has a preceding visit for each dependency that has yet
/// to be entered. Back edges already expose their provisional values.
pub open spec fn reads_scheduled(s: Search, edges: Edges) -> bool {
    forall |i: int, j: int| 0 <= i < s.todo.len() && s.todo[i] is Finish
        && 0 <= j < edges(s.todo[i].key()).len() && fresh(s, #[trigger] edges(s.todo[i].key())[j])
        ==> s.todo.take(i).contains(Task::Visit(edges(s.todo[i].key())[j]))
}

pub open spec fn reads_available(s: Search, edges: Edges) -> bool {
    s.todo.len() > 0 && s.todo.first() is Finish ==>
        forall |j: int| 0 <= j < edges(s.todo.first().key()).len()
            ==> !fresh(s, #[trigger] edges(s.todo.first().key())[j])
}

pub open spec fn ready_exterior(s: Search, restrict: Option<Region>) -> bool {
    match restrict {
        None => true,
        Some(inside) => forall |k: int| !inside(k) ==> !#[trigger] fresh(s,k),
    }
}

proof fn project_keeps_visit(keys: Seq<int>, inside: Region, key: int)
    requires keys.contains(key), inside(key),
    ensures project(requests(keys), inside).contains(Task::Visit(key)),
    decreases keys.len(),
{
    let head = keys.first();
    let tail = keys.drop_first();
    assert(requests(keys).first() == Task::Visit(head));
    assert(requests(keys).drop_first() =~= requests(tail));
    let earlier = choose |j: int| 0 <= j < keys.len() && keys[j] == key;
    if earlier != 0 {
        assert(tail[earlier - 1] == key);
        project_keeps_visit(tail, inside, key);
        let rest = project(requests(tail), inside);
        let found = choose |j: int| 0 <= j < rest.len() && rest[j] == Task::Visit(key);
        let i = if inside(head) { found + 1 } else { found };
        assert(project(requests(keys), inside)[i] == Task::Visit(key));
    } else {
        assert(project(requests(keys), inside)[0] == Task::Visit(key));
    }
}

pub(crate) proof fn step_keeps_reads_scheduled(s: Search, edges: Edges, initial: spec_fn(int) -> Seq<u32>,
    restrict: Option<Region>)
    requires s.todo.len() > 0, reads_scheduled(s, edges), ready_exterior(s, restrict),
    ensures reads_available(s, edges),
        reads_scheduled(step(s, edges, initial, restrict).next, edges),
        ready_exterior(step(s, edges, initial, restrict).next, restrict),
{
    let task = s.todo.first();
    let key = task.key();
    let after = step(s, edges, initial, restrict).next;
    let expands = task is Visit && fresh(s, key);
    let deps = match restrict {
        None => requests(edges(key)),
        Some(inside) => project(requests(edges(key)), inside),
    };
    let inserted = if expands { deps + seq![Task::Finish(key)] } else { Seq::empty() };
    assert(after.todo =~= inserted + s.todo.drop_first());
    assert(!fresh(after, key));
    assert forall |k: int| #[trigger] fresh(after, k) implies fresh(s, k) by {};
    if task is Finish {
        assert forall |j: int| 0 <= j < edges(key).len()
            implies !fresh(s, #[trigger] edges(key)[j]) by {
            assert(s.todo[0] == task);
            assert(s.todo.take(0) =~= Seq::<Task>::empty());
        }
    }
    assert forall |i: int, j: int| 0 <= i < after.todo.len() && after.todo[i] is Finish
        && 0 <= j < edges(after.todo[i].key()).len() && fresh(after, #[trigger] edges(after.todo[i].key())[j])
        implies after.todo.take(i).contains(Task::Visit(edges(after.todo[i].key())[j])) by {
        let dependency = edges(after.todo[i].key())[j];
        let visit = Task::Visit(dependency);
        if i < inserted.len() {
            assert(expands);
            if i < deps.len() {
                match restrict {
                    None => { assert(deps[i] is Visit); },
                    Some(inside) => { projected_requests_are_visits(edges(key), inside, i); },
                }
                assert(after.todo[i] == deps[i]);
                assert(false);
            }
            assert(i == deps.len() && after.todo[i] == Task::Finish(key));
            match restrict {
                None => { assert(deps[j] == visit); },
                Some(inside) => {
                    assert(inside(dependency));
                    assert(edges(key).contains(dependency));
                    project_keeps_visit(edges(key), inside, dependency);
                }
            }
            assert(after.todo.take(i) =~= deps);
        } else {
            let prior = i - inserted.len() + 1;
            assert(s.todo[prior] == after.todo[i]);
            assert(s.todo.take(prior).contains(visit));
            let before = choose |q: int| 0 <= q < prior && s.todo.take(prior)[q] == visit;
            assert(s.todo[before] == visit);
            if before == 0 {
                assert(key == dependency);
                assert(false);
            }
            let still_before = inserted.len() + before - 1;
            assert(after.todo.take(i)[still_before] == visit);
        }
    }
}

proof fn projected_requests_are_visits(keys: Seq<int>, inside: Region, i: int)
    requires 0 <= i < project(requests(keys), inside).len(),
    ensures project(requests(keys), inside)[i] is Visit,
    decreases keys.len(),
{
    let head = keys.first();
    let rest = keys.drop_first();
    assert(requests(keys).first() == Task::Visit(head));
    assert(requests(keys).drop_first() =~= requests(rest));
    if inside(head) {
        if i > 0 { projected_requests_are_visits(rest, inside, i - 1); }
    } else {
        projected_requests_are_visits(rest, inside, i);
    }
}

pub open spec fn available_through(s: Search, edges: Edges, initial: spec_fn(int) -> Seq<u32>,
    restrict: Option<Region>, steps: nat) -> bool
    decreases steps,
{
    steps == 0 || s.todo.len() == 0 || (reads_available(s, edges)
        && available_through(step(s, edges, initial, restrict).next, edges, initial, restrict,
            (steps - 1) as nat))
}

/// The full traversal and a restricted traversal with an already ready
/// exterior both reach every scheduled read after its dependency was entered.
pub proof fn dfs_roots_read_available_slots(roots: Seq<int>, state: spec_fn(int) -> u32,
    edges: Edges, initial: spec_fn(int) -> Seq<u32>, restrict: Option<Region>, steps: nat)
    requires ready_exterior(Search { todo: requests(roots), state }, restrict),
    ensures available_through(Search { todo: requests(roots), state }, edges, initial, restrict, steps),
{
    let s = Search { todo: requests(roots), state };
    assert forall |i: int| 0 <= i < s.todo.len() implies (#[trigger] s.todo[i]) is Visit by {};
    dfs_reads_available_slots(s, edges, initial, restrict, steps);
}

proof fn dfs_reads_available_slots(s: Search, edges: Edges, initial: spec_fn(int) -> Seq<u32>,
    restrict: Option<Region>, steps: nat)
    requires reads_scheduled(s, edges), ready_exterior(s, restrict),
    ensures available_through(s, edges, initial, restrict, steps),
    decreases steps,
{
    if steps > 0 && s.todo.len() > 0 {
        step_keeps_reads_scheduled(s, edges, initial, restrict);
        dfs_reads_available_slots(step(s, edges, initial, restrict).next, edges, initial, restrict,
            (steps - 1) as nat);
    }
}

/// Unopened nodes pay for their own finish task and every potential child
/// request. Dropping a hit uses one unit; expanding an unseen node also uses
/// one net unit after transferring its credit to the work list.
pub open spec fn budget(s:Search,edges:Edges,n:nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else {
        let k = n-1;
        budget(s,edges,k as nat) + if fresh(s,k) {edges(k).len()+1} else {0}
    }
}
pub open spec fn bounded(s:Search,edges:Edges,n:nat) -> bool {
    &&& forall|j:int| 0 <= j < s.todo.len() ==> 0 <= (#[trigger] s.todo[j]).key() < n
    &&& forall|k:int,j:int| 0 <= k < n && 0 <= j < edges(k).len() ==> 0 <= #[trigger] edges(k)[j] < n
}

/// Finish markers on an explicit stack belong to distinct open slots.
pub open spec fn active_finishes(s: Search) -> bool {
    &&& forall |i: int| 0 <= i < s.todo.len() && (#[trigger] s.todo[i]) is Finish
        ==> (s.state)(s.todo[i].key()) == kernel::IN_PROGRESS
    &&& forall |i: int, j: int| 0 <= i < j < s.todo.len()
        && (#[trigger] s.todo[i]) is Finish && (#[trigger] s.todo[j]) is Finish
        ==> s.todo[i].key() != s.todo[j].key()
}

pub open spec fn pending_or_solved(s: Search, k: int) -> bool {
    (s.state)(k) == kernel::SOLVED || s.todo.contains(Task::Finish(k))
}

pub(crate) proof fn full_step_preserves_goal(s: Search, edges: Edges,
    initial: spec_fn(int) -> Seq<u32>, goal: int)
    requires s.todo.len() > 0, pending_or_solved(s, goal),
    ensures pending_or_solved(step(s, edges, initial, None).next, goal),
{
    let head = s.todo.first();
    let next = step(s, edges, initial, None).next;
    if (next.state)(goal) != kernel::SOLVED {
        assert((s.state)(goal) != kernel::SOLVED);
        let i = choose |i: int| 0 <= i < s.todo.len() && s.todo[i] == Task::Finish(goal);
        if i == 0 { assert(head == Task::Finish(goal)); }
        let extra = if head is Visit && fresh(s, head.key()) { edges(head.key()).len() + 1 } else { 0nat };
        assert(next.todo[i - 1 + extra] == Task::Finish(goal));
    }
}

pub(crate) proof fn full_step_preserves_driver_invariants(s: Search, edges: Edges,
    initial: spec_fn(int) -> Seq<u32>, n: nat)
    requires s.todo.len() > 0, bounded(s, edges, n), active_finishes(s),
    ensures ({
        let next = step(s, edges, initial, None).next;
        &&& bounded(next, edges, n)
        &&& active_finishes(next)
        &&& next.todo.len() + budget(next, edges, n) < s.todo.len() + budget(s, edges, n)
    }),
{
    let head = s.todo.first();
    let k = head.key();
    let next = step(s, edges, initial, None).next;
    let deps = requests(edges(k));
    let expands = head is Visit && fresh(s, k);
    let extra = if expands { deps.len() + 1 } else { 0nat };
    assert(s.todo[0] == head);
    assert(next.todo.len() == s.todo.len() - 1 + extra);
    assert(!fresh(next,k));
    assert(!expands ==> !fresh(s,k));
    budget_change(s,next,edges,n,k);
    assert forall |i: int| 0 <= i < next.todo.len() implies 0 <= (#[trigger] next.todo[i]).key() < n by {
        if i < extra {
            if i == deps.len() { assert(next.todo[i] == Task::Finish(k)); }
            else { assert(next.todo[i] == Task::Visit(edges(k)[i])); }
        } else {
            assert(next.todo[i] == s.todo[i-extra+1]);
        }
    }
    assert forall |i: int| 0 <= i < next.todo.len() && (#[trigger] next.todo[i]) is Finish
        implies (next.state)(next.todo[i].key()) == kernel::IN_PROGRESS by {
        if i < extra {
            if i < deps.len() { assert(next.todo[i] is Visit); }
            assert(next.todo[i] == Task::Finish(k));
        } else {
            let prior = i-extra+1;
            assert(next.todo[i] == s.todo[prior]);
            assert((s.state)(s.todo[prior].key()) == kernel::IN_PROGRESS);
            if head is Finish { assert(s.todo[prior].key() != s.todo[0].key()); }
        }
    }
    assert forall |i: int, j: int| 0 <= i < j < next.todo.len()
        && (#[trigger] next.todo[i]) is Finish && (#[trigger] next.todo[j]) is Finish
        implies next.todo[i].key() != next.todo[j].key() by {
        if i < extra {
            assert(i == deps.len() && next.todo[i] == Task::Finish(k));
            let prior = j-extra+1;
            assert(next.todo[j] == s.todo[prior]);
            assert((s.state)(s.todo[prior].key()) == kernel::IN_PROGRESS);
        } else {
            assert(next.todo[i] == s.todo[i-extra+1]);
            assert(next.todo[j] == s.todo[j-extra+1]);
        }
    }
}
proof fn budget_change(a:Search, b:Search, edges:Edges,n:nat, key:int)
    requires forall|k:int| k != key ==> #[trigger] fresh(a,k) == fresh(b,k), !fresh(b,key),
    ensures budget(a,edges,n) == budget(b,edges,n) + if 0 <= key < n && fresh(a,key) {edges(key).len()+1} else {0},
    decreases n,
{
    if n > 0 { budget_change(a,b,edges,(n-1) as nat,key); }
}

pub proof fn finite_full_dfs_finishes(s:Search,edges:Edges,initial:spec_fn(int)->Seq<u32>,inside:Region,n:nat,gas:nat)
    requires bounded(s,edges,n), s.todo.len()+budget(s,edges,n) <= gas,
        // A finish token is emitted only after its node has been entered.
        forall|j:int| 0 <= j < s.todo.len() && (#[trigger] s.todo[j]) is Finish ==> !fresh(s,s.todo[j].key()),
    ensures drive(s,edges,initial,None,inside,gas).1,
    decreases gas,
{
    if s.todo.len() > 0 {
        let t = s.todo.first();
        let k = t.key();
        let a = step(s,edges,initial,None).next;
        let deps = requests(edges(k));
        assert(t == s.todo[0]);
        assert(bounded(a,edges,n)) by {
            assert forall|j:int| 0 <= j < a.todo.len() implies 0 <= (#[trigger] a.todo[j]).key() < n by {
                if t is Visit && fresh(s,k) {
                    if j < deps.len() { assert(a.todo[j] == Task::Visit(edges(k)[j])); }
                    else if j == deps.len() { assert(a.todo[j].key() == k); }
                    else { assert(a.todo[j] == s.todo[j-deps.len()]); }
                } else { assert(a.todo[j] == s.todo[j+1]); }
            }
        }
        assert(!fresh(a,k));
        budget_change(s,a,edges,n,k);
        assert forall|j:int| 0 <= j < a.todo.len() && (#[trigger] a.todo[j]) is Finish
            implies !fresh(a,a.todo[j].key()) by {
            if t is Visit && fresh(s,k) {
                if j < deps.len() { assert(a.todo[j] == Task::Visit(edges(k)[j])); }
                else if j == deps.len() { assert(a.todo[j].key() == k); }
                else { assert(a.todo[j] == s.todo[j-deps.len()]); }
            } else { assert(a.todo[j] == s.todo[j+1]); }
        }
        finite_full_dfs_finishes(a,edges,initial,inside,n,(gas-1) as nat);
    }
}

/// Starting with ordered root *requests* removes even the full-run termination
/// premise. The region may contain disjoint cycles and cached slots on either side.
pub proof fn finite_region_from_roots(roots:Seq<int>, inside:Region, edges:Edges, n:nat,
    full_state:spec_fn(int)->u32, partial_state:spec_fn(int)->u32, initial:spec_fn(int)->Seq<u32>)
    requires ({
        let s=Search {todo:requests(roots),state:full_state};
        &&& bounded(s,edges,n)
        &&& isolated(s,edges,inside)
        &&& forall|i:int| #[trigger] inside(i) ==> partial_state(i) == full_state(i)
    }),
    ensures ({
        let a=Search {todo:requests(roots),state:full_state};
        let b=Search {todo:project(requests(roots),inside),state:partial_state};
        let gas=a.todo.len()+budget(a,edges,n);
        &&& drive(a,edges,initial,None,inside,gas).1
        &&& drive(b,edges,initial,Some(inside),inside,gas).1
        &&& drive(a,edges,initial,None,inside,gas).0 == drive(b,edges,initial,Some(inside),inside,gas).0
    }),
{
    let a=Search {todo:requests(roots),state:full_state};
    let b=Search {todo:project(requests(roots),inside),state:partial_state};
    let gas=a.todo.len()+budget(a,edges,n);
    finite_full_dfs_finishes(a,edges,initial,inside,n,gas);
    restricted_dfs_generates_canonical_events(a,b,edges,initial,inside,gas,gas);
}

/// A slot already seeded as solved can be reached from either side of a
/// region. Calls into it emit no Begin or Finish, even if it appears in many
/// adjacency lists. Excluding such crossings leaves the same transcript.
pub proof fn ready_boundaries_emit_no_events(s:Search, edges:Edges, initial:spec_fn(int)->Seq<u32>,
    restrict:Option<Region>, inside:Region, ready:Region, gas:nat)
    requires
        forall|k:int| #[trigger] ready(k) ==> kernel::enter((s.state)(k)) is Reuse,
        forall|j:int| 0 <= j < s.todo.len() && (#[trigger] s.todo[j]) is Finish ==> !ready(s.todo[j].key()),
    ensures
        drive(s,edges,initial,restrict,inside,gas)
            == drive(s,edges,initial,restrict,|k:int| inside(k) && !ready(k),gas),
    decreases gas,
{
    if s.todo.len() > 0 && gas > 0 {
        let t = s.todo.first();
        let k = t.key();
        let a = step(s,edges,initial,restrict);
        assert(t == s.todo[0]);
        assert(a.event.is_some() ==> !ready(k));
        assert forall|j:int| 0 <= j < a.next.todo.len() && (#[trigger] a.next.todo[j]) is Finish
            implies !ready(a.next.todo[j].key()) by {
            if t is Visit && fresh(s,k) {
                let deps = requests(edges(k));
                let filtered = match restrict {
                    Some(scope) => {
                        only_requests_stay_requests(deps,scope);
                        project(deps,scope)
                    },
                    None => deps,
                };
                if j < filtered.len() { assert(a.next.todo[j] == filtered[j]); }
                else if j == filtered.len() { assert(a.next.todo[j].key() == k); }
                else { assert(a.next.todo[j] == s.todo[j - filtered.len()]); }
            } else { assert(a.next.todo[j] == s.todo[j+1]); }
        }
        ready_boundaries_emit_no_events(a.next,edges,initial,restrict,inside,ready,(gas-1) as nat);
    }
}

proof fn only_requests_stay_requests(tasks:Seq<Task>, scope:Region)
    requires forall|j:int| 0 <= j < tasks.len() ==> (#[trigger] tasks[j]) is Visit,
    ensures forall|j:int| 0 <= j < project(tasks,scope).len() ==> (#[trigger] project(tasks,scope)[j]) is Visit,
    decreases tasks.len(),
{
    if tasks.len() > 0 {
        let tail = tasks.drop_first();
        assert forall|j:int| 0 <= j < tail.len() implies (#[trigger] tail[j]) is Visit by {
            assert(tail[j] == tasks[j+1]);
        }
        only_requests_stay_requests(tail,scope);
        let filtered=project(tail,scope);
        assert forall|j:int| 0 <= j < project(tasks,scope).len() implies (#[trigger] project(tasks,scope)[j]) is Visit by {
            if scope(tasks.first().key()) && j>0 { assert(project(tasks,scope)[j] == filtered[j-1]); }
        }
    }
}

pub open spec fn visible(events:Seq<Event>, inside:Region) -> Seq<Event>
    decreases events.len(),
{
    if events.len() == 0 { Seq::empty() } else {
        let first=events.first();
        let rest=visible(events.drop_first(),inside);
        if inside(first.target()) {seq![first]+rest} else {rest}
    }
}

pub(crate) proof fn visibility_is_event_filter(s:Search, edges:Edges, initial:spec_fn(int)->Seq<u32>,
    inside:Region, gas:nat)
    ensures visible(drive(s,edges,initial,None,|_:int|true,gas).0,inside)
        == drive(s,edges,initial,None,inside,gas).0,
    decreases gas,
{
    if s.todo.len() > 0 && gas > 0 {
        let it=step(s,edges,initial,None);
        let next_gas=(gas-1) as nat;
        visibility_is_event_filter(it.next,edges,initial,inside,next_gas);
        let tail=drive(it.next,edges,initial,None,|_:int|true,next_gas).0;
        if let Some(e)=it.event {
            assert((seq![e]+tail).first()==e);
            assert((seq![e]+tail).drop_first() =~= tail);
        }
    }
}
proof fn visible_push(events:Seq<Event>,e:Event,inside:Region)
    ensures visible(events.push(e),inside) == (if inside(e.target()) {visible(events,inside).push(e)}
        else {visible(events,inside)}),
    decreases events.len(),
{
    reveal_with_fuel(visible,2);
    if events.len()>0 {
        assert(events.push(e).drop_first() =~= events.drop_first().push(e));
        visible_push(events.drop_first(),e,inside);
        assert(events.push(e).first()==events.first());
        let tail=visible(events.drop_first(),inside);
        assert((seq![events.first()]+tail).push(e) =~= seq![events.first()]+tail.push(e));
    }
}

pub proof fn visible_contains_only_inside(events: Seq<Event>, inside: Region)
    ensures forall |i: int| 0 <= i < visible(events, inside).len()
        ==> inside((#[trigger] visible(events, inside)[i]).target()),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let last = events.last();
        assert(prefix.push(last) =~= events);
        visible_push(prefix, last, inside);
        visible_contains_only_inside(prefix, inside);
        assert forall |i: int| 0 <= i < visible(events, inside).len()
            implies inside((#[trigger] visible(events, inside)[i]).target()) by {
            if i >= visible(prefix, inside).len() {
                assert(visible(events, inside)[i] == last);
            } else {
                assert(visible(events, inside)[i] == visible(prefix, inside)[i]);
            }
        }
    }
}

/// Boundary read agreement is only required at the time an internal invocation
/// reads an external slot. External entries may be overwritten elsewhere in the
/// full schedule. Internal entries start at the same bits or are initialized.
pub open spec fn boundary_cache(events:Seq<Event>, full:Storage, cached:Storage, inside:Region, eval:Compute) -> bool
    decreases events.len(),
{
    if events.len()==0 { true } else {
        let prefix=events.drop_last(); let e=events.last(); let reads=e.inputs();
        let before=replay(prefix,full,eval);
        &&& boundary_cache(prefix,full,cached,inside,eval)
        &&& inside(e.target()) ==> (forall|j:int| 0<=j<reads.len() && !inside(#[trigger] reads[j]) ==>
            before.contains_key(reads[j]) && cached.contains_key(reads[j]) && before[reads[j]]==cached[reads[j]])
    }
}

/// Use the unfiltered *full* execution as the reference. This handles
/// interleaved external finishes as well as internal back edges.
pub proof fn replay_projection(events:Seq<Event>, a:Storage,b:Storage,inside:Region,eval:Compute,k:int)
    requires boundary_cache(events,a,b,inside,eval),
        forall|i:int| #[trigger] inside(i) ==> a.contains_key(i) && b.contains_key(i) && a[i]==b[i],
    ensures ({
        let x=replay(events,a,eval);
        let y=replay(visible(events,inside),b,eval);
        &&& inside(k) ==> x.contains_key(k) && y.contains_key(k) && x[k]==y[k]
        &&& !inside(k) ==> y.contains_key(k)==b.contains_key(k) && (b.contains_key(k) ==> y[k]==b[k])
    }),
    decreases events.len(),
{
    if events.len()>0 {
        let prefix=events.drop_last();
        let e=events.last();
        replay_projection(prefix,a,b,inside,eval,k);
        assert(prefix.push(e) == events);
        visible_push(prefix,e,inside);
        let seen=visible(prefix,inside);
        assert(seen.push(e).drop_last()==seen);
        assert(seen.push(e).last()==e);
        if inside(k) && e.target()==k {
            if let Event::Finish {reads,..}=e {
                let x=replay(prefix,a,eval); let y=replay(seen,b,eval);
                assert(arguments(reads,x) =~= arguments(reads,y)) by {
                    assert forall|j:int| 0<=j<reads.len() implies x[#[trigger] reads[j]]==y[reads[j]] by {
                        let r=reads[j];
                        replay_projection(prefix,a,b,inside,eval,r);
                        if !inside(r) {
                            assert(events.last().inputs()[j]==r);
                            assert(x.contains_key(r) && b.contains_key(r) && x[r]==b[r]);
                        }
                    }
                }
            }
        }
    }
}

pub proof fn finite_region_rebuilds_full_values(roots:Seq<int>,inside:Region,edges:Edges,n:nat,
    full_state:spec_fn(int)->u32, partial_state:spec_fn(int)->u32, initial:spec_fn(int)->Seq<u32>,
    a:Storage,b:Storage,eval:Compute,k:int)
    requires
        inside(k),
        forall|i:int| #[trigger] inside(i) ==> full_state(i)==partial_state(i) && a.contains_key(i) && b.contains_key(i) && a[i]==b[i],
        ({
            let s=Search {todo:requests(roots),state:full_state};
            let gas=s.todo.len()+budget(s,edges,n);
            &&& bounded(s,edges,n) && isolated(s,edges,inside)
            &&& boundary_cache(drive(s,edges,initial,None,|_:int|true,gas).0,a,b,inside,eval)
        }),
    ensures ({
        let s=Search {todo:requests(roots),state:full_state};
        let region=Search {todo:project(requests(roots),inside),state:partial_state};
        let gas=s.todo.len()+budget(s,edges,n);
        let full=drive(s,edges,initial,None,|_:int|true,gas);
        let partial=drive(region,edges,initial,Some(inside),inside,gas);
        let x=replay(full.0,a,eval); let y=replay(partial.0,b,eval);
        &&& partial.1 && full.1
        &&& partial.0 == visible(full.0,inside)
        &&& x.contains_key(k) && y.contains_key(k) && x[k]==y[k]
    }),
{
    let s=Search {todo:requests(roots),state:full_state};
    let gas=s.todo.len()+budget(s,edges,n);
    finite_region_from_roots(roots,inside,edges,n,full_state,partial_state,initial);
    finite_full_dfs_finishes(s,edges,initial,|_:int|true,n,gas);
    visibility_is_event_filter(s,edges,initial,inside,gas);
    replay_projection(drive(s,edges,initial,None,|_:int|true,gas).0,a,b,inside,eval,k);
}

}
