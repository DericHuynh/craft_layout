//! Bounded native descent and the ordered spill to the sizing worklist.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::cycles::{dfs, kernel};
use super::sizing_requests::{self, Request, RequestAccess, RequestModel, RequestSource};
use core::marker::PhantomData;
use crate::vec_memory::VecMemory;
use crate::work_stack::{WorkStack, work_stack};

#[path = "sizing_stack/native.rs"]
mod native;
pub(crate) use native::{NativeAccess, NativeModel, drive};
#[cfg(test)]
pub(crate) use native::drive_spill;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[derive(Clone, Copy)]
pub(crate) enum Task<S, O> {
    Enter(S),
    Finish(O, bool),
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait TaskModel<S, O> {}

#[cfg(verus_keep_ghost)]
verus! {
// The resource boundary is the ordinary stack's allocation and copying of
// Copy items. The driver itself verifies how it uses the stack.
pub(crate) trait TaskModel<S, O> {
    spec fn tasks(&self) -> Seq<Task<S, O>>;
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait TaskStack<S: Copy, O: Copy>: TaskModel<S, O> {
    #[cfg_attr(verus_keep_ghost, verus_spec(n => ensures n == self.tasks().len(), no_unwind))]
    fn task_count(&self) -> usize;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).tasks() == old(self).tasks().push(task), no_unwind
    ))]
    fn push_task(&mut self, task: Task<S, O>);

    #[cfg_attr(verus_keep_ghost, verus_spec(task =>
        ensures
            if old(self).tasks().len() == 0 {
                task.is_none() && final(self).tasks() == old(self).tasks()
            } else {
                task == Some(old(self).tasks().last()) && final(self).tasks() == old(self).tasks().drop_last()
            },
        no_unwind
    ))]
    fn pop_task(&mut self) -> Option<Task<S, O>>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires start <= old(self).tasks().len(),
        ensures final(self).tasks().len() == old(self).tasks().len(),
            forall |i: int| 0 <= i < start ==> #[trigger] final(self).tasks()[i] == old(self).tasks()[i],
            forall |i: int| start <= i < old(self).tasks().len() ==>
                #[trigger] final(self).tasks()[i] == old(self).tasks()[start + old(self).tasks().len() - i - 1],
        no_unwind
    ))]
    fn reverse_from(&mut self, start: usize);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct TaskBuffer<S, O, M> {
    pending: WorkStack<Task<S, O>, 0>,
    memory: PhantomData<M>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<S, O, M> TaskBuffer<S, O, M> {
    #[verifier::type_invariant]
    spec fn invariant(&self) -> bool { self.pending.valid() }
}

impl<S, O, M> TaskModel<S, O> for TaskBuffer<S, O, M> {
    closed spec fn tasks(&self) -> Seq<Task<S, O>> { self.pending.items() }
}
}

#[cfg(not(verus_keep_ghost))]
impl<S, O, M> TaskModel<S, O> for TaskBuffer<S, O, M> {}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(buffer => ensures buffer.tasks().len() == 0, no_unwind))]
pub(crate) fn task_buffer<S: Copy, O: Copy, M: VecMemory>(spill: Vec<Task<S, O>>) -> TaskBuffer<S, O, M> {
    TaskBuffer { pending: work_stack::<_, 0, M>(spill), memory: PhantomData::<M> }
}

impl<S: Copy, O: Copy, M: VecMemory> TaskBuffer<S, O, M> {
    // Keep the allocation and discard inactive tasks so cloning LayoutData
    // does not copy a previous walk's scratch contents.
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(spill => ensures spill.len() == 0, no_unwind))]
    pub(crate) fn recycle(self) -> Vec<Task<S, O>> {
        let mut spill = self.pending.into_spill();
        M::clear(&mut spill);
        spill
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<S: Copy, O: Copy, M: VecMemory> TaskStack<S, O> for TaskBuffer<S, O, M> {
    #[inline(always)]
    fn task_count(&self) -> usize {
        #[cfg(verus_keep_ghost)]
        proof! { use_type_invariant(self); }
        self.pending.live_len()
    }

    #[inline(always)]
    fn push_task(&mut self, task: Task<S, O>) {
        #[cfg(verus_keep_ghost)]
        proof! { use_type_invariant(&*self); }
        self.pending.push::<M>(task);
    }

    #[inline(always)]
    fn pop_task(&mut self) -> Option<Task<S, O>> {
        #[cfg(verus_keep_ghost)]
        proof! { use_type_invariant(&*self); }
        self.pending.pop()
    }

    #[inline(always)]
    fn reverse_from(&mut self, start: usize) {
        #[cfg(verus_keep_ghost)]
        proof! { use_type_invariant(&*self); }
        self.pending.reverse_from(start);
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct RequestTasks<'a, V: RequestSource + ?Sized, S, O> {
    source: &'a V,
    tasks: S,
    opened: PhantomData<O>,
}

#[cfg(not(verus_keep_ghost))]
impl<V: RequestSource + ?Sized, S, O> RequestModel for RequestTasks<'_, V, S, O> {
    type Id = V::Id;
    type Source = V;
}

#[cfg(verus_keep_ghost)]
verus! {
impl<V: RequestSource + ?Sized, S: TaskModel<Request<V::Id>, O>, O>
    RequestModel for RequestTasks<'_, V, S, O>
{
    type Id = V::Id;
    type Source = V;
    type Event = Task<Request<V::Id>, O>;
    type Context = ();

    closed spec fn context(&self) -> Self::Context { () }

    closed spec fn topology(&self) -> sizing_requests::Topology<Self::Id> { self.source.topology() }
    closed spec fn projection(&self) -> spec_fn(Request<Self::Id>) -> Self::Event {
        |request: Request<Self::Id>| Task::Enter(request)
    }
    closed spec fn requests(&self) -> Seq<Self::Event> { self.tasks.tasks() }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<V: RequestSource + ?Sized, S: TaskStack<Request<V::Id>, O>, O: Copy>
    RequestAccess for RequestTasks<'_, V, S, O>
{
    #[inline(always)]
    fn source(&self) -> &Self::Source { self.source }

    #[inline(always)]
    fn emit(&mut self, slot: Request<Self::Id>) { self.tasks.push_task(Task::Enter(slot)); }
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn live_task_suffix<I: Copy, O>(tasks: Seq<Task<Request<I>, O>>, start: nat, live: Set<I>) -> bool {
    forall |i: int| start <= i < tasks.len() ==> match #[trigger] tasks[i] {
        Task::Enter(slot) => live.contains(slot.node),
        Task::Finish(_, _) => false,
    }
}

pub(crate) proof fn appended_slots_are_live<I: Copy, O>(
    topology: sizing_requests::Topology<I>, slot: Request<I>, live: Set<I>, prefix: Seq<Task<Request<I>, O>>,
)
    requires sizing_requests::live::closed(topology, live), live.contains(slot.node),
    ensures live_task_suffix(prefix + sizing_requests::inputs(topology, slot).map_values(
        |request: Request<I>| Task::<Request<I>, O>::Enter(request)), prefix.len(), live),
{
    sizing_requests::live::inputs_stay_live(topology, live, slot);
    let deps = sizing_requests::inputs(topology, slot);
    let pending = prefix + deps.map_values(|request: Request<I>| Task::<Request<I>, O>::Enter(request));
    assert forall |i: int| prefix.len() <= i < pending.len() implies match #[trigger] pending[i] {
        Task::Enter(dependency) => live.contains(dependency.node),
        Task::Finish(_, _) => false,
    } by {
        let slot = deps[i - prefix.len()];
        assert(pending[i] == Task::<Request<I>, O>::Enter(slot));
        assert(live.contains(slot.node));
    }
}

pub(crate) open spec fn owned_task_live<I, O>(task: Task<Request<I>, O>, live: Set<I>,
    owner: spec_fn(O) -> Request<I>,
) -> bool {
    match task {
        Task::Enter(slot) => live.contains(slot.node),
        Task::Finish(opened, _) => live.contains(owner(opened).node),
    }
}

pub(crate) open spec fn after_suffix_reverse(start: nat, end: nat, index: int) -> int {
    if index < start { index } else { start + end - index - 1 }
}

pub(crate) proof fn opened_task_path_stays_live<I: Copy, O: Copy>(
    topology: sizing_requests::Topology<I>, live: Set<I>, root: Request<I>,
    prefix: Seq<Task<Request<I>, O>>, opened: O, check: bool, owner: spec_fn(O) -> Request<I>,
)
    requires sizing_requests::live::closed(topology, live), live.contains(root.node),
        owner(opened) == root,
        forall |i: int| 0 <= i < prefix.len() ==> #[trigger] owned_task_live(prefix[i], live, owner),
    ensures ({
        let start = prefix.push(Task::Finish(opened, check));
        let queued = start + sizing_requests::inputs(topology, root).map_values(
            |slot: Request<I>| Task::<Request<I>, O>::Enter(slot));
        forall |j: int| 0 <= j < queued.len() ==>
            #[trigger] owned_task_live(queued[after_suffix_reverse(start.len(), queued.len(), j)],
                live, owner)
    }),
{
    let start = prefix.push(Task::Finish(opened, check));
    let queued = start + sizing_requests::inputs(topology, root).map_values(
        |slot: Request<I>| Task::<Request<I>, O>::Enter(slot));
    appended_slots_are_live(topology, root, live, start);
    assert forall |j: int| 0 <= j < queued.len() implies
        #[trigger] owned_task_live(queued[after_suffix_reverse(start.len(), queued.len(), j)],
            live, owner) by {
        if j < prefix.len() {
            assert(queued[j] == prefix[j]);
        } else if j == prefix.len() {
            assert(queued[j] == Task::Finish(opened, check));
        } else {
            let flipped = start.len() + queued.len() - j - 1;
            assert(start.len() <= flipped < queued.len());
            assert(queued[flipped] is Enter);
            if let Task::Enter(input) = queued[flipped] {
                assert(live.contains(input.node));
            }
        }
    }
}

}

/// Queue the actual ordered declaration and flow requests in the task stack.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires sizing_requests::ordered_children(source.topology(), slot),
    ensures result.tasks() == tasks.tasks() + sizing_requests::inputs(source.topology(), slot).map_values(
        |request: Request<V::Id>| Task::<Request<V::Id>, O>::Enter(request),
    ), forall |live: Set<V::Id>| sizing_requests::live::closed(source.topology(), live) && live.contains(slot.node)
        ==> #[trigger] live_task_suffix(result.tasks(), tasks.tasks().len(), live),
    no_unwind
))]
pub(crate) fn append_inputs<V: RequestSource + ?Sized, S: TaskStack<Request<V::Id>, O>, O: Copy>(
    source: &V, slot: Request<V::Id>, tasks: S,
) -> S {
    let pending = sizing_requests::request_inputs(RequestTasks { source, tasks, opened: PhantomData::<O> }, slot);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |live: Set<V::Id>| sizing_requests::live::closed(source.topology(), live) && live.contains(slot.node)
            implies #[trigger] live_task_suffix(pending.tasks.tasks(), tasks.tasks().len(), live) by {
            appended_slots_are_live(source.topology(), slot, live, tasks.tasks());
        }
    }
    pending.tasks
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait WorkModel {
    type Slot: Copy;
    type Opened: Copy;
    type Storage: TaskStack<Self::Slot, Self::Opened>;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait WorkModel {
    type Slot: Copy;
    type Opened: Copy;
    type Storage: TaskStack<Self::Slot, Self::Opened>;

    spec fn slot_key(slot: Self::Slot) -> int;
    spec fn opened_key(opened: Self::Opened) -> int;
    spec fn state(&self) -> spec_fn(int) -> u32;
    spec fn edges(&self) -> dfs::Edges;
}

pub(crate) open spec fn task_key<W: WorkModel + ?Sized>(task: Task<W::Slot, W::Opened>) -> dfs::Task {
    match task {
        Task::Enter(slot) => dfs::Task::Visit(W::slot_key(slot)),
        Task::Finish(opened, _) => dfs::Task::Finish(W::opened_key(opened)),
    }
}

pub(crate) open spec fn ready<W: WorkModel + ?Sized>(w: &W, key: int) -> bool {
    let entry = kernel::enter((w.state())(key));
    entry is Reuse || entry is BackEdge
}

pub(crate) open spec fn preserved_reads(before: spec_fn(int) -> u32, after: spec_fn(int) -> u32) -> bool {
    forall |key: int|
        before(key) == kernel::IN_PROGRESS || before(key) == kernel::SOLVED ==>
            (#[trigger] after(key)) == kernel::IN_PROGRESS || after(key) == kernel::SOLVED
}

proof fn step_keeps_ready_words(search: dfs::Search, edges: dfs::Edges, initial: spec_fn(int) -> Seq<u32>, key: int)
    requires search.todo.len() > 0,
        (search.state)(key) == kernel::IN_PROGRESS || (search.state)(key) == kernel::SOLVED,
    ensures (dfs::step(search, edges, initial, None).next.state)(key) == kernel::IN_PROGRESS
        || (dfs::step(search, edges, initial, None).next.state)(key) == kernel::SOLVED,
{
    match search.todo.first() {
        dfs::Task::Visit(target) => {
            if target == key { assert(!dfs::fresh(search, key)); }
        },
        dfs::Task::Finish(_) => {},
    }
}

pub(crate) open spec fn pending<W: WorkModel + ?Sized>(w: &W, tasks: &W::Storage) -> dfs::Search {
    let stack = tasks.tasks();
    dfs::Search {
        todo: Seq::new(stack.len(), |i: int| task_key::<W>(stack[stack.len() - i - 1])),
        state: w.state(),
    }
}

pub(crate) open spec fn set_phase(state: spec_fn(int) -> u32, key: int, phase: u32) -> spec_fn(int) -> u32 {
    |i: int| if key == i { phase } else { state(i) }
}

fn snapshot<W: WorkModel + ?Sized>(work: &W, tasks: &W::Storage)
    -> (saved: Ghost<(Seq<Task<W::Slot, W::Opened>>, dfs::Search)>)
    ensures saved@ == (tasks.tasks(), pending(work, tasks))
    no_unwind
{
    Ghost((tasks.tasks(), pending(work, tasks)))
}
}

/// The solver executes declarations, callbacks, and slot writes. Its graph
/// is fixed while this driver is active. A finish receives every declared
/// dependency in the in-progress or solved phase.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait SizingWork: WorkModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(check =>
        ensures check.is_none() == ready(old(self), Self::slot_key(slot)),
            final(self).state() == old(self).state(), final(self).edges() == old(self).edges(),
        no_unwind
    ))]
    fn enter(&mut self, slot: Self::Slot) -> Option<bool>;

    #[cfg_attr(verus_keep_ghost, verus_spec(opened =>
        requires !ready(old(self), Self::slot_key(slot)),
        ensures Self::opened_key(opened) == Self::slot_key(slot),
            final(self).state() == set_phase(old(self).state(), Self::slot_key(slot), kernel::IN_PROGRESS),
            final(self).edges() == old(self).edges(),
        no_unwind
    ))]
    fn open(&mut self, slot: Self::Slot, check: bool) -> Self::Opened;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires (old(self).state())(Self::opened_key(opened)) == kernel::IN_PROGRESS,
            forall |j: int| 0 <= j < (old(self).edges())(Self::opened_key(opened)).len()
                ==> ready(old(self), #[trigger] (old(self).edges())(Self::opened_key(opened))[j]),
        ensures final(self).state() == set_phase(old(self).state(), Self::opened_key(opened), kernel::SOLVED),
            final(self).edges() == old(self).edges(),
        no_unwind
    ))]
    fn finish(&mut self, opened: Self::Opened, check: bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(slot =>
        ensures Self::slot_key(slot) == Self::opened_key(opened), no_unwind
    ))]
    fn slot(&self, opened: Self::Opened) -> Self::Slot;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures ({
            let prefix = old(tasks).tasks();
            let after = final(tasks).tasks();
            let requests = (self.edges())(Self::slot_key(slot));
            &&& after.len() == prefix.len() + requests.len()
            &&& after.take(prefix.len() as int) == prefix
            &&& forall |j: int| 0 <= j < requests.len()
                ==> #[trigger] task_key::<Self>(after[prefix.len() + j]) == dfs::Task::Visit(requests[j])
        }),
        no_unwind
    ))]
    fn append_requests(&self, slot: Self::Slot, tasks: &mut Self::Storage);
}

/// Check cache/cycle state, then open only a slot that needs computation.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(start =>
    ensures
        final(work).edges() == old(work).edges(),
        match start {
            None => ready(old(work), W::slot_key(slot)) && final(work).state() == old(work).state(),
            Some((opened, _)) => !ready(old(work), W::slot_key(slot))
                && W::opened_key(opened) == W::slot_key(slot)
                && final(work).state() == set_phase(old(work).state(), W::slot_key(slot), kernel::IN_PROGRESS),
        },
    no_unwind
))]
pub(crate) fn begin<W: SizingWork + ?Sized>(work: &mut W, slot: W::Slot) -> Option<(W::Opened, bool)> {
    let Some(check) = work.enter(slot) else { return None; };
    Some((work.open(slot, check), check))
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(work).state() == old(work).state(), final(work).edges() == old(work).edges(),
        pending(final(work), final(tasks)).todo
            == dfs::requests((old(work).edges())(W::opened_key(opened)))
                + seq![dfs::Task::Finish(W::opened_key(opened))]
                + pending(old(work), old(tasks)).todo,
    no_unwind
))]
fn push_opened<W: SizingWork + ?Sized>(work: &mut W, tasks: &mut W::Storage, opened: W::Opened, check: bool) {
    tasks.push_task(Task::Finish(opened, check));
    let start = tasks.task_count();
    let slot = work.slot(opened);
    work.append_requests(slot, tasks);
    #[cfg(verus_keep_ghost)]
    let saved = snapshot(work, tasks);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(start == old(tasks).tasks().len() + 1);
        assert(saved@.0.take(start as int) == old(tasks).tasks().push(Task::Finish(opened, check)));
    }
    tasks.reverse_from(start);
    #[cfg(verus_keep_ghost)]
    proof! {
        let before = saved@.0;
        let visits = dfs::requests((work.edges())(W::opened_key(opened)));
        let after = pending(work, tasks).todo;
        let previous = pending(old(work), old(tasks)).todo;
        let wanted = visits + seq![dfs::Task::Finish(W::opened_key(opened))] + previous;
        assert(after =~= wanted) by {
            assert forall |j: int| 0 <= j < wanted.len() implies after[j] == wanted[j] by {
                let i = before.len() - j - 1;
                if j < visits.len() {
                    assert(i >= start && tasks.tasks()[i] == before[start+j]);
                } else if j == visits.len() {
                    assert(i == start-1);
                    assert(tasks.tasks()[i] == before[i]);
                    assert(before.take(start as int)[i] == Task::Finish(opened, check));
                    assert(i == start-1 && tasks.tasks()[i] == Task::Finish(opened, check));
                } else {
                    assert(i == old(tasks).tasks().len() - (j-visits.len()-1) - 1);
                    assert(tasks.tasks()[i] == before[i]);
                    assert(before.take(start as int)[i] == old(tasks).tasks()[i]);
                    assert(i < old(tasks).tasks().len() && tasks.tasks()[i] == old(tasks).tasks()[i]);
                }
            }
        }
    }
}

/// Finish the open slot and its dependency walk without recursive native
/// calls. Reverse only the new requests so pop retains the DFS callback order.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tasks).tasks().len() == 0,
        (old(work).state())(W::opened_key(opened)) == kernel::IN_PROGRESS,
        0 <= W::opened_key(opened) < universe@,
        dfs::bounded(pending(old(work), old(tasks)), old(work).edges(), universe@),
    ensures final(tasks).tasks().len() == 0, final(work).edges() == old(work).edges(),
        (final(work).state())(W::opened_key(opened)) == kernel::SOLVED,
        preserved_reads(old(work).state(), final(work).state()),
    no_unwind
))]
pub(crate) fn finish_worklist<W: SizingWork + ?Sized>(work: &mut W, opened: W::Opened, check: bool,
    tasks: &mut W::Storage, #[cfg(verus_keep_ghost)] universe: Ghost<nat>,
) {
    push_opened(work, tasks, opened, check);
    #[cfg(verus_keep_ghost)]
    proof! {
        let search = pending(work, tasks);
        let deps = dfs::requests((work.edges())(W::opened_key(opened)));
        assert(search.todo.take(deps.len() as int) =~= deps);
        assert(dfs::bounded(search, work.edges(), universe@)) by {
            assert forall |i: int| 0 <= i < search.todo.len()
                implies 0 <= (#[trigger] search.todo[i]).key() < universe@ by {
                if i < deps.len() { assert(search.todo[i] == deps[i]); }
            }
        }
        assert(dfs::reads_scheduled(search, work.edges())) by {
            assert forall |i: int, j: int| 0 <= i < search.todo.len() && search.todo[i] is Finish
                && 0 <= j < (work.edges())(search.todo[i].key()).len()
                && dfs::fresh(search, #[trigger] (work.edges())(search.todo[i].key())[j])
                implies search.todo.take(i).contains(dfs::Task::Visit((work.edges())(search.todo[i].key())[j])) by {
                assert(i == deps.len());
                assert(search.todo.take(i)[j] == dfs::Task::Visit((work.edges())(search.todo[i].key())[j]));
            }
        }
        assert(dfs::active_finishes(search));
        assert(search.todo[deps.len() as int] == dfs::Task::Finish(W::opened_key(opened)));
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant work.edges() == old(work).edges(),
            preserved_reads(old(work).state(), work.state()),
            dfs::bounded(pending(work, tasks), work.edges(), universe@),
            dfs::reads_scheduled(pending(work, tasks), work.edges()),
            dfs::active_finishes(pending(work, tasks)),
            dfs::pending_or_solved(pending(work, tasks), W::opened_key(opened)),
        decreases pending(work, tasks).todo.len() + dfs::budget(pending(work, tasks), work.edges(), universe@),
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        let saved = snapshot(work, tasks);
        let Some(task) = tasks.pop_task() else { return; };
        #[cfg(verus_keep_ghost)]
        proof! {
            let prior = saved@.1;
            let rest = pending(work, tasks);
            let init = |_: int| Seq::<u32>::empty();
            assert(prior.todo.first() == task_key::<W>(task));
            assert(rest.todo =~= prior.todo.drop_first());
            assert(rest.state == prior.state);
            dfs::step_keeps_reads_scheduled(prior, work.edges(), init, None);
            dfs::full_step_preserves_driver_invariants(prior, work.edges(), init, universe@);
            dfs::full_step_preserves_goal(prior, work.edges(), init, W::opened_key(opened));
        }
        match task {
            Task::Enter(slot) => {
                if let Some((opened, check)) = begin(work, slot) {
                    push_opened(work, tasks, opened, check);
                }
            }
            Task::Finish(opened, check) => {
                #[cfg(verus_keep_ghost)]
                proof! { assert(saved@.1.todo[0] == dfs::Task::Finish(W::opened_key(opened))); }
                work.finish(opened, check);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let init = |_: int| Seq::<u32>::empty();
            let after = dfs::step(saved@.1, work.edges(), init, None).next;
            assert(pending(work, tasks).todo =~= after.todo);
            assert(pending(work, tasks).state =~= after.state);
            assert forall |key: int| (old(work).state())(key) == kernel::IN_PROGRESS
                || (old(work).state())(key) == kernel::SOLVED implies
                    (#[trigger] (work.state())(key)) == kernel::IN_PROGRESS || (work.state())(key) == kernel::SOLVED by {
                assert((saved@.1.state)(key) == kernel::IN_PROGRESS || (saved@.1.state)(key) == kernel::SOLVED);
                step_keeps_ready_words(saved@.1, work.edges(), init, key);
            }
        }
    }
}
