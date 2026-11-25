use vstd::prelude::*;
use crate::queue_storage::tape_plan::{self, Event, EventModel, Ranked};
use crate::dependencies::sizing_requests::{self, Request, Topology};
use crate::declarations::{Axis, Size, Y};
use crate::cycles::kernel::Kind;
use crate::dependencies::rules::Form;
use crate::queue_storage::readers;


verus! {

pub type Datum = Seq<u32>;
pub type Inputs = Seq<Seq<u32>>;

pub struct DependencyOrder {
    pub reads: Seq<Seq<int>>,
    pub finish: spec_fn(int, Seq<u32>, Seq<Datum>) -> Datum,
}

impl DependencyOrder {
    pub open spec fn ordered(self) -> bool {
        forall |slot: int, input: int|
            0 <= slot < self.reads.len() && 0 <= input < self.reads[slot].len()
            ==> 0 <= #[trigger] self.reads[slot][input] < slot
    }

    pub open spec fn read(self, slot: int, values: Seq<Datum>) -> Seq<Datum> {
        Seq::new(self.reads[slot].len(), |index: int| values[self.reads[slot][index]])
    }

    pub open spec fn closed(self, touched: Set<int>) -> bool {
        forall |slot: int, input: int|
            0 <= slot < self.reads.len() && 0 <= input < self.reads[slot].len()
            && touched.contains(#[trigger] self.reads[slot][input])
            ==> touched.contains(slot)
    }
}

pub open spec fn fresh_prefix(order: DependencyOrder, local: Inputs, count: nat) -> Seq<Datum>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let slot = count - 1;
        let previous = fresh_prefix(order, local, slot as nat);
        previous.push((order.finish)(slot, local[slot], order.read(slot, previous)))
    }
}

pub open spec fn replay_prefix(
    order: DependencyOrder, local: Inputs, settled: Seq<Datum>, touched: Set<int>, count: nat,
) -> Seq<Datum>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let slot = count - 1;
        let previous = replay_prefix(order, local, settled, touched, slot as nat);
        let value = if touched.contains(slot) {
            (order.finish)(slot, local[slot], order.read(slot, previous))
        } else {
            settled[slot]
        };
        previous.push(value)
    }
}

/// Ordered replay is exact when the retained slot set contains every edited
/// local input and every downstream dependency. A datum can contain the
/// complete producer publication, including marks and paired metric words.
pub proof fn replay_matches_fresh(
    order: DependencyOrder, old_local: Inputs, local: Inputs, settled: Seq<Datum>,
    touched: Set<int>, count: nat,
)
    requires
        order.ordered(), order.closed(touched),
        count <= order.reads.len(),
        old_local.len() == order.reads.len(), local.len() == order.reads.len(),
        settled.len() == order.reads.len(),
        forall |slot: int| 0 <= slot < local.len() && old_local[slot] != local[slot]
            ==> #[trigger] touched.contains(slot),
        forall |slot: int| 0 <= slot < settled.len()
            ==> #[trigger] settled[slot] == (order.finish)(slot, old_local[slot], order.read(slot, settled)),
    ensures
        replay_prefix(order, local, settled, touched, count).len() == count,
        replay_prefix(order, local, settled, touched, count) == fresh_prefix(order, local, count),
        forall |slot: int| 0 <= slot < count && !touched.contains(slot)
            ==> #[trigger] replay_prefix(order, local, settled, touched, count)[slot] == settled[slot],
    decreases count,
{
    if count == 0 { return; }
    let slot = count - 1;
    replay_matches_fresh(order, old_local, local, settled, touched, slot as nat);
    let prior = replay_prefix(order, local, settled, touched, slot as nat);
    let current = replay_prefix(order, local, settled, touched, count);
    if !touched.contains(slot) {
        assert(order.read(slot, prior) =~= order.read(slot, settled)) by {
            assert forall |i: int| 0 <= i < order.reads[slot].len()
                implies prior[#[trigger] order.reads[slot][i]] == settled[order.reads[slot][i]] by {
                let input = order.reads[slot][i];
                assert(!touched.contains(input));
            }
        }
        assert(old_local[slot] == local[slot]);
    }
    assert(current == fresh_prefix(order, local, count));
    assert forall |i: int| 0 <= i < count && !touched.contains(i)
        implies #[trigger] current[i] == settled[i] by {
        if i < slot { assert(current[i] == prior[i]); }
    }
}


pub(crate) open spec fn projected_requests<I: Copy>(log: Seq<(I, Axis, Kind)>) -> Seq<Request<I>> {
    log.map_values(|entry: (I, Axis, Kind)| sizing_requests::target(entry.0, entry.1 is Y, entry.2))
}

proof fn close_one_reader<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>, producer: Request<S::Id>, reader: Request<S::Id>,
)
    requires tape_plan::covers_readers(source, wrap, steps, steps.len() as int),
        tape_plan::scheduled(steps).contains(producer),
        tape_plan::eligible(source, wrap, reader),
        tape_plan::calls(source, Event::Readers(producer)).contains(reader),
    ensures tape_plan::scheduled(steps).contains(reader),
{
    tape_plan::describe_membership(steps);
    let discovered = choose |i: int| 0 <= i < steps.len() && (#[trigger] steps[i]).request == producer;
    assert(tape_plan::covers_event(source, wrap, steps, Event::Readers(steps[discovered].request)));
    let calls = tape_plan::calls(source, Event::Readers(producer));
    let called = choose |i: int| 0 <= i < calls.len() && #[trigger] calls[i] == reader;
    assert(tape_plan::eligible(source, wrap, calls[called]));
}

/// Composes the actual EvenShare notification with the later native request
/// for the opposite-axis Flow. The adapter's ordinary notification may add
/// a prefix of other requests before it runs the Wrap dispatcher.
pub(crate) proof fn captured_wrap_share_wakes_cross_flow<S: EventModel + ?Sized>(
    source: &S, steps: Seq<Ranked<S::Id>>, topology: Topology<S::Id>, node: S::Id, main: Axis,
)
    requires
        tape_plan::covers_readers(source, true, steps, steps.len() as int), source.wrap_queue(),
        match (tape_plan::capture_reader_inputs(source).parameters)(node).children_layout {
            crate::declarations::ChildrenLayout::Wrap { axis, .. } => axis == main,
            _ => false,
        },
        (topology.flow_mode)(node) == sizing_requests::FlowMode::Wrap(main is Y),
        tape_plan::scheduled(steps).contains(sizing_requests::target(node, main is Y, Kind::EvenShare)),
        tape_plan::eligible(source, true, sizing_requests::target(node, readers::wrap_cross_axis(main) is Y, Kind::Flow)),
    ensures ({
        let flow = sizing_requests::target(node, readers::wrap_cross_axis(main) is Y, Kind::Flow);
        let share = sizing_requests::target(node, main is Y, Kind::EvenShare);
        tape_plan::scheduled(steps).contains(flow)
            && sizing_requests::inputs(topology, flow).len() > 0
            && sizing_requests::inputs(topology, flow)[0] == share
    }),
{
    let inputs = tape_plan::capture_reader_inputs(source);
    readers::native_wrap_share_requests_flow(inputs, topology, node, main);
    let cross = readers::wrap_cross_axis(main);
    let flow = sizing_requests::target(node, cross is Y, Kind::Flow);
    let share = sizing_requests::target(node, main is Y, Kind::EvenShare);
    reveal(tape_plan::source_reader_calls);
    let ordinary = readers::share_readers(inputs, node, main, inputs.links.children[node].len());
    let source_log = tape_plan::source_reader_calls(inputs, true, Event::Readers(share));
    assert(source_log[ordinary.len() as int] == (node, cross, Kind::Flow));
    assert(tape_plan::calls(source, Event::Readers(share))[ordinary.len() as int] == flow);
    close_one_reader(source, true, steps, share, flow);
}

/// The retained schedule cannot omit a settled Fill declaration which reads
/// its parent's main-axis share in the actual forward dispatcher.
pub(crate) proof fn captured_share_wakes_fill_child<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>,
    topology: Topology<S::Id>, parent: S::Id, at: int, axis: Axis, kind: Kind,
)
    requires
        tape_plan::covers_readers(source, wrap, steps, steps.len() as int),
        source.wrap_queue() == wrap,
        kind is Regular || kind is Min || kind is Max,
        ({
            let inputs = tape_plan::capture_reader_inputs(source);
            let child = inputs.links.children[parent][at];
            let slot = sizing_requests::target(child, axis is Y, kind);
            let producer = sizing_requests::target(parent, axis is Y, Kind::EvenShare);
            &&& inputs.links.children.contains_key(parent)
            &&& 0 <= at < inputs.links.children[parent].len()
            &&& !(inputs.parameters)(child).disabled
            &&& readers::stack_parent_of(inputs, child, axis) == Some(parent)
            &&& (inputs.declaration)(child, axis, kind) == Some(Size::Fill)
            &&& (topology.form)(slot) == Some(Form::Fill)
            &&& (topology.stack_parent)(slot) == readers::stack_parent_of(inputs, child, axis)
            &&& tape_plan::eligible(source, wrap, slot)
            &&& tape_plan::scheduled(steps).contains(producer)
        }),
    ensures ({
        let inputs = tape_plan::capture_reader_inputs(source);
        let child = inputs.links.children[parent][at];
        let slot = sizing_requests::target(child, axis is Y, kind);
        let producer = sizing_requests::target(parent, axis is Y, Kind::EvenShare);
        tape_plan::scheduled(steps).contains(slot) && sizing_requests::inputs(topology, slot) == seq![producer]
    }),
{
    let inputs = tape_plan::capture_reader_inputs(source);
    readers::requests_native_share_reader(inputs, topology, parent, at, axis, kind);
    let child = inputs.links.children[parent][at];
    let slot = sizing_requests::target(child, axis is Y, kind);
    let producer = sizing_requests::target(parent, axis is Y, Kind::EvenShare);
    let log = readers::share_readers(inputs, parent, axis, inputs.links.children[parent].len());
    let notified = choose |i: int| 0 <= i < log.len() && #[trigger] log[i] == (child, axis, kind);
    reveal(tape_plan::source_reader_calls);
    let source_log = tape_plan::source_reader_calls(inputs, wrap, Event::Readers(producer));
    assert(source_log[notified] == (child, axis, kind));
    assert(tape_plan::calls(source, Event::Readers(producer))[notified] == slot);
    close_one_reader(source, wrap, steps, producer, slot);
}

/// A successful native capture closes the affected part of an ordered
/// dependency graph when the reader dispatch includes each matching forward
/// edge. The edge premise is pointwise, so callers can discharge it using
/// the corresponding declaration, share, grid, or Wrap reader rule.
pub(crate) proof fn captured_readers_close<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>,
    keys: Seq<Request<S::Id>>, order: DependencyOrder, affected: Set<int>,
)
    requires
        order.ordered(), keys.len() == order.reads.len(),
        tape_plan::covers_readers(source, wrap, steps, steps.len() as int),
        forall |i: int| 0 <= i < keys.len() ==>
            #[trigger] affected.contains(i) == tape_plan::scheduled(steps).contains(keys[i]),
        forall |slot: int, input: int| 0 <= slot < keys.len() && 0 <= input < order.reads[slot].len()
            ==> ({
                let reader = keys[slot];
                let producer = keys[#[trigger] order.reads[slot][input]];
                &&& tape_plan::eligible(source, wrap, reader)
                &&& tape_plan::calls(source, Event::Readers(producer)).contains(reader)
            }),
    ensures order.closed(affected),
{
    assert forall |slot: int, input: int|
        0 <= slot < order.reads.len() && 0 <= input < order.reads[slot].len()
        && affected.contains(#[trigger] order.reads[slot][input])
        implies affected.contains(slot) by {
        let producer_index = order.reads[slot][input];
        let producer = keys[producer_index];
        let reader = keys[slot];
        assert(tape_plan::scheduled(steps).contains(producer));
        close_one_reader(source, wrap, steps, producer, reader);
    }
}


/// A physical publication model. Each row owns its scalar slot bits and any
/// associated producer output, such as cells or line metrics.
pub(crate) struct SlotProgram<I> {
    pub keys: Seq<Request<I>>,
    pub order: DependencyOrder,
    pub previous_inputs: Inputs,
    pub inputs: Inputs,
}

impl<I> SlotProgram<I> {
    pub(crate) open spec fn valid(self) -> bool {
        self.order.ordered() && self.keys.no_duplicates()
            && self.keys.len() == self.order.reads.len()
            && self.keys.len() == self.previous_inputs.len()
            && self.keys.len() == self.inputs.len()
    }

    pub(crate) open spec fn position(self, slot: Request<I>) -> int {
        self.keys.index_of_first(slot).unwrap()
    }

    pub(crate) open spec fn selected(self, steps: Seq<Ranked<I>>) -> Set<int> {
        steps.map_values(|step: Ranked<I>| self.position(step.request)).to_set()
    }

    pub(crate) open spec fn word_at(self, words: Seq<Datum>, slot: int) -> Datum {
        (self.order.finish)(slot, self.inputs[slot], self.order.read(slot, words))
    }

    pub(crate) open spec fn fresh(self) -> Seq<Datum> {
        fresh_prefix(self.order, self.inputs, self.keys.len())
    }

    pub(crate) open spec fn previous(self, words: Seq<Datum>) -> bool {
        words.len() == self.keys.len()
            && forall |i: int| 0 <= i < words.len() ==>
                #[trigger] words[i] == (self.order.finish)(i, self.previous_inputs[i], self.order.read(i, words))
    }

    pub(crate) open spec fn live_plan(self, steps: Seq<Ranked<I>>) -> bool {
        forall |i: int| 0 <= i < steps.len() ==> self.keys.contains((#[trigger] steps[i]).request)
    }

    pub(crate) open spec fn inputs_covered(self, selected: Set<int>) -> bool {
        forall |i: int| 0 <= i < self.keys.len() && self.previous_inputs[i] != self.inputs[i]
            ==> #[trigger] selected.contains(i)
    }

    pub(crate) open spec fn ready_plan(self, steps: Seq<Ranked<I>>) -> bool {
        &&& self.live_plan(steps)
        &&& self.order.closed(self.selected(steps))
        &&& self.inputs_covered(self.selected(steps))
        &&& forall |i: int, j: int| 0 <= i < steps.len()
            && 0 <= j < self.order.reads[self.position(steps[i].request)].len()
            ==> ({
                let dependency = #[trigger] self.order.reads[self.position(steps[i].request)][j];
                self.selected(steps).contains(dependency)
                    ==> self.selected(steps.take(i)).contains(dependency)
            })
    }

    pub(crate) open spec fn replayed_prefix(self, previous: Seq<Datum>, words: Seq<Datum>, prefix: Seq<Ranked<I>>) -> bool {
        words.len() == self.keys.len()
            && forall |i: int| 0 <= i < self.keys.len() ==> {
                #[trigger] words[i] == if self.selected(prefix).contains(i) { self.fresh()[i] } else { previous[i] }
            }
    }
}

/// Event coverage and rank evidence needed to interpret a native resize
/// capture as an ordered execution of a particular sizing program.
pub(crate) struct CaptureInputs<I> {
    pub(crate) root: I,
    pub(crate) axes: crate::queue_storage::tape::Axes,
    pub(crate) declarations: Seq<(I, readers::NodeChange)>,
    pub(crate) content: Seq<I>,
}

impl<I> CaptureInputs<I> {
    pub(crate) open spec fn contains(self, event: Event<I>) -> bool {
        match event {
            Event::Viewport(node, axis) => node == self.root
                && (if axis is Y { self.axes.vertical } else { self.axes.horizontal }),
            Event::Declaration(node, change) => self.declarations.contains((node, change)),
            Event::Content(node) => self.content.contains(node),
            Event::Readers(_) => false,
        }
    }
}

pub(crate) type CaptureDispatch<I> = (spec_fn(Event<I>) -> Seq<Request<I>>, spec_fn(Request<I>) -> Option<u16>);

pub(crate) open spec fn capture_dispatch<S: EventModel + ?Sized>(source: &S) -> CaptureDispatch<S::Id> {
    let inputs = tape_plan::capture_reader_inputs(source);
    let wrap = source.wrap_queue();
    (|event: Event<S::Id>| tape_plan::project_reader_calls(inputs, wrap, event), tape_plan::capture_ranks(source))
}

pub(crate) open spec fn dispatchable<I>(dispatch: CaptureDispatch<I>, wrap: bool, request: Request<I>) -> bool {
    (dispatch.1)(request).is_some() && (wrap || !(request.kind is Flow))
}

pub(crate) open spec fn capture_bindings<I>(
    dispatch: CaptureDispatch<I>, wrap: bool, program: SlotProgram<I>, inputs: CaptureInputs<I>,
) -> bool {
    &&& program.valid()
    &&& forall |request: Request<I>| #[trigger] dispatchable(dispatch, wrap, request)
        ==> program.keys.contains(request)
    &&& forall |reader: int, read: int| 0 <= reader < program.keys.len()
        && 0 <= read < program.order.reads[reader].len() ==> {
        let producer = program.keys[#[trigger] program.order.reads[reader][read]];
        let consumer = program.keys[reader];
        &&& dispatchable(dispatch, wrap, consumer)
        &&& (dispatch.1)(producer).is_some()
        &&& (dispatch.1)(producer).unwrap() < (dispatch.1)(consumer).unwrap()
        &&& (dispatch.0)(Event::Readers(producer)).contains(consumer)
    }
    &&& forall |index: int| 0 <= index < program.keys.len()
        && program.previous_inputs[index] != program.inputs[index] ==> {
        let request = #[trigger] program.keys[index];
        &&& dispatchable(dispatch, wrap, request)
        &&& exists |event: Event<I>| inputs.contains(event)
            && #[trigger] (dispatch.0)(event).contains(request)
    }
}

proof fn scheduled_position<I>(program: SlotProgram<I>, steps: Seq<Ranked<I>>, position: int)
    requires program.valid(), program.live_plan(steps), 0 <= position < program.keys.len(),
    ensures program.selected(steps).contains(position) == tape_plan::scheduled(steps).contains(program.keys[position]),
{
    let positions = steps.map_values(|step: Ranked<I>| program.position(step.request));
    positions.to_set_ensures();
    tape_plan::describe_membership(steps);
    if positions.contains(position) {
        let i = choose |i: int| 0 <= i < positions.len() && #[trigger] positions[i] == position;
        let request = steps[i].request;
        program.keys.index_of_first_ensures(request);
        assert(program.keys[position] == request);
        assert(tape_plan::request_at(steps, request, steps.len() as int));
    } else if tape_plan::scheduled(steps).contains(program.keys[position]) {
        let request = program.keys[position];
        let i = choose |i: int| 0 <= i < steps.len() && (#[trigger] steps[i]).request == request;
        program.keys.index_of_first_ensures(request);
        assert(program.keys[program.position(request)] == request);
        assert(program.position(request) == position);
        assert(positions[i] == position);
    }
}

proof fn captured_event<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>, input: CaptureInputs<S::Id>,
    admitted: crate::queue_storage::tape::Axes, event: Event<S::Id>, request: Request<S::Id>,
)
    requires admitted.covers(input.axes), input.contains(event),
        tape_plan::covers_seeds(source, wrap, steps, input.root, admitted, input.declarations, input.content),
        tape_plan::calls(source, event).contains(request), tape_plan::eligible(source, wrap, request),
    ensures tape_plan::scheduled(steps).contains(request),
{
    match event {
        Event::Viewport(node, axis) => {
            if axis is Y {
                assert(tape_plan::covers_event(source, wrap, steps, Event::Viewport(node, Y)));
            } else {
                assert(axis == crate::declarations::X);
            }
        },
        Event::Declaration(node, change) => {
            let i = choose |i: int| 0 <= i < input.declarations.len() && #[trigger] input.declarations[i] == (node, change);
            assert(tape_plan::covers_event(source, wrap, steps,
                Event::Declaration(input.declarations[i].0, input.declarations[i].1)));
        },
        Event::Content(node) => {
            let i = choose |i: int| 0 <= i < input.content.len() && #[trigger] input.content[i] == node;
            assert(tape_plan::covers_event(source, wrap, steps, Event::Content(input.content[i])));
        },
        Event::Readers(_) => {},
    }
    assert(tape_plan::covers_event(source, wrap, steps, event));
    let requests = tape_plan::calls(source, event);
    let i = choose |i: int| 0 <= i < requests.len() && #[trigger] requests[i] == request;
    assert(tape_plan::eligible(source, wrap, requests[i]));
}

pub(crate) proof fn capture_readies_program<S: EventModel + ?Sized>(
    source: &S, wrap: bool, steps: Seq<Ranked<S::Id>>, program: SlotProgram<S::Id>,
    inputs: CaptureInputs<S::Id>, admitted: crate::queue_storage::tape::Axes,
)
    requires
        capture_bindings(capture_dispatch(source), wrap, program, inputs), admitted.covers(inputs.axes),
        tape_plan::settled_steps(source, wrap, steps),
        tape_plan::ordered_prefix(steps, steps.len() as int),
        tape_plan::covers_seeds(source, wrap, steps, inputs.root, admitted, inputs.declarations, inputs.content),
        tape_plan::covers_readers(source, wrap, steps, steps.len() as int),
    ensures program.ready_plan(steps),
{
    let dispatch = capture_dispatch(source);
    assert forall |i: int| 0 <= i < steps.len() implies program.keys.contains((#[trigger] steps[i]).request) by {
        assert(tape_plan::eligible(source, wrap, steps[i].request));
        assert(dispatchable(dispatch, wrap, steps[i].request));
    }
    let selected = program.selected(steps);
    assert forall |i: int| 0 <= i < program.keys.len()
        implies #[trigger] selected.contains(i) == tape_plan::scheduled(steps).contains(program.keys[i]) by {
        scheduled_position(program, steps, i);
    }
    captured_readers_close(source, wrap, steps, program.keys, program.order, selected);
    assert forall |i: int| 0 <= i < program.keys.len() && program.previous_inputs[i] != program.inputs[i]
        implies #[trigger] selected.contains(i) by {
        let request = program.keys[i];
        assert(exists |event: Event<S::Id>| inputs.contains(event) && #[trigger] (dispatch.0)(event).contains(request));
        let event = choose |event: Event<S::Id>| inputs.contains(event) && #[trigger] (dispatch.0)(event).contains(request);
        captured_event(source, wrap, steps, inputs, admitted, event, request);
    }
    tape_plan::describe_membership(steps);
    assert forall |i: int, j: int| 0 <= i < steps.len()
        && 0 <= j < program.order.reads[program.position(steps[i].request)].len() implies ({
            let producer = #[trigger] program.order.reads[program.position(steps[i].request)][j];
            selected.contains(producer) ==> program.selected(steps.take(i)).contains(producer)
        }) by {
        let consumer = program.position(steps[i].request);
        program.keys.index_of_first_ensures(steps[i].request);
        let producer = program.order.reads[consumer][j];
        if selected.contains(producer) {
            let request = program.keys[producer];
            assert(tape_plan::scheduled(steps).contains(request));
            let before = choose |k: int| 0 <= k < steps.len() && (#[trigger] steps[k]).request == request;
            assert(tape_plan::settled(source, request) == Some(steps[before].rank));
            assert(tape_plan::settled(source, steps[i].request) == Some(steps[i].rank));
            assert(steps[before].rank < steps[i].rank);
            assert(before < i);
            let prefix = steps.take(i);
            assert(prefix[before] == steps[before]);
            assert(program.live_plan(prefix));
            tape_plan::describe_membership(prefix);
            assert(tape_plan::request_at(prefix, request, prefix.len() as int));
            scheduled_position(program, prefix, producer);
        }
    }
}

pub(crate) proof fn start_physical_replay<I>(program: SlotProgram<I>, previous: Seq<Datum>)
    requires program.valid(), program.previous(previous),
    ensures program.replayed_prefix(previous, previous, Seq::empty()),
{
    let empty = Seq::<Ranked<I>>::empty();
    let indices = empty.map_values(|step: Ranked<I>| program.position(step.request));
    assert(indices =~= Seq::<int>::empty());
    indices.to_set_ensures();
}

proof fn fresh_prefix_has_equation(order: DependencyOrder, local: Inputs, len: nat)
    requires order.ordered(), len <= order.reads.len(),
    ensures fresh_prefix(order, local, len).len() == len,
        forall |slot: int| 0 <= slot < len ==>
            #[trigger] fresh_prefix(order, local, len)[slot]
                == (order.finish)(slot, local[slot], order.read(slot, fresh_prefix(order, local, len))),
    decreases len,
{
    if len == 0 { return; }
    let last = len - 1;
    fresh_prefix_has_equation(order, local, last as nat);
    let earlier = fresh_prefix(order, local, last as nat);
    let now = fresh_prefix(order, local, len);
    assert forall |slot: int| 0 <= slot < len implies
        #[trigger] now[slot] == (order.finish)(slot, local[slot], order.read(slot, now)) by {
        assert(order.read(slot, earlier) =~= order.read(slot, now)) by {
            assert forall |i: int| 0 <= i < order.reads[slot].len()
                implies earlier[#[trigger] order.reads[slot][i]] == now[order.reads[slot][i]] by {
                assert(order.reads[slot][i] < last);
            }
        }
        if slot < last { assert(now[slot] == earlier[slot]); }
    }
}

pub(crate) proof fn advance_physical_replay<I>(
    program: SlotProgram<I>, previous: Seq<Datum>, words: Seq<Datum>, steps: Seq<Ranked<I>>, at: int,
)
    requires
        program.valid(), program.previous(previous), program.ready_plan(steps),
        0 <= at < steps.len(), program.replayed_prefix(previous, words, steps.take(at)),
    ensures ({
        let slot = program.position(steps[at].request);
        &&& 0 <= slot < words.len()
        &&& program.replayed_prefix(previous, words.update(slot, program.word_at(words, slot)), steps.take(at + 1))
    }),
{
    let before = steps.take(at);
    let after = steps.take(at + 1);
    assert(after =~= before.push(steps[at]));
    let request = steps[at].request;
    program.keys.index_of_first_ensures(request);
    let slot = program.position(request);
    let selected = program.selected(steps);
    replay_matches_fresh(program.order, program.previous_inputs, program.inputs, previous, selected, program.keys.len());
    fresh_prefix_has_equation(program.order, program.inputs, program.keys.len());
    let fresh = program.fresh();
    assert(program.order.read(slot, words) =~= program.order.read(slot, fresh)) by {
        assert forall |i: int| 0 <= i < program.order.reads[slot].len() implies {
            let dependency = #[trigger] program.order.reads[slot][i];
            words[dependency] == fresh[dependency]
        } by {
            let dependency = program.order.reads[slot][i];
            if program.selected(steps).contains(dependency) {
                assert(program.selected(before).contains(dependency));
            } else if !program.selected(before).contains(dependency) {
                assert(previous[dependency] == fresh[dependency]);
            }
        }
    }
    let positions = before.map_values(|step: Ranked<I>| program.position(step.request));
    let next_positions = after.map_values(|step: Ranked<I>| program.position(step.request));
    assert(next_positions =~= positions.push(slot));
    positions.lemma_push_to_set_commute(slot);
    assert(program.selected(after) =~= program.selected(before).insert(slot));
    let updated = words.update(slot, program.word_at(words, slot));
    assert forall |i: int| 0 <= i < program.keys.len() implies
        #[trigger] updated[i] == if program.selected(after).contains(i) { fresh[i] } else { previous[i] } by {
        if i != slot { assert(updated[i] == words[i]); }
    }
}

pub(crate) proof fn end_physical_replay<I>(
    program: SlotProgram<I>, previous: Seq<Datum>, words: Seq<Datum>, steps: Seq<Ranked<I>>,
)
    requires
        program.valid(), program.previous(previous), program.ready_plan(steps),
        program.replayed_prefix(previous, words, steps),
    ensures words == program.fresh(),
{
    replay_matches_fresh(program.order, program.previous_inputs, program.inputs, previous,
        program.selected(steps), program.keys.len());
    fresh_prefix_has_equation(program.order, program.inputs, program.keys.len());
    assert(words =~= program.fresh()) by {
        assert forall |i: int| 0 <= i < words.len() implies
            #[trigger] words[i] == program.fresh()[i] by {
            if !program.selected(steps).contains(i) {
                assert(program.fresh()[i] == previous[i]);
            }
        }
    }
}


impl<I> SlotProgram<I> {
    pub(crate) open spec fn queue_sound(self, words: Seq<Datum>, pending: Set<int>) -> bool {
        words.len() == self.keys.len()
            && forall |i: int| 0 <= i < words.len() && !pending.contains(i)
                ==> #[trigger] words[i] == self.word_at(words, i)
    }
}

/// Seeding each changed local input establishes the queue invariant before
/// the first ranked dequeue. Unchanged local equations already hold.
pub(crate) proof fn seeded_queue_words<I>(program: SlotProgram<I>, words: Seq<Datum>, pending: Set<int>)
    requires program.valid(), program.previous(words),
        forall |i: int| 0 <= i < words.len() && program.previous_inputs[i] != program.inputs[i]
            ==> #[trigger] pending.contains(i),
    ensures program.queue_sound(words, pending),
{
    assert forall |i: int| 0 <= i < words.len() && !pending.contains(i)
        implies #[trigger] words[i] == program.word_at(words, i) by {
        assert(program.previous_inputs[i] == program.inputs[i]);
    }
}

pub(crate) proof fn published_and_notified<I>(
    program: SlotProgram<I>, before: Seq<Datum>, after: Seq<Datum>,
    pending_before: Set<int>, pending_after: Set<int>, slot: int,
)
    requires
        program.valid(), program.queue_sound(before, pending_before), 0 <= slot < before.len(),
        after == before.update(slot, program.word_at(before, slot)),
        pending_before.remove(slot).subset_of(pending_after),
        forall |i: int| 0 <= i < before.len() && i != slot && before[slot] != after[slot]
            && program.order.reads[i].contains(slot) ==> #[trigger] pending_after.contains(i),
    ensures program.queue_sound(after, pending_after),
{
    assert forall |i: int| 0 <= i < after.len() && !pending_after.contains(i) implies
        #[trigger] after[i] == program.word_at(after, i) by {
        assert(program.order.read(i, before) =~= program.order.read(i, after)) by {
            assert forall |j: int| 0 <= j < program.order.reads[i].len() implies
                before[#[trigger] program.order.reads[i][j]] == after[program.order.reads[i][j]] by {
                let input = program.order.reads[i][j];
                if input == slot {
                    assert(input < i);
                    assert(program.order.reads[i].contains(slot));
                    assert(before[slot] == after[slot]);
                }
            }
        }
        if i != slot {
            assert(!pending_before.contains(i));
            assert(after[i] == before[i]);
        }
    }
}

pub(crate) proof fn settled_queue_words<I>(program: SlotProgram<I>, words: Seq<Datum>)
    requires program.valid(), program.queue_sound(words, Set::empty()),
    ensures words == program.fresh(),
{
    exact_settled_prefix(program, words, program.keys.len());
    assert(words.take(words.len() as int) =~= words);
}

proof fn exact_settled_prefix<I>(program: SlotProgram<I>, words: Seq<Datum>, count: nat)
    requires program.valid(), program.queue_sound(words, Set::empty()), count <= words.len(),
    ensures words.take(count as int) == fresh_prefix(program.order, program.inputs, count),
    decreases count,
{
    if count == 0 {
        assert(words.take(count as int) =~= Seq::<Datum>::empty());
        return;
    }
    let at = count - 1;
    exact_settled_prefix(program, words, at as nat);
    let earlier = words.take(at as int);
    assert(program.order.read(at, words) =~= program.order.read(at, earlier)) by {
        assert forall |j: int| 0 <= j < program.order.reads[at].len() implies
            words[#[trigger] program.order.reads[at][j]] == earlier[program.order.reads[at][j]] by {
            assert(program.order.reads[at][j] < at);
        }
    }
    assert(words.take(count as int) =~= earlier.push(words[at]));
}

}
