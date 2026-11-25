//! Compare successful sizing routes with an independent full layout.
use crate::prepare_frame::FrameWords;
use vstd::prelude::*;
use crate::cycles::{Compute, Event, Storage, kernel, replay};
use crate::cycles::dfs::Region;
use crate::replay_view::{self, Draw, PlaceNode, Placements, Replay};
use crate::retained_view::{self, Outputs};
use crate::publication::{self, FrameResult};
use crate::queue_storage::numeric;
use crate::sizing_pass::{self, FullMeasurement, FullSizing};
use crate::dependencies::{sizing_finish, sizing_requests};
use crate::{Geometry, Key, RectBits, Work, dependencies, mixed_regions, production_schedule, ranked_full,
    replay_publication, replay_retained, sizing_tape};

verus! {

pub enum Sizing {
    Queue {
        graph: dependencies::Graph,
        prior_locals: dependencies::Locals,
        current_locals: dependencies::Locals,
        seeds: Set<int>,
    },
    Tape {
        order: sizing_tape::DependencyOrder,
        prior_inputs: sizing_tape::Inputs,
        current_inputs: sizing_tape::Inputs,
        touched: Set<int>,
    },
    Regions {
        edit: replay_retained::Edit,
        cuts: Seq<Region>,
        prior_storage: Storage,
    },
    RootReplay,
}

pub open spec fn table(values: Seq<Seq<u32>>) -> Storage {
    Map::new(Seq::new(values.len(), |key: int| key).to_set(), |key: int| values[key])
}

proof fn table_contains(values: Seq<Seq<u32>>, key: int)
    requires 0 <= key < values.len(),
    ensures table(values).contains_key(key), table(values)[key] == values[key],
{
    let keys = Seq::new(values.len(), |index: int| index);
    assert(keys[key] == key);
    assert(keys.contains(key));
    keys.to_set_ensures();
}

impl Sizing {
    pub open spec fn words(self, reference: Replay) -> Storage {
        let count = reference.n;
        match self {
            Sizing::Queue { graph, prior_locals: prior, current_locals: current, seeds } => {
                let before = dependencies::full_prefix(graph, prior, count);
                table(dependencies::queue_prefix(graph, current, before, seeds, count).values)
            },
            Sizing::Tape { order, prior_inputs: prior, current_inputs: current, touched } => {
                let before = sizing_tape::fresh_prefix(order, prior, count);
                table(sizing_tape::replay_prefix(order, current, before, touched, count))
            },
            Sizing::Regions { edit, cuts, prior_storage } => mixed_regions::run(edit.new, cuts, prior_storage),
            Sizing::RootReplay => reference.rebuilt_sizing(),
        }
    }

    pub open spec fn valid(self, reference: Replay) -> bool {
        let count = reference.n;
        let roots = production_schedule::walk(reference.visits);
        match self {
            Sizing::Queue { graph, prior_locals: prior, current_locals: current, seeds } => {
                &&& graph.valid() && count == graph.reads.len()
                &&& prior.len() == current.len() == count
                &&& reference.edges == ranked_full::queue_edges(graph)
                &&& reference.eval == ranked_full::queue_finish(graph, current)
                &&& ranked_full::prepared_words(reference.initial_state, reference.initial,
                    dependencies::full_prefix(graph, current, count))
                &&& forall |k: int| 0 <= k < count && prior[k] != current[k]
                    ==> #[trigger] seeds.contains(k)
                &&& forall |i: int| 0 <= i < roots.len() ==> 0 <= #[trigger] roots[i] < count
            },
            Sizing::Tape { order, prior_inputs: prior, current_inputs: current, touched } => {
                &&& order.ordered() && order.closed(touched) && count == order.reads.len()
                &&& prior.len() == current.len() == count
                &&& reference.edges == ranked_full::tape_edges(order)
                &&& reference.eval == ranked_full::tape_finish(order, current)
                &&& ranked_full::prepared_words(reference.initial_state, reference.initial,
                    sizing_tape::fresh_prefix(order, current, count))
                &&& forall |k: int| 0 <= k < count && prior[k] != current[k]
                    ==> #[trigger] touched.contains(k)
                &&& forall |i: int| 0 <= i < roots.len() ==> 0 <= #[trigger] roots[i] < count
            },
            Sizing::Regions { edit, cuts, prior_storage: prior } => {
                &&& edit.new == reference && edit.same_shell() && mixed_regions::runnable(reference, cuts, prior)
                &&& forall |k: int| 0 <= k < count ==> #[trigger] prior.contains_key(k)
                &&& forall |k: int| #[trigger] reference.inside(k)
                    == mixed_regions::includes(reference, cuts, k)
                &&& forall |k: int| #[trigger] edit.outside(k) ==> prior[k] == edit.old.full_sizing()[k]
                &&& forall |k: int| 0 <= k < count ==> #[trigger] reference.initial.contains_key(k)
            },
            Sizing::RootReplay => reference.closed(),
        }
    }

    pub open spec fn available(self, reference: Replay, key: int) -> bool {
        0 <= key < reference.n && match self {
            Sizing::Queue { .. } | Sizing::Tape { .. } => {
                production_schedule::walk(reference.visits).contains(key)
                    || (reference.initial_state)(key) == kernel::SOLVED
            },
            Sizing::Regions { .. } => true,
            Sizing::RootReplay => reference.inside(key),
        }
    }
}

/// Every word used by placement comes from its own successful sizing route.
/// The reference computation uses the same document's full root sequence.
pub proof fn exact_sizing_word(sizing: Sizing, reference: Replay, key: int)
    requires sizing.valid(reference), sizing.available(reference, key),
    ensures sizing.words(reference).contains_key(key), reference.full_sizing().contains_key(key),
        sizing.words(reference)[key] == reference.full_sizing()[key],
{
    let count = reference.n;
    let roots = production_schedule::walk(reference.visits);
    match sizing {
        Sizing::Queue { graph, prior_locals: prior, current_locals: current, seeds } => {
            ranked_full::registered_queue_matches_full(graph, prior, current, seeds, roots,
                reference.initial_state, reference.initial, reference.provisional, key);
            let before = dependencies::full_prefix(graph, prior, count);
            table_contains(dependencies::queue_prefix(graph, current, before, seeds, count).values, key);
        },
        Sizing::Tape { order, prior_inputs: prior, current_inputs: current, touched } => {
            ranked_full::retained_tape_matches_full(order, prior, current, touched, roots,
                reference.initial_state, reference.initial, reference.provisional, key);
            let before = sizing_tape::fresh_prefix(order, prior, count);
            table_contains(sizing_tape::replay_prefix(order, current, before, touched, count), key);
        },
        Sizing::Regions { edit, cuts, prior_storage: prior } => {
            mixed_regions::mixed_regions_match_fresh_sizing(edit, cuts, prior, key);
            // Full execution starts with a word for every producer. Replay
            // replaces existing words, including provisional words on cycles.
            replay_preserves_key(reference.full_events(), reference.initial, reference.eval, key);
        },
        Sizing::RootReplay => replay_view::rebuilt_producers_match_the_document(reference, key),
    }
}

proof fn replay_preserves_key(events: Seq<Event>, initial: Storage, eval: Compute, key: int)
    requires initial.contains_key(key),
    ensures replay(events, initial, eval).contains_key(key),
    decreases events.len(),
{
    if events.len() > 0 { replay_preserves_key(events.drop_last(), initial, eval, key); }
}

pub struct Placement {
    pub nodes: Seq<PlaceNode>,
    pub draw: Draw,
    pub plan: spec_fn(Key) -> Work,
    pub previous: Placements,
    pub host: Outputs,
}

impl Placement {
    pub open spec fn valid(self, reference: Replay) -> bool {
        let full = replay_view::place_frame(self.nodes, reference.full_sizing(), self.draw);
        &&& replay_publication::sound(self.previous, self.draw)
        &&& replay_publication::retained_outputs_are_sound(self.previous, self.host)
        &&& forall |i: int, j: int| 0 <= i < j < self.nodes.len()
            ==> (#[trigger] self.nodes[i]).key != (#[trigger] self.nodes[j]).key
        &&& forall |i: int| 0 <= i < self.nodes.len() ==> {
            let key = (#[trigger] self.nodes[i]).key;
            let work = (self.plan)(key);
            &&& crate::valid_route(work)
            &&& !crate::requested(work) ==> self.previous.contains_key(key)
                && replay_publication::local_input_matches(self.previous[key], full[key])
        }
    }
}

/// From completed sizing and exact placement inputs, derive equality of the
/// ordered retained view, including the entries for which no write is issued.
pub proof fn successful_frame_publishes_fresh_view(sizing: Sizing, reference: Replay, output: Placement)
    requires sizing.valid(reference), output.valid(reference),
        forall |i: int, j: int| 0 <= i < output.nodes.len() && 0 <= j < output.nodes[i].inputs.len()
            ==> sizing.available(reference, (#[trigger] output.nodes[i].inputs[j]).producer),
    ensures ({
        let retained = replay_publication::commit(output.nodes, sizing.words(reference), output.draw,
            output.plan, output.host);
        let fresh = replay_view::place_frame(output.nodes, reference.full_sizing(), output.draw);
        let keys = Seq::new(output.nodes.len(), |i: int| output.nodes[i].key);
        &&& replay_publication::retained_outputs_are_sound(fresh, retained)
        &&& retained_view::emitted_view(keys, retained) == replay_view::ordered_view(output.nodes, fresh)
    }),
{
    let nodes = output.nodes;
    let old = sizing.words(reference);
    let full = reference.full_sizing();
    assert forall |i: int, j: int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len() implies {
        let producer = (#[trigger] nodes[i].inputs[j]).producer;
        old.contains_key(producer) && full.contains_key(producer) && old[producer] == full[producer]
    } by { exact_sizing_word(sizing, reference, nodes[i].inputs[j].producer); }
    replay_publication::sizing_and_placement_publish_fresh_view(
        nodes, old, full, output.draw, output.plan, output.previous, output.host,
    );
}

/// Connect the sizing and placement theorem to the host's observed writes.
/// The two streams each expose the selected IDs and their own local recipe
/// outputs. No equality between the input streams is required.
pub proof fn successful_frame_matches_observed_full_view(
    sizing: Sizing, reference: Replay, output: Placement,
    incremental_writes: Seq<(Key, Geometry)>, full_writes: Seq<(Key, Geometry)>,
)
    requires sizing.valid(reference), output.valid(reference),
        forall |i: int, j: int| 0 <= i < output.nodes.len() && 0 <= j < output.nodes[i].inputs.len()
            ==> sizing.available(reference, (#[trigger] output.nodes[i].inputs[j]).producer),
        incremental_writes == replay_publication::placement_rows(output.nodes, sizing.words(reference),
            output.draw, |key: Key| crate::writes((output.plan)(key))),
        full_writes == replay_publication::placement_rows(output.nodes, reference.full_sizing(),
            output.draw, |_: Key| true),
    ensures ({
        let keys = Seq::new(output.nodes.len(), |i: int| output.nodes[i].key);
        let actual = replay_publication::apply_rows(output.host, incremental_writes);
        retained_view::emitted_view(keys, actual) == full_writes
    }),
{
    successful_frame_publishes_fresh_view(sizing, reference, output);
    replay_publication::placement_rows_commit(output.nodes, sizing.words(reference), output.draw,
        output.plan, output.host);
    replay_publication::full_placement_rows_are_the_visible_view(output.nodes, reference.full_sizing(), output.draw);
}

pub(crate) type NativeEdges = crate::placement_adapter::Edges<f32>;
pub(crate) type NativeOutputs<I> = Map<I, (NativeEdges, NativeEdges)>;
pub(crate) type NativeWrite<I> = (I, NativeEdges, NativeEdges);

pub(crate) open spec fn edge_words<F: crate::prepare_frame::FrameFloat>(edges: NativeEdges) -> RectBits {
    let [[left, right], [top, bottom]] = edges;
    (F::word(left), F::word(right), F::word(top), F::word(bottom))
}

pub(crate) open spec fn callback_words<F: crate::prepare_frame::FrameFloat>(edges: (NativeEdges, NativeEdges)) -> Geometry {
    Geometry { absolute: edge_words::<F>(edges.0), local: edge_words::<F>(edges.1) }
}

/// The native host callback overwrites exactly one row for the logical ID.
pub(crate) open spec fn native_commit<I>(previous: NativeOutputs<I>, rows: Seq<NativeWrite<I>>) -> NativeOutputs<I>
    decreases rows.len(),
{
    if rows.len() == 0 { previous } else {
        let (id, absolute, local) = rows.last();
        native_commit(previous, rows.drop_last()).insert(id, (absolute, local))
    }
}

pub(crate) open spec fn native_rows<I, F: crate::prepare_frame::FrameFloat>(
    events: Seq<NativeWrite<I>>, key: spec_fn(I) -> Key,
) -> Seq<(Key, Geometry)> {
    events.map_values(|event: NativeWrite<I>| (key(event.0), callback_words::<F>((event.1, event.2))))
}

pub(crate) open spec fn project_native_view<I, F: crate::prepare_frame::FrameFloat>(
    visible: Set<Key>, id: spec_fn(Key) -> I, native: NativeOutputs<I>,
) -> Outputs {
    Map::new(visible.filter(|key: Key| native.contains_key(id(key))),
        |key: Key| callback_words::<F>(native[id(key)]))
}

/// Compare actual pairs of host rectangles by their four words on each side.
/// A live incarnation identifies the exact record used by its native callback.
pub(crate) proof fn native_callbacks_project_to_frame_commit<I, F: crate::prepare_frame::FrameFloat>(
    previous: NativeOutputs<I>, rows: Seq<NativeWrite<I>>, visible: Set<Key>,
    id: spec_fn(Key) -> I, key: spec_fn(I) -> Key,
)
    requires
        forall |k: Key| #[trigger] visible.contains(k) ==> key(id(k)) == k,
        forall |i: int| 0 <= i < rows.len() ==> {
            let node = (#[trigger] rows[i]).0;
            visible.contains(key(node)) && id(key(node)) == node
        },
    ensures project_native_view::<I, F>(visible, id, native_commit(previous, rows))
        == replay_publication::apply_rows(project_native_view::<I, F>(visible, id, previous), native_rows::<I, F>(rows, key)),
    decreases rows.len(),
{
    let projected = project_native_view::<I, F>(visible, id, previous);
    let observed = native_rows::<I, F>(rows, key);
    if rows.len() == 0 {
        assert(observed =~= Seq::<(Key, Geometry)>::empty());
    } else {
        let prefix = rows.drop_last();
        assert forall|i: int| 0 <= i < prefix.len() implies
            visible.contains(key((#[trigger] prefix[i]).0)) && id(key(prefix[i].0)) == prefix[i].0 by {
            assert(prefix[i] == rows[i]);
        }
        native_callbacks_project_to_frame_commit::<I, F>(previous, prefix, visible, id, key);
        let (node, absolute, local) = rows.last();
        let record = (absolute, local);
        let current = key(node);
        assert(rows[rows.len() - 1] == rows.last());
        assert(visible.contains(current) && id(current) == node);
        let past = native_commit(previous, prefix);
        let replay = replay_publication::apply_rows(projected, native_rows::<I, F>(prefix, key));
        assert(observed.drop_last() =~= native_rows::<I, F>(prefix, key));
        assert(observed.last() == (current, callback_words::<F>(record)));
        let after = project_native_view::<I, F>(visible, id, past.insert(node, record));
        let expected = replay.insert(current, callback_words::<F>(record));
        assert forall|k: Key| after.contains_key(k) || expected.contains_key(k) implies {
            &&& #[trigger] after.contains_key(k) == expected.contains_key(k)
            &&& after.contains_key(k) ==> after[k] == expected[k]
        } by {
            if k != current {
                assert(visible.contains(k));
                assert(key(id(k)) == k);
                assert(id(k) != node);
            }
        }
        assert(after =~= expected);
    }
}

/// The reference uses the packed program's ordered producer requests and
/// local declarations. Initial prepared slots must implement their own rules.
pub(crate) open spec fn reference_binds_slot_program<I>(reference: Replay, program: sizing_tape::SlotProgram<I>) -> bool {
    let roots = production_schedule::walk(reference.visits);
    &&& reference.n == program.keys.len()
    &&& reference.edges == ranked_full::tape_edges(program.order)
    &&& reference.eval == ranked_full::tape_finish(program.order, program.inputs)
    &&& ranked_full::prepared_words(reference.initial_state, reference.initial, program.fresh())
    &&& forall |i: int| 0 <= i < roots.len() ==> 0 <= #[trigger] roots[i] < reference.n
}

/// Consume the production frame driver's certified numeric postcondition.
/// Placement can read the computed producer words from that frame.
pub(crate) proof fn certified_numeric_frame_uses_full_words<W: Copy, F: numeric::CachedQueue<W> + ?Sized>(
    before: &F, after: &F, window: W, result: FrameResult<F::Id>, reference: Replay, key: int,
)
    requires
        result.evidence@.measured is Success, result.evidence@.route is Queue,
        publication::certified_numeric_inputs(before, window, result.evidence@.track_output),
        publication::numeric_sizing_exact(before, after, window,
            result.evidence@.route, result.evidence@.track_output, result.evidence@.measured),
        reference_binds_slot_program(reference, before.program_for_window(window)),
        0 <= key < reference.n,
        production_schedule::walk(reference.visits).contains(key)
            || (reference.initial_state)(key) == kernel::SOLVED,
    ensures 0 <= key < after.slot_words().len(), reference.full_sizing().contains_key(key),
        after.slot_words()[key] == reference.full_sizing()[key],
{
    let program = before.program_for_window(window);
    let roots = production_schedule::walk(reference.visits);
    ranked_full::tape_prefix_solves_edges(program.order, program.inputs);
    ranked_full::full_roots_match_ranked_values(roots, reference.initial_state, reference.edges,
        reference.provisional, reference.initial, reference.eval, program.fresh(), key);
}

/// A certified queue, tape, or idle frame supplies the sizing used by the
/// actual incremental callbacks. Compare their published view with the
/// independent full callback stream when both implement the local recipes.
pub(crate) proof fn certified_numeric_callbacks_match_full<W: Copy, F: numeric::CachedQueue<W> + ?Sized>(
    before: &F, after: &F, window: W, result: FrameResult<F::Id>, reference: Replay, output: Placement,
    incremental_writes: Seq<(Key, Geometry)>, full_writes: Seq<(Key, Geometry)>,
)
    requires
        publication::frame_result(result, false),
        result.evidence@.measured is Success, result.evidence@.route is Queue,
        publication::certified_numeric_inputs(before, window, result.evidence@.track_output),
        publication::numeric_sizing_exact(before, after, window,
            result.evidence@.route, result.evidence@.track_output, result.evidence@.measured),
        reference_binds_slot_program(reference, before.program_for_window(window)),
        output.valid(reference),
        forall |i: int, j: int| 0 <= i < output.nodes.len() && 0 <= j < output.nodes[i].inputs.len() ==> {
            let key = (#[trigger] output.nodes[i].inputs[j]).producer;
            &&& 0 <= key < reference.n
            &&& production_schedule::walk(reference.visits).contains(key) || (reference.initial_state)(key) == kernel::SOLVED
        },
        incremental_writes == replay_publication::placement_rows(output.nodes, table(after.slot_words()),
            output.draw, |key: Key| crate::writes((output.plan)(key))),
        full_writes == replay_publication::placement_rows(output.nodes, reference.full_sizing(),
            output.draw, |_: Key| true),
    ensures
        retained_view::emitted_view(Seq::new(output.nodes.len(), |i: int| output.nodes[i].key),
            replay_publication::apply_rows(output.host, incremental_writes)) == full_writes,
{
    let words = table(after.slot_words());
    let full = reference.full_sizing();
    let nodes = output.nodes;
    assert forall |i: int, j: int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len() implies {
        let key = (#[trigger] nodes[i].inputs[j]).producer;
        words.contains_key(key) && full.contains_key(key) && words[key] == full[key]
    } by {
        let key = nodes[i].inputs[j].producer;
        certified_numeric_frame_uses_full_words(before, after, window, result, reference, key);
        table_contains(after.slot_words(), key);
    }
    replay_publication::sizing_and_placement_publish_fresh_view(
        nodes, words, full, output.draw, output.plan, output.previous, output.host,
    );
    replay_publication::placement_rows_commit(nodes, words, output.draw, output.plan, output.host);
    replay_publication::full_placement_rows_are_the_visible_view(nodes, full, output.draw);
}

pub(crate) open spec fn full_root_numbers<I: Copy>(
    measurement: FullMeasurement<I>, program: sizing_tape::SlotProgram<I>,
) -> Seq<int> {
    match measurement {
        FullMeasurement::Walk { visits, .. } => sizing_pass::visit_calls(visits).map_values(
            |(node, axis, kind): sizing_pass::RootCall<I>| program.position(
                dependencies::sizing_requests::target(node, axis is Y, kind),
            ),
        ),
        _ => Seq::empty(),
    }
}

/// Use the root requests emitted by the actual full sizing walk. The slot
/// program supplies the key translation and the producer operations.
pub(crate) proof fn compare_emitted_full_roots_with_numeric_frame<W: Copy, F: numeric::CachedQueue<W> + ?Sized>(
    before: &F, after: &F, window: W, result: FrameResult<F::Id>, full: FullSizing<F::Id>,
    state: spec_fn(int) -> u32, initial: Storage, provisional: spec_fn(int) -> Seq<u32>, key: int,
)
    requires
        result.evidence@.measured is Success, result.evidence@.route is Queue,
        publication::certified_numeric_inputs(before, window, result.evidence@.track_output),
        publication::numeric_sizing_exact(before, after, window, result.evidence@.route,
            result.evidence@.track_output, result.evidence@.measured),
        ({
            let program = before.program_for_window(window);
            let roots = full_root_numbers(full.evidence@, program);
            &&& ranked_full::prepared_words(state, initial, program.fresh())
            &&& forall |i: int| 0 <= i < roots.len() ==> 0 <= #[trigger] roots[i] < program.keys.len()
            &&& 0 <= key < program.keys.len()
            &&& roots.contains(key) || state(key) == kernel::SOLVED
        }),
    ensures ({
        let program = before.program_for_window(window);
        let roots = full_root_numbers(full.evidence@, program);
        let reference = ranked_full::full_run(roots, state, ranked_full::tape_edges(program.order), provisional,
            initial, ranked_full::tape_finish(program.order, program.inputs), program.keys.len());
        &&& 0 <= key < after.slot_words().len()
        &&& reference.contains_key(key)
        &&& after.slot_words()[key] == reference[key]
    }),
{
    let program = before.program_for_window(window);
    let roots = full_root_numbers(full.evidence@, program);
    ranked_full::tape_prefix_solves_edges(program.order, program.inputs);
    ranked_full::full_roots_match_ranked_values(roots, state, ranked_full::tape_edges(program.order), provisional,
        initial, ranked_full::tape_finish(program.order, program.inputs), program.fresh(), key);
}

/// The full solver's viewport shortcut replaces ordinary root Regular and
/// Final producers with the same words. Other records never enter this proof.
pub(crate) proof fn viewport_shortcut_matches_root_producers<A: sizing_finish::FinishModel>(
    evidence: FullMeasurement<A::Id>, order: crate::prepare_frame::Order<A::Id>,
    reference: &A, window: crate::declarations::Xy<f32>, vertical: bool,
)
    requires evidence.valid(order, window), match evidence {
        FullMeasurement::Viewport { root, params, record } => {
            let regular = sizing_requests::target(root, vertical, kernel::Kind::Regular);
            &&& reference.finish_window() == window
            &&& (reference.topology().parent)(root) == (order.parent)(root)
            &&& (reference.topology().stack_parent)(regular).is_none()
            &&& reference.finish_layout(root) == params
            &&& reference.finish_flags(root) == record.flags
            &&& reference.finish_values(root)[sizing_finish::key(regular).1 as int]
                == record.values@[sizing_finish::key(regular).1 as int]
        },
        _ => false,
    },
    ensures match evidence {
        FullMeasurement::Viewport { root, record, .. } => {
            let regular = sizing_requests::target(root, vertical, kernel::Kind::Regular);
            let final_slot = sizing_requests::target(root, vertical, kernel::Kind::Final);
            &&& sizing_finish::declared_scalar(reference, regular)
                == Some(record.values@[sizing_finish::key(regular).1 as int])
            &&& sizing_finish::final_extent(reference, final_slot)
                == record.values@[sizing_finish::key(final_slot).1 as int]
        },
        _ => false,
    },
{
    let (root, params, record) = match evidence {
        FullMeasurement::Viewport { root, params, record } => (root, params, record),
        _ => { assert(false); return; },
    };
    let regular = sizing_requests::target(root, vertical, kernel::Kind::Regular);
    let final_slot = sizing_requests::target(root, vertical, kernel::Kind::Final);
    let flags = record.flags;
    let auto_block = flags.0 & crate::node_flags::NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0;
    assert(sizing_requests::resolved_size(params, vertical, kernel::Kind::Regular, flags.is_block_item(), auto_block)
        == Some(crate::declarations::Size::Fill));
    assert(sizing_requests::resolved_size(params, vertical, kernel::Kind::Min, flags.is_block_item(), auto_block).is_none());
    assert(sizing_requests::resolved_size(params, vertical, kernel::Kind::Max, flags.is_block_item(), auto_block).is_none());
    assert(sizing_finish::declared_scalar(reference, regular)
        == Some(sizing_finish::viewport_extent(reference, regular.axis())));
    assert(sizing_finish::bound_word(reference, final_slot, kernel::Kind::Min).is_none());
    assert(sizing_finish::bound_word(reference, final_slot, kernel::Kind::Max).is_none());
}

/// A declared scalar writes the same singleton datum that numeric replay observes.
pub(crate) proof fn observe_scalar_receipt<A: sizing_finish::FinishModel>(
    before: &A, slot: sizing_requests::Request<A::Id>, receipt: sizing_finish::StoredSize<A::Id>,
    packing: numeric::producers::Packing<A::Id>, records: spec_fn(A::Id) -> crate::node_data::NodeLayoutData,
)
    requires sizing_finish::declared_scalar(before, slot) == Some(receipt.value), receipt.slot == slot,
        records(slot.node).values[sizing_finish::key(slot).1 as int] == receipt.value,
    ensures numeric::producers::observe::<A::Float, A::Id>(packing, records, slot)
        == seq![A::Float::word(receipt.value)],
{
    let lane = numeric::producers::scalar_lane(slot);
    let index = sizing_finish::key(slot).1 as int;
    assert(0 <= index < kernel::N_SLOTS);
    assert(lane == numeric::producers::Lane::Size(slot.node, index as usize));
    assert(packing.lanes(slot) =~= seq![lane]);
    assert(numeric::producers::observe::<A::Float, A::Id>(packing, records, slot)
        =~= seq![A::Float::word(receipt.value)]);
}

/// A retained Fill leaf resized by the Stack-tail path uses the same physical
/// EvenShare input and writes the same two main-axis lanes as the full producer.
pub(crate) proof fn resized_stack_fill_matches_fresh<A: sizing_finish::FinishModel>(
    fresh_before_regular: &A, fresh_before_final: &A, child: A::Id, parent: A::Id,
    axis: crate::declarations::Axis, share: f32, prior: Seq<f32>, resized: Seq<f32>, bounded: bool,
    published_regular: sizing_finish::StoredSize<A::Id>, published_final: sizing_finish::StoredSize<A::Id>,
)
    requires ({
        let vertical = axis is Y;
        let regular = sizing_requests::target(child, vertical, kernel::Kind::Regular);
        let final_slot = sizing_requests::target(child, vertical, kernel::Kind::Final);
        let share_slot = sizing_requests::target(parent, vertical, kernel::Kind::EvenShare);
        let p = fresh_before_regular.finish_layout(child);
        let child_flags = fresh_before_regular.finish_flags(child);
        &&& crate::stack_tail::active_fill(p, axis) && !crate::stack_tail::prefix_bounds(p, axis)
        &&& prior.len() == kernel::N_SLOTS
        &&& resized == crate::stack_tail::resized_prefix::<A::Float>(p, prior, axis, share, bounded)
        &&& (fresh_before_regular.topology().stack_parent)(regular) == Some(parent)
        &&& !child_flags.is_block_item()
        &&& child_flags.0 & crate::node_flags::NodeFlags::BLOCK_PARENT_AUTO_HEIGHT == 0
        &&& fresh_before_regular.finish_flags(parent).0 & crate::node_flags::NodeFlags::WRAP_CONTAINER == 0
        &&& fresh_before_regular.finish_values(parent)[sizing_finish::key(share_slot).1 as int] == share
        &&& published_regular.slot == regular
        &&& sizing_finish::declared_scalar(fresh_before_regular, regular) == Some(published_regular.value)
        &&& fresh_before_final.finish_layout(child) == p
        &&& !fresh_before_final.finish_flags(child).is_block_item()
        &&& sizing_finish::direct_regular(fresh_before_final, final_slot) == published_regular.value
        &&& published_final.slot == final_slot
        &&& published_final.value == sizing_finish::final_extent(fresh_before_final, final_slot)
    }),
    ensures
        resized[kernel::slot_index(axis.index(), kernel::Kind::Regular) as int] == published_regular.value,
        resized[kernel::slot_index(axis.index(), kernel::Kind::Final) as int] == published_final.value,
        forall |i: int| 0 <= i < prior.len() && i != kernel::slot_index(axis.index(), kernel::Kind::Regular)
            && i != kernel::slot_index(axis.index(), kernel::Kind::Final)
            ==> #[trigger] resized[i] == prior[i],
{
    let p = fresh_before_regular.finish_layout(child);
    let vertical = axis is Y;
    let regular = sizing_requests::target(child, vertical, kernel::Kind::Regular);
    let final_slot = sizing_requests::target(child, vertical, kernel::Kind::Final);
    assert(sizing_finish::declared_scalar(fresh_before_regular, regular) == Some(A::Float::product(share, p.fill_weight)));
    assert(sizing_finish::bound_word(fresh_before_final, final_slot, kernel::Kind::Min).is_none());
    assert(sizing_finish::bound_word(fresh_before_final, final_slot, kernel::Kind::Max).is_none());
    assert(sizing_finish::final_extent(fresh_before_final, final_slot) == published_regular.value);
}

/// A Free intrinsic declaration has one packed size lane. Its canonical
/// receipt exposes exactly what the numeric observer reads from that lane.
pub(crate) proof fn observe_free_intrinsic_receipt<A: sizing_finish::FinishModel + sizing_finish::IntrinsicOracle<A::Id>>(
    before: &A, slot: sizing_requests::Request<A::Id>, receipt: sizing_finish::StoredSize<A::Id>,
    packing: numeric::producers::Packing<A::Id>, records: spec_fn(A::Id) -> crate::node_data::NodeLayoutData,
)
    requires sizing_finish::free_intrinsic(before, slot), receipt.slot == slot,
        receipt.value == sizing_finish::free_intrinsic_value(before, slot),
        (packing.layout)(slot.node) == before.finish_layout(slot.node).children_layout,
        records(slot.node).values[sizing_finish::key(slot).1 as int] == receipt.value,
    ensures Some(numeric::producers::observe::<A::Float, A::Id>(packing, records, slot))
        == sizing_finish::free_intrinsic_datum(before, slot),
{
    let lane = numeric::producers::scalar_lane(slot);
    let index = sizing_finish::key(slot).1 as int;
    assert(0 <= index < kernel::N_SLOTS);
    assert(lane == numeric::producers::Lane::Size(slot.node, index as usize));
    assert(packing.lanes(slot) =~= seq![lane]);
    assert(numeric::producers::observe::<A::Float, A::Id>(packing, records, slot)
        =~= seq![A::Float::word(receipt.value)]);
}

/// A main-axis Stack or Wrap intrinsic request publishes one size word.
/// Its canonical receipt is the word that the numeric observer reads.
pub(crate) proof fn observe_stack_intrinsic_receipt<A: sizing_finish::FinishModel + sizing_finish::IntrinsicOracle<A::Id>>(
    before: &A, slot: sizing_requests::Request<A::Id>, receipt: sizing_finish::StoredSize<A::Id>,
    packing: numeric::producers::Packing<A::Id>, records: spec_fn(A::Id) -> crate::node_data::NodeLayoutData,
)
    requires sizing_finish::stack_intrinsic(before, slot), receipt.slot == slot,
        receipt.value == sizing_finish::stack_intrinsic_value(before, slot),
        (packing.layout)(slot.node) == before.finish_layout(slot.node).children_layout,
        records(slot.node).values[sizing_finish::key(slot).1 as int] == receipt.value,
    ensures Some(numeric::producers::observe::<A::Float, A::Id>(packing, records, slot))
        == sizing_finish::stack_intrinsic_datum(before, slot),
{
    let lane = numeric::producers::scalar_lane(slot);
    let index = sizing_finish::key(slot).1 as int;
    assert(0 <= index < kernel::N_SLOTS);
    assert(lane == numeric::producers::Lane::Size(slot.node, index as usize));
    assert(packing.lanes(slot) =~= seq![lane]);
    assert(numeric::producers::observe::<A::Float, A::Id>(packing, records, slot)
        =~= seq![A::Float::word(receipt.value)]);
}

/// Every declared intrinsic request publishes the one native size lane
/// selected by numeric sizing's packed observer.
pub(crate) proof fn observe_intrinsic_receipt<A: sizing_finish::FinishModel + sizing_finish::IntrinsicOracle<A::Id>>(
    before: &A, slot: sizing_requests::Request<A::Id>, receipt: sizing_finish::StoredSize<A::Id>,
    packing: numeric::producers::Packing<A::Id>, records: spec_fn(A::Id) -> crate::node_data::NodeLayoutData,
)
    requires sizing_finish::is_intrinsic(before, slot), receipt.slot == slot,
        sizing_finish::intrinsic_datum(before, slot) == Some(seq![A::Float::word(receipt.value)]),
        records(slot.node).values[sizing_finish::key(slot).1 as int] == receipt.value,
    ensures Some(numeric::producers::observe::<A::Float, A::Id>(packing, records, slot))
        == sizing_finish::intrinsic_datum(before, slot),
{
    let lane = numeric::producers::scalar_lane(slot);
    let index = sizing_finish::key(slot).1 as int;
    assert(0 <= index < kernel::N_SLOTS);
    assert(lane == numeric::producers::Lane::Size(slot.node, index as usize));
    assert(packing.lanes(slot) =~= seq![lane]);
    assert(numeric::producers::observe::<A::Float, A::Id>(packing, records, slot)
        =~= seq![A::Float::word(receipt.value)]);
}

pub struct Frame {
    pub sizing: Sizing,
    pub reference: Replay,
    pub nodes: Seq<PlaceNode>,
    pub plan: spec_fn(Key) -> Work,
    pub writes: Seq<(Key, Geometry)>,
}

impl Frame {
    pub open spec fn geometry(self, draw: Draw) -> Placements {
        replay_view::place_frame(self.nodes, self.reference.full_sizing(), draw)
    }

    pub open spec fn follows(self, previous: Placements, draw: Draw) -> bool {
        let placement = Placement {
            nodes: self.nodes, plan: self.plan, draw, previous,
            host: Map::new(previous.dom(), |key: Key| previous[key].result.output),
        };
        &&& placement.valid(self.reference)
        &&& self.sizing.valid(self.reference)
        &&& forall |i: int, j: int| 0 <= i < self.nodes.len() && 0 <= j < self.nodes[i].inputs.len()
            ==> self.sizing.available(self.reference, (#[trigger] self.nodes[i].inputs[j]).producer)
        &&& self.writes == replay_publication::placement_rows(self.nodes, self.sizing.words(self.reference),
            draw, |key: Key| crate::writes((self.plan)(key)))
    }
}

pub open spec fn prior_geometry(frames: Seq<Frame>, draw: Draw) -> Placements {
    if frames.len() == 0 { Map::empty() } else { frames.last().geometry(draw) }
}

pub open spec fn supported(frames: Seq<Frame>, draw: Draw) -> bool
    decreases frames.len(),
{
    if frames.len() == 0 { true } else {
        let before = frames.drop_last();
        supported(before, draw) && frames.last().follows(prior_geometry(before, draw), draw)
    }
}

pub open spec fn observe(frames: Seq<Frame>) -> Outputs
    decreases frames.len(),
{
    if frames.len() == 0 { Map::empty() } else {
        replay_publication::apply_rows(observe(frames.drop_last()), frames.last().writes)
    }
}

/// The prior host view is derived by replaying the observed callbacks. Each
/// frame may choose a different sizing route, and completed frames preserve
/// the retained-output premise used by their successors.
pub proof fn mixed_frames_match_fresh_after_every_edit(frames: Seq<Frame>, draw: Draw)
    requires supported(frames, draw),
    ensures replay_publication::retained_outputs_are_sound(prior_geometry(frames, draw), observe(frames)),
        frames.len() > 0 ==> {
            let frame = frames.last();
            let keys = Seq::new(frame.nodes.len(), |i: int| frame.nodes[i].key);
            retained_view::emitted_view(keys, observe(frames)) == replay_view::ordered_view(frame.nodes, frame.geometry(draw))
        },
    decreases frames.len(),
{
    if frames.len() > 0 {
        let before = frames.drop_last();
        mixed_frames_match_fresh_after_every_edit(before, draw);
        let frame = frames.last();
        let output = Placement {
            nodes: frame.nodes, plan: frame.plan, draw,
            previous: prior_geometry(before, draw), host: observe(before),
        };
        assert(output.valid(frame.reference));
        successful_frame_publishes_fresh_view(frame.sizing, frame.reference, output);
        replay_publication::placement_rows_commit(frame.nodes, frame.sizing.words(frame.reference), draw,
            frame.plan, observe(before));
    }
}

}
