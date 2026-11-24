//! The concrete ranked producer model of an unbounded Fill viewport.
use vstd::prelude::*;
use crate::cycles::kernel::{self, Kind};
use crate::declarations::{Xy, X, Y, Size};
use crate::dependencies::sizing_requests::{Request, target};
use crate::node_data::NodeLayoutData;
use crate::prepare_frame::FrameWords;
use crate::sizing_pass::{self, FullMeasurement};
use crate::sizing_tape::{DependencyOrder, SlotProgram, Datum, Inputs};
use super::{self as numeric, CachedQueue};
use crate::queue_storage::{intake, readers};
use crate::publication::{self, FrameResult};

verus! {

pub(crate) open spec fn root_keys<I: Copy>(id: I) -> Seq<Request<I>> {
    seq![target(id, false, Kind::Regular), target(id, true, Kind::Regular),
         target(id, false, Kind::Final), target(id, true, Kind::Final)]
}

pub(crate) open spec fn root_locals<F: FrameWords>(window: Xy<f32>) -> Inputs {
    seq![seq![F::word(window.x)], seq![F::word(window.y)], Seq::<u32>::empty(), Seq::empty()]
}

pub(crate) open spec fn root_program<F: FrameWords, I: Copy>(
    id: I, old: Xy<f32>, new: Xy<f32>,
) -> SlotProgram<I> {
    SlotProgram {
        keys: root_keys(id),
        order: DependencyOrder {
            reads: seq![Seq::<int>::empty(), Seq::<int>::empty(), seq![0int], seq![1int]],
            finish: |i: int, local: Seq<u32>, inputs: Seq<Datum>| if i < 2 { local } else { inputs[0] },
        },
        previous_inputs: root_locals::<F>(old),
        inputs: root_locals::<F>(new),
    }
}

pub(crate) open spec fn root_words<F: FrameWords>(record: NodeLayoutData) -> Seq<Datum> {
    seq![
        seq![F::word(record.values[kernel::slot_index(0, Kind::Regular) as int])],
        seq![F::word(record.values[kernel::slot_index(1, Kind::Regular) as int])],
        seq![F::word(record.values[kernel::slot_index(0, Kind::Final) as int])],
        seq![F::word(record.values[kernel::slot_index(1, Kind::Final) as int])],
    ]
}

pub(crate) open spec fn viewport_words<F: FrameWords>(window: Xy<f32>) -> Seq<Datum> {
    let x = seq![F::word(window.x)];
    let y = seq![F::word(window.y)];
    seq![x, y, x, y]
}

pub(crate) proof fn key_positions<I: Copy>(id: I)
    ensures
        root_keys(id).no_duplicates(),
        root_keys(id).index_of_first(target(id, false, Kind::Regular)) == Some(0int),
        root_keys(id).index_of_first(target(id, true, Kind::Regular)) == Some(1int),
        root_keys(id).index_of_first(target(id, false, Kind::Final)) == Some(2int),
        root_keys(id).index_of_first(target(id, true, Kind::Final)) == Some(3int),
{
    let keys = root_keys(id);
    assert forall |i: int, j: int| 0 <= i < j < keys.len()
        implies #[trigger] keys[i] != #[trigger] keys[j] by {
        assert(i == 0 || i == 1 || i == 2 || i == 3);
        assert(j == 0 || j == 1 || j == 2 || j == 3);
    }
    assert(keys.contains(keys[0]) && keys.contains(keys[1]) && keys.contains(keys[2]) && keys.contains(keys[3]));
    keys.index_of_first_ensures(keys[0]);
    keys.index_of_first_ensures(keys[1]);
    keys.index_of_first_ensures(keys[2]);
    keys.index_of_first_ensures(keys[3]);
}

pub(crate) proof fn root_program_words<F: FrameWords, I: Copy>(id: I, prior: Xy<f32>, window: Xy<f32>)
    ensures root_program::<F,I>(id, prior, window).valid(),
        root_program::<F,I>(id, prior, window).previous(viewport_words::<F>(prior)),
        root_program::<F,I>(id, prior, window).fresh() == viewport_words::<F>(window),
{
    let program = root_program::<F,I>(id, prior, window);
    key_positions(id);
    assert forall |i: int, j: int| 0 <= i < program.keys.len() && 0 <= j < program.order.reads[i].len()
        implies 0 <= #[trigger] program.order.reads[i][j] < i by {
        assert(i == 0 || i == 1 || i == 2 || i == 3);
        assert(i >= 2 && j == 0);
    }
    let words = viewport_words::<F>(prior);
    assert forall |i: int| 0 <= i < program.keys.len()
        implies #[trigger] words[i] == (program.order.finish)(i, program.previous_inputs[i], program.order.read(i, words)) by {
        if i == 2 { assert(program.order.read(i, words) =~= seq![words[0]]); }
        if i == 3 { assert(program.order.read(i, words) =~= seq![words[1]]); }
    }
    let locals = root_locals::<F>(window);
    reveal_with_fuel(crate::sizing_tape::fresh_prefix, 5);
    let prefix2 = crate::sizing_tape::fresh_prefix(program.order, locals, 2);
    let prefix3 = crate::sizing_tape::fresh_prefix(program.order, locals, 3);
    let now = viewport_words::<F>(window);
    assert(prefix2 =~= now.take(2));
    assert(program.order.read(2, prefix2) =~= seq![now[0]]);
    assert(prefix3 =~= now.take(3));
    assert(program.order.read(3, prefix3) =~= seq![now[1]]);
    assert(program.fresh() =~= now);
}

pub(crate) open spec fn viewport_seed<I: Copy>(
    program: SlotProgram<I>, events: readers::ReaderInputs<I>, root: I, vertical: bool,
) -> Set<int> {
    let axis = if vertical { Y } else { X };
    readers::filtered_kinds(events, root, axis, readers::Filter::Flexible, 3).map_values(
        |(node, axis, kind): (I, crate::declarations::Axis, Kind)|
            program.position(target(node, axis is Y, kind)),
    ).to_set()
}

pub(crate) open spec fn viewport_declarations<I: Copy>(events: readers::ReaderInputs<I>, root: I) -> bool {
    &&& (events.declaration)(root, X, Kind::Regular) == Some(Size::Fill)
    &&& (events.declaration)(root, Y, Kind::Regular) == Some(Size::Fill)
    &&& (events.declaration)(root, X, Kind::Min).is_none()
    &&& (events.declaration)(root, Y, Kind::Min).is_none()
    &&& (events.declaration)(root, X, Kind::Max).is_none()
    &&& (events.declaration)(root, Y, Kind::Max).is_none()
}

proof fn root_receives_viewport_seed<F: FrameWords, I: Copy>(
    events: readers::ReaderInputs<I>, id: I, prior: Xy<f32>, window: Xy<f32>, vertical: bool,
)
    requires viewport_declarations(events, id),
    ensures viewport_seed(root_program::<F,I>(id, prior, window), events, id, vertical).contains(vertical as int),
{
    let program = root_program::<F,I>(id, prior, window);
    key_positions(id);
    let axis = if vertical { Y } else { X };
    reveal_with_fuel(readers::filtered_kinds, 4);
    let calls = readers::filtered_kinds(events, id, axis, readers::Filter::Flexible, 3);
    assert(calls =~= seq![(id, axis, Kind::Regular)]);
    let mapped = calls.map_values(|(node, axis, kind): (I, crate::declarations::Axis, Kind)|
        program.position(target(node, axis is Y, kind)));
    assert(mapped =~= seq![vertical as int]);
    let i = vertical as int;
    assert(mapped.len() == 1 && mapped[0] == i);
    mapped.to_set_ensures();
    assert(exists |j: int| 0 <= j < mapped.len() && #[trigger] mapped[j] == i);
    assert(mapped.contains(i));
}

pub(crate) open spec fn fixed_children_viewport_inputs<A: CachedQueue<Xy<f32>> + ?Sized>(
    before: &A, prior: Xy<f32>, window: Xy<f32>, prior_full: FullMeasurement<A::Id>,
    events: readers::ReaderInputs<A::Id>,
) -> bool {
    let root = before.recorded_root();
    let record = before.layout_record(root);
    let delta = before.window_change(window);
    &&& prior_full.valid(before.order(), prior)
    &&& prior_full is Viewport
    &&& prior_full->Viewport_root == root && prior_full->Viewport_record == record
    &&& viewport_declarations(events, root)
    &&& before.scalar_mode()
    &&& before.slot_words() == root_words::<A::Float>(record)
    &&& before.program_for_window(window) == root_program::<A::Float,A::Id>(root, prior, window)
    &&& before.pending_declarations().len() == 0 && before.pending_content().len() == 0
    &&& !delta.edits_pending && 1 <= delta.budget < 32
    &&& (delta.horizontal || delta.vertical)
    &&& delta.horizontal == (A::Float::word(prior.x) != A::Float::word(window.x))
    &&& delta.vertical == (A::Float::word(prior.y) != A::Float::word(window.y))
    &&& (before.seed_positions())(intake::Seed::Window(root, 0))
        == viewport_seed(before.program_for_window(window), events, root, false)
    &&& (before.seed_positions())(intake::Seed::Window(root, 1))
        == viewport_seed(before.program_for_window(window), events, root, true)
}

/// Derive the ordinary queue certificate from the canonical viewport producer's
/// actual packed record and the source filter's exact requested indices.
pub(crate) proof fn fixed_children_viewport_certifies_queue<A: CachedQueue<Xy<f32>> + ?Sized>(
    before: &A, prior: Xy<f32>, window: Xy<f32>, prior_full: FullMeasurement<A::Id>,
    events: readers::ReaderInputs<A::Id>, track_output: bool,
)
    requires fixed_children_viewport_inputs(before, prior, window, prior_full, events),
    ensures numeric::certified_scalar_seeded_frame(before, window, track_output),
        before.program_for_window(window).fresh() == viewport_words::<A::Float>(window),
{
    let root = before.recorded_root();
    let delta = before.window_change(window);
    let program = before.program_for_window(window);
    root_program_words::<A::Float, A::Id>(root, prior, window);
    root_receives_viewport_seed::<A::Float, A::Id>(events, root, prior, window, false);
    root_receives_viewport_seed::<A::Float, A::Id>(events, root, prior, window, true);
    assert(sizing_pass::seeded_viewport(before.layout_record(root), prior));
    assert(before.slot_words() =~= viewport_words::<A::Float>(prior));
    let seeds = intake::window_seeds(root, delta.horizontal, delta.vertical)
        + intake::node_seeds(before.pending_declarations()) + intake::content_seeds::<A::Id, A::Change>(before.pending_content());
    assert(intake::node_seeds(before.pending_declarations()) =~= Seq::empty());
    assert(intake::content_seeds::<A::Id, A::Change>(before.pending_content()) =~= Seq::empty());
    assert(seeds =~= intake::window_seeds(root, delta.horizontal, delta.vertical));
    assert forall |i: int| 0 <= i < program.keys.len() && #[trigger] program.previous_inputs[i] != program.inputs[i]
        implies before.scalar_pending().contains(i) || exists |j: int| 0 <= j < seeds.len()
            && (before.seed_positions())(#[trigger] seeds[j]).contains(i) by {
        if i == 0 {
            assert(delta.horizontal && seeds[0] == intake::Seed::Window(root, 0));
            assert((before.seed_positions())(seeds[0]).contains(i));
        } else {
            assert(i == 1 && delta.vertical);
            let j = if delta.horizontal { 1 } else { 0 };
            assert(seeds[j] == intake::Seed::Window(root, 1));
            assert((before.seed_positions())(seeds[j]).contains(i));
        }
    }
}

/// Compare the successful ordinary queue with a separate full viewport
/// measurement using the two source-linked receipts.
pub(crate) proof fn fixed_children_viewport_matches_full<A: CachedQueue<Xy<f32>> + ?Sized>(
    before: &A, after: &A, prior: Xy<f32>, window: Xy<f32>,
    prior_full: FullMeasurement<A::Id>, fresh_full: FullMeasurement<A::Id>,
    events: readers::ReaderInputs<A::Id>, result: FrameResult<A::Id>,
)
    requires
        fixed_children_viewport_inputs(before, prior, window, prior_full, events),
        fresh_full.valid(after.order(), window), fresh_full is Viewport,
        fresh_full->Viewport_root == before.recorded_root(),
        result.evidence@.route is Queue, result.evidence@.measured is Success,
        publication::numeric_sizing_exact(before, after, window,
            result.evidence@.route, result.evidence@.track_output, result.evidence@.measured),
    ensures after.slot_words() == root_words::<A::Float>(fresh_full->Viewport_record),
{
    fixed_children_viewport_certifies_queue(before, prior, window, prior_full, events, result.evidence@.track_output);
    assert(root_words::<A::Float>(fresh_full->Viewport_record) =~= viewport_words::<A::Float>(window));
}

}
