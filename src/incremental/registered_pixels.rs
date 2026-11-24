//! Same-window ranked updates of a prepared fixed-pixel producer.
use vstd::prelude::*;
use crate::cycles::kernel::{self, Kind};
use crate::declarations::{Axis, X, Xy, Y, LayoutParams};
use crate::dependencies::registration::{changed_on_axis, declaration_changed};
use crate::dependencies::sizing_requests::target;
use crate::node_data::NodeLayoutData;
use crate::prepare_frame::{self, FrameFloat, FrameWords};
use crate::prepare_nodes;
use crate::publication::IncrementalRelayoutOutcome;
use crate::queue_storage::{intake, readers::{self, NodeChange}};
use crate::sizing_tape::SlotProgram;
use crate::vec_memory::VecMemory;
use super::{self as numeric, root_viewport as axes, CachedQueue};

verus! {

pub(crate) open spec fn explicit_regular_seeds<I: Copy>(
    program: SlotProgram<I>, node: I, change: NodeChange,
) -> Set<int> {
    readers::edited_declarations(node, change).filter(
        |(_, _, kind): (I, Axis, Kind)| kind is Regular,
    ).map_values(|(id, axis, kind): (I, Axis, Kind)|
        program.position(target(id, axis is Y, kind)),
    ).to_set()
}

proof fn register_one_axis<F: FrameWords, I: Copy>(
    node: I, change: NodeChange, old: Xy<f32>, current: Xy<f32>, vertical: bool,
)
    requires declaration_changed(change.declared, kernel::slot_index(vertical as usize, Kind::Regular)),
    ensures explicit_regular_seeds(axes::root_program::<F,I>(node, old, current), node, change)
        .contains(vertical as int),
{
    let axis = if vertical { Y } else { X };
    let program = axes::root_program::<F,I>(node, old, current);
    let prefix = readers::edited_declarations(node, change);
    let request = (node, axis, Kind::Regular);
    let same_axis = readers::masked_declarations(node, axis, change.declared);
    let view = prefix.filter(|(_, _, kind): (I, Axis, Kind)| kind is Regular);
    let positions = view.map_values(|(id, axis, kind): (I, Axis, Kind)|
        program.position(target(id, axis is Y, kind)),
    );
    assert(same_axis.len() > 0 && same_axis[0] == request);
    let index = if vertical { readers::masked_declarations(node, X, change.declared).len() as int } else { 0int };
    assert(0 <= index < prefix.len() && prefix[index] == request);
    assert(prefix.contains(request));
    prefix.lemma_filter_contains(|(_, _, kind): (I, Axis, Kind)| kind is Regular, index);
    assert(view.contains(request));
    let found = choose |i: int| 0 <= i < view.len() && #[trigger] view[i] == request;
    axes::key_positions(node);
    assert(positions[found] == vertical as int);
    positions.to_set_ensures();
    let i = vertical as int;
    assert(exists |j: int| 0 <= j < positions.len() && #[trigger] positions[j] == i);
    assert(positions.contains(i));
}

pub(crate) open spec fn fixed_pixels<F: FrameFloat>(record: NodeLayoutData, size: Xy<f32>) -> bool {
    &&& prepare_frame::pixel_slots::<F>(record.values, X) == (F::word(size.x), F::word(size.x))
    &&& prepare_frame::pixel_slots::<F>(record.values, Y) == (F::word(size.y), F::word(size.y))
}

pub(crate) open spec fn registered_pixel_inputs<A: CachedQueue<Xy<f32>> + ?Sized>(
    before: &A, window: Xy<f32>, node: A::Id, change: NodeChange,
    previous: Xy<f32>, current: Xy<f32>, previous_params: LayoutParams, current_params: LayoutParams,
) -> bool {
    let delta = before.window_change(window);
    let program = axes::root_program::<A::Float,A::Id>(node, previous, current);
    &&& before.scalar_mode()
    &&& !before.layout_params(node).disabled
    &&& !delta.horizontal && !delta.vertical && delta.edits_pending && delta.budget > 0
    &&& before.pending_declarations() == seq![(node, change)] && before.pending_content().len() == 0
    &&& before.slot_words() == axes::root_words::<A::Float>(before.layout_record(node))
    &&& fixed_pixels::<A::Float>(before.layout_record(node), previous)
    &&& before.program_for_window(window) == program
    &&& explicit_regular_seeds(program, node, change).subset_of(
        (before.seed_positions())(intake::Seed::Declaration(node, change)),
    )
    &&& prepare_frame::pixel_decl(previous_params, X) == Some(previous.x)
    &&& prepare_frame::pixel_decl(previous_params, Y) == Some(previous.y)
    &&& prepare_frame::pixel_decl(current_params, X) == Some(current.x)
    &&& prepare_frame::pixel_decl(current_params, Y) == Some(current.y)
    &&& before.layout_params(node) == current_params
    &&& forall |index: usize| index < 8 ==> #[trigger] declaration_changed(change.declared, index)
        == (changed_on_axis::<A::Float>(previous_params, current_params, X, index)
            || changed_on_axis::<A::Float>(previous_params, current_params, Y, index))
}

pub(crate) proof fn registered_pixels_certify_queue<A: CachedQueue<Xy<f32>> + ?Sized>(
    before: &A, window: Xy<f32>, node: A::Id, change: NodeChange,
    previous: Xy<f32>, current: Xy<f32>, previous_params: LayoutParams, current_params: LayoutParams,
    track_output: bool,
)
    requires registered_pixel_inputs(before, window, node, change, previous, current, previous_params, current_params),
    ensures numeric::certified_scalar_seeded_frame(before, window, track_output),
        before.program_for_window(window).fresh() == axes::viewport_words::<A::Float>(current),
{
    axes::root_program_words::<A::Float,A::Id>(node, previous, current);
    assert(before.slot_words() =~= axes::viewport_words::<A::Float>(previous));
    let program = before.program_for_window(window);
    let seeds = intake::window_seeds(before.recorded_root(), false, false)
        + intake::node_seeds(before.pending_declarations())
        + intake::content_seeds::<A::Id,A::Change>(before.pending_content());
    assert(seeds =~= seq![intake::Seed::Declaration(node, change)]);
    assert forall |i: int| 0 <= i < program.keys.len() && #[trigger] program.previous_inputs[i] != program.inputs[i]
        implies before.scalar_pending().contains(i) || exists |j: int| 0 <= j < seeds.len()
            && (before.seed_positions())(#[trigger] seeds[j]).contains(i) by {
        assert(i == 0 || i == 1);
        let axis = if i == 0 { X } else { Y };
        let index = kernel::slot_index(axis.index(), Kind::Regular);
        assert(changed_on_axis::<A::Float>(previous_params, current_params, axis, index));
        assert(declaration_changed(change.declared, index));
        register_one_axis::<A::Float,A::Id>(node, change, previous, current, i == 1);
        assert(explicit_regular_seeds(program, node, change).contains(i));
        assert((before.seed_positions())(seeds[0]).contains(i));
    }
}

/// Run the actual ordinary numeric attempt and separately execute the full
/// preparation's fixed-pixel producer on a fresh reference record.
pub(crate) fn registered_pixels_match_fresh<A: CachedQueue<Xy<f32>> + ?Sized, M: VecMemory>(
    work: &mut A, reference: &mut NodeLayoutData,
    previous_params: &LayoutParams, params: &LayoutParams, window: Xy<f32>,
    node: A::Id, change: NodeChange, previous: Xy<f32>, current: Xy<f32>, track_output: bool,
) -> (out: IncrementalRelayoutOutcome)
    requires registered_pixel_inputs(old(work), window, node, change, previous, current, *previous_params, *params),
        prepare_frame::pixel_final::<A::Float>(*params, X, false, None),
        prepare_frame::pixel_final::<A::Float>(*params, Y, false, None),
        prepare_frame::pixel_decl(*params, X) == Some(current.x),
        prepare_frame::pixel_decl(*params, Y) == Some(current.y),
    ensures out is Success ==> final(work).slot_words() == axes::root_words::<A::Float>(*final(reference)),
    no_unwind
{
    proof {
        registered_pixels_certify_queue(work, window, node, change, previous, current,
            *previous_params, *params, track_output);
    }
    let out = numeric::measure_cached::<_, A, M>(work, window, track_output);
    let ready = prepare_nodes::seed_pixels::<A::Float>(reference, params, false, None);
    proof {
        assert(ready);
        assert(axes::root_words::<A::Float>(*reference) =~= axes::viewport_words::<A::Float>(current));
    }
    out
}

}
