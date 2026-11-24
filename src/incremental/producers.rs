//! The physical words owned by ordered numeric sizing producers.
use vstd::prelude::*;
use crate::cycles::kernel::{self, Kind};
use crate::grid::frame as grid;
use crate::declarations::{ChildrenLayout, MainAxisCellSize};
use crate::dependencies::sizing_requests::{Child, Request};
use crate::node_data::NodeLayoutData;
use crate::node_flags::NodeFlags;
use crate::prepare_frame::FrameWords;
use crate::sizing_pass;
use crate::sizing_tape::{Datum, SlotProgram};

verus! {

/// Child line metrics and grid-cell coordinates occupy the same two words.
/// The parent layout decides which producer owns those words.
pub(crate) enum Lane<I> {
    Size(I, usize),
    ParentFlow(I, bool),
    LineStart(I),
}

pub(crate) open spec fn scalar_lane<I>(slot: Request<I>) -> Lane<I> {
    Lane::Size(slot.node, kernel::slot_index(slot.vertical as usize, slot.kind))
}

pub(crate) open spec fn grid_track_lanes<I>(node: I) -> Seq<Lane<I>> {
    seq![Lane::Size(node, kernel::slot_index(0, Kind::EvenShare)),
         Lane::Size(node, kernel::slot_index(1, Kind::Flow))]
}

pub(crate) open spec fn side_lanes<I>(
    slot: Request<I>, layout: ChildrenLayout, children: Seq<Child<I>>, observe_wrap_cross: bool,
) -> Seq<Lane<I>> {
    match layout {
        ChildrenLayout::Grid { main_axis, columns: MainAxisCellSize::Width(_), .. }
            if slot.kind is Final && main_axis.index() == slot.vertical as usize => {
            let active = children.filter(|child: Child<I>| child.in_flow);
            grid_track_lanes(slot.node) + Seq::new(2 * active.len(), |i: int| {
                Lane::ParentFlow(active[i / 2].node, i % 2 == 1)
            })
        },
        ChildrenLayout::Wrap { axis, .. } if slot.kind is EvenShare && axis.index() == slot.vertical as usize => {
            children.filter(|child: Child<I>| child.in_flow).flat_map(
                |child: Child<I>| seq![Lane::LineStart(child.node), Lane::ParentFlow(child.node, false)],
            )
        },
        ChildrenLayout::Wrap { axis, .. } if observe_wrap_cross
            && slot.kind is Flow && axis.index() != slot.vertical as usize => {
            children.filter(|child: Child<I>| child.in_flow)
                .map_values(|child: Child<I>| Lane::ParentFlow(child.node, true))
        },
        _ => Seq::empty(),
    }
}

#[verifier::reject_recursive_types(I)]
pub(crate) struct Packing<I> {
    pub(crate) layout: spec_fn(I) -> ChildrenLayout,
    pub(crate) children: spec_fn(I) -> Seq<Child<I>>,
    // Simple numeric Wrap does not size from the cross metric. Its normal
    // placement path rescans the settled dimensions for each line.
    pub(crate) observe_wrap_cross: bool,
}

impl<I> Packing<I> {
    pub(crate) open spec fn lanes(self, slot: Request<I>) -> Seq<Lane<I>> {
        seq![scalar_lane(slot)] + side_lanes(slot, (self.layout)(slot.node),
            (self.children)(slot.node), self.observe_wrap_cross)
    }

    pub(crate) open spec fn disjoint(self, keys: Seq<Request<I>>) -> bool {
        forall |i: int, j: int| 0 <= i < keys.len() && 0 <= j < keys.len() && i != j
            ==> self.lanes(#[trigger] keys[i]).to_set().disjoint(self.lanes(#[trigger] keys[j]).to_set())
    }
}

pub(crate) open spec fn read<F: FrameWords, I>(records: spec_fn(I) -> NodeLayoutData, lane: Lane<I>) -> u32 {
    match lane {
        Lane::Size(node, index) => if index < kernel::N_SLOTS {
            F::word(records(node).values[index as int])
        } else { 0 },
        Lane::ParentFlow(node, vertical) => records(node).parent_flow[vertical as int],
        Lane::LineStart(node) => if records(node).flags.0 & NodeFlags::WRAP_LINE_START != 0 { 1 } else { 0 },
    }
}

pub(crate) open spec fn observe<F: FrameWords, I>(
    plan: Packing<I>, records: spec_fn(I) -> NodeLayoutData, slot: Request<I>,
) -> Datum {
    plan.lanes(slot).map_values(|lane: Lane<I>| read::<F, I>(records, lane))
}

pub(crate) open spec fn words<F: FrameWords, I>(
    plan: Packing<I>, records: spec_fn(I) -> NodeLayoutData, program: SlotProgram<I>,
) -> Seq<Datum> {
    program.keys.map_values(|slot: Request<I>| observe::<F, I>(plan, records, slot))
}

pub(crate) open spec fn writes_only<F: FrameWords, I>(
    before: spec_fn(I) -> NodeLayoutData, after: spec_fn(I) -> NodeLayoutData, legal: Set<Lane<I>>,
) -> bool {
    forall |lane: Lane<I>| !legal.contains(lane) ==> #[trigger] read::<F, I>(after, lane) == read::<F, I>(before, lane)
}

/// After one physical producer write, the program vector changes at exactly
/// that producer's index. Source adapters prove the individual raw stores.
pub(crate) proof fn only_one_producer<F: FrameWords, I>(
    plan: Packing<I>, program: SlotProgram<I>, before: spec_fn(I) -> NodeLayoutData,
    after: spec_fn(I) -> NodeLayoutData, index: int,
)
    requires
        0 <= index < program.keys.len(),
        plan.disjoint(program.keys),
        writes_only::<F, I>(before, after, plan.lanes(program.keys[index]).to_set()),
    ensures words::<F, I>(plan, after, program) == words::<F, I>(plan, before, program)
        .update(index, observe::<F, I>(plan, after, program.keys[index])),
{
    let updated = words::<F, I>(plan, before, program)
        .update(index, observe::<F, I>(plan, after, program.keys[index]));
    let observed = words::<F, I>(plan, after, program);
    assert(observed =~= updated) by {
        assert forall |i: int| 0 <= i < updated.len() implies
            #[trigger] observed[i] == updated[i] by {
            if i != index {
                let slot = program.keys[i];
                let addresses = plan.lanes(slot);
                assert(addresses.to_set().disjoint(plan.lanes(program.keys[index]).to_set()));
                addresses.to_set_ensures();
                assert(observe::<F, I>(plan, after, slot) =~= observe::<F, I>(plan, before, slot)) by {
                    assert forall |k: int| 0 <= k < addresses.len() implies
                        read::<F, I>(after, #[trigger] addresses[k]) == read::<F, I>(before, addresses[k]) by {
                        assert(addresses.contains(addresses[k]));
                        assert(addresses.to_set().contains(addresses[k]));
                    }
                }
            }
        }
    }
}

/// The packed phase bits are disjoint from the line-start marker read by
/// placement, even when the finishing slot belongs to the line's child.
proof fn phase_keeps_wrap_mark(word: u32, index: u32)
    requires index < kernel::N_SLOTS,
    ensures kernel::phase_word(word, index, kernel::SOLVED) & NodeFlags::WRAP_LINE_START
        == word & NodeFlags::WRAP_LINE_START,
{
    let shift = (index * 2) as u32;
    let after = kernel::phase_word(word, index, kernel::SOLVED);
    let mark = NodeFlags::WRAP_LINE_START;
    assert(shift < 20 && mark == 1u32 << 29);
    assert(after == (word & !(3u32 << shift)) | (kernel::SOLVED << shift));
    assert(after & mark == word & mark) by(bit_vector)
        requires shift < 20, mark == 1u32 << 29,
            after == (word & !(3u32 << shift)) | (kernel::SOLVED << shift);
}

pub(crate) proof fn scalar_store_is_local<F: FrameWords, I>(
    before: spec_fn(I) -> NodeLayoutData, after: spec_fn(I) -> NodeLayoutData, slot: Request<I>, value: f32,
)
    requires
        ({
            let left = before(slot.node);
            let right = after(slot.node);
            let index = kernel::slot_index(slot.vertical as usize, slot.kind);
            &&& index < kernel::N_SLOTS
            &&& right.values@ == left.values@.update(index as int, value)
            &&& right.flags.0 == kernel::phase_word(left.flags.0, index as u32, kernel::SOLVED)
            &&& right.parent_flow == left.parent_flow
        }),
        forall |node: I| node != slot.node ==> #[trigger] after(node) == before(node),
    ensures writes_only::<F, I>(before, after, Set::empty().insert(scalar_lane(slot))),
{
    let index = kernel::slot_index(slot.vertical as usize, slot.kind);
    phase_keeps_wrap_mark(before(slot.node).flags.0, index as u32);
    assert forall |lane: Lane<I>| lane != scalar_lane(slot) implies
        #[trigger] read::<F, I>(after, lane) == read::<F, I>(before, lane) by {
        match lane {
            Lane::Size(node, at) if node == slot.node => {
                if at < kernel::N_SLOTS { assert(after(node).values[at as int] == before(node).values[at as int]); }
            },
            Lane::ParentFlow(node, _) if node == slot.node => {},
            Lane::LineStart(node) if node == slot.node => {},
            Lane::Size(node, _) | Lane::ParentFlow(node, _) | Lane::LineStart(node) => {
                assert(after(node) == before(node));
            },
        }
    }
}

pub(crate) open spec fn grid_cells_are_stored<F: FrameWords, I>(
    plan: Packing<I>, records: spec_fn(I) -> NodeLayoutData, request: Request<I>,
    grid: grid::Producer, run: grid::Run,
) -> bool {
    let active = (plan.children)(request.node).filter(|row: Child<I>| row.in_flow);
    let tracks = grid.lines(run);
    &&& match (plan.layout)(request.node) {
        ChildrenLayout::Grid { main_axis, columns: MainAxisCellSize::Width(_), .. } =>
            request.kind is Final && main_axis.index() == request.vertical as usize,
        _ => false,
    }
    &&& read::<F,I>(records, grid_track_lanes(request.node)[0]) == tracks.0
    &&& read::<F,I>(records, grid_track_lanes(request.node)[1]) == tracks.1
    &&& active.len() == grid.items.len()
    &&& forall |i: int| 0 <= i < active.len() ==>
        records((#[trigger] active[i]).node).parent_flow == grid.cell(run, i)
}

/// The queue observes the parent's Final and two track words. With unchanged
/// item order and exact spans, equal observed words also preserve every cell
/// lane that belongs to this producer.
pub(crate) proof fn unchanged_width_grid_keeps_packed_datum<F: FrameWords, I>(
    plan: Packing<I>, records: spec_fn(I) -> NodeLayoutData, next: spec_fn(I) -> NodeLayoutData,
    request: Request<I>, before: grid::Producer, after: grid::Producer, old_run: grid::Run, new_run: grid::Run,
)
    requires grid_cells_are_stored::<F,I>(plan, records, request, before, old_run),
        grid_cells_are_stored::<F,I>(plan, next, request, after, new_run),
        read::<F,I>(records, scalar_lane(request)) == read::<F,I>(next, scalar_lane(request)),
        before.observes(old_run), after.observes(new_run), before.items == after.items,
        before.binary32_to_columns == after.binary32_to_columns, before.encode == after.encode,
        before.vertical == after.vertical, before.layout.backfill == after.layout.backfill,
        before.layout.stride == (before.layout.columns + 63) / 64,
        after.layout.stride == (after.layout.columns + 63) / 64,
        !grid::state::count_changed(before.lines(old_run), after.lines(new_run)),
    ensures observe::<F,I>(plan, records, request) == observe::<F,I>(plan, next, request),
{
    grid::skipped_notification_preserves_assignment(before, after, old_run, new_run);
    let addresses = plan.lanes(request);
    let active = (plan.children)(request.node).filter(|row: Child<I>| row.in_flow);
    let tracks = grid_track_lanes(request.node);
    let cells = Seq::new(2 * active.len(), |i: int| Lane::ParentFlow(active[i / 2].node, i % 2 == 1));
    assert(addresses == seq![scalar_lane(request)] + (tracks + cells));
    assert(observe::<F,I>(plan, records, request) =~= observe::<F,I>(plan, next, request)) by {
        assert forall |i: int| 0 <= i < addresses.len() implies
            read::<F,I>(records, #[trigger] addresses[i]) == read::<F,I>(next, addresses[i]) by {
            if i == 0 { assert(addresses[i] == scalar_lane(request)); }
            else if i < 3 { assert(addresses[i] == tracks[i - 1]); }
            else {
                let cell = (i - 3) / 2;
                assert(0 <= cell < active.len());
                assert(addresses[i] == Lane::ParentFlow(active[cell].node, (i - 3) % 2 == 1));
                assert(before.cell(old_run, cell) == after.cell(new_run, cell));
            }
        }
    }
}

pub(crate) open spec fn line_reset_address<I>(lane: Lane<I>, children: Seq<I>) -> bool {
    match lane {
        Lane::Size(_, _) => false,
        Lane::ParentFlow(node, _) | Lane::LineStart(node) => children.contains(node),
    }
}

pub(crate) proof fn wrap_reset_only_changes_line_words<F: FrameWords, I>(
    before: spec_fn(I) -> NodeLayoutData, after: spec_fn(I) -> NodeLayoutData, children: Seq<I>,
)
    requires sizing_pass::reset_records(before, after, children.to_set()),
    ensures forall |lane: Lane<I>| !line_reset_address(lane, children)
        ==> #[trigger] read::<F, I>(after, lane) == read::<F, I>(before, lane),
{
    reveal(sizing_pass::reset_records);
    children.to_set_ensures();
    assert forall |lane: Lane<I>| !line_reset_address(lane, children) implies
        #[trigger] read::<F, I>(after, lane) == read::<F, I>(before, lane) by {
        match lane {
            Lane::Size(node, _) => { assert(after(node).values == before(node).values); },
            Lane::ParentFlow(node, _) | Lane::LineStart(node) => { assert(after(node) == before(node)); },
        }
    }
}

}
