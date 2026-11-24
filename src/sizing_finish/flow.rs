//! Sizing continuations for wrapping lines and Block margins.
#![allow(unexpected_cfgs)]

use super::*;
#[cfg(verus_keep_ghost)]
use crate::wrap_lines::{self as wrap_plan, kernel as line_kernel};
#[cfg(not(verus_keep_ghost))]
use crate::flow::wrap_lines as line_kernel;
use line_kernel::{LineSource, WrapLine};
use crate::prepare_frame::FrameFloat;
use wrap_metrics::LineRecordAccess;
#[cfg(verus_keep_ghost)]
use wrap_metrics::CacheModel;
#[cfg(verus_keep_ghost)]
use crate::{prepare_frame::FrameWords, wrap_metrics as metric_plan};
#[cfg(verus_keep_ghost)]
use super::super::sizing_child;
#[cfg(verus_keep_ghost)]
use crate::fill::kernel::{self as fill, FloatModel};
#[cfg(not(verus_keep_ghost))]
use crate::solve::fill_compaction as fill;
use crate::vec_memory::CapacityMemory;
#[cfg(verus_keep_ghost)]
use crate::vec_memory::capacity_limit;
use crate::node_data::NodeLayoutData;
use crate::vec_memory::VecMemory;
#[path = "block.rs"]
pub(crate) mod block;
#[cfg(verus_keep_ghost)]
use crate::declarations::Y;
#[cfg(not(verus_keep_ghost))]
use crate::flow::{BlockFlow, BlockItem, BlockMargins, BlockScalar as Scalar, edge_adjoins, implicit_edges, item_adjoins};
#[cfg(verus_keep_ghost)]
use crate::block_flow::kernel::{BlockFlow, BlockItem, BlockMargins, Scalar, edge_adjoins, implicit_edges, item_adjoins};

#[cfg(verus_keep_ghost)]
verus! {

/// Repeatable Wrap effects at the native line-controller boundary.
pub(crate) enum LineWrite<I> {
    Start(I),
    Metric(Option<I>, Option<I>, wrap_metrics::Metric, f32),
}

pub(crate) open spec fn is_share_write<I>(write: LineWrite<I>) -> bool {
    match write {
        LineWrite::Start(_) => true,
        LineWrite::Metric(first, _, metric, _) => first.is_some() && metric is Share,
    }
}

pub(crate) open spec fn is_cross_write<I>(write: LineWrite<I>) -> bool {
    match write {
        LineWrite::Start(_) => false,
        LineWrite::Metric(first, _, metric, _) => first.is_some() && metric is Cross,
    }
}

pub(crate) open spec fn same_channel<I>(before: Map<I, (u32, u32)>, after: Map<I, (u32, u32)>,
    metric: wrap_metrics::Metric,
) -> bool {
    forall |id: I| #[trigger] after.contains_key(id) == before.contains_key(id) && (
        before.contains_key(id) ==> metric_plan::read_word(after[id], metric) == metric_plan::read_word(before[id], metric)
    )
}

proof fn same_channel_transitive<I>(first: Map<I, (u32, u32)>, middle: Map<I, (u32, u32)>,
    last: Map<I, (u32, u32)>, metric: wrap_metrics::Metric,
)
    requires same_channel(first, middle, metric), same_channel(middle, last, metric),
    ensures same_channel(first, last, metric),
{
    assert forall |id: I| #[trigger] last.contains_key(id) == first.contains_key(id) && (
        first.contains_key(id) ==> metric_plan::read_word(last[id], metric) == metric_plan::read_word(first[id], metric)
    ) by {
        assert(middle.contains_key(id) == first.contains_key(id));
        assert(last.contains_key(id) == middle.contains_key(id));
    }
}

pub(crate) open spec fn writes_extend<I>(before: Seq<LineWrite<I>>, after: Seq<LineWrite<I>>,
    keep: spec_fn(LineWrite<I>) -> bool,
) -> bool {
    &&& before.len() <= after.len()
    &&& after.take(before.len() as int) == before
    &&& forall |i: int| before.len() <= i < after.len() ==> keep(#[trigger] after[i])
}

proof fn append_write<I>(before: Seq<LineWrite<I>>, after: Seq<LineWrite<I>>,
    keep: spec_fn(LineWrite<I>) -> bool, event: LineWrite<I>,
)
    requires writes_extend(before, after, keep), keep(event),
    ensures writes_extend(before, after.push(event), keep),
{
    assert(after.push(event).take(before.len() as int) =~= before);
    assert forall |i: int| before.len() <= i < after.push(event).len() implies
        keep(#[trigger] after.push(event)[i]) by {
        if i < after.len() { assert(after.push(event)[i] == after[i]); }
    }
}

proof fn empty_extension<I>(before: Seq<LineWrite<I>>, keep: spec_fn(LineWrite<I>) -> bool)
    ensures writes_extend(before, before, keep),
{
    assert(before.take(before.len() as int) =~= before);
}

pub(crate) open spec fn valid_cursor<I>(rows: Seq<sizing_requests::Child<I>>, cursor: Option<I>) -> bool {
    cursor.is_none() || exists |i: nat| i < rows.len() && #[trigger] sizing_requests::child_at(rows, i) == cursor
}

pub(crate) open spec fn remaining<I>(rows: Seq<sizing_requests::Child<I>>, cursor: Option<I>) -> nat {
    if cursor.is_none() { 0 } else {
        let i = choose |i:nat| i < rows.len() && #[trigger] sizing_requests::child_at(rows, i) == cursor;
        (rows.len() - i) as nat
    }
}

pub(crate) open spec fn cache_rows<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>)
    -> Seq<sizing_requests::Child<A::Id>>
{
    (access.topology().children)(slot.node)
}

pub(crate) open spec fn flow_mode(layout: ChildrenLayout) -> sizing_requests::FlowMode {
    match layout {
        ChildrenLayout::Block => sizing_requests::FlowMode::Block,
        ChildrenLayout::Wrap { axis, .. } => sizing_requests::FlowMode::Wrap(axis is Y),
        _ => sizing_requests::FlowMode::Other,
    }
}

fn snapshot_line_words<A: FinishModel + ?Sized>(access: &A) -> (words: Ghost<Map<A::Id, (u32, u32)>>)
    ensures words@ == access.wrap_words(),
    no_unwind
{
    Ghost(access.wrap_words())
}

fn start_blocks() -> (index: Ghost<nat>)
    ensures index@ == 0,
    no_unwind
{
    Ghost(0nat)
}

fn step_block(index: Ghost<nat>) -> (next: Ghost<nat>)
    ensures next@ == index@ + 1,
    no_unwind
{
    Ghost(index@ + 1)
}

} // verus!

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait FlowShareModel: FinishModel {
    type ShareFloat: fill::FloatOps;
    type MetricFloat: FrameFloat;
    type ShareMemory: CapacityMemory + VecMemory;
    type ShareSpill: fill::SpillMemory;

    spec fn fill_live(&self, child: Self::Id) -> bool;
    spec fn fill_remaining(&self, first: Option<Self::Id>, stop: Option<Self::Id>) -> nat;
    spec fn fill_constraints(&self, axis: Axis, first: Option<Self::Id>, stop: Option<Self::Id>) -> nat;
    spec fn fill_rows(&self, axis: Axis, first: Option<Self::Id>, stop: Option<Self::Id>)
        -> Seq<Option<fill::ChildTerms<fill::FillNumber<Self::ShareFloat>>>>;
}

pub(crate) open spec fn fill_scope<A: FlowShareModel + ?Sized>(before: &A, after: &A) -> bool {
    &&& after.topology() == before.topology()
    &&& after.ready() == before.ready()
    &&& after.wrap_effects() == before.wrap_effects()
    &&& after.wrap_words() == before.wrap_words()
    &&& same_fill_rows(before, after)
}

pub(crate) open spec fn same_fill_rows<A: FlowShareModel + ?Sized>(before: &A, after: &A) -> bool {
    &&& forall |child: A::Id| #[trigger] after.fill_live(child) == before.fill_live(child)
    &&& forall |first: Option<A::Id>, stop: Option<A::Id>|
        #[trigger] after.fill_remaining(first, stop) == before.fill_remaining(first, stop)
    &&& forall |axis: Axis, first: Option<A::Id>, stop: Option<A::Id>|
        #[trigger] after.fill_constraints(axis, first, stop) == before.fill_constraints(axis, first, stop)
    &&& forall |axis: Axis, first: Option<A::Id>, stop: Option<A::Id>|
        #[trigger] after.fill_rows(axis, first, stop) == before.fill_rows(axis, first, stop)
}

pub(crate) open spec fn admitted_fill<A: FlowShareModel + ?Sized>(tree: &A, axis: Axis,
    first: Option<A::Id>, stop: Option<A::Id>,
) -> bool {
    &&& first.is_some() ==> tree.fill_live(first.unwrap())
    &&& tree.fill_rows(axis, None, stop).len() == 0
    &&& tree.fill_constraints(axis, first, stop) <= capacity_limit::<fill::FillChild>()
}

/// The scanner and its publisher use the same half-open sibling range.
pub(crate) open spec fn line_segment<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>,
    first: Option<A::Id>, stop: Option<A::Id>,
) -> Seq<(A::Id, bool)> {
    segment(cache_rows(access, slot), first, stop)
}

pub(crate) open spec fn segment<I>(rows: Seq<sizing_requests::Child<I>>, first: Option<I>, stop: Option<I>) -> Seq<(I, bool)> {
    let start = rows.len() - remaining(rows, first);
    let count = (remaining(rows, first) - remaining(rows, stop)) as nat;
    Seq::new(count, |i: int| {
        let child = rows[start + i];
        (child.node, child.in_flow)
    })
}

pub(crate) closed spec fn cross_result<A: FlowShareModel + ?Sized>(
    rows: Seq<sizing_requests::Child<A::Id>>, initial: Map<A::Id, (u32, u32)>,
    writes: Seq<LineWrite<A::Id>>, spacing: f32,
) -> (f32, Map<A::Id, (u32, u32)>)
    decreases writes.len(),
{
    if writes.len() == 0 {
        (0.0f32, initial)
    } else {
        let (extent, cache) = cross_result::<A>(rows, initial, writes.drop_last(), spacing);
        match writes.last() {
            LineWrite::Metric(first, stop, wrap_metrics::Metric::Cross, cross) => {
                let run = segment(rows, first, stop);
                let next = A::Float::sum(extent, cross);
                let total = if stop.is_some() { A::Float::sum(next, spacing) } else { next };
                (total, metric_plan::stamp(run, run.len(), cache, wrap_metrics::Metric::Cross, A::MetricFloat::word(cross)))
            },
            _ => (extent, cache),
        }
    }
}

pub(crate) open spec fn cross_extent_and_words<A: FlowShareModel + ?Sized>(
    before: &A, after: &A, slot: Request<A::Id>, spacing: f32, extent: f32,
) -> bool {
    let writes = after.wrap_effects().skip(before.wrap_effects().len() as int);
    let result = cross_result::<A>(cache_rows(before, slot), before.wrap_words(), writes, spacing);
    result == (extent, after.wrap_words())
}

proof fn start_cross<A: FlowShareModel + ?Sized>(access: &A, slot: Request<A::Id>, spacing: f32)
    ensures cross_extent_and_words(access, access, slot, spacing, 0.0f32),
{
    reveal(cross_result);
    let writes = access.wrap_effects();
    assert(writes.skip(writes.len() as int) =~= Seq::<LineWrite<A::Id>>::empty());
}

proof fn step_cross<A: FlowShareModel + ?Sized>(
    initial: &A, access: &A, slot: Request<A::Id>, spacing: f32, extent: f32,
    first: Option<A::Id>, stop: Option<A::Id>, cross: f32,
)
    requires access.topology() == initial.topology(), cross_extent_and_words(initial, access, slot, spacing, extent),
        initial.wrap_effects().len() <= access.wrap_effects().len(),
    ensures {
        let event = LineWrite::Metric(first, stop, wrap_metrics::Metric::Cross, cross);
        let writes = access.wrap_effects().push(event).skip(initial.wrap_effects().len() as int);
        let run = line_segment(access, slot, first, stop);
        let next = A::Float::sum(extent, cross);
        let next = if stop.is_some() { A::Float::sum(next, spacing) } else { next };
        cross_result::<A>(cache_rows(initial, slot), initial.wrap_words(), writes, spacing)
            == (next, metric_plan::stamp(run, run.len(), access.wrap_words(), wrap_metrics::Metric::Cross, A::MetricFloat::word(cross)))
    },
{
    reveal(cross_result);
    let event = LineWrite::Metric(first, stop, wrap_metrics::Metric::Cross, cross);
    let all = access.wrap_effects();
    let start = initial.wrap_effects().len() as int;
    assert(all.push(event).skip(start) =~= all.skip(start).push(event));
    let writes = all.push(event).skip(start);
    assert(writes.drop_last() =~= all.skip(start));
    assert(writes.last() == event);
}

pub(crate) open spec fn line_range<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>,
    first: Option<A::Id>, stop: Option<A::Id>,
) -> bool {
    let rows = cache_rows(access, slot);
    first.is_some() && valid_cursor(rows, first) && valid_cursor(rows, stop)
        && remaining(rows, stop) < remaining(rows, first)
}

pub(crate) open spec fn child_inputs<A: FinishModel + ?Sized>(access: &A, child: A::Id) -> sizing_child::ChildInputs {
    let flags = access.finish_flags(child);
    sizing_child::ChildInputs { layout: access.finish_layout(child), values: access.finish_values(child),
        block_item: flags.is_block_item(), block_parent_auto_height: flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0 }
}

closed spec fn margin_extent<A: FlowShareModel + ?Sized>(size: f32, params: LayoutParams, vertical: bool) -> f32 {
    let margins = if vertical { params.margin.y } else { params.margin.x };
    let total = A::ShareFloat::sum(A::MetricFloat::margin_value(margins[0]), A::MetricFloat::margin_value(margins[1]));
    if A::MetricFloat::word(total) & 0x7fff_ffffu32 == 0 { size } else { A::ShareFloat::sum(size, total) }
}

pub(crate) closed spec fn suffix_scan_rows<A: FlowShareModel + ?Sized>(access: &A, slot: Request<A::Id>, axis: Axis,
    first: Option<A::Id>, marked: bool,
) -> Seq<wrap_plan::Item<A::Id, f32>> {
    let rows = cache_rows(access, slot);
    let count = remaining(rows, first);
    let vertical = axis.index() == 1;
    Seq::new(count, |i: int| {
        let row = rows[rows.len() - count + i];
        let child = row.node;
        let inputs = child_inputs(access, child);
        wrap_plan::Item {
            id: child,
            in_flow: row.in_flow,
            marked: marked && (access.finish_flags(child).0 & NodeFlags::WRAP_LINE_START != 0),
            fill: sizing_child::inputs_use_fill(inputs, vertical),
            base: margin_extent::<A>(sizing_child::inputs_before_growth::<A::ShareFloat>(inputs, vertical, false), inputs.layout, vertical),
            main: margin_extent::<A>(sizing_child::input_word(inputs, vertical, Kind::Final), inputs.layout, vertical),
            cross: margin_extent::<A>(sizing_child::inputs_before_growth::<A::ShareFloat>(inputs, !vertical, true), inputs.layout, !vertical),
        }
    })
}

/// A Wrap cross scan ends before the next marked in-flow row, after it has
/// consumed at least one in-flow row. Its extent is the ordered maximum.
closed spec fn cross_prefix<A: FlowShareModel + ?Sized>(items: Seq<wrap_plan::Item<A::Id, f32>>, n: nat) -> (bool, f32)
    decreases n,
{
    if n == 0 { (false, 0.0f32) } else {
        let (seen, cross) = cross_prefix::<A>(items, (n - 1) as nat);
        let item = items[n - 1];
        if item.in_flow { (true, A::ShareFloat::maximum(cross, item.cross)) } else { (seen, cross) }
    }
}

spec fn cross_break<A: FlowShareModel + ?Sized>(items: Seq<wrap_plan::Item<A::Id, f32>>, index: int) -> bool {
    items[index].in_flow && items[index].marked && cross_prefix::<A>(items, index as nat).0
}

spec fn cross_endpoint<A: FlowShareModel + ?Sized>(items: Seq<wrap_plan::Item<A::Id, f32>>, n: nat) -> bool {
    &&& 0 < n <= items.len()
    &&& n == items.len() || cross_break::<A>(items, n as int)
    &&& forall |i: int| 0 <= i < n ==> !#[trigger] cross_break::<A>(items, i)
}

spec fn exact_cross_line<A: FlowShareModel + ?Sized>(
    items: Seq<wrap_plan::Item<A::Id, f32>>, next: Option<A::Id>, cross: f32,
) -> bool {
    exists |i: nat| #[trigger] cross_endpoint::<A>(items, i)
        && next == wrap_plan::at(items, i as int) && cross == cross_prefix::<A>(items, i).1
}

proof fn cross_summary<A: FlowShareModel + ?Sized, S: LineSource<Id = A::Id, Metric = f32>>(source: &S, n: nat)
    requires n <= source.items().len(), source.zero() == 0.0f32,
        forall |l: f32, r: f32| #[trigger] source.cross_max(l, r) == A::ShareFloat::maximum(l, r),
    ensures (wrap_plan::summary(source, None, n).count > 0, wrap_plan::summary(source, None, n).cross)
        == cross_prefix::<A>(source.items(), n),
    decreases n,
{
    reveal(cross_prefix);
    reveal(wrap_plan::summary);
    if n > 0 {
        cross_summary::<A, S>(source, (n - 1) as nat);
    }
}

proof fn project_cross_scan<A: FlowShareModel + ?Sized, S: LineSource<Id = A::Id, Metric = f32>>(
    source: &S, end: nat, line: WrapLine<A::Id>,
)
    requires 0 < end, wrap_plan::endpoint(source, None, end), line.next == wrap_plan::at(source.items(), end as int),
        line.cross == wrap_plan::summary(source, None, end).cross,
        source.zero() == 0.0f32,
        forall |l: f32, r: f32| #[trigger] source.cross_max(l, r) == A::ShareFloat::maximum(l, r),
    ensures exact_cross_line::<A>(source.items(), line.next, line.cross),
{
    let items = source.items();
    cross_summary::<A, S>(source, end);
    assert forall |i: int| 0 <= i < end implies !#[trigger] cross_break::<A>(items, i) by {
        cross_summary::<A, S>(source, i as nat);
        assert(!wrap_plan::stop_at(source, None, i));
    }
    assert(cross_endpoint::<A>(items, end));
}

pub(crate) open spec fn same_scan_fields<A: FinishModel + ?Sized>(before: &A, after: &A) -> bool {
    &&& forall |node: A::Id| #[trigger] after.finish_layout(node) == before.finish_layout(node)
    &&& forall |node: A::Id| #[trigger] after.finish_flags(node) == before.finish_flags(node)
    &&& forall |node: A::Id| #[trigger] after.finish_values(node) == before.finish_values(node)
}

proof fn stable_scan_rows<A: FlowShareModel + ?Sized>(
    before: &A, after: &A, slot: Request<A::Id>, axis: Axis, first: Option<A::Id>, marked: bool,
)
    requires same_scan_fields(before, after), cache_rows(before, slot) == cache_rows(after, slot),
    ensures suffix_scan_rows(before, slot, axis, first, marked) == suffix_scan_rows(after, slot, axis, first, marked),
{
    reveal(suffix_scan_rows);
    let old = suffix_scan_rows(before, slot, axis, first, marked);
    let new = suffix_scan_rows(after, slot, axis, first, marked);
    assert(new =~= old) by {
        assert forall |i: int| 0 <= i < new.len() implies #[trigger] new[i] == old[i] by {
            let rows = cache_rows(after, slot);
            let child = rows[rows.len() - new.len() + i].node;
            assert(after.finish_layout(child) == before.finish_layout(child));
            assert(after.finish_flags(child) == before.finish_flags(child));
            assert(after.finish_values(child) == before.finish_values(child));
        }
    }
}

/// Each consecutive write is the canonical cross result for the next raw
/// sibling suffix. The endpoint is the cursor left by the preceding writes.
pub(crate) closed spec fn cross_trace<A: FlowShareModel + ?Sized>(
    before: &A, slot: Request<A::Id>, axis: Axis, marked: bool, first: Option<A::Id>,
    writes: Seq<LineWrite<A::Id>>, next: Option<A::Id>,
) -> bool
    decreases writes.len(),
{
    if writes.len() == 0 { first == next } else {
        match writes[0] {
            LineWrite::Metric(start, stop, wrap_metrics::Metric::Cross, cross) => {
                &&& start == first && first.is_some()
                &&& exact_cross_line::<A>(suffix_scan_rows(before, slot, axis, first, marked), stop, cross)
                &&& cross_trace(before, slot, axis, marked, stop, writes.skip(1), next)
            },
            _ => false,
        }
    }
}

pub(crate) open spec fn uses_wrap_starts<A: FinishModel + ?Sized>(before: &A, slot: Request<A::Id>, axis: Axis) -> bool {
    producer_phase(before, target(slot.node, axis is Y, Kind::EvenShare)) == cycle_rules::SOLVED
}

pub(crate) open spec fn cross_writes_from<A: FlowShareModel + ?Sized>(
    before: &A, after: &A, slot: Request<A::Id>, axis: Axis, next: Option<A::Id>,
) -> bool {
    let first = sizing_requests::child_at(cache_rows(before, slot), 0);
    cross_trace(before, slot, axis, uses_wrap_starts(before, slot, axis), first,
        after.wrap_effects().skip(before.wrap_effects().len() as int), next)
}

proof fn start_cross_trace<A: FlowShareModel + ?Sized>(access: &A, slot: Request<A::Id>, axis: Axis, first: Option<A::Id>)
    requires first == sizing_requests::child_at(cache_rows(access, slot), 0),
    ensures cross_writes_from(access, access, slot, axis, first),
{
    reveal(cross_trace);
    let writes = access.wrap_effects();
    assert(writes.skip(writes.len() as int) =~= Seq::<LineWrite<A::Id>>::empty());
}

proof fn extend_cross_trace<A: FlowShareModel + ?Sized>(
    before: &A, slot: Request<A::Id>, axis: Axis, marked: bool, start: Option<A::Id>,
    writes: Seq<LineWrite<A::Id>>, first: Option<A::Id>, stop: Option<A::Id>, cross: f32,
)
    requires cross_trace(before, slot, axis, marked, start, writes, first), first.is_some(),
        exact_cross_line::<A>(suffix_scan_rows(before, slot, axis, first, marked), stop, cross),
    ensures cross_trace(before, slot, axis, marked, start,
        writes.push(LineWrite::Metric(first, stop, wrap_metrics::Metric::Cross, cross)), stop),
    decreases writes.len(),
{
    reveal_with_fuel(cross_trace, 2);
    let event = LineWrite::Metric(first, stop, wrap_metrics::Metric::Cross, cross);
    let longer = writes.push(event);
    if writes.len() == 0 {
        assert(start == first);
        assert(longer[0] == event);
        assert(longer.skip(1) =~= Seq::<LineWrite<A::Id>>::empty());
        assert(cross_trace(before, slot, axis, marked, stop, longer.skip(1), stop));
        assert(cross_trace(before, slot, axis, marked, start, longer, stop));
    } else {
        assert(longer[0] == writes[0]);
        assert(longer.skip(1) =~= writes.skip(1).push(event));
        match writes[0] {
            LineWrite::Metric(head, boundary, wrap_metrics::Metric::Cross, size) => {
                assert(head == start && start.is_some());
                assert(exact_cross_line::<A>(suffix_scan_rows(before, slot, axis, head, marked), boundary, size));
                extend_cross_trace(before, slot, axis, marked, boundary, writes.skip(1), first, stop, cross);
                assert(cross_trace(before, slot, axis, marked, boundary, longer.skip(1), stop));
                assert(cross_trace(before, slot, axis, marked, start, longer, stop));
            },
            _ => { assert(false); },
        }
    }
}

proof fn step_cross_trace<A: FlowShareModel + ?Sized>(
    before: &A, access: &A, slot: Request<A::Id>, axis: Axis, marked: bool,
    first: Option<A::Id>, stop: Option<A::Id>, cross: f32,
)
    requires same_scan_fields(before, access), cache_rows(before, slot) == cache_rows(access, slot),
        before.wrap_effects().len() <= access.wrap_effects().len(), marked == uses_wrap_starts(before, slot, axis),
        cross_writes_from(before, access, slot, axis, first), first.is_some(),
        exact_cross_line::<A>(suffix_scan_rows(access, slot, axis, first, marked), stop, cross),
    ensures cross_trace(before, slot, axis, marked, sizing_requests::child_at(cache_rows(before, slot), 0),
        access.wrap_effects().push(LineWrite::Metric(first, stop, wrap_metrics::Metric::Cross, cross))
            .skip(before.wrap_effects().len() as int), stop),
{
    stable_scan_rows(before, access, slot, axis, first, marked);
    let event = LineWrite::Metric(first, stop, wrap_metrics::Metric::Cross, cross);
    let effects = access.wrap_effects();
    let offset = before.wrap_effects().len() as int;
    extend_cross_trace(before, slot, axis, marked, sizing_requests::child_at(cache_rows(before, slot), 0),
        effects.skip(offset), first, stop, cross);
    assert(effects.push(event).skip(offset) =~= effects.skip(offset).push(event));
}

/// Main-axis and disabled-row words do not affect a cross-only scan.
pub(crate) open spec fn same_cross_items<I>(left: Seq<wrap_plan::Item<I, f32>>, right: Seq<wrap_plan::Item<I, f32>>) -> bool {
    &&& left.len() == right.len()
    &&& forall |i: int| 0 <= i < left.len() ==> {
        let l = #[trigger] left[i];
        let r = right[i];
        &&& l.id == r.id && l.in_flow == r.in_flow
        &&& l.in_flow ==> l.marked == r.marked && l.cross == r.cross
    }
}

proof fn equal_cross_prefix<A: FlowShareModel + ?Sized>(
    left: Seq<wrap_plan::Item<A::Id, f32>>, right: Seq<wrap_plan::Item<A::Id, f32>>, n: nat,
)
    requires same_cross_items(left, right), n <= left.len(),
    ensures cross_prefix::<A>(left, n) == cross_prefix::<A>(right, n),
    decreases n,
{
    reveal(cross_prefix);
    if n > 0 {
        equal_cross_prefix::<A>(left, right, (n - 1) as nat);
        assert(left[n - 1].in_flow == right[n - 1].in_flow);
    }
}

proof fn equal_cross_break<A: FlowShareModel + ?Sized>(
    left: Seq<wrap_plan::Item<A::Id, f32>>, right: Seq<wrap_plan::Item<A::Id, f32>>, i: int,
)
    requires same_cross_items(left, right), 0 <= i < left.len(),
    ensures cross_break::<A>(left, i) == cross_break::<A>(right, i),
{
    equal_cross_prefix::<A>(left, right, i as nat);
    assert(left[i].in_flow == right[i].in_flow);
}

proof fn matching_cross_endpoints<A: FlowShareModel + ?Sized>(
    left: Seq<wrap_plan::Item<A::Id, f32>>, right: Seq<wrap_plan::Item<A::Id, f32>>, l: nat, r: nat,
)
    requires same_cross_items(left, right), cross_endpoint::<A>(left, l), cross_endpoint::<A>(right, r),
    ensures l == r,
{
    if l < r {
        equal_cross_break::<A>(left, right, l as int);
        assert(cross_break::<A>(left, l as int));
        assert(!cross_break::<A>(right, l as int));
    }
    if r < l {
        equal_cross_break::<A>(left, right, r as int);
        assert(cross_break::<A>(right, r as int));
        assert(!cross_break::<A>(left, r as int));
    }
}

proof fn unique_cross_line<A: FlowShareModel + ?Sized>(
    left_items: Seq<wrap_plan::Item<A::Id, f32>>, right_items: Seq<wrap_plan::Item<A::Id, f32>>,
    left: (Option<A::Id>, f32), right: (Option<A::Id>, f32),
)
    requires same_cross_items(left_items, right_items),
        exact_cross_line::<A>(left_items, left.0, left.1), exact_cross_line::<A>(right_items, right.0, right.1),
    ensures left == right,
{
    let i = choose |i: nat| #[trigger] cross_endpoint::<A>(left_items, i)
        && left.0 == wrap_plan::at(left_items, i as int) && left.1 == cross_prefix::<A>(left_items, i).1;
    let j = choose |j: nat| #[trigger] cross_endpoint::<A>(right_items, j)
        && right.0 == wrap_plan::at(right_items, j as int) && right.1 == cross_prefix::<A>(right_items, j).1;
    matching_cross_endpoints::<A>(left_items, right_items, i, j);
    equal_cross_prefix::<A>(left_items, right_items, i);
    if i < left_items.len() {
        assert(left_items[i as int].id == right_items[i as int].id);
    }
}

/// Compare the physical sibling order, sizes, declarations, and mark bits
/// observed by the cross scanner in each sizing route.
pub(crate) open spec fn same_cross_inputs<A: FlowShareModel + ?Sized>(
    numeric: &A, full: &A, slot: Request<A::Id>, axis: Axis,
) -> bool {
    let marked = uses_wrap_starts(numeric, slot, axis);
    &&& cache_rows(numeric, slot) == cache_rows(full, slot)
    &&& uses_wrap_starts(full, slot, axis) == marked
    &&& forall |first: Option<A::Id>| same_cross_items(
        #[trigger] suffix_scan_rows(numeric, slot, axis, first, marked), suffix_scan_rows(full, slot, axis, first, marked),
    )
}

proof fn matching_cross_traces<A: FlowShareModel + ?Sized>(
    numeric: &A, full: &A, slot: Request<A::Id>, axis: Axis, first: Option<A::Id>,
    left: Seq<LineWrite<A::Id>>, right: Seq<LineWrite<A::Id>>,
)
    requires same_cross_inputs(numeric, full, slot, axis),
        cross_trace(numeric, slot, axis, uses_wrap_starts(numeric, slot, axis), first, left, None),
        cross_trace(full, slot, axis, uses_wrap_starts(full, slot, axis), first, right, None),
    ensures left == right,
    decreases left.len(),
{
    reveal(cross_trace);
    if first.is_none() {
        assert(left.len() == 0 && right.len() == 0);
        assert(left =~= right);
    } else {
        assert(left.len() > 0 && right.len() > 0);
        match (left[0], right[0]) {
            (LineWrite::Metric(_, left_stop, wrap_metrics::Metric::Cross, left_cross),
                LineWrite::Metric(_, right_stop, wrap_metrics::Metric::Cross, right_cross)) => {
                let marked = uses_wrap_starts(numeric, slot, axis);
                let left_items = suffix_scan_rows(numeric, slot, axis, first, marked);
                let right_items = suffix_scan_rows(full, slot, axis, first, marked);
                unique_cross_line::<A>(left_items, right_items, (left_stop, left_cross), (right_stop, right_cross));
                matching_cross_traces(numeric, full, slot, axis, left_stop, left.skip(1), right.skip(1));
                assert(left[0] == right[0]);
                assert(left.len() == right.len());
                assert(left =~= right) by {
                    assert forall |i: int| 0 <= i < left.len() implies #[trigger] left[i] == right[i] by {
                        if i > 0 {
                            assert(left[i] == left.skip(1)[i - 1]);
                            assert(right[i] == right.skip(1)[i - 1]);
                        }
                    }
                }
            },
            _ => { assert(false); },
        }
    }
}

proof fn cross_extent_ignores_old_words<A: FlowShareModel + ?Sized>(
    rows: Seq<sizing_requests::Child<A::Id>>, left: Map<A::Id, (u32, u32)>, right: Map<A::Id, (u32, u32)>,
    writes: Seq<LineWrite<A::Id>>, spacing: f32,
)
    ensures cross_result::<A>(rows, left, writes, spacing).0 == cross_result::<A>(rows, right, writes, spacing).0,
    decreases writes.len(),
{
    reveal(cross_result);
    if writes.len() != 0 {
        cross_extent_ignores_old_words::<A>(rows, left, right, writes.drop_last(), spacing);
    }
}

pub(crate) proof fn matching_wrap_flow<A: FlowShareModel + ?Sized>(
    numeric: &A, full: &A, numeric_after: &A, full_after: &A,
    slot: Request<A::Id>, axis: Axis, spacing: f32, numeric_extent: f32, full_extent: f32,
)
    requires same_cross_inputs(numeric, full, slot, axis),
        cross_writes_from(numeric, numeric_after, slot, axis, None),
        cross_writes_from(full, full_after, slot, axis, None),
        cross_extent_and_words(numeric, numeric_after, slot, spacing, numeric_extent),
        cross_extent_and_words(full, full_after, slot, spacing, full_extent),
    ensures numeric_extent == full_extent,
        numeric.wrap_words() == full.wrap_words() ==> numeric_after.wrap_words() == full_after.wrap_words(),
        numeric_after.wrap_effects().skip(numeric.wrap_effects().len() as int)
            == full_after.wrap_effects().skip(full.wrap_effects().len() as int),
{
    let left = numeric_after.wrap_effects().skip(numeric.wrap_effects().len() as int);
    let right = full_after.wrap_effects().skip(full.wrap_effects().len() as int);
    let first = sizing_requests::child_at(cache_rows(numeric, slot), 0);
    matching_cross_traces(numeric, full, slot, axis, first, left, right);
    cross_extent_ignores_old_words::<A>(cache_rows(numeric, slot), numeric.wrap_words(), full.wrap_words(), left, spacing);
}

pub(crate) closed spec fn segment_fill_rows<A: FlowShareModel + ?Sized>(access: &A, slot: Request<A::Id>, axis: Axis,
    first: Option<A::Id>, stop: Option<A::Id>,
) -> Seq<Option<fill::ChildTerms<fill::FillNumber<A::ShareFloat>>>> {
    let segment = line_segment(access, slot, first, stop);
    let vertical = axis.index() == 1;
    Seq::new(segment.len(), |i: int| {
        let row = segment[i];
        if !row.1 { None } else {
            let inputs = child_inputs(access, row.0);
            let margins = if vertical { inputs.layout.margin.y } else { inputs.layout.margin.x };
            Some(fill::ChildTerms {
                margins: [fill::FillNumber::new(A::MetricFloat::margin_value(margins[0])),
                          fill::FillNumber::new(A::MetricFloat::margin_value(margins[1]))],
                terms: sizing_child::inputs_fill_terms::<A::ShareFloat>(inputs, vertical, inputs.layout.fill_weight),
            })
        }
    })
}

pub(crate) open spec fn prepared_scan<A: FlowShareModel + ?Sized, S: LineSource<Id = A::Id, Metric = f32>>(
    access: &A, slot: Request<A::Id>, axis: Axis, first: Option<A::Id>, marked: bool,
    available: Option<f32>, spacing: f32, scan: &S,
) -> bool {
    let rows = cache_rows(access, slot);
    let items = scan.items();
    &&& items == suffix_scan_rows(access, slot, axis, first, marked)
    &&& wrap_plan::valid_chain(items)
    &&& wrap_plan::at(items, 0) == first
    &&& remaining(rows, first) == items.len()
    &&& forall |i: int| 0 <= i < items.len() ==> {
        let next = #[trigger] wrap_plan::at(items, i);
        let row = rows[rows.len() - items.len() + i];
        &&& valid_cursor(rows, next) && remaining(rows, next) == items.len() - i
        &&& items[i].id == row.node && items[i].in_flow == row.in_flow
    }
    &&& scan.zero() == 0.0f32
    &&& forall |l: f32, r: f32| #[trigger] scan.summed(l, r)
        == A::ShareFloat::sum(A::ShareFloat::sum(l, spacing), r)
    &&& forall |l: f32, r: f32| #[trigger] scan.cross_max(l, r) == A::ShareFloat::maximum(l, r)
    &&& forall |main: f32, limit: f32| #[trigger] scan.overflows(main, limit) == A::ShareFloat::less(limit, main)
    &&& forall |i: nat| #[trigger] wrap_plan::endpoint(scan, available, i)
        && wrap_plan::summary(scan, available, i).has_fill ==> {
        let stop = wrap_plan::at(items, i as int);
        &&& admitted_fill(access, axis, first, stop)
        &&& access.fill_rows(axis, first, stop) == segment_fill_rows(access, slot, axis, first, stop)
    }
}

pub(crate) open spec fn fill_row_effect<A: FlowShareModel + ?Sized>(tree: &A, child: A::Id, axis: Axis,
    stop: Option<A::Id>, row: Option<(Option<A::Id>, Option<fill::ChildTerms<fill::FillNumber<A::ShareFloat>>>)>,
) -> bool {
    &&& row.is_none() == (tree.fill_rows(axis, Some(child), stop).len() == 0)
    &&& (row matches Some((next, terms)) ==> {
        &&& tree.fill_rows(axis, Some(child), stop) == seq![terms] + tree.fill_rows(axis, next, stop)
        &&& tree.fill_remaining(next, stop) < tree.fill_remaining(Some(child), stop)
        &&& tree.fill_constraints(axis, next, stop) + (if fill::has_resolved_constraint(terms) { 1nat } else { 0nat })
            == tree.fill_constraints(axis, Some(child), stop)
        &&& next.is_some() ==> tree.fill_live(next.unwrap())
    })
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait FlowShareModel: FinishModel {
    type ShareFloat: fill::FloatOps;
    type MetricFloat: FrameFloat;
    type ShareMemory: CapacityMemory + VecMemory;
    type ShareSpill: fill::SpillMemory;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FlowAccess: IntrinsicRows + block::Model<Self::Id> + FlowShareModel {
    type MarkedScan<'a>: LineSource<Id = Self::Id, Metric = f32> where Self: 'a;
    type FreshScan<'a>: LineSource<Id = Self::Id, Metric = f32> where Self: 'a;
    type LineRecords<'a>: wrap_metrics::LineRecordAccess<Id = Self::Id> where Self: 'a;

    #[cfg_attr(verus_keep_ghost, verus_spec(layout =>
        ensures flow_mode(layout) == (self.topology().flow_mode)(parent),
            layout == self.finish_layout(parent).children_layout,
        no_unwind
    ))]
    fn flow_layout(&self, parent: Self::Id) -> ChildrenLayout;

    #[cfg_attr(verus_keep_ghost, verus_spec(scan =>
        requires first.is_some(), valid_cursor(cache_rows(self, slot), first), ready_inputs(self, slot),
        ensures prepared_scan(self, slot, axis, first, true, available, spacing, &scan),
        no_unwind
    ))]
    fn marked_scan<'a>(
        &'a self, slot: Request<Self::Id>, axis: Axis, first: Option<Self::Id>, available: Option<f32>, spacing: f32,
    ) -> Self::MarkedScan<'a>;

    #[cfg_attr(verus_keep_ghost, verus_spec(scan =>
        requires first.is_some(), valid_cursor(cache_rows(self, slot), first), ready_inputs(self, slot),
        ensures prepared_scan(self, slot, axis, first, false, available, spacing, &scan),
        no_unwind
    ))]
    fn fresh_scan<'a>(
        &'a self, slot: Request<Self::Id>, axis: Axis, first: Option<Self::Id>, available: Option<f32>, spacing: f32,
    ) -> Self::FreshScan<'a>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            final(self).wrap_effects() == old(self).wrap_effects().push(LineWrite::Start(next)),
            final(self).wrap_words() == old(self).wrap_words(),
            same_fill_rows(old(self), final(self)),
        no_unwind
    ))]
    fn mark_line(&mut self, next: Self::Id);

    #[cfg_attr(verus_keep_ghost, verus_spec(records =>
        requires line_range(old(self), slot, first, stop),
        ensures records.run() == line_segment(old(self), slot, first, stop),
            records.cache() == old(self).wrap_words(), records.stop() == stop,
            metric_plan::distinct(records.run(), stop),
            first == metric_plan::cursor(records.run(), stop, 0),
            forall |i: int| 0 <= i < records.run().len() ==>
                records.cache().contains_key((#[trigger] records.run()[i]).0),
            final(self).wrap_words() == records.returned_cache(),
            final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            final(self).wrap_effects() == old(self).wrap_effects().push(LineWrite::Metric(first, stop, metric, value)),
            metric is Cross ==> same_scan_fields(old(self), final(self)),
        no_unwind
    ))]
    fn stamp_source<'a>(&'a mut self, slot: Request<Self::Id>, first: Option<Self::Id>, stop: Option<Self::Id>,
        metric: wrap_metrics::Metric, value: f32,
    ) -> Self::LineRecords<'a>;

    #[cfg_attr(verus_keep_ghost, verus_spec(first =>
        ensures first == sizing_requests::child_at((self.topology().children)(parent), 0),
            admitted_fill(self, axis, first, None),
            self.fill_rows(axis, first, None) == segment_fill_rows(self,
                sizing_requests::target(parent, axis.index() == 1, Kind::EvenShare), axis, first, None),
        no_unwind
    ))]
    fn first_fill(&self, parent: Self::Id, axis: Axis) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(row =>
        requires self.fill_live(child),
        ensures fill_row_effect(self, child, axis, stop, row),
        no_unwind
    ))]
    fn fill_row(&self, child: Self::Id, axis: Axis, stop: Option<Self::Id>)
        -> Option<(Option<Self::Id>, Option<fill::ChildTerms<fill::FillNumber<Self::ShareFloat>>>)>;

    #[cfg_attr(verus_keep_ghost, verus_spec(spill =>
        ensures spill.len() == 0, fill_scope(old(self), final(self)),
        no_unwind
    ))]
    fn take_fill_spill(&mut self) -> Vec<fill::FillChild>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires spill.len() == 0,
        ensures fill_scope(old(self), final(self)),
        no_unwind
    ))]
    fn return_fill_spill(&mut self, spill: Vec<fill::FillChild>);

    #[cfg_attr(verus_keep_ghost, verus_spec(record =>
        ensures *record == self.block_record_value(node), record.values == self.finish_values(node),
            record.flags == self.finish_flags(node), no_unwind
    ))]
    fn block_record(&self, node: Self::Id) -> &NodeLayoutData;

    #[cfg_attr(verus_keep_ghost, verus_spec(record =>
        ensures *record == old(self).block_record_value(node), *final(record) == final(self).block_record_value(node),
            final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            final(self).wrap_effects() == old(self).wrap_effects(), final(self).block_margin_arena() == old(self).block_margin_arena(),
            forall |id: Self::Id| id != node ==> #[trigger] final(self).block_record_value(id) == old(self).block_record_value(id),
        no_unwind
    ))]
    fn edit_block_record(&mut self, node: Self::Id) -> &mut NodeLayoutData;

    #[cfg_attr(verus_keep_ghost, verus_spec(arena =>
        ensures arena@ == old(self).block_margin_arena(), final(arena)@ == final(self).block_margin_arena(),
            arena.len() < isize::MAX as usize, final(self).topology() == old(self).topology(),
            final(self).ready() == old(self).ready(), final(self).wrap_effects() == old(self).wrap_effects(),
            forall |id: Self::Id| #[trigger] final(self).block_record_value(id) == old(self).block_record_value(id),
            forall |id: Self::Id| #[trigger] final(self).finish_layout(id) == old(self).finish_layout(id),
        no_unwind
    ))]
    fn block_margins(&mut self) -> &mut Vec<BlockMargins<Self::Block>>;

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == Self::lift(value), no_unwind))]
    fn lift_block(value: f32) -> Self::Block;

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == Self::lower(value), no_unwind))]
    fn lower_block(value: Self::Block) -> f32;
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires line_range(old(access), slot, first, stop),
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        final(access).wrap_effects() == old(access).wrap_effects().push(LineWrite::Metric(first, stop, metric, value)),
        ({
            let run = line_segment(old(access), slot, first, stop);
            final(access).wrap_words() == metric_plan::stamp(run, run.len(), old(access).wrap_words(), metric,
                A::MetricFloat::word(value))
        }),
        same_channel(old(access).wrap_words(), final(access).wrap_words(), metric_plan::other(metric)),
        metric is Cross ==> same_scan_fields(old(access), final(access)),
    no_unwind
))]
fn stamp_line<A: FlowAccess>(access: &mut A, slot: Request<A::Id>, first: Option<A::Id>, stop: Option<A::Id>,
    metric: wrap_metrics::Metric, value: f32,
) {
    let mut records = access.stamp_source(slot, first, stop, metric, value);
    wrap_metrics::publish_line::<_, A::MetricFloat>(&mut records, first, stop, metric, value);
    records.finish();
    #[cfg(verus_keep_ghost)]
    proof! {
        let run = line_segment(old(access), slot, first, stop);
        let before = old(access).wrap_words();
        let after = access.wrap_words();
        let bits = A::MetricFloat::word(value);
        assert forall |id: A::Id| #[trigger] after.contains_key(id) == before.contains_key(id) && (
            before.contains_key(id) ==> metric_plan::read_word(after[id], metric_plan::other(metric))
                == metric_plan::read_word(before[id], metric_plan::other(metric))
        ) by {
            metric_plan::stamp_preserves_other_words(run, run.len(), before, metric, bits, id);
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(line =>
    requires first.is_some(), valid_cursor(cache_rows(access, slot), first), ready_inputs(access, slot),
    ensures valid_cursor(cache_rows(access, slot), line.next),
        remaining(cache_rows(access, slot), line.next) < remaining(cache_rows(access, slot), first),
        line.has_fill ==> admitted_fill(access, axis, first, line.next),
        line.has_fill ==> access.fill_rows(axis, first, line.next) == segment_fill_rows(access, slot, axis, first, line.next),
        available.is_none() ==> exact_cross_line::<A>(suffix_scan_rows(access, slot, axis, first, marked), line.next, line.cross),
    no_unwind
))]
fn scan_line<A: FlowAccess>(access: &A, slot: Request<A::Id>, axis: Axis,
    first: Option<A::Id>, available: Option<f32>, spacing: f32, marked: bool,
) -> WrapLine<A::Id> {
    if marked {
        let source = access.marked_scan(slot, axis, first, available, spacing);
        scan_prepared(access, slot, axis, first, available, spacing, true, &source)
    } else {
        let source = access.fresh_scan(slot, axis, first, available, spacing);
        scan_prepared(access, slot, axis, first, available, spacing, false, &source)
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(line =>
    requires first.is_some(), prepared_scan(_access, _slot, _axis, first, _marked, available, _spacing, source),
    ensures valid_cursor(cache_rows(_access, _slot), line.next),
        remaining(cache_rows(_access, _slot), line.next) < remaining(cache_rows(_access, _slot), first),
        line.has_fill ==> admitted_fill(_access, _axis, first, line.next),
        line.has_fill ==> _access.fill_rows(_axis, first, line.next) == segment_fill_rows(_access, _slot, _axis, first, line.next),
        available.is_none() ==> exact_cross_line::<A>(suffix_scan_rows(_access, _slot, _axis, first, _marked), line.next, line.cross),
    no_unwind
))]
fn scan_prepared<A: FlowAccess, S: LineSource<Id = A::Id, Metric = f32>>(_access: &A, _slot: Request<A::Id>,
    _axis: Axis, first: Option<A::Id>, available: Option<f32>, _spacing: f32, _marked: bool, source: &S,
) -> WrapLine<A::Id> {
    let line = line_kernel::scan_line(source, first, available);
    #[cfg(verus_keep_ghost)]
    proof! {
        let items = source.items();
        let end = choose |i: nat| #[trigger] wrap_plan::endpoint(source, available, i)
            && line.next == wrap_plan::at(items, i as int)
            && line.has_fill == wrap_plan::summary(source, available, i).has_fill
            && line.cross == wrap_plan::summary(source, available, i).cross
            && (items.len() > 0 ==> i > 0);
        if end < items.len() {
            assert(remaining(cache_rows(_access, _slot), line.next) == items.len() - end);
        } else {
            assert(line.next.is_none());
        }
        if available.is_none() {
            project_cross_scan::<A, S>(source, end, line);
        }
    }
    line
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct FlowFill<'a, A> {
    access: &'a mut A,
    axis: Axis,
}

#[cfg(verus_keep_ghost)]
verus! {
type FlowState<I> = (sizing_requests::Topology<I>, Set<(I, usize)>, Seq<LineWrite<I>>, Map<I, (u32, u32)>);

spec fn flow_state<A: FlowAccess>(access: &A) -> FlowState<A::Id> {
    (access.topology(), access.ready(), access.wrap_effects(), access.wrap_words())
}

impl<'a, A: FlowAccess> fill::ChildrenModel for FlowFill<'a, A> {
    type Child = A::Id;
    type Number = fill::FillNumber<A::ShareFloat>;
    type Fixed = (Axis, FlowState<A::Id>, FlowState<A::Id>);

    // A borrowed controller preserves both its current frame and the frame
    // returned to the caller when the borrow ends.
    #[verifier::prophetic]
    closed spec fn fixed(&self) -> Self::Fixed {
        (self.axis, flow_state(self.access), flow_state(final(self.access)))
    }
    closed spec fn live(&self, child: A::Id) -> bool { self.access.fill_live(child) }
    closed spec fn ordered_rows(&self, first: Option<A::Id>, end: Option<A::Id>)
        -> Seq<Option<fill::ChildTerms<Self::Number>>> {
        self.access.fill_rows(self.axis, first, end)
    }
    closed spec fn remaining(&self, first: Option<A::Id>, end: Option<A::Id>) -> nat {
        self.access.fill_remaining(first, end)
    }
    closed spec fn remaining_constraints(&self, first: Option<A::Id>, end: Option<A::Id>) -> nat {
        self.access.fill_constraints(self.axis, first, end)
    }
}
}

#[cfg(not(verus_keep_ghost))]
impl<'a, A: FlowAccess> fill::ChildrenModel for FlowFill<'a, A> {
    type Child = A::Id;
    type Number = fill::FillNumber<A::ShareFloat>;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<'a, A: FlowAccess> fill::Children for FlowFill<'a, A> {
    #[inline(always)]
    fn read(&self, child: A::Id, end: Option<A::Id>) -> Option<(Option<A::Id>, Option<fill::ChildTerms<Self::Number>>)> {
        self.access.fill_row(child, self.axis, end)
    }

    #[inline(always)]
    fn take_spill(&mut self) -> Vec<fill::FillChild> { self.access.take_fill_spill() }

    #[inline(always)]
    fn return_spill(&mut self, spill: Vec<fill::FillChild>) { self.access.return_fill_spill(spill); }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires admitted_fill(old(access), axis, first, stop),
    ensures final(access).topology() == old(access).topology(),
        final(access).ready() == old(access).ready(),
        final(access).wrap_effects() == old(access).wrap_effects(),
        final(access).wrap_words() == old(access).wrap_words(),
        out == fill::share_for_rows::<A::ShareFloat>(old(access).fill_rows(axis, first, stop), budget),
    no_unwind
))]
fn resolve_flow_fill<A: FlowAccess>(access: &mut A, axis: Axis, budget: f32,
    first: Option<A::Id>, stop: Option<A::Id>,
) -> f32 {
    let share = {
        let mut input = FlowFill { access: &mut *access, axis };
        let result = fill::distribute_with::<_, A::ShareFloat, A::ShareSpill, A::ShareMemory>(
            &mut input, first, stop, budget,
        );
        #[cfg(verus_keep_ghost)]
        proof! { assert(flow_state(input.access) == flow_state(old(access))); }
        result
    };
    #[cfg(verus_keep_ghost)]
    proof! { assert(flow_state(access) == flow_state(old(access))); }
    share
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn share_inner<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    let size = access.finish_values(slot.node)[key(target(slot.node, slot.vertical, Kind::Final)).1 as int];
    inner_extent::<A::Float>(size, pad_extent::<A::Float>(access.finish_layout(slot.node), slot.axis()))
}

pub(crate) open spec fn even_share_value<A: FlowShareModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    if access.finish_layout(slot.node).children_layout is Wrap {
        0.0f32
    } else {
        let first = sizing_requests::child_at(cache_rows(access, slot), 0);
        let gaps = declared_gaps(access, slot.node, slot.axis());
        let budget = inner_extent::<A::Float>(share_inner(access, slot), gaps);
        let rows = segment_fill_rows(access, slot, slot.axis(), first, None);
        fill::share_for_rows::<A::ShareFloat>(rows, budget)
    }
}

pub(crate) open spec fn same_stack_share_inputs<A: FlowShareModel + ?Sized>(
    numeric: &A, full: &A, slot: Request<A::Id>,
) -> bool {
    let node = slot.node;
    let size = key(target(node, slot.vertical, Kind::Final)).1 as int;
    let first_numeric = sizing_requests::child_at(cache_rows(numeric, slot), 0);
    let first_full = sizing_requests::child_at(cache_rows(full, slot), 0);
    &&& numeric.finish_layout(node).children_layout == full.finish_layout(node).children_layout
    &&& !(numeric.finish_layout(node).children_layout is Wrap)
    &&& numeric.finish_values(node)[size] == full.finish_values(node)[size]
    &&& numeric.finish_layout(node).padding == full.finish_layout(node).padding
    &&& numeric.finish_child_count(node) == full.finish_child_count(node)
    &&& segment_fill_rows(numeric, slot, slot.axis(), first_numeric, None)
        == segment_fill_rows(full, slot, slot.axis(), first_full, None)
}

}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(share =>
    requires slot.kind is EvenShare, ready_inputs(old(access), slot),
    ensures share == even_share_value(old(access), slot),
        final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        writes_extend(old(access).wrap_effects(), final(access).wrap_effects(), |event| is_share_write(event)),
        same_channel(old(access).wrap_words(), final(access).wrap_words(), wrap_metrics::Metric::Cross),
        (old(access).topology().flow_mode)(slot.node) is Wrap || (
            final(access).wrap_effects() == old(access).wrap_effects()
                && final(access).wrap_words() == old(access).wrap_words()
        ),
    no_unwind
))]
pub(crate) fn measure_share<A: FlowAccess>(access: &mut A, slot: Request<A::Id>) -> f32 {
    let axis = slot.axis();
    let final_slot = target(slot.node, slot.vertical, Kind::Final);
    #[cfg(verus_keep_ghost)]
    proof! {
        let deps = sizing_requests::inputs(access.topology(), slot);
        assert(deps.len() > 0 && deps[0] == final_slot);
        read_dependency(access, slot, final_slot);
    }
    let own = inner::<A::Float>(read(access, final_slot), padding_for::<A::Float>(access.params(slot.node), axis));
    let first = access.first_fill(slot.node, axis);
    #[cfg(verus_keep_ghost)]
    proof! { empty_extension(access.wrap_effects(), |event| is_share_write(event)); }
    if let ChildrenLayout::Wrap { spacing, .. } = access.flow_layout(slot.node) {
        let mut first = first;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant access.topology() == old(access).topology(), access.ready() == old(access).ready(),
                valid_cursor(cache_rows(access, slot), first), ready_inputs(access, slot),
                writes_extend(old(access).wrap_effects(), access.wrap_effects(), |event| is_share_write(event)),
                same_channel(old(access).wrap_words(), access.wrap_words(), wrap_metrics::Metric::Cross),
            decreases remaining(cache_rows(access, slot), first),
        ))]
        while first.is_some() {
            let line = scan_line(access, slot, axis, first, Some(own), spacing, false);
            if let Some(next) = line.next {
                #[cfg(verus_keep_ghost)]
                proof! {
                    append_write(old(access).wrap_effects(), access.wrap_effects(),
                        |event| is_share_write(event), LineWrite::Start(next));
                }
                access.mark_line(next);
            }
            if line.has_fill {
                let gaps = spacing * line.count.saturating_sub(1) as f32;
                let share = resolve_flow_fill(access, axis, A::Float::max(own - gaps, 0.0), first, line.next);
                #[cfg(verus_keep_ghost)]
                proof! {
                    append_write(old(access).wrap_effects(), access.wrap_effects(), |event| is_share_write(event),
                        LineWrite::Metric(first, line.next, wrap_metrics::Metric::Share, share));
                }
                stamp_line(access, slot, first, line.next, wrap_metrics::Metric::Share, share);
            }
            first = line.next;
        }
        return 0.0;
    }
    let budget = inner::<A::Float>(own, access.stack_gaps(slot.node, axis));
    resolve_flow_fill(access, axis, budget, first, None)
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn block_items<A: FlowAccess>(access: &A, slot: Request<A::Id>, count: nat) -> Seq<BlockItem<A::Block>>
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let prev = (count - 1) as nat;
        let row = cache_rows(access, slot)[prev as int];
        let items = block_items(access, slot, prev);
        if row.in_flow { items.push(block::item(access, row.node)) } else { items }
    }
}

pub(crate) open spec fn block_result<A: FlowAccess>(access: &A, slot: Request<A::Id>) -> (A::Block, BlockMargins<A::Block>) {
    let (top, bottom) = block::edges(access, slot.node);
    crate::block_flow::finish(crate::block_flow::replay(block_items(access, slot, cache_rows(access, slot).len()), top, bottom))
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(size =>
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        final(access).wrap_effects() == old(access).wrap_effects(),
        size == A::lower(block_result(old(access), slot).0),
        final(access).block_margin_arena() == if block::explicit::<A>(old(access).block_record_value(slot.node), block_result(old(access), slot).1) {
            old(access).block_margin_arena().push(block_result(old(access), slot).1)
        } else { old(access).block_margin_arena() },
    no_unwind
))]
fn block_flow<A: FlowAccess>(access: &mut A, slot: Request<A::Id>) -> f32 {
    let mut flow = block::start(access, slot.node);
    let mut next = access.first_child(slot.node);
    #[cfg(verus_keep_ghost)]
    let mut cursor = start_blocks();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant access.topology() == old(access).topology(), access.ready() == old(access).ready(),
            access.wrap_effects() == old(access).wrap_effects(), access.block_margin_arena() == old(access).block_margin_arena(),
            forall |id: A::Id| #[trigger] access.block_record_value(id) == old(access).block_record_value(id),
            forall |id: A::Id| #[trigger] access.finish_layout(id) == old(access).finish_layout(id),
            flow == crate::block_flow::replay(block_items(old(access), slot, cursor@),
                block::edges(old(access), slot.node).0, block::edges(old(access), slot.node).1),
            cursor@ <= cache_rows(access, slot).len(),
            next == sizing_requests::child_at(cache_rows(access, slot), cursor@),
        decreases cache_rows(access, slot).len() - cursor@,
    ))]
    loop {
        let Some(child) = next else {
            #[cfg(verus_keep_ghost)]
            proof! {
                if cursor@ < cache_rows(access, slot).len() {
                    assert(sizing_requests::child_at(cache_rows(access, slot), cursor@).is_some());
                }
                assert(cursor@ == cache_rows(access, slot).len());
            }
            let (height, margins) = flow.finish();
            block::store(access, slot.node, margins);
            return A::lower_block(height);
        };
        let (following, in_flow) = access.child(slot.node, child);
        next = following;
        if in_flow {
            let item = block::read_child(access, child);
            #[cfg(verus_keep_ghost)]
            proof! {
                let items = block_items(old(access), slot, cursor@ + 1);
                assert(item == block::item(old(access), child));
                assert(items == block_items(old(access), slot, cursor@).push(item));
                assert(items.drop_last() =~= block_items(old(access), slot, cursor@));
            }
            flow.push(item);
        }
        #[cfg(verus_keep_ghost)]
        { cursor = step_block(cursor); }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(extent =>
    requires slot.kind is Flow, ready_inputs(old(access), slot),
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        writes_extend(old(access).wrap_effects(), final(access).wrap_effects(), |event| is_cross_write(event)),
        (old(access).topology().flow_mode)(slot.node) is Block ==> extent == A::lower(block_result(old(access), slot).0),
        (old(access).topology().flow_mode)(slot.node) is Other ==> extent == 0.0f32,
        (old(access).topology().flow_mode)(slot.node) is Wrap
            || final(access).wrap_effects() == old(access).wrap_effects(),
        match old(access).finish_layout(slot.node).children_layout {
            ChildrenLayout::Wrap { axis, line_spacing, .. } => {
                &&& cross_writes_from(old(access), final(access), slot, axis, None)
                &&& cross_extent_and_words(old(access), final(access), slot, line_spacing, extent)
                &&& same_channel(old(access).wrap_words(), final(access).wrap_words(), wrap_metrics::Metric::Share)
            },
            _ => true,
        },
    no_unwind
))]
pub(super) fn measure_flow<A: FlowAccess>(access: &mut A, slot: Request<A::Id>) -> f32 {
    #[cfg(verus_keep_ghost)]
    proof! { empty_extension(access.wrap_effects(), |event| is_cross_write(event)); }
    match access.flow_layout(slot.node) {
        ChildrenLayout::Wrap { axis, spacing, line_spacing, .. } => {
            #[cfg(verus_keep_ghost)]
            proof! {
                let share = target(slot.node, axis is Y, Kind::EvenShare);
                let deps = sizing_requests::inputs(access.topology(), slot);
                assert(deps.len() > 0 && deps[0] == share);
                read_dependency(access, slot, share);
            }
            // Until a back edge finishes the share, the line marks are provisional.
            let marked = access.flags(slot.node).check_state(axis, Kind::EvenShare) == cycle_rules::SOLVED;
            let mut next = access.first_child(slot.node);
            let mut extent = 0.0;
            #[cfg(verus_keep_ghost)]
            proof! {
                start_cross(access, slot, line_spacing);
                start_cross_trace(access, slot, axis, next);
                assert(marked == uses_wrap_starts(access, slot, axis));
            }
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant access.topology() == old(access).topology(), access.ready() == old(access).ready(),
                    valid_cursor(cache_rows(access, slot), next), ready_inputs(access, slot),
                    writes_extend(old(access).wrap_effects(), access.wrap_effects(), |event| is_cross_write(event)),
                    same_channel(old(access).wrap_words(), access.wrap_words(), wrap_metrics::Metric::Share),
                    cross_extent_and_words(old(access), access, slot, line_spacing, extent),
                    same_scan_fields(old(access), access), marked == uses_wrap_starts(old(access), slot, axis),
                    cross_writes_from(old(access), access, slot, axis, next),
                decreases remaining(cache_rows(access, slot), next),
            ))]
            while next.is_some() {
                let line = scan_line(access, slot, axis, next, None, spacing, marked);
                #[cfg(verus_keep_ghost)]
                proof! {
                    append_write(old(access).wrap_effects(), access.wrap_effects(), |event| is_cross_write(event),
                        LineWrite::Metric(next, line.next, wrap_metrics::Metric::Cross, line.cross));
                    step_cross(old(access), access, slot, line_spacing, extent, next, line.next, line.cross);
                    step_cross_trace(old(access), access, slot, axis, marked, next, line.next, line.cross);
                }
                #[cfg(verus_keep_ghost)]
                let before_stamp = snapshot_line_words(access);
                stamp_line(access, slot, next, line.next, wrap_metrics::Metric::Cross, line.cross);
                #[cfg(verus_keep_ghost)]
                proof! {
                    same_channel_transitive(old(access).wrap_words(), before_stamp@, access.wrap_words(), wrap_metrics::Metric::Share);
                }
                next = line.next;
                extent = A::Float::add(extent, line.cross);
                if next.is_some() {
                    extent = A::Float::add(extent, line_spacing);
                }
            }
            extent
        }
        ChildrenLayout::Block => block_flow(access, slot),
        _ => 0.0,
    }
}
