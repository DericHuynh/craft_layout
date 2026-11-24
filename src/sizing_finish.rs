//! Value reads and publication for a slot whose sizing dependencies are ready.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(not(verus_keep_ghost))]
use super::{cycle_rules, grid_state, sizing_requests};
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel as cycle_rules;
#[cfg(verus_keep_ghost)]
use crate::grid::frame::state as grid_state;
#[cfg(verus_keep_ghost)]
use super::sizing_requests;

#[cfg(not(verus_keep_ghost))]
use crate::{placement_geometry::FloatBounds, prepare_leaf::aspect_size};
#[cfg(verus_keep_ghost)]
use crate::{placement::geometry::{FloatBounds, FloatClassification}, prepare_frame::FrameWords,
    prepare_leaf::{aspect, aspect_size}};
use crate::prepare_frame::FrameFloat;

use crate::declarations::{Axis, ChildrenLayout, LayoutParams, MainAxisCellSize, Size};
use crate::node_flags::NodeFlags;
#[cfg(not(verus_keep_ghost))]
use crate::flow::wrap_metrics;
#[cfg(verus_keep_ghost)]
use crate::wrap_metrics::kernel as wrap_metrics;
use cycle_rules::{Kind, N_SLOTS};
use sizing_requests::{Request, target};

#[path = "sizing_finish/intrinsic.rs"]
mod intrinsic;
use intrinsic::fit_content;
pub(crate) use intrinsic::{IntrinsicContent, IntrinsicRows};
#[cfg(any(feature = "incremental", verus_keep_ghost))]
pub(crate) use intrinsic::IntrinsicOracle;
#[cfg(verus_keep_ghost)]
pub(crate) use intrinsic::{flow_intrinsic, flow_intrinsic_value, free_intrinsic, free_intrinsic_value,
    grid_intrinsic, grid_intrinsic_value, intrinsic_flow_word, largest_intrinsic,
    largest_intrinsic_value, measurement_requests_for, opposite_content, own_extent, stack_intrinsic,
    stack_intrinsic_value, stack_intrinsic_warnings, stack_rows};
#[cfg(verus_keep_ghost)]
use intrinsic::{intrinsic_effects_stable, measurement_inputs_stable, text_request};
#[cfg(feature = "incremental")]
pub(crate) use intrinsic::intrinsic_content;

#[path = "sizing_finish/flow.rs"]
mod flow;
use flow::measure_flow;
pub(crate) use flow::{FlowAccess, FlowShareModel, measure_share};
pub(crate) use flow::block;

#[path = "sizing_finish/phase.rs"]
pub(crate) mod phase;

#[cfg(verus_keep_ghost)]
use super::rules::Form;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum Warning {
    MinAboveMax,
    FitContentCollapsed,
    ImpossibleFracChildren,
    NotFinite,
}

// The child declarations stay borrowed while sizing its parent's cell.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct ParentContext<'a> {
    pub(crate) child: &'a LayoutParams,
    pub(crate) layout: ChildrenLayout,
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait FinishModel {
    type Id: Copy + Eq;
    type Float: FrameFloat;
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) trait FinishModel: IntrinsicOracle<Self::Id> {
    type Id: Copy + Eq;
    type Float: FrameFloat;
    spec fn topology(&self) -> sizing_requests::Topology<Self::Id>;
    spec fn ready(&self) -> Set<(Self::Id, usize)>;
    spec fn finish_layout(&self, node: Self::Id) -> LayoutParams;
    spec fn finish_flags(&self, node: Self::Id) -> NodeFlags;
    spec fn finish_values(&self, node: Self::Id) -> [f32; N_SLOTS];
    spec fn finish_child_count(&self, node: Self::Id) -> u32;
    spec fn finish_window(&self) -> crate::declarations::Xy<f32>;
    spec fn finish_effects(&self) -> Seq<FinishEffect<Self::Id>>;
    spec fn wrap_effects(&self) -> Seq<flow::LineWrite<Self::Id>>;
    spec fn wrap_words(&self) -> Map<Self::Id, (u32, u32)>;
}

pub(crate) enum FinishEffect<I> {
    Warning(Request<I>, Warning),
    Publish(Request<I>, f32),
    AssignWidthGrid(Request<I>, f32, f32, bool),
}

pub(crate) open spec fn assigns_width_grid(params: LayoutParams, axis: Axis) -> bool {
    match params.children_layout {
        ChildrenLayout::Grid { main_axis, columns: MainAxisCellSize::Width(_), .. } =>
            main_axis.index() == axis.index(),
        _ => false,
    }
}

pub(crate) open spec fn has_unbounded_final_inputs(params: LayoutParams, axis: Axis, fit: bool) -> bool {
    &&& sizing_requests::raw_size(params, axis.index() == 1, Kind::Min).is_none()
    &&& sizing_requests::raw_size(params, axis.index() == 1, Kind::Max).is_none()
    &&& fit == (sizing_requests::raw_size(params, axis.index() == 1, Kind::Regular)
        is Some && sizing_requests::raw_size(params, axis.index() == 1, Kind::Regular).unwrap() is FitContent)
}

pub(crate) open spec fn permits_direct_final(params: LayoutParams, axis: Axis, flags: NodeFlags) -> bool {
    &&& exists |fit: bool| has_unbounded_final_inputs(params, axis, fit)
        && (!fit || flags.0 & NodeFlags::flex_child(axis) == 0)
    &&& !flags.is_block_item()
}

pub(crate) open spec fn direct_regular<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    access.finish_values(slot.node)[cycle_rules::slot_index(slot.vertical as usize, Kind::Regular) as int]
}

pub(crate) open spec fn canonical_direct_final<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    &&& slot.kind is Final
    &&& permits_direct_final(access.finish_layout(slot.node), slot.axis(), access.finish_flags(slot.node))
    &&& !assigns_width_grid(access.finish_layout(slot.node), slot.axis())
    &&& A::Float::finite_word(direct_regular(access, slot))
}

/// The singleton packed result of a Free intrinsic producer with no in-flow children.
pub(crate) open spec fn free_intrinsic_datum<A: FinishModel + IntrinsicOracle<A::Id> + ?Sized>(
    access: &A, slot: Request<A::Id>,
) -> Option<Seq<u32>> {
    if free_intrinsic(access, slot) {
        Some(seq![A::Float::word(free_intrinsic_value(access, slot))])
    } else { None }
}

/// The packed result of an intrinsic main-axis Stack or Wrap request.
pub(crate) open spec fn stack_intrinsic_datum<A: FinishModel + IntrinsicOracle<A::Id> + ?Sized>(
    access: &A, slot: Request<A::Id>,
) -> Option<Seq<u32>> {
    if stack_intrinsic(access, slot) {
        Some(seq![A::Float::word(stack_intrinsic_value(access, slot))])
    } else { None }
}

pub(crate) open spec fn form(declaration: Option<Size>) -> Option<Form> {
    match declaration {
        None => None,
        Some(size) => Some(size.dependency_form()),
    }
}

pub(crate) open spec fn key<I>(slot: Request<I>) -> (I, usize) {
    (slot.node, cycle_rules::slot_index(slot.vertical as usize, slot.kind))
}

pub(crate) open spec fn is_ready<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    access.ready().contains(key(slot))
}

pub(crate) open spec fn all_inputs_ready<I: Copy>(
    topology: sizing_requests::Topology<I>, ready: Set<(I, usize)>, slot: Request<I>,
) -> bool {
    forall |input: Request<I>| sizing_requests::inputs(topology, slot).contains(input)
        ==> #[trigger] ready.contains(key(input))
}

pub(crate) open spec fn ready_inputs<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    all_inputs_ready(access.topology(), access.ready(), slot)
}

pub(crate) open spec fn regular_present<A: FinishModel>(access: &A, slot: Request<A::Id>) -> bool {
    (access.topology().form)(target(slot.node, slot.vertical, Kind::Regular)).is_some()
}

pub(crate) open spec fn parent_inner<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>, parent: A::Id) -> f32 {
    inner_extent::<A::Float>(
        access.finish_values(parent)[key(target(parent, slot.vertical, Kind::Final)).1 as int],
        pad_extent::<A::Float>(access.finish_layout(parent), slot.axis()),
    )
}

/// A Block item reads the physical parent's Final and padding directly.
pub(crate) open spec fn block_parent_extent<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> Option<f32> {
    match (access.topology().parent)(slot.node) {
        Some(parent) if access.finish_layout(parent).children_layout is Block => Some(parent_inner(access, slot, parent)),
        _ => None,
    }
}

pub(crate) open spec fn line_extent<A: FinishModel + ?Sized>(
    access: &A, child: A::Id, phase: u32, metric: wrap_metrics::Metric,
) -> f32 {
    if phase == cycle_rules::SOLVED {
        let (share, cross) = access.wrap_words()[child];
        A::Float::decode(if metric is Share { share } else { cross })
    } else { 0.0f32 }
}

pub(crate) open spec fn producer_phase<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> u32 {
    cycle_rules::read_state(access.finish_flags(slot.node).0, key(slot).1 as u32)
}

pub(crate) open spec fn grid_track_word<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    let values = access.finish_values(slot.node);
    if slot.vertical { values[cycle_rules::slot_index(1, Kind::Flow) as int] }
    else { values[cycle_rules::slot_index(0, Kind::EvenShare) as int] }
}

pub(crate) open spec fn grid_track<F: FrameFloat>(inner: f32, tracks: f32, spacing: f32) -> GridTrack {
    let count = F::maximum(tracks, 1.0f32);
    let gaps = F::product(spacing, F::difference(tracks, 1.0f32));
    let cell = F::maximum(F::quotient(F::difference(inner, gaps), count), 0.0f32);
    GridTrack { count, cell, spacing }
}

pub(crate) open spec fn grid_span<F: FrameFloat>(grid: GridTrack, span: u16) -> f32 {
    let span = F::minimum(F::count_value(if span == 0 { 1u32 } else { span as u32 }), grid.count);
    F::sum(F::product(span, grid.cell), F::product(F::difference(span, 1.0f32), grid.spacing))
}

/// The child's extent uses the same physical parent records as the native read.
pub(crate) open spec fn parent_extent<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>, fill: bool) -> f32 {
    match (access.topology().parent)(slot.node) {
        None => viewport_extent(access, slot.axis()),
        Some(parent) => {
            let params = access.finish_layout(slot.node);
            let layout = access.finish_layout(parent).children_layout;
            let inner = parent_inner(access, slot, parent);
            if params.free_placement { inner } else {
                let available = match layout {
                    ChildrenLayout::Wrap { axis, .. } if axis.index() != slot.axis().index() => {
                        let phase = producer_phase(access, target(parent, slot.vertical, Kind::Flow));
                        line_extent(access, slot.node, phase, wrap_metrics::Metric::Cross)
                    },
                    ChildrenLayout::Grid { spacing_x, spacing_y, .. } => {
                        let spacing = if slot.vertical { spacing_y } else { spacing_x };
                        let span = if slot.vertical { params.grid_span.y } else { params.grid_span.x };
                        let tracks = grid_track_word(access, target(parent, slot.vertical, Kind::Final));
                        grid_span::<A::Float>(grid_track::<A::Float>(inner, tracks, spacing), span)
                    },
                    ChildrenLayout::Stack { axis, .. } if axis.index() == slot.axis().index() =>
                        A::Float::maximum(A::Float::difference(inner, declared_gaps(access, parent, slot.axis())), 0.0f32),
                    _ => inner,
                };
                if fill && !(layout is Free) {
                    subtract_margins::<A::Float>(available, margin_pair::<A::Float>(params, slot.axis()))
                } else { available }
            }
        },
    }
}

pub(crate) open spec fn shared_fill_extent<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>, parent: A::Id) -> f32 {
    let share = target(parent, slot.vertical, Kind::EvenShare);
    let value = if access.finish_flags(parent).0 & NodeFlags::WRAP_CONTAINER == 0 {
        access.finish_values(parent)[key(share).1 as int]
    } else {
        line_extent(access, slot.node, producer_phase(access, share), wrap_metrics::Metric::Share)
    };
    A::Float::product(value, access.finish_layout(slot.node).fill_weight)
}

pub(crate) open spec fn scalar_declaration<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> Option<Size> {
    if !(slot.kind is Regular || slot.kind is Min || slot.kind is Max) { None } else {
        let flags = access.finish_flags(slot.node);
        sizing_requests::resolved_size(access.finish_layout(slot.node), slot.vertical, slot.kind,
            flags.is_block_item(), flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0)
    }
}

/// The scalar declaration reads its physical inputs before publishing a size.
pub(crate) open spec fn declared_scalar<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> Option<f32> {
    match scalar_declaration(access, slot) {
        Some(Size::Pixels(px)) => Some(px),
        Some(Size::AspectRatio(ratio)) => Some(aspect::<A::Float>(slot.axis(),
            access.finish_values(slot.node)[key(target(slot.node, !slot.vertical, Kind::Final)).1 as int], ratio)),
        Some(Size::Frac(fraction)) => Some(A::Float::product(parent_extent(access, slot, false), fraction)),
        Some(Size::Fill) => Some(match (access.topology().stack_parent)(slot) {
            Some(parent) => shared_fill_extent(access, slot, parent),
            None => parent_extent(access, slot, true),
        }),
        _ => None,
    }
}

pub(crate) open spec fn scalar_effects_stable<A: FinishModel + ?Sized>(before: &A, after: &A) -> bool {
    &&& intrinsic_effects_stable(before, after)
    &&& after.measurement_requests() == before.measurement_requests()
}

pub(crate) open spec fn viewport_extent<A: FinishModel + ?Sized>(access: &A, axis: Axis) -> f32 {
    if axis is X { access.finish_window().x } else { access.finish_window().y }
}

pub(crate) open spec fn reads_parent_extent<A: FinishModel + ?Sized>(
    access: &A, slot: Request<A::Id>,
) -> bool {
    match (access.topology().form)(slot) {
        Some(Form::Fraction) => true,
        Some(Form::Fill) => (access.topology().stack_parent)(slot).is_none(),
        _ => false,
    }
}

pub(crate) open spec fn wrap_cross<I>(context: ParentContext, slot: Request<I>) -> bool {
    !context.child.free_placement && match context.layout {
        ChildrenLayout::Wrap { axis, .. } => axis.index() != slot.vertical as usize,
        _ => false,
    }
}

pub(crate) open spec fn grid_other_axis<I>(context: ParentContext, slot: Request<I>) -> bool {
    !context.child.free_placement && match context.layout {
        ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } =>
            main_axis.index() != slot.vertical as usize,
        _ => false,
    }
}

proof fn read_dependency<A: FinishModel>(access: &A, slot: Request<A::Id>, input: Request<A::Id>)
    requires ready_inputs(access, slot), sizing_requests::inputs(access.topology(), slot).contains(input),
    ensures is_ready(access, input),
{
    assert(is_ready(access, input));
}

pub(crate) open spec fn is_intrinsic<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    &&& slot.kind is Regular || slot.kind is Min || slot.kind is Max
    &&& (access.topology().form)(slot) == Some(Form::Intrinsic)
}

proof fn intrinsic_constraint_is_ready<A: FinishModel>(access: &A, slot: Request<A::Id>)
    requires is_intrinsic(access, slot), ready_inputs(access, slot), (access.topology().intrinsic_other)(slot),
    ensures is_ready(access, target(slot.node, !slot.vertical, Kind::Final)),
{
    let other = target(slot.node, !slot.vertical, Kind::Final);
    let inputs = sizing_requests::inputs(access.topology(), slot);
    assert(inputs.len() > 0 && inputs[inputs.len() - 1] == other);
    read_dependency(access, slot, other);
}

proof fn is_final_input<A: FinishModel>(access: &A, slot: Request<A::Id>, kind: Kind)
    requires slot.kind is Final, kind is Regular || kind is Min || kind is Max,
        (access.topology().form)(target(slot.node, slot.vertical, kind)).is_some(),
    ensures sizing_requests::inputs(access.topology(), slot).contains(target(slot.node, slot.vertical, kind)),
{
    reveal_with_fuel(sizing_requests::declaration_prefix, 4);
    let order = cycle_rules::declaration_order(Kind::Regular, Kind::Min, Kind::Max);
    assert(order@[0] == Kind::Regular && order@[1] == Kind::Min && order@[2] == Kind::Max);
    let regular = target(slot.node, slot.vertical, Kind::Regular);
    let min = target(slot.node, slot.vertical, Kind::Min);
    let max = target(slot.node, slot.vertical, Kind::Max);
    let form = access.topology().form;
    let prefix = sizing_requests::declaration_prefix(access.topology(), slot, false, 1);
    let through_min = sizing_requests::declaration_prefix(access.topology(), slot, false, 2);
    let all = sizing_requests::inputs(access.topology(), slot);
    assert(prefix == if form(regular).is_some() { Seq::<Request<A::Id>>::empty().push(regular) } else { Seq::empty() });
    assert(through_min == if form(min).is_some() { prefix.push(min) } else { prefix });
    assert(all == if form(max).is_some() { through_min.push(max) } else { through_min });
    let wanted = if kind is Regular { 0 } else if kind is Min { prefix.len() as int } else { through_min.len() as int };
    assert(0 <= wanted < all.len());
    assert(all[wanted] == target(slot.node, slot.vertical, kind));
}

} // verus!

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FinishAccess: FinishModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(size =>
        ensures form(size) == (self.topology().form)(slot),
            size == sizing_requests::resolved_size(self.finish_layout(slot.node), slot.vertical, slot.kind,
                self.finish_flags(slot.node).is_block_item(),
                self.finish_flags(slot.node).0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0),
            slot.kind is Regular ==> size.is_some(),
        no_unwind
    ))]
    fn declaration(&self, slot: Request<Self::Id>) -> Option<Size>;

    // The record words are initialized in every phase. Computed-size routing
    // additionally establishes request readiness for each semantic read.
    #[cfg_attr(verus_keep_ghost, verus_spec(words => ensures *words == self.finish_values(slot.node), no_unwind))]
    fn words(&self, slot: Request<Self::Id>) -> &[f32; N_SLOTS];

    #[cfg_attr(verus_keep_ghost, verus_spec(parent =>
        ensures parent == (self.topology().stack_parent)(slot),
        no_unwind
    ))]
    fn stack_parent(&self, slot: Request<Self::Id>) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(params => ensures *params == self.finish_layout(node), no_unwind))]
    fn params(&self, node: Self::Id) -> &LayoutParams;

    #[cfg_attr(verus_keep_ghost, verus_spec(flags => ensures flags == self.finish_flags(node), no_unwind))]
    fn flags(&self, node: Self::Id) -> NodeFlags;

    #[cfg_attr(verus_keep_ghost, verus_spec(words =>
        ensures (words[0], words[1]) == self.wrap_words()[node],
        no_unwind
    ))]
    fn line_words(&self, node: Self::Id) -> &[u32; 2];

    #[cfg_attr(verus_keep_ghost, verus_spec(parent =>
        ensures parent == (self.topology().parent)(node),
        no_unwind
    ))]
    fn parent(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(context =>
        ensures wrap_cross(context, slot) == (self.topology().parent_flow)(slot, parent),
            grid_other_axis(context, slot) == (self.topology().parent_other)(slot, parent),
            *context.child == self.finish_layout(slot.node),
            context.layout == self.finish_layout(parent).children_layout,
        no_unwind
    ))]
    fn parent_context(&self, slot: Request<Self::Id>, parent: Self::Id) -> ParentContext<'_>;

    #[cfg_attr(verus_keep_ghost, verus_spec(extent =>
        ensures extent == viewport_extent(old(self), axis),
            final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            scalar_effects_stable(old(self), final(self)),
        no_unwind
    ))]
    fn window_extent(&mut self, axis: Axis) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(count => ensures count == self.finish_child_count(node), no_unwind))]
    fn placed_child_count(&self, node: Self::Id) -> u32;

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(gaps => ensures gaps == declared_gaps(self, node, axis), no_unwind))]
    fn stack_gaps(&self, node: Self::Id, axis: Axis) -> f32 {
        let layout = self.params(node).children_layout;
        let (ChildrenLayout::Stack { axis: main, spacing, .. } | ChildrenLayout::Wrap { axis: main, spacing, .. }) = layout else {
            return 0.0;
        };
        if main.index() != axis.index() { return 0.0; }
        stack_gap_total::<Self::Float>(spacing, self.placed_child_count(node))
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == margin_pair::<Self::Float>(*params, axis), no_unwind))]
    fn margins(params: &LayoutParams, axis: Axis) -> [f32; 2];

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            final(self).finish_effects() == old(self).finish_effects().push(FinishEffect::Warning(slot, warning)),
            final(self).measurement() == old(self).measurement(),
            final(self).measurement_requests() == old(self).measurement_requests(),
            final(self).wrap_effects() == old(self).wrap_effects(),
            final(self).wrap_words() == old(self).wrap_words(),
            forall |node: Self::Id| #[trigger] final(self).finish_child_count(node) == old(self).finish_child_count(node),
            forall |node: Self::Id| #[trigger] final(self).finish_values(node) == old(self).finish_values(node),
            forall |node: Self::Id| #[trigger] final(self).finish_flags(node) == old(self).finish_flags(node),
            forall |node: Self::Id| #[trigger] final(self).finish_layout(node) == old(self).finish_layout(node),
        no_unwind
    ))]
    fn warn(&mut self, slot: Request<Self::Id>, warning: Warning);
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires is_ready(access, slot),
    ensures value == access.finish_values(slot.node)[key(slot).1 as int],
    no_unwind
))]
fn read<A: FinishAccess>(access: &A, slot: Request<A::Id>) -> f32 {
    cycle_rules::read_slot(access.words(slot), slot.vertical as usize, slot.kind)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(tracks => ensures tracks == grid_track_word(access, slot), no_unwind))]
fn grid_tracks<A: FinishAccess + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    let kind = if slot.vertical { Kind::Flow } else { Kind::EvenShare };
    access.words(slot)[crate::node_flags::slot_index(slot.axis(), kind)]
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn margin_pair<F: FrameFloat>(params: LayoutParams, axis: Axis) -> [f32; 2] {
    let margins = if axis is X { params.margin.x } else { params.margin.y };
    [F::margin_value(margins[0]), F::margin_value(margins[1])]
}

pub(crate) open spec fn gap_extent<F: FrameFloat>(spacing: f32, count: u32) -> f32 {
    F::product(spacing, F::maximum(F::difference(F::count_value(count), 1.0f32), 0.0f32))
}

pub(crate) open spec fn declared_gaps<A: FinishModel + ?Sized>(access: &A, node: A::Id, axis: Axis) -> f32 {
    match access.finish_layout(node).children_layout {
        ChildrenLayout::Stack { axis: main, spacing, .. } | ChildrenLayout::Wrap { axis: main, spacing, .. } =>
            if main.index() == axis.index() { gap_extent::<A::Float>(spacing, access.finish_child_count(node)) }
            else { 0.0f32 },
        _ => 0.0f32,
    }
}

pub(crate) open spec fn pad_extent<F: FrameFloat>(params: LayoutParams, axis: Axis) -> f32 {
    let pads = if axis is X { params.padding.x } else { params.padding.y };
    F::sum(pads[0], pads[1])
}

pub(crate) open spec fn inner_extent<F: FrameFloat>(size: f32, padding: f32) -> f32 {
    let extent = F::difference(size, padding);
    if 0u32 < F::word(extent) <= 0x7f80_0000u32 { extent } else { 0.0f32 }
}

pub(crate) open spec fn inherent_extent<F: FrameFloat>(children: f32, own: f32, gaps: f32, padding: f32) -> f32 {
    F::sum(F::sum(F::maximum(children, own), gaps), padding)
}

pub(crate) open spec fn subtract_margins<F: FrameFloat>(size: f32, margins: [f32; 2]) -> f32 {
    let margin = F::sum(margins[0], margins[1]);
    if F::word(margin) & 0x7fff_ffffu32 == 0 { size } else { inner_extent::<F>(size, margin) }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn padding(params: &LayoutParams, axis: Axis) -> f32 {
    #[cfg(not(verus_keep_ghost))]
    { padding_for::<crate::placement_geometry::RustFloat>(params, axis) }
    #[cfg(verus_keep_ghost)]
    {
        let [start, end] = *params.padding.component(axis);
        start + end
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == pad_extent::<F>(*params, axis), no_unwind))]
pub(crate) fn padding_for<F: FrameFloat>(params: &LayoutParams, axis: Axis) -> f32 {
    let [start, end] = *params.padding.component(axis);
    F::add(start, end)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(gaps => ensures gaps == gap_extent::<F>(spacing, count), no_unwind))]
fn stack_gap_total<F: FrameFloat>(spacing: f32, count: u32) -> f32 {
    let gap_count = F::max(F::subtract(F::from_count(count), 1.0), 0.0);
    F::multiply(spacing, gap_count)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == inner_extent::<F>(size, padding), no_unwind))]
pub(crate) fn inner<F: FrameFloat>(size: f32, padding: f32) -> f32 {
    let extent = F::subtract(size, padding);
    if F::positive(extent) { extent } else { 0.0 }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == subtract_margins::<F>(size, margins), no_unwind))]
pub(crate) fn inside_margins<F: FrameFloat>(size: f32, margins: [f32; 2]) -> f32 {
    let [start, end] = margins;
    let margin = F::add(start, end);
    if F::is_zero(margin) { size } else { inner::<F>(size, margin) }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == inherent_extent::<F>(children, own, gaps, padding), no_unwind))]
pub(crate) fn intrinsic_extent<F: FrameFloat>(children: f32, own: f32, gaps: f32, padding: f32) -> f32 {
    F::add(F::add(F::max(children, own), gaps), padding)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct GridTrack {
    pub(crate) count: f32,
    pub(crate) cell: f32,
    pub(crate) spacing: f32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl GridTrack {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(grid => ensures grid == grid_track::<F>(inner, n, spacing), no_unwind))]
    pub(crate) fn new<F: FrameFloat>(inner: f32, n: f32, spacing: f32) -> Self {
        let count = F::max(n, 1.0);
        let gaps = F::multiply(spacing, F::subtract(n, 1.0));
        let cell = F::max(F::divide(F::subtract(inner, gaps), count), 0.0);
        Self { count, cell, spacing }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(extent => ensures extent == grid_span::<F>(*self, span), no_unwind))]
    pub(crate) fn extent<F: FrameFloat>(&self, span: u16) -> f32 {
        let span = F::min(F::from_count(if span == 0 { 1 } else { span as u32 }), self.count);
        F::add(F::multiply(span, self.cell), F::multiply(F::subtract(span, 1.0), self.spacing))
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(extent => ensures extent == line_extent(access, child, phase, metric), no_unwind))]
fn line_metric<A: FinishAccess>(access: &A, child: A::Id, phase: u32, metric: wrap_metrics::Metric) -> f32 {
    match wrap_metrics::ready_metric(phase == cycle_rules::SOLVED, metric) {
        Some(metric) => A::Float::from_word(wrap_metrics::read_metric(access.line_words(child), metric)),
        None => 0.0,
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(extent =>
    requires ready_inputs(old(access), slot), reads_parent_extent(old(access), slot),
        slot.kind is Regular || slot.kind is Min || slot.kind is Max,
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        extent == parent_extent(old(access), slot, fill),
        scalar_effects_stable(old(access), final(access)),
    no_unwind
))]
fn parent_size<A: FinishAccess>(access: &mut A, slot: Request<A::Id>, fill: bool) -> f32 {
    let axis = slot.axis();
    let Some(parent) = access.parent(slot.node) else { return access.window_extent(axis); };
    let context = access.parent_context(slot, parent);
    let params = context.child;
    let layout = context.layout;
    if !params.free_placement {
        if let ChildrenLayout::Wrap { axis: main, .. } = layout {
            if main.index() != axis.index() {
                #[cfg(verus_keep_ghost)]
                proof! {
                    let input = target(parent, slot.vertical, Kind::Flow);
                    let deps = sizing_requests::inputs(access.topology(), slot);
                    assert(wrap_cross(context, slot));
                    assert(deps == seq![input]);
                    assert(deps[0] == input);
                    read_dependency(access, slot, input);
                }
                let phase = access.flags(parent).check_state(axis, Kind::Flow);
                let extent = line_metric(access, slot.node, phase, wrap_metrics::Metric::Cross);
                return if fill { inside_margins::<A::Float>(extent, A::margins(params, axis)) } else { extent };
            }
        }
    }
    let parent_final = target(parent, slot.vertical, Kind::Final);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(!wrap_cross(context, slot));
        let deps = sizing_requests::inputs(access.topology(), slot);
        let other = target(parent, !slot.vertical, Kind::Final);
        if (access.topology().parent_other)(slot, parent) {
            assert(deps == seq![parent_final, other]);
            assert(deps[1] == other);
            read_dependency(access, slot, other);
        } else {
            assert(deps == seq![parent_final]);
        }
        assert(deps[0] == parent_final);
        read_dependency(access, slot, parent_final);
    }
    let inner = inner::<A::Float>(read(access, parent_final), padding_for::<A::Float>(access.params(parent), axis));
    if params.free_placement {
        return inner;
    }
    let available = match layout {
        ChildrenLayout::Grid { spacing_x, spacing_y, .. } => {
            let spacing = if slot.vertical { spacing_y } else { spacing_x };
            let grid = GridTrack::new::<A::Float>(inner, grid_tracks(access, parent_final), spacing);
            grid.extent::<A::Float>(*params.grid_span.component(axis))
        }
        ChildrenLayout::Stack { axis: main, .. } if main.index() == axis.index() => {
            A::Float::max(A::Float::subtract(inner, access.stack_gaps(parent, axis)), 0.0)
        }
        _ => inner,
    };
    if fill && !matches!(layout, ChildrenLayout::Free) {
        inside_margins::<A::Float>(available, A::margins(params, axis))
    } else {
        available
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn clamp_extent<F: FloatBounds>(size: f32, min: Option<f32>, max: Option<f32>) -> f32 {
    let capped = match max { Some(upper) => F::minimum(size, upper), None => size };
    match min { Some(lower) => F::maximum(capped, lower), None => capped }
}

pub(crate) open spec fn bound_word<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>, kind: Kind) -> Option<f32> {
    let params = access.finish_layout(slot.node);
    let flags = access.finish_flags(slot.node);
    let resolved = sizing_requests::resolved_size(params, slot.vertical, kind, flags.is_block_item(),
        flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0);
    if resolved.is_some() {
        Some(access.finish_values(slot.node)[key(target(slot.node, slot.vertical, kind)).1 as int])
    } else { None }
}

pub(crate) open spec fn final_extent<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    let params = access.finish_layout(slot.node);
    let block_min = if access.finish_flags(slot.node).is_block_item() { Some(pad_extent::<A::Float>(params, slot.axis())) }
        else { None };
    bounded_extent::<A::Float>(direct_regular(access, slot), bound_word(access, slot, Kind::Min),
        bound_word(access, slot, Kind::Max), block_min)
}

pub(crate) open spec fn bounded_extent<F: FrameFloat>(size: f32, min: Option<f32>, max: Option<f32>, block_min: Option<f32>) -> f32 {
    let clamped = clamp_extent::<F>(size, min, max);
    match block_min { Some(padding) => F::maximum(clamped, padding), None => clamped }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == clamp_extent::<F>(size, min, max), no_unwind))]
pub(crate) fn clamp<F: FloatBounds>(size: f32, min: Option<f32>, max: Option<f32>) -> f32 {
    let size = match max { Some(max) => F::min(size, max), None => size };
    match min { Some(min) => F::max(size, min), None => size }
}

/// Bounds apply before the padding floor of an in-flow Block item.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == bounded_extent::<F>(size, min, max, block_min), no_unwind))]
pub(crate) fn bounded_axis<F: FrameFloat>(size: f32, min: Option<f32>, max: Option<f32>, block_min: Option<f32>) -> f32 {
    let clamped = clamp::<F>(size, min, max);
    match block_min { Some(padding) => F::max(clamped, padding), None => clamped }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires slot.kind is Final, kind is Min || kind is Max, ready_inputs(access, slot),
    ensures value == bound_word(access, slot, kind),
        sizing_requests::raw_size(access.finish_layout(slot.node), slot.vertical, kind).is_none() ==> value.is_none(),
    no_unwind
))]
fn bound<A: FinishAccess>(access: &A, slot: Request<A::Id>, kind: Kind) -> Option<f32> {
    let input = target(slot.node, slot.vertical, kind);
    if access.declaration(input).is_none() { return None; }
    #[cfg(verus_keep_ghost)]
    proof! {
        is_final_input(access, slot, kind);
        read_dependency(access, slot, input);
    }
    Some(read(access, input))
}

/// A numeric Final can publish its Regular directly when no bound or grid
/// assignment has to run. Report whether the intrinsic warning check applies.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.is_some() ==> has_unbounded_final_inputs(*params, axis, out.unwrap())
        && !assigns_width_grid(*params, axis),
    no_unwind
))]
pub(crate) fn unbounded_final_input(params: &LayoutParams, axis: Axis) -> Option<bool> {
    if params.min_size.component(axis).is_some() || params.max_size.component(axis).is_some()
        || matches!(params.children_layout, ChildrenLayout::Grid {
            main_axis, columns: MainAxisCellSize::Width(_), ..
        } if main_axis.index() == axis.index())
    {
        return None;
    }
    Some(matches!(*params.size.component(axis), Size::FitContent))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires slot.kind is Final, regular_present(old(access), slot), ready_inputs(old(access), slot),
    ensures value == final_extent(old(access), slot),
        final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        slot.kind is Final && permits_direct_final(old(access).finish_layout(slot.node), slot.axis(),
            old(access).finish_flags(slot.node)) ==> value == direct_regular(old(access), slot)
                && final(access).finish_effects() == old(access).finish_effects()
                && final(access).finish_layout(slot.node) == old(access).finish_layout(slot.node),
    no_unwind
))]
fn final_size<A: FinishAccess>(access: &mut A, slot: Request<A::Id>) -> f32 {
    let min = bound(access, slot, Kind::Min);
    let max = bound(access, slot, Kind::Max);
    if let (Some(min), Some(max)) = (min, max) {
        if min > max { access.warn(slot, Warning::MinAboveMax); }
    }
    let regular = target(slot.node, slot.vertical, Kind::Regular);
    #[cfg(verus_keep_ghost)]
    proof! {
        is_final_input(access, slot, Kind::Regular);
        read_dependency(access, slot, regular);
    }
    let initial = read(access, regular);
    let axis = slot.axis();
    let flags = access.flags(slot.node);
    let block_min = if flags.is_block_item() { Some(padding_for::<A::Float>(access.params(slot.node), axis)) } else { None };
    let size = bounded_axis::<A::Float>(initial, min, max, block_min);
    if flags.0 & NodeFlags::flex_child(axis) != 0
        && size <= padding_for::<A::Float>(access.params(slot.node), axis)
        && matches!(*access.params(slot.node).size.component(axis), Size::FitContent)
        && !matches!(access.params(slot.node).children_layout, ChildrenLayout::Block | ChildrenLayout::Wrap { .. })
    {
        access.warn(slot, Warning::FitContentCollapsed);
    }
    size
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires ready_inputs(old(access), slot), slot.kind is Final ==> regular_present(old(access), slot),
    ensures slot.kind is Final ==> value == final_extent(old(access), slot),
        slot.kind is EvenShare ==> value == flow::even_share_value(old(access), slot),
        slot.kind is Flow ==> match old(access).finish_layout(slot.node).children_layout {
            ChildrenLayout::Wrap { axis, line_spacing, .. } => {
                &&& flow::cross_writes_from(old(access), final(access), slot, axis, None)
                &&& flow::cross_extent_and_words(old(access), final(access), slot, line_spacing, value)
            },
            _ => true,
        },
        final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        slot.kind is Final && permits_direct_final(old(access).finish_layout(slot.node), slot.axis(),
            old(access).finish_flags(slot.node)) ==> value == direct_regular(old(access), slot)
                && final(access).finish_effects() == old(access).finish_effects()
                && final(access).finish_layout(slot.node) == old(access).finish_layout(slot.node),
        declared_scalar(old(access), slot).is_some() ==> {
            &&& value == declared_scalar(old(access), slot).unwrap()
            &&& scalar_effects_stable(old(access), final(access))
        },
        free_intrinsic(old(access), slot) ==> {
            &&& value == free_intrinsic_value(old(access), slot)
            &&& intrinsic_effects_stable(old(access), final(access))
            &&& measurement_inputs_stable(old(access), final(access))
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
        grid_intrinsic(old(access), slot) ==> {
            &&& value == grid_intrinsic_value(old(access), slot)
            &&& intrinsic_effects_stable(old(access), final(access))
            &&& measurement_inputs_stable(old(access), final(access))
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
        flow_intrinsic(old(access), slot) ==> {
            &&& value == flow_intrinsic_value(old(access), slot)
            &&& intrinsic_effects_stable(old(access), final(access))
            &&& measurement_inputs_stable(old(access), final(access))
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
        largest_intrinsic(old(access), slot) ==> {
            &&& value == largest_intrinsic_value(old(access), slot)
            &&& intrinsic_effects_stable(old(access), final(access))
            &&& measurement_inputs_stable(old(access), final(access))
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
        stack_intrinsic(old(access), slot) ==> {
            &&& value == stack_intrinsic_value(old(access), slot)
            &&& final(access).finish_effects() == old(access).finish_effects() + stack_intrinsic_warnings(old(access), slot)
            &&& final(access).wrap_effects() == old(access).wrap_effects()
            &&& measurement_inputs_stable(old(access), final(access))
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
    no_unwind
))]
pub(crate) fn compute_size<A: FlowAccess>(access: &mut A, slot: Request<A::Id>) -> f32 {
    match slot.kind {
        Kind::Final => final_size(access, slot),
        Kind::EvenShare => measure_share(access, slot),
        Kind::Flow => measure_flow(access, slot),
        _ => match access.declaration(slot) {
            None => A::Float::from_word(cycle_rules::provisional_bits(matches!(slot.kind, Kind::Max))),
            Some(Size::Pixels(pixels)) => pixels,
            Some(Size::AspectRatio(ratio)) => {
                let opposite = target(slot.node, !slot.vertical, Kind::Final);
                #[cfg(verus_keep_ghost)]
                proof! {
                    let deps = sizing_requests::inputs(access.topology(), slot);
                    assert(deps == seq![opposite]);
                    assert(deps[0] == opposite);
                    read_dependency(access, slot, opposite);
                }
                let size = read(access, opposite);
                aspect_size::<A::Float>(slot.axis(), size, ratio)
            }
            Some(Size::Frac(fraction)) => A::Float::multiply(parent_size(access, slot, false), fraction),
            Some(Size::FitContent | Size::Auto) => fit_content(access, slot),
            Some(Size::Fill) => {
                if let Some(parent) = access.stack_parent(slot) {
                    let share = target(parent, slot.vertical, Kind::EvenShare);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        let deps = sizing_requests::inputs(access.topology(), slot);
                        assert(deps == seq![share]);
                        assert(deps[0] == share);
                        read_dependency(access, slot, share);
                    }
                    let flags = access.flags(parent);
                    let value = if flags.0 & NodeFlags::WRAP_CONTAINER == 0 {
                        read(access, share)
                    } else {
                        line_metric(access, slot.node, flags.check_state(slot.axis(), Kind::EvenShare), wrap_metrics::Metric::Share)
                    };
                    A::Float::multiply(value, access.params(slot.node).fill_weight)
                } else {
                    parent_size(access, slot, true)
                }
            }
        },
    }
}


#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FinishPublication: FlowAccess {
    #[cfg_attr(verus_keep_ghost, verus_spec(finite => ensures finite == Self::Float::finite_word(value), no_unwind))]
    fn finite(value: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(stored =>
        ensures stored.slot == slot, stored.value == value,
            final(self).topology() == old(self).topology(),
            final(self).ready() == old(self).ready().insert(key(slot)),
            final(self).finish_layout(slot.node) == old(self).finish_layout(slot.node),
            final(self).finish_values(slot.node)@ == old(self).finish_values(slot.node)@.update(key(slot).1 as int, value),
            final(self).finish_flags(slot.node).0 == cycle_rules::phase_word(old(self).finish_flags(slot.node).0,
                key(slot).1 as u32, cycle_rules::SOLVED),
            cycle_rules::read_state(final(self).finish_flags(slot.node).0, key(slot).1 as u32) == cycle_rules::SOLVED,
            final(self).finish_effects() == old(self).finish_effects().push(FinishEffect::Publish(slot, value)),
            final(self).measurement_requests() == old(self).measurement_requests(),
            final(self).wrap_effects() == old(self).wrap_effects(),
            final(self).wrap_words() == old(self).wrap_words(),
        no_unwind
    ))]
    fn publish(&mut self, slot: Request<Self::Id>, value: f32) -> StoredSize<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires slot.kind is Final, is_ready(old(self), slot),
        ensures final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            final(self).finish_values(slot.node)[key(slot).1 as int] == old(self).finish_values(slot.node)[key(slot).1 as int],
            cycle_rules::read_state(final(self).finish_flags(slot.node).0, key(slot).1 as u32)
                == cycle_rules::read_state(old(self).finish_flags(slot.node).0, key(slot).1 as u32),
            final(self).finish_effects() == old(self).finish_effects().push(FinishEffect::AssignWidthGrid(slot, width, spacing, backfill)),
        no_unwind
    ))]
    fn assign_width_grid(&mut self, slot: Request<Self::Id>, width: f32, spacing: f32, backfill: bool);
}

/// A value stored for the specified packed sizing slot. The receipt is erased
/// from ordinary builds.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct StoredSize<I> {
    #[cfg(verus_keep_ghost)]
    pub(crate) slot: Request<I>,
    #[cfg(verus_keep_ghost)]
    pub(crate) value: f32,
    #[cfg(not(verus_keep_ghost))]
    slot: core::marker::PhantomData<I>,
}

/// Store one word in the record borrowed for this request.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(stored =>
    ensures stored.slot == slot, stored.value == value,
        final(record).values@ == old(record).values@.update(key(slot).1 as int, value),
        final(record).flags.0 == cycle_rules::phase_word(old(record).flags.0, key(slot).1 as u32, cycle_rules::SOLVED),
        cycle_rules::read_state(final(record).flags.0, key(slot).1 as u32) == cycle_rules::SOLVED,
        forall |other: u32| other < 16 && other != key(slot).1 ==>
            #[trigger] cycle_rules::read_state(final(record).flags.0, other) == cycle_rules::read_state(old(record).flags.0, other),
        *final(record) == (crate::node_data::NodeLayoutData {
            flags: final(record).flags, values: final(record).values, ..*old(record)
        }),
    no_unwind
))]
pub(crate) fn store_size<I: Copy>(record: &mut crate::node_data::NodeLayoutData, slot: Request<I>, value: f32) -> StoredSize<I> {
    record.publish_slot(crate::node_flags::slot_index(slot.axis(), slot.kind), value);
    #[cfg(verus_keep_ghost)]
    { StoredSize { slot, value } }
    #[cfg(not(verus_keep_ghost))]
    { StoredSize { slot: core::marker::PhantomData } }
}

/// Width-derived grid cells consume the just-published Final, so this write
/// precedes the grid scan even when the declaration produced a nonfinite value.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(stored =>
    requires ready_inputs(old(access), slot), slot.kind is Final ==> regular_present(old(access), slot),
    ensures final(access).topology() == old(access).topology(),
        final(access).ready() == old(access).ready().insert(key(slot)),
        canonical_direct_final(old(access), slot) ==> final(access).finish_effects()
            == old(access).finish_effects().push(FinishEffect::Publish(slot, direct_regular(old(access), slot))),
        stored.slot == slot, stored.value == final(access).finish_values(slot.node)[key(slot).1 as int],
        slot.kind is Final ==> stored.value == final_extent(old(access), slot),
        cycle_rules::read_state(final(access).finish_flags(slot.node).0, key(slot).1 as u32) == cycle_rules::SOLVED,
        declared_scalar(old(access), slot).is_some() ==> {
            &&& stored.value == declared_scalar(old(access), slot).unwrap()
            &&& final(access).finish_effects() == old(access).finish_effects().push(FinishEffect::Publish(slot, stored.value))
            &&& final(access).wrap_effects() == old(access).wrap_effects()
            &&& final(access).measurement_requests() == old(access).measurement_requests()
        },
        slot.kind is EvenShare ==> stored.value == flow::even_share_value(old(access), slot),
        slot.kind is Flow ==> match old(access).finish_layout(slot.node).children_layout {
            ChildrenLayout::Wrap { axis, line_spacing, .. } => {
                &&& flow::cross_writes_from(old(access), final(access), slot, axis, None)
                &&& flow::cross_extent_and_words(old(access), final(access), slot, line_spacing, stored.value)
            },
            _ => true,
        },
        canonical_direct_final(old(access), slot) ==> stored.value == direct_regular(old(access), slot),
        free_intrinsic(old(access), slot) ==> {
            &&& stored.value == free_intrinsic_value(old(access), slot)
            &&& free_intrinsic_datum(old(access), slot) == Some(seq![A::Float::word(stored.value)])
            &&& final(access).finish_values(slot.node)@ == old(access).finish_values(slot.node)@.update(key(slot).1 as int, stored.value)
            &&& final(access).finish_effects() == old(access).finish_effects().push(FinishEffect::Publish(slot, stored.value))
            &&& final(access).wrap_effects() == old(access).wrap_effects()
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
        grid_intrinsic(old(access), slot) ==> {
            &&& stored.value == grid_intrinsic_value(old(access), slot)
            &&& final(access).finish_values(slot.node)@ == old(access).finish_values(slot.node)@.update(key(slot).1 as int, stored.value)
            &&& final(access).finish_effects() == old(access).finish_effects().push(FinishEffect::Publish(slot, stored.value))
            &&& final(access).wrap_effects() == old(access).wrap_effects()
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
        flow_intrinsic(old(access), slot) ==> {
            &&& stored.value == flow_intrinsic_value(old(access), slot)
            &&& final(access).finish_values(slot.node)@ == old(access).finish_values(slot.node)@.update(key(slot).1 as int, stored.value)
            &&& final(access).finish_effects() == old(access).finish_effects().push(FinishEffect::Publish(slot, stored.value))
            &&& final(access).wrap_effects() == old(access).wrap_effects()
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
        largest_intrinsic(old(access), slot) ==> {
            &&& stored.value == largest_intrinsic_value(old(access), slot)
            &&& final(access).finish_values(slot.node)@ == old(access).finish_values(slot.node)@.update(key(slot).1 as int, stored.value)
            &&& final(access).finish_effects() == old(access).finish_effects().push(FinishEffect::Publish(slot, stored.value))
            &&& final(access).wrap_effects() == old(access).wrap_effects()
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
        stack_intrinsic(old(access), slot) ==> {
            &&& stored.value == stack_intrinsic_value(old(access), slot)
            &&& stack_intrinsic_datum(old(access), slot) == Some(seq![A::Float::word(stored.value)])
            &&& final(access).finish_values(slot.node)@ == old(access).finish_values(slot.node)@.update(key(slot).1 as int, stored.value)
            &&& final(access).finish_effects() == (old(access).finish_effects() + stack_intrinsic_warnings(old(access), slot))
                .push(FinishEffect::Publish(slot, stored.value))
            &&& final(access).wrap_effects() == old(access).wrap_effects()
            &&& final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot)
        },
    no_unwind
))]
pub(crate) fn finish_size<A: FinishPublication>(access: &mut A, slot: Request<A::Id>) -> StoredSize<A::Id> {
    let size = compute_size(access, slot);
    let is_final = matches!(slot.kind, Kind::Final);
    if is_final && !A::finite(size) {
        access.warn(slot, Warning::NotFinite);
    }
    let stored = access.publish(slot, size);
    if is_final {
        if let ChildrenLayout::Grid {
            columns: MainAxisCellSize::Width(width), spacing_x, spacing_y, main_axis, backfill,
        } = access.params(slot.node).children_layout {
            if grid_state::writes_width_grid(true, main_axis.index() == slot.vertical as usize) {
                let spacing = if slot.vertical { spacing_y } else { spacing_x };
                access.assign_width_grid(slot, width, spacing, backfill);
            }
        }
    }
    stored
}

#[cfg(verus_keep_ghost)]
verus! {

/// Own-content inputs shared by independent numeric and full sizing runs.
/// Only active measurement constraints and requests need to agree.
pub(crate) open spec fn same_parent_inputs<A: FinishModel>(numeric: &A, full: &A, slot: Request<A::Id>) -> bool {
    let parent = (numeric.topology().parent)(slot.node);
    &&& parent == (full.topology().parent)(slot.node)
    &&& numeric.finish_layout(slot.node) == full.finish_layout(slot.node)
    &&& match parent {
        None => viewport_extent(numeric, slot.axis()) == viewport_extent(full, slot.axis()),
        Some(parent) => {
            let child_free = numeric.finish_layout(slot.node).free_placement;
            let params = numeric.finish_layout(parent);
            let context = ParentContext { child: &numeric.finish_layout(slot.node), layout: params.children_layout };
            let parent_final = target(parent, slot.vertical, Kind::Final);
            &&& params.children_layout == full.finish_layout(parent).children_layout
            &&& if wrap_cross(context, slot) {
                let flow = target(parent, slot.vertical, Kind::Flow);
                &&& producer_phase(numeric, flow) == producer_phase(full, flow)
                &&& producer_phase(numeric, flow) == cycle_rules::SOLVED ==>
                    numeric.wrap_words()[slot.node].1 == full.wrap_words()[slot.node].1
            } else {
                &&& params.padding == full.finish_layout(parent).padding
                &&& numeric.finish_values(parent)[key(parent_final).1 as int]
                    == full.finish_values(parent)[key(parent_final).1 as int]
                &&& !child_free ==> match params.children_layout {
                    ChildrenLayout::Stack { axis, .. } if axis.index() == slot.axis().index() =>
                        numeric.finish_child_count(parent) == full.finish_child_count(parent),
                    ChildrenLayout::Grid { .. } => grid_track_word(numeric, parent_final) == grid_track_word(full, parent_final),
                    _ => true,
                }
            }
        },
    }
}

pub(crate) open spec fn same_shared_fill_inputs<A: FinishModel>(
    numeric: &A, full: &A, slot: Request<A::Id>, parent: A::Id,
) -> bool {
    let wrap = numeric.finish_flags(parent).0 & NodeFlags::WRAP_CONTAINER != 0;
    let share = target(parent, slot.vertical, Kind::EvenShare);
    &&& wrap == (full.finish_flags(parent).0 & NodeFlags::WRAP_CONTAINER != 0)
    &&& if wrap {
        &&& producer_phase(numeric, share) == producer_phase(full, share)
        &&& producer_phase(numeric, share) == cycle_rules::SOLVED ==>
            numeric.wrap_words()[slot.node].0 == full.wrap_words()[slot.node].0
    } else {
        numeric.finish_values(parent)[key(share).1 as int] == full.finish_values(parent)[key(share).1 as int]
    }
}

/// Compare the physical inputs of Pixels, AspectRatio, Frac and Fill producers.
pub(crate) open spec fn same_scalar_inputs<A: FinishModel>(numeric: &A, full: &A, slot: Request<A::Id>) -> bool {
    let declaration = scalar_declaration(numeric, slot);
    &&& declaration == scalar_declaration(full, slot)
    &&& match declaration {
        Some(Size::Pixels(_)) => true,
        Some(Size::AspectRatio(_)) => {
            let opposite = target(slot.node, !slot.vertical, Kind::Final);
            numeric.finish_values(slot.node)[key(opposite).1 as int] == full.finish_values(slot.node)[key(opposite).1 as int]
        },
        Some(Size::Frac(_)) => same_parent_inputs(numeric, full, slot),
        Some(Size::Fill) => {
            let shared_parent = (numeric.topology().stack_parent)(slot);
            &&& shared_parent == (full.topology().stack_parent)(slot)
            &&& match shared_parent {
                Some(parent) => {
                    &&& numeric.finish_layout(slot.node).fill_weight == full.finish_layout(slot.node).fill_weight
                    &&& same_shared_fill_inputs(numeric, full, slot, parent)
                },
                None => same_parent_inputs(numeric, full, slot),
            }
        },
        _ => false,
    }
}

proof fn matching_parent_extent<A: FinishModel>(numeric: &A, full: &A, slot: Request<A::Id>, fill: bool)
    requires same_parent_inputs(numeric, full, slot),
    ensures parent_extent(numeric, slot, fill) == parent_extent(full, slot, fill),
{}

proof fn matching_scalar_value<A: FinishModel>(numeric: &A, full: &A, slot: Request<A::Id>)
    requires same_scalar_inputs(numeric, full, slot),
    ensures declared_scalar(numeric, slot).is_some(), declared_scalar(numeric, slot) == declared_scalar(full, slot),
{
    match scalar_declaration(numeric, slot) {
        Some(Size::Frac(_)) => matching_parent_extent(numeric, full, slot, false),
        Some(Size::Fill) if (numeric.topology().stack_parent)(slot).is_none() => matching_parent_extent(numeric, full, slot, true),
        _ => {},
    }
}

/// The native finishers publish the same scalar from matching physical inputs.
pub(crate) fn compare_scalar_producers<A: FinishPublication>(
    numeric: &mut A, full: &mut A, slot: Request<A::Id>,
) -> (stored: (StoredSize<A::Id>, StoredSize<A::Id>))
    requires slot.kind is Regular || slot.kind is Min || slot.kind is Max,
        ready_inputs(old(numeric), slot), ready_inputs(old(full), slot),
        same_scalar_inputs(old(numeric), old(full), slot),
    ensures stored.0.slot == slot, stored.1.slot == slot, stored.0.value == stored.1.value,
        final(numeric).finish_values(slot.node)[key(slot).1 as int] == final(full).finish_values(slot.node)[key(slot).1 as int],
        final(numeric).finish_effects() == old(numeric).finish_effects().push(FinishEffect::Publish(slot, stored.1.value)),
        final(full).finish_effects() == old(full).finish_effects().push(FinishEffect::Publish(slot, stored.1.value)),
        final(numeric).wrap_effects() == old(numeric).wrap_effects(),
        final(full).wrap_effects() == old(full).wrap_effects(),
        final(numeric).measurement_requests() == old(numeric).measurement_requests(),
        final(full).measurement_requests() == old(full).measurement_requests(),
    no_unwind
{
    proof { matching_scalar_value(numeric, full, slot); }
    let incremental = finish_size(numeric, slot);
    let reference = finish_size(full, slot);
    (incremental, reference)
}

/// The Stack share uses the same ordered budget and constrained child terms.
pub(crate) fn compare_stack_share_producers<A: FinishPublication>(
    numeric: &mut A, full: &mut A, slot: Request<A::Id>,
) -> (stored: (StoredSize<A::Id>, StoredSize<A::Id>))
    requires slot.kind is EvenShare, ready_inputs(old(numeric), slot), ready_inputs(old(full), slot),
        flow::same_stack_share_inputs(old(numeric), old(full), slot),
    ensures stored.0.slot == slot, stored.1.slot == slot, stored.0.value == stored.1.value,
        final(numeric).finish_values(slot.node)[key(slot).1 as int] == final(full).finish_values(slot.node)[key(slot).1 as int],
    no_unwind
{
    proof {
        assert(flow::share_inner(numeric, slot) == flow::share_inner(full, slot));
        assert(declared_gaps(numeric, slot.node, slot.axis()) == declared_gaps(full, slot.node, slot.axis()));
        assert(flow::even_share_value(numeric, slot) == flow::even_share_value(full, slot));
    }
    let incremental = finish_size(numeric, slot);
    let reference = finish_size(full, slot);
    (incremental, reference)
}

/// The non-exhausted Stack-tail path measures the share without changing its
/// solved phase, then stores it in the same lane the full finisher publishes.
pub(crate) fn compare_measured_tail_share<A: FinishPublication>(
    tail: &mut A, full: &mut A, tail_values: &mut [f32; N_SLOTS],
    slot: Request<A::Id>,
) -> (reference: StoredSize<A::Id>)
    requires slot.kind is EvenShare, ready_inputs(old(tail), slot), ready_inputs(old(full), slot),
        flow::same_stack_share_inputs(old(tail), old(full), slot),
    ensures reference.slot == slot,
        reference.value == final(full).finish_values(slot.node)[key(slot).1 as int],
        final(tail_values)@ == old(tail_values)@.update(key(slot).1 as int, reference.value),
        final(tail_values)[key(slot).1 as int] == final(full).finish_values(slot.node)[key(slot).1 as int],
    no_unwind
{
    proof {
        assert(flow::share_inner(tail, slot) == flow::share_inner(full, slot));
        assert(declared_gaps(tail, slot.node, slot.axis()) == declared_gaps(full, slot.node, slot.axis()));
        assert(flow::even_share_value(tail, slot) == flow::even_share_value(full, slot));
    }
    let share = measure_share(tail, slot);
    let reference = finish_size(full, slot);
    crate::stack_tail::write_tail_slot(tail_values, slot.axis(), Kind::EvenShare, share);
    reference
}

/// Compare the packed Wrap Flow size and every stamped line word.
pub(crate) fn compare_wrap_flow_producers<A: FinishPublication>(
    numeric: &mut A, full: &mut A, slot: Request<A::Id>, axis: Axis, line_spacing: f32,
) -> (stored: (StoredSize<A::Id>, StoredSize<A::Id>))
    requires slot.kind is Flow, ready_inputs(old(numeric), slot), ready_inputs(old(full), slot),
        old(numeric).finish_layout(slot.node).children_layout == old(full).finish_layout(slot.node).children_layout,
        match old(full).finish_layout(slot.node).children_layout {
            ChildrenLayout::Wrap { axis: main, line_spacing: spacing, .. } => main == axis && spacing == line_spacing,
            _ => false,
        },
        flow::same_cross_inputs(old(numeric), old(full), slot, axis),
    ensures stored.0.slot == slot, stored.1.slot == slot, stored.0.value == stored.1.value,
        final(numeric).finish_values(slot.node)[key(slot).1 as int] == final(full).finish_values(slot.node)[key(slot).1 as int],
        old(numeric).wrap_words() == old(full).wrap_words() ==> final(numeric).wrap_words() == final(full).wrap_words(),
        final(numeric).wrap_effects().skip(old(numeric).wrap_effects().len() as int)
            == final(full).wrap_effects().skip(old(full).wrap_effects().len() as int),
    no_unwind
{
    let incremental = finish_size(numeric, slot);
    let reference = finish_size(full, slot);
    proof {
        flow::matching_wrap_flow(old(numeric), old(full), numeric, full, slot, axis, line_spacing,
            incremental.value, reference.value);
    }
    (incremental, reference)
}

pub(crate) open spec fn same_intrinsic_leaf_inputs<A: FinishModel + IntrinsicOracle<A::Id>>(
    numeric: &A, full: &A, slot: Request<A::Id>,
) -> bool {
    let params = numeric.finish_layout(slot.node);
    let opposite = target(slot.node, !slot.vertical, Kind::Final);
    let requests = measurement_requests_for(numeric, slot);
    &&& params == full.finish_layout(slot.node)
    &&& (params.text_wraps_on(slot.axis()) || params.content_measure.reads_other_axis(slot.axis()))
        ==> numeric.finish_values(slot.node)[key(opposite).1 as int] == full.finish_values(slot.node)[key(opposite).1 as int]
    &&& forall |i: int| 0 <= i < requests.len() ==> {
        let (node, request) = #[trigger] requests[i];
        (numeric.measurement())(node, request) == (full.measurement())(node, request)
    }
}

pub(crate) proof fn matching_own_content<A: FinishModel + IntrinsicOracle<A::Id>>(
    numeric: &A, full: &A, slot: Request<A::Id>,
)
    requires same_intrinsic_leaf_inputs(numeric, full, slot),
    ensures measurement_requests_for(numeric, slot) == measurement_requests_for(full, slot),
        own_extent(numeric, slot) == own_extent(full, slot),
{
    assert(text_request(numeric, slot) == text_request(full, slot));
    assert(measurement_requests_for(numeric, slot) == measurement_requests_for(full, slot));
    let requests = measurement_requests_for(numeric, slot);
    if text_request(numeric, slot).is_some() {
        assert(requests[0] == (slot.node, text_request(numeric, slot).unwrap()));
    }
    if !(numeric.finish_layout(slot.node).content_measure is None) {
        assert(requests[requests.len() - 1] == (slot.node, intrinsic::canonical_request(numeric, slot)));
    }
}

/// Both native sizing routes call the canonical finisher for this declared
/// slot. Compare its physical receipts without assuming equal slot results.
pub(crate) fn compare_free_intrinsic_producers<A: FinishPublication>(
    numeric: &mut A, full: &mut A, slot: Request<A::Id>,
) -> (stored: (StoredSize<A::Id>, StoredSize<A::Id>))
    requires free_intrinsic(old(numeric), slot), free_intrinsic(old(full), slot),
        ready_inputs(old(numeric), slot), ready_inputs(old(full), slot),
        same_intrinsic_leaf_inputs(old(numeric), old(full), slot),
    ensures stored.0.slot == slot, stored.1.slot == slot, stored.0.value == stored.1.value,
        final(numeric).finish_values(slot.node)[key(slot).1 as int] == final(full).finish_values(slot.node)[key(slot).1 as int],
        final(numeric).measurement_requests() == old(numeric).measurement_requests() + measurement_requests_for(old(full), slot),
        final(full).measurement_requests() == old(full).measurement_requests() + measurement_requests_for(old(full), slot),
        final(numeric).finish_effects() == old(numeric).finish_effects().push(FinishEffect::Publish(slot, stored.1.value)),
        final(full).finish_effects() == old(full).finish_effects().push(FinishEffect::Publish(slot, stored.1.value)),
    no_unwind
{
    proof {
        matching_own_content(numeric, full, slot);
        assert(free_intrinsic_value(numeric, slot) == free_intrinsic_value(full, slot));
    }
    let incremental = finish_size(numeric, slot);
    let reference = finish_size(full, slot);
    (incremental, reference)
}

/// Grid width on its main axis supplies both operands from its declaration.
pub(crate) open spec fn reads_intrinsic_grid_scan<A: FinishModel>(access: &A, slot: Request<A::Id>) -> bool {
    match access.finish_layout(slot.node).children_layout {
        ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } =>
            main_axis.index() != slot.axis().index(),
        ChildrenLayout::Grid { .. } => true,
        _ => false,
    }
}

/// Input observations consumed by a declared intrinsic size producer.
pub(crate) open spec fn same_intrinsic_inputs<A: FinishModel + IntrinsicOracle<A::Id>>(
    numeric: &A, full: &A, slot: Request<A::Id>,
) -> bool {
    &&& same_intrinsic_leaf_inputs(numeric, full, slot)
    &&& stack_intrinsic(numeric, slot) ==> numeric.finish_child_count(slot.node) == full.finish_child_count(slot.node)
    &&& (stack_intrinsic(numeric, slot) || largest_intrinsic(numeric, slot) || reads_intrinsic_grid_scan(numeric, slot))
        ==> stack_rows(numeric, slot) == stack_rows(full, slot)
    &&& reads_intrinsic_grid_scan(numeric, slot) ==> grid_track_word(numeric, slot) == grid_track_word(full, slot)
    &&& flow_intrinsic(numeric, slot) ==> intrinsic_flow_word(numeric, slot) == intrinsic_flow_word(full, slot)
}

pub(crate) open spec fn intrinsic_warnings<A: FinishModel>(access: &A, slot: Request<A::Id>) -> Seq<FinishEffect<A::Id>> {
    if stack_intrinsic(access, slot) { stack_intrinsic_warnings(access, slot) } else { Seq::empty() }
}

pub(crate) open spec fn intrinsic_datum<A: FinishModel + IntrinsicOracle<A::Id>>(
    access: &A, slot: Request<A::Id>,
) -> Option<Seq<u32>> {
    if !is_intrinsic(access, slot) {
        None
    } else {
        let value = if stack_intrinsic(access, slot) {
            stack_intrinsic_value(access, slot)
        } else if grid_intrinsic(access, slot) {
            grid_intrinsic_value(access, slot)
        } else if flow_intrinsic(access, slot) {
            flow_intrinsic_value(access, slot)
        } else {
            largest_intrinsic_value(access, slot)
        };
        Some(seq![A::Float::word(value)])
    }
}

/// Compare the actual packed `Auto` and `FitContent` writes for every layout.
/// Also compare the measurement requests and warning effects issued in order.
pub(crate) fn compare_intrinsic_producers<A: FinishPublication>(
    numeric: &mut A, full: &mut A, slot: Request<A::Id>,
) -> (stored: (StoredSize<A::Id>, StoredSize<A::Id>))
    requires is_intrinsic(old(numeric), slot), is_intrinsic(old(full), slot),
        ready_inputs(old(numeric), slot), ready_inputs(old(full), slot),
        same_intrinsic_inputs(old(numeric), old(full), slot),
    ensures stored.0.slot == slot, stored.1.slot == slot, stored.0.value == stored.1.value,
        intrinsic_datum(old(full), slot) == Some(seq![A::Float::word(stored.1.value)]),
        intrinsic_datum(old(full), slot) == intrinsic_datum(old(numeric), slot),
        final(numeric).finish_values(slot.node)[key(slot).1 as int] == final(full).finish_values(slot.node)[key(slot).1 as int],
        final(numeric).measurement_requests() == old(numeric).measurement_requests() + measurement_requests_for(old(full), slot),
        final(full).measurement_requests() == old(full).measurement_requests() + measurement_requests_for(old(full), slot),
        final(numeric).finish_effects() == (old(numeric).finish_effects() + intrinsic_warnings(old(full), slot))
            .push(FinishEffect::Publish(slot, stored.1.value)),
        final(full).finish_effects() == (old(full).finish_effects() + intrinsic_warnings(old(full), slot))
            .push(FinishEffect::Publish(slot, stored.1.value)),
        final(numeric).wrap_effects() == old(numeric).wrap_effects(),
        final(full).wrap_effects() == old(full).wrap_effects(),
    no_unwind
{
    proof {
        matching_own_content(numeric, full, slot);
        assert(stack_intrinsic(numeric, slot) == stack_intrinsic(full, slot));
        assert(largest_intrinsic(numeric, slot) == largest_intrinsic(full, slot));
        assert(flow_intrinsic(numeric, slot) == flow_intrinsic(full, slot));
        assert(grid_intrinsic(numeric, slot) == grid_intrinsic(full, slot));
        assert(stack_intrinsic(numeric, slot) || largest_intrinsic(numeric, slot)
            || flow_intrinsic(numeric, slot) || grid_intrinsic(numeric, slot));
        if stack_intrinsic(numeric, slot) {
            assert(stack_intrinsic_value(numeric, slot) == stack_intrinsic_value(full, slot));
            assert(stack_intrinsic_warnings(numeric, slot) == stack_intrinsic_warnings(full, slot));
        } else if largest_intrinsic(numeric, slot) {
            assert(largest_intrinsic_value(numeric, slot) == largest_intrinsic_value(full, slot));
        } else if flow_intrinsic(numeric, slot) {
            assert(flow_intrinsic_value(numeric, slot) == flow_intrinsic_value(full, slot));
        } else {
            assert(grid_intrinsic_value(numeric, slot) == grid_intrinsic_value(full, slot));
        }
    }
    let incremental = finish_size(numeric, slot);
    let reference = finish_size(full, slot);
    (incremental, reference)
}

/// Compare the native ordered child folds using the input words each route
/// reads. Each route publishes exactly one intrinsic size word.
pub(crate) fn compare_stack_intrinsic_producers<A: FinishPublication>(
    numeric: &mut A, full: &mut A, slot: Request<A::Id>,
) -> (stored: (StoredSize<A::Id>, StoredSize<A::Id>))
    requires stack_intrinsic(old(numeric), slot), stack_intrinsic(old(full), slot),
        ready_inputs(old(numeric), slot), ready_inputs(old(full), slot),
        same_intrinsic_leaf_inputs(old(numeric), old(full), slot),
        old(numeric).finish_child_count(slot.node) == old(full).finish_child_count(slot.node),
        stack_rows(old(numeric), slot) == stack_rows(old(full), slot),
    ensures stored.0.slot == slot, stored.1.slot == slot, stored.0.value == stored.1.value,
        final(numeric).finish_values(slot.node)[key(slot).1 as int] == final(full).finish_values(slot.node)[key(slot).1 as int],
        final(numeric).measurement_requests() == old(numeric).measurement_requests() + measurement_requests_for(old(full), slot),
        final(full).measurement_requests() == old(full).measurement_requests() + measurement_requests_for(old(full), slot),
        final(numeric).finish_effects() == (old(numeric).finish_effects() + stack_intrinsic_warnings(old(full), slot))
            .push(FinishEffect::Publish(slot, stored.1.value)),
        final(full).finish_effects() == (old(full).finish_effects() + stack_intrinsic_warnings(old(full), slot))
            .push(FinishEffect::Publish(slot, stored.1.value)),
    no_unwind
{
    proof {
        matching_own_content(numeric, full, slot);
        assert(stack_intrinsic_value(numeric, slot) == stack_intrinsic_value(full, slot));
        assert(stack_intrinsic_warnings(numeric, slot) == stack_intrinsic_warnings(full, slot));
    }
    let incremental = finish_size(numeric, slot);
    let reference = finish_size(full, slot);
    (incremental, reference)
}

/// Compare the two executable finishers with the same declarations and packed words.
/// The caller provides the already-ready inputs of a Final dependency.
fn compare_unbounded_final<A: FinishPublication>(
    reference: &mut A, direct: &mut crate::node_data::NodeLayoutData, slot: Request<A::Id>,
) -> (accepted: bool)
    where A::Float: crate::prepare_frame::FrameFloat,
    requires slot.kind is Final, ready_inputs(old(reference), slot), regular_present(old(reference), slot),
        old(direct).values == old(reference).finish_values(slot.node),
        old(direct).flags == old(reference).finish_flags(slot.node),
    ensures
        accepted ==> {
            &&& final(reference).finish_effects() == old(reference).finish_effects().push(
                FinishEffect::Publish(slot, final(direct).values[key(slot).1 as int]))
            &&& final(direct).levels == old(direct).levels
        },
        !accepted ==> *final(reference) == *old(reference) && *final(direct) == *old(direct),
    no_unwind
{
    let axis = slot.axis();
    let Some(fit) = unbounded_final_input(reference.params(slot.node), axis) else { return false; };
    if !direct.try_finish_unbounded_final::<A::Float>(axis, fit) { return false; }
    proof {
        assert(has_unbounded_final_inputs(reference.finish_layout(slot.node), axis, fit));
        assert(permits_direct_final(reference.finish_layout(slot.node), axis, reference.finish_flags(slot.node))) by {
            assert(exists |mode: bool| has_unbounded_final_inputs(reference.finish_layout(slot.node), axis, mode)
                && (!mode || reference.finish_flags(slot.node).0 & NodeFlags::flex_child(axis) == 0));
        }
        assert(canonical_direct_final(reference, slot));
    }
    finish_size(reference, slot);
    true
}
}
