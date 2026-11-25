//! Intrinsic child geometry and the text and custom measurement inputs.
#![allow(unexpected_cfgs)]

use super::*;
use crate::declarations::{ContentMeasure, TextContent, X, Xy, Y};

#[cfg(verus_keep_ghost)]
use crate::{measurement_contract::{Axis as MeasureAxis, Request as MeasureRequest}, prepare_leaf::on_axis};

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait IntrinsicOracle<I> {
    spec fn measurement(&self) -> spec_fn(I, MeasureRequest) -> f32;
    /// Requests at the measurement boundary, including hits in the host's cache.
    spec fn measurement_requests(&self) -> Seq<(I, MeasureRequest)>;
}

pub(crate) open spec fn known_limit<F: FrameFloat>(params: LayoutParams, axis: Axis) -> Option<f32> {
    match on_axis(params.max_size, axis) {
        Some(Size::Pixels(value)) => Some(inner_extent::<F>(value, pad_extent::<F>(params, axis))),
        _ => None,
    }
}

pub(crate) open spec fn measure_axis(axis: Axis) -> MeasureAxis {
    if axis is X { MeasureAxis::X } else { MeasureAxis::Y }
}

pub(crate) open spec fn measure_word<F: FrameFloat>(number: Option<f32>) -> Option<u32> {
    match number { Some(value) => Some(F::word(value)), None => None }
}

pub(crate) open spec fn content_request<F: FrameFloat>(axis: Axis, known: Xy<Option<f32>>, max: Xy<Option<f32>>) -> MeasureRequest {
    MeasureRequest::Content {
        axis: measure_axis(axis),
        known_dimensions: [measure_word::<F>(known.x), measure_word::<F>(known.y)],
        max_size: [measure_word::<F>(max.x), measure_word::<F>(max.y)],
    }
}

pub(crate) open spec fn opposite_content<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    let opposite = target(slot.node, !slot.vertical, Kind::Final);
    inner_extent::<A::Float>(access.finish_values(slot.node)[key(opposite).1 as int],
        pad_extent::<A::Float>(access.finish_layout(slot.node), opposite.axis()))
}

pub(crate) open spec fn canonical_request<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> MeasureRequest {
    let params = access.finish_layout(slot.node);
    let known = if params.content_measure.reads_other_axis(slot.axis()) {
        if slot.vertical { Xy { x: Some(opposite_content(access, slot)), y: None } }
        else { Xy { x: None, y: Some(opposite_content(access, slot)) } }
    } else { Xy { x: None, y: None } };
    content_request::<A::Float>(slot.axis(), known, Xy { x: known_limit::<A::Float>(params, X), y: known_limit::<A::Float>(params, Y) })
}

pub(crate) open spec fn measurement_inputs_stable<A: FinishModel + IntrinsicOracle<A::Id> + ?Sized>(before: &A, after: &A) -> bool {
    &&& before.measurement() == after.measurement()
    &&& forall |node: A::Id| #[trigger] after.finish_layout(node) == before.finish_layout(node)
    &&& forall |node: A::Id| #[trigger] after.finish_values(node) == before.finish_values(node)
}

pub(crate) open spec fn text_request<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> Option<MeasureRequest> {
    let params = access.finish_layout(slot.node);
    if params.text is None { None }
    else if params.text_wraps_on(slot.axis()) {
        Some(MeasureRequest::TextHeight { wrap_width: Some(A::Float::word(opposite_content(access, slot))) })
    } else if slot.vertical {
        Some(MeasureRequest::TextHeight { wrap_width: None })
    } else {
        Some(MeasureRequest::TextWidth)
    }
}

pub(crate) open spec fn measurement_requests_for<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>)
    -> Seq<(A::Id, MeasureRequest)>
{
    let text = match text_request(access, slot) { Some(req) => seq![(slot.node, req)], None => Seq::empty() };
    if access.finish_layout(slot.node).content_measure is None { text }
    else { text.push((slot.node, canonical_request(access, slot))) }
}

pub(crate) open spec fn own_extent<A: FinishModel + IntrinsicOracle<A::Id> + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    let params = access.finish_layout(slot.node);
    let text = match text_request(access, slot) {
        Some(req) => (access.measurement())(slot.node, req), None => 0.0f32,
    };
    let with_image = match params.image { Some(image) => A::Float::maximum(text, on_axis(image, slot.axis())), None => text };
    if params.content_measure is None { with_image }
    else { A::Float::maximum(with_image, (access.measurement())(slot.node, canonical_request(access, slot))) }
}

pub(crate) open spec fn no_in_flow_children<A: FinishModel + ?Sized>(access: &A, node: A::Id) -> bool {
    let children = (access.topology().children)(node);
    forall |i: int| 0 <= i < children.len() ==> !(#[trigger] children[i]).in_flow
}

/// A Free item's intrinsic content has no child contribution when its
/// child list is empty or every child is disabled or freely placed.
pub(crate) open spec fn free_intrinsic<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    &&& is_intrinsic(access, slot)
    &&& access.finish_layout(slot.node).children_layout is Free
    &&& no_in_flow_children(access, slot.node)
}

pub(crate) open spec fn free_intrinsic_value<A: FinishModel + IntrinsicOracle<A::Id> + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    inherent_extent::<A::Float>(0.0f32, own_extent(access, slot), 0.0f32,
        pad_extent::<A::Float>(access.finish_layout(slot.node), slot.axis()))
}

pub(crate) open spec fn child_declaration<A: FinishModel + ?Sized>(access: &A, child: Request<A::Id>) -> Option<Size> {
    let flags = access.finish_flags(child.node);
    sizing_requests::resolved_size(access.finish_layout(child.node), child.vertical, child.kind,
        flags.is_block_item(), flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0)
}

pub(crate) open spec fn pre_grow_bound<A: FinishModel + ?Sized>(access: &A, child: Request<A::Id>) -> Option<f32> {
    match child_declaration(access, child) {
        Some(size) if !size.is_flex() => Some(access.finish_values(child.node)[key(child).1 as int]),
        _ => None,
    }
}

/// The word and bounds read before assigning any remaining space to Fill.
pub(crate) open spec fn pre_grow_input<A: FinishModel + ?Sized>(access: &A, regular: Request<A::Id>) -> f32 {
    match child_declaration(access, regular) {
        Some(Size::Fill | Size::Frac(_)) => 0.0f32,
        _ => access.finish_values(regular.node)[key(regular).1 as int],
    }
}

pub(crate) open spec fn pre_grow_extent<A: FinishModel + ?Sized>(access: &A, regular: Request<A::Id>) -> f32 {
    clamp_extent::<A::Float>(pre_grow_input(access, regular),
        pre_grow_bound(access, target(regular.node, regular.vertical, Kind::Min)),
        pre_grow_bound(access, target(regular.node, regular.vertical, Kind::Max)))
}

pub(crate) struct StackRow {
    pub(crate) regular: f32,
    pub(crate) minimum: Option<f32>,
    pub(crate) maximum: Option<f32>,
    pub(crate) margins: [f32; 2],
    pub(crate) fraction: Option<f32>,
    pub(crate) span: u16,
}

pub(crate) open spec fn stack_row<A: FinishModel + ?Sized>(
    access: &A, slot: Request<A::Id>, child: sizing_requests::Child<A::Id>,
) -> Option<StackRow> {
    let other = child.node;
    let regular = target(other, slot.vertical, Kind::Regular);
    if child.in_flow {
        Some(StackRow {
            regular: pre_grow_input(access, regular),
            minimum: pre_grow_bound(access, target(other, slot.vertical, Kind::Min)),
            maximum: pre_grow_bound(access, target(other, slot.vertical, Kind::Max)),
            margins: margin_pair::<A::Float>(access.finish_layout(other), slot.axis()),
            fraction: match child_declaration(access, regular) {
                Some(Size::Frac(fraction)) => Some(fraction), _ => None,
            },
            span: on_axis(access.finish_layout(other).grid_span, slot.axis()),
        })
    } else { None }
}

pub(crate) closed spec fn stack_rows<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> Seq<Option<StackRow>> {
    (access.topology().children)(slot.node).map_values(|child: sizing_requests::Child<A::Id>| stack_row(access, slot, child))
}

proof fn stack_rows_count<A: FinishModel>(access: &A, slot: Request<A::Id>)
    ensures stack_rows(access, slot).len() == (access.topology().children)(slot.node).len(),
{
    reveal(stack_rows);
}

proof fn stack_row_at<A: FinishModel>(access: &A, slot: Request<A::Id>, index: nat)
    requires index < (access.topology().children)(slot.node).len(),
    ensures stack_rows(access, slot)[index as int] == stack_row(access, slot,
        (access.topology().children)(slot.node)[index as int]),
{
    reveal(stack_rows);
}

pub(crate) open spec fn with_stack_margin<F: FrameFloat>(size: f32, margin: f32) -> f32 {
    if F::word(margin) & 0x7fff_ffffu32 == 0 { size } else { F::sum(size, margin) }
}

pub(crate) open spec fn stack_row_extent<F: FrameFloat>(row: StackRow) -> f32 {
    with_stack_margin::<F>(clamp_extent::<F>(row.regular, row.minimum, row.maximum),
        F::sum(row.margins[0], row.margins[1]))
}

/// Earliest finite parent size at which this child's positive fraction reaches
/// its maximum. Division can round just below the necessary breakpoint.
pub(crate) open spec fn next_bound<F: FrameFloat>(frac: f32, maximum: Option<f32>, wanted: f32,
    prior: Option<f32>) -> Option<f32> {
    match maximum {
        Some(cap) if F::at_most(0.0f32, frac) && !F::number_eq(0.0f32, frac)
            && F::at_most(wanted, cap) && !F::number_eq(wanted, cap) => {
            let x = F::quotient(cap, frac);
            let probe = if F::at_most(F::product(x, frac), cap) && !F::number_eq(F::product(x, frac), cap) {
                F::decode(F::word(x).saturating_add(1))
            } else { x };
            if !F::finite_word(probe) { prior } else {
                Some(match prior { Some(prev) => F::minimum(prev, probe), None => probe })
            }
        }
        _ => prior,
    }
}

/// A fractional contribution is either accumulated into the free fraction
/// or clamped and added to the fixed extent. Each margin reaches the sum first.
pub(crate) open spec fn stack_row_progress<F: FrameFloat>(
    row: StackRow, estimate: f32, current: (f32, f32, bool, Option<f32>),
) -> (f32, f32, bool, Option<f32>) {
    let (extent, free_frac, has_frac, next_cap) = current;
    let margin = F::sum(row.margins[0], row.margins[1]);
    match row.fraction {
        Some(frac) => {
            let extent = F::sum(extent, margin);
            let wanted = F::product(estimate, frac);
            let allowed = clamp_extent::<F>(wanted, row.minimum, row.maximum);
            let next_cap = next_bound::<F>(frac, row.maximum, wanted, next_cap);
            if F::number_eq(allowed, wanted) && !matches!(row.maximum, Some(cap) if F::number_eq(wanted, cap)) {
                (extent, F::sum(free_frac, frac), true, next_cap)
            } else { (F::sum(extent, allowed), free_frac, true, next_cap) }
        }
        None => (F::sum(extent, stack_row_extent::<F>(row)), free_frac, has_frac, next_cap),
    }
}

/// Keep the execution order of floating point addition, including skipped rows.
pub(crate) closed spec fn stack_prefix<F: FrameFloat>(
    rows: Seq<Option<StackRow>>, estimate: f32, end: nat,
) -> (f32, f32, bool, Option<f32>)
    decreases end,
{
    if end == 0 { (0.0f32, 0.0f32, false, None) } else {
        let before = stack_prefix::<F>(rows, estimate, (end - 1) as nat);
        match rows[end - 1] {
            Some(row) => stack_row_progress::<F>(row, estimate, before), None => before,
        }
    }
}

proof fn stack_step<F: FrameFloat>(rows: Seq<Option<StackRow>>, estimate: f32, end: nat)
    requires end < rows.len(),
    ensures stack_prefix::<F>(rows, estimate, end + 1) == match rows[end as int] {
        Some(row) => stack_row_progress::<F>(row, estimate, stack_prefix::<F>(rows, estimate, end)),
        None => stack_prefix::<F>(rows, estimate, end),
    },
{
    reveal(stack_prefix);
}

pub(crate) open spec fn stack_intrinsic<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    &&& is_intrinsic(access, slot)
    &&& match access.finish_layout(slot.node).children_layout {
        ChildrenLayout::Stack { axis, .. } | ChildrenLayout::Wrap { axis, .. } =>
            axis.index() == slot.axis().index(),
        _ => false,
    }
}

pub(crate) open spec fn stack_intrinsic_value<A: FinishModel + IntrinsicOracle<A::Id> + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    let result = fit_stack_recipe::<A::Float>(stack_rows(access, slot), 0.0f32, false, (MAX_FIT_STACK_STEPS + access.finish_child_count(slot.node)) as nat);
    inherent_extent::<A::Float>(result.0, own_extent(access, slot),
        declared_gaps(access, slot.node, slot.axis()), pad_extent::<A::Float>(access.finish_layout(slot.node), slot.axis()))
}

pub(crate) open spec fn stack_intrinsic_warnings<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> Seq<FinishEffect<A::Id>> {
    let result = fit_stack_recipe::<A::Float>(stack_rows(access, slot), 0.0f32, false, (MAX_FIT_STACK_STEPS + access.finish_child_count(slot.node)) as nat);
    if result.1 { seq![FinishEffect::Warning(slot, Warning::ImpossibleFracChildren)] }
    else { Seq::empty() }
}

pub(crate) open spec fn flow_intrinsic<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    is_intrinsic(access, slot) && intrinsic_uses_flow(slot, access.finish_layout(slot.node).children_layout)
}

pub(crate) open spec fn intrinsic_flow_word<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    access.finish_values(slot.node)[key(target(slot.node, slot.vertical, Kind::Flow)).1 as int]
}

pub(crate) open spec fn flow_intrinsic_value<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    inherent_extent::<A::Float>(intrinsic_flow_word(access, slot), own_extent(access, slot), 0.0f32,
        pad_extent::<A::Float>(access.finish_layout(slot.node), slot.axis()))
}

pub(crate) open spec fn largest_row_extent<F: FrameFloat>(row: StackRow, free: bool) -> f32 {
    let size = clamp_extent::<F>(row.regular, row.minimum, row.maximum);
    if free { size } else { with_stack_margin::<F>(size, F::sum(row.margins[0], row.margins[1])) }
}

/// Free layout ignores margins. Cross-axis Stack and inline Block use the
/// same scan with each in-flow child's margin included.
pub(crate) closed spec fn largest_prefix<F: FrameFloat>(rows: Seq<Option<StackRow>>, free: bool, end: nat) -> f32
    decreases end,
{
    if end == 0 { 0.0f32 } else {
        let previous = largest_prefix::<F>(rows, free, (end - 1) as nat);
        match rows[end - 1] {
            Some(row) => F::maximum(previous, largest_row_extent::<F>(row, free)),
            None => previous,
        }
    }
}

proof fn largest_step<F: FrameFloat>(rows: Seq<Option<StackRow>>, free: bool, end: nat)
    requires end < rows.len(),
    ensures largest_prefix::<F>(rows, free, end + 1) == match rows[end as int] {
        Some(row) => F::maximum(largest_prefix::<F>(rows, free, end), largest_row_extent::<F>(row, free)),
        None => largest_prefix::<F>(rows, free, end),
    },
{
    reveal(largest_prefix);
}

pub(crate) open spec fn largest_intrinsic<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    &&& is_intrinsic(access, slot)
    &&& match access.finish_layout(slot.node).children_layout {
        ChildrenLayout::Free => true,
        ChildrenLayout::Stack { axis, .. } => axis.index() != slot.axis().index(),
        ChildrenLayout::Block => !slot.vertical,
        _ => false,
    }
}

pub(crate) open spec fn largest_intrinsic_value<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    let rows = stack_rows(access, slot);
    let layout = access.finish_layout(slot.node).children_layout;
    inherent_extent::<A::Float>(largest_prefix::<A::Float>(rows, layout is Free, rows.len()), own_extent(access, slot),
        0.0f32, pad_extent::<A::Float>(access.finish_layout(slot.node), slot.axis()))
}

pub(crate) open spec fn grid_cell_extent<F: FrameFloat>(row: StackRow, tracks: f32, spacing: f32) -> f32 {
    let span = F::count_value(if row.span == 0 { 1u32 } else { row.span as u32 });
    let span = F::minimum(span, F::maximum(tracks, 1.0f32));
    let footprint = largest_row_extent::<F>(row, false);
    F::quotient(F::difference(footprint, F::product(F::difference(span, 1.0f32), spacing)), span)
}

pub(crate) closed spec fn grid_prefix<F: FrameFloat>(rows: Seq<Option<StackRow>>, tracks: f32, spacing: f32, end: nat) -> f32
    decreases end,
{
    if end == 0 { 0.0f32 } else {
        let previous = grid_prefix::<F>(rows, tracks, spacing, (end - 1) as nat);
        match rows[end - 1] {
            Some(row) => F::maximum(previous, grid_cell_extent::<F>(row, tracks, spacing)),
            None => previous,
        }
    }
}

proof fn grid_step<F: FrameFloat>(rows: Seq<Option<StackRow>>, tracks: f32, spacing: f32, end: nat)
    requires end < rows.len(),
    ensures grid_prefix::<F>(rows, tracks, spacing, end + 1) == match rows[end as int] {
        Some(row) => F::maximum(grid_prefix::<F>(rows, tracks, spacing, end), grid_cell_extent::<F>(row, tracks, spacing)),
        None => grid_prefix::<F>(rows, tracks, spacing, end),
    },
{
    reveal(grid_prefix);
}

pub(crate) open spec fn grid_intrinsic<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> bool {
    is_intrinsic(access, slot) && access.finish_layout(slot.node).children_layout is Grid
}

pub(crate) open spec fn grid_extent<F: FrameFloat>(tracks: f32, cell: f32, spacing: f32) -> f32 {
    F::maximum(F::sum(F::product(tracks, cell), F::product(spacing, F::difference(tracks, 1.0f32))), 0.0f32)
}

pub(crate) open spec fn grid_intrinsic_value<A: FinishModel + ?Sized>(access: &A, slot: Request<A::Id>) -> f32 {
    match access.finish_layout(slot.node).children_layout {
        ChildrenLayout::Grid { columns, spacing_x, spacing_y, main_axis, .. } => {
            let spacing = if slot.vertical { spacing_y } else { spacing_x };
            let (tracks, cell) = match columns {
                MainAxisCellSize::Width(width) if main_axis.index() == slot.axis().index() => (1.0f32, width),
                _ => {
                    let tracks = grid_track_word(access, slot);
                    let rows = stack_rows(access, slot);
                    (tracks, grid_prefix::<A::Float>(rows, tracks, spacing, rows.len()))
                }
            };
            inherent_extent::<A::Float>(grid_extent::<A::Float>(tracks, cell, spacing), own_extent(access, slot),
                0.0f32, pad_extent::<A::Float>(access.finish_layout(slot.node), slot.axis()))
        },
        _ => 0.0f32,
    }
}

pub(crate) open spec fn intrinsic_effects_stable<A: FinishModel + ?Sized>(before: &A, after: &A) -> bool {
    after.finish_effects() == before.finish_effects() && after.wrap_effects() == before.wrap_effects()
}

}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait IntrinsicOracle<I> {}
#[cfg(not(verus_keep_ghost))]
impl<T: ?Sized, I> IntrinsicOracle<I> for T {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait IntrinsicContent: FinishAccess + IntrinsicOracle<Self::Id> {
    #[cfg_attr(verus_keep_ghost, verus_spec(wrap =>
        ensures wrap == self.finish_layout(slot.node).text_wraps_on(slot.axis()),
            wrap ==> slot.vertical && (self.topology().intrinsic_other)(slot),
        no_unwind
    ))]
    fn wrapping_text(&self, slot: Request<Self::Id>) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(cross =>
        ensures cross == params.content_measure.reads_other_axis(slot.axis()),
            cross ==> (self.topology().intrinsic_other)(slot),
        no_unwind
    ))]
    fn content_needs_constraint(&self, slot: Request<Self::Id>, params: &LayoutParams) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            measurement_inputs_stable(old(self), final(self)),
            intrinsic_effects_stable(old(self), final(self)),
            final(self).measurement_requests() == old(self).measurement_requests(),
        no_unwind
    ))]
    fn track_content(&mut self);

    #[cfg_attr(verus_keep_ghost, verus_spec(value =>
        ensures final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            measurement_inputs_stable(old(self), final(self)),
            value == (old(self).measurement())(node, MeasureRequest::TextWidth),
            intrinsic_effects_stable(old(self), final(self)),
            final(self).measurement_requests() == old(self).measurement_requests().push((node, MeasureRequest::TextWidth)),
        no_unwind
    ))]
    fn text_width(&mut self, node: Self::Id) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(value =>
        ensures final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            measurement_inputs_stable(old(self), final(self)),
            value == (old(self).measurement())(node, MeasureRequest::TextHeight { wrap_width: measure_word::<Self::Float>(width) }),
            intrinsic_effects_stable(old(self), final(self)),
            final(self).measurement_requests() == old(self).measurement_requests().push((node, MeasureRequest::TextHeight { wrap_width: measure_word::<Self::Float>(width) })),
        no_unwind
    ))]
    fn text_height(&mut self, node: Self::Id, width: Option<f32>) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(value =>
        ensures final(self).topology() == old(self).topology(), final(self).ready() == old(self).ready(),
            measurement_inputs_stable(old(self), final(self)),
            value == (old(self).measurement())(node, content_request::<Self::Float>(axis, known, maximum)),
            intrinsic_effects_stable(old(self), final(self)),
            final(self).measurement_requests() == old(self).measurement_requests().push((node, content_request::<Self::Float>(axis, known, maximum))),
        no_unwind
    ))]
    fn content_size(
        &mut self, node: Self::Id, axis: Axis, known: Xy<Option<f32>>, maximum: Xy<Option<f32>>,
    ) -> f32;
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires *params == access.finish_layout(node),
    ensures result == known_limit::<A::Float>(*params, axis),
    no_unwind
))]
fn pixel_max<A: IntrinsicContent>(access: &A, node: A::Id, params: &LayoutParams, axis: Axis) -> Option<f32> {
    match *params.max_size.component(axis) {
        Some(Size::Pixels(pixels)) => Some(inner::<A::Float>(pixels, padding_for::<A::Float>(access.params(node), axis))),
        _ => None,
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires ready_inputs(old(access), slot), is_intrinsic(old(access), slot),
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        value == (old(access).measurement())(slot.node, canonical_request(old(access), slot)),
        measurement_inputs_stable(old(access), final(access)),
        intrinsic_effects_stable(old(access), final(access)),
        final(access).measurement_requests() == old(access).measurement_requests().push((slot.node, canonical_request(old(access), slot))),
    no_unwind
))]
fn custom_content<A: IntrinsicContent>(access: &mut A, slot: Request<A::Id>) -> f32 {
    access.track_content();
    let params = access.params(slot.node);
    let known = if access.content_needs_constraint(slot, params) {
        let other = target(slot.node, !slot.vertical, Kind::Final);
        #[cfg(verus_keep_ghost)]
        proof! { intrinsic_constraint_is_ready(access, slot); }
        let content = inner::<A::Float>(read(access, other), padding_for::<A::Float>(access.params(slot.node), other.axis()));
        if slot.vertical { Xy::new(Some(content), None) } else { Xy::new(None, Some(content)) }
    } else { Xy::new(None, None) };
    let maximum = Xy::new(pixel_max(access, slot.node, params, X), pixel_max(access, slot.node, params, Y));
    access.content_size(slot.node, slot.axis(), known, maximum)
}

/// Child geometry is combined with text, image and custom measurements in the
/// same order as the host callbacks. Only constrained measurements read Final.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires ready_inputs(old(access), slot), is_intrinsic(old(access), slot),
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        measurement_inputs_stable(old(access), final(access)),
        intrinsic_effects_stable(old(access), final(access)),
        final(access).measurement_requests() == old(access).measurement_requests() + measurement_requests_for(old(access), slot),
        value == inherent_extent::<A::Float>(children, own_extent(old(access), slot), gaps,
            pad_extent::<A::Float>(old(access).finish_layout(slot.node), slot.axis())),
    no_unwind
))]
pub(crate) fn intrinsic_content<A: IntrinsicContent>(access: &mut A, slot: Request<A::Id>, children: f32, gaps: f32) -> f32 {
    let axis = slot.axis();
    let mut own = match access.params(slot.node).text {
        TextContent::None => 0.0,
        _ => {
            access.track_content();
            if access.wrapping_text(slot) {
                let input = target(slot.node, false, Kind::Final);
                #[cfg(verus_keep_ghost)]
                proof! { intrinsic_constraint_is_ready(access, slot); }
                let width = inner::<A::Float>(read(access, input), padding_for::<A::Float>(access.params(slot.node), X));
                access.text_height(slot.node, Some(width))
            } else if slot.vertical {
                access.text_height(slot.node, None)
            } else {
                access.text_width(slot.node)
            }
        }
    };
    if let Some(image) = access.params(slot.node).image {
        own = A::Float::max(own, *image.component(axis));
    }
    if !matches!(access.params(slot.node).content_measure, ContentMeasure::None) {
        own = A::Float::max(own, custom_content(access, slot));
    }
    intrinsic_extent::<A::Float>(children, own, gaps, padding_for::<A::Float>(access.params(slot.node), axis))
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn intrinsic_uses_flow<I>(slot: Request<I>, layout: ChildrenLayout) -> bool {
    match layout {
        ChildrenLayout::Block => slot.vertical,
        ChildrenLayout::Wrap { axis, .. } => axis.index() != slot.vertical as usize,
        _ => false,
    }
}

pub(crate) open spec fn intrinsic_tracks_need_other<I>(slot: Request<I>, layout: ChildrenLayout) -> bool {
    match layout {
        ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } =>
            main_axis.index() != slot.vertical as usize,
        _ => false,
    }
}

pub(crate) open spec fn child_bound<A: FinishModel>(access: &A, slot: Request<A::Id>, cursor: nat) -> bool {
    let children = (access.topology().children)(slot.node);
    &&& cursor < children.len()
    &&& children[cursor as int].in_flow
}

proof fn child_prefix_preserves<A: FinishModel>(
    access: &A, slot: Request<A::Id>, through: nat, input: Request<A::Id>,
)
    requires through < (access.topology().children)(slot.node).len(),
        sizing_requests::child_prefix(access.topology(), slot, through).contains(input),
    ensures sizing_requests::child_prefix(access.topology(), slot, (access.topology().children)(slot.node).len()).contains(input),
    decreases (access.topology().children)(slot.node).len() - through,
{
    let topology = access.topology();
    let prior = sizing_requests::child_prefix(topology, slot, through);
    let grown = sizing_requests::child_prefix(topology, slot, through + 1);
    let at = choose |i: int| 0 <= i < prior.len() && #[trigger] prior[i] == input;
    assert(grown[at] == prior[at]);
    assert(0 <= at < grown.len() && grown[at] == input);
    if through + 1 < (topology.children)(slot.node).len() {
        child_prefix_preserves(access, slot, through + 1, input);
    }
}

proof fn child_value_ready<A: FinishModel>(
    access: &A, slot: Request<A::Id>, input: Request<A::Id>, cursor: nat,
)
    requires is_intrinsic(access, slot), ready_inputs(access, slot),
        !(access.topology().intrinsic_flow)(slot), child_bound(access, slot, cursor),
        input == target((access.topology().children)(slot.node)[cursor as int].node, slot.vertical, input.kind),
        input.kind is Regular || input.kind is Min || input.kind is Max,
        sizing_requests::selected((access.topology().form)(input), true),
    ensures is_ready(access, input),
{
    let layout = access.topology();
    let rows = (layout.children)(slot.node);
    let child = rows[cursor as int];
    let row_slot = target(child.node, slot.vertical, slot.kind);
    reveal_with_fuel(sizing_requests::declaration_prefix, 4);
    let order = cycle_rules::declaration_order(Kind::Regular, Kind::Min, Kind::Max);
    assert(order@[0] == Kind::Regular && order@[1] == Kind::Min && order@[2] == Kind::Max);
    let regular = target(child.node, slot.vertical, Kind::Regular);
    let min = target(child.node, slot.vertical, Kind::Min);
    let max = target(child.node, slot.vertical, Kind::Max);
    let prefix = sizing_requests::declaration_prefix(layout, row_slot, true, 1);
    let through_min = sizing_requests::declaration_prefix(layout, row_slot, true, 2);
    let all = sizing_requests::declaration_prefix(layout, row_slot, true, 3);
    let form = layout.form;
    assert(prefix == if sizing_requests::selected(form(regular), true) {
        Seq::<Request<A::Id>>::empty().push(regular)
    } else { Seq::empty() });
    assert(through_min == if sizing_requests::selected(form(min), true) { prefix.push(min) } else { prefix });
    assert(all == if sizing_requests::selected(form(max), true) { through_min.push(max) } else { through_min });
    let local = if input.kind is Regular { 0 } else if input.kind is Min { prefix.len() as int } else { through_min.len() as int };
    assert(0 <= local < all.len() && all[local] == input);
    let offset = sizing_requests::child_prefix(layout, slot, cursor).len() + local;
    let next = sizing_requests::child_prefix(layout, slot, cursor + 1);
    assert(offset < next.len() && next[offset] == input);
    if cursor + 1 < rows.len() {
        child_prefix_preserves(access, slot, cursor + 1, input);
    }
    let requested = sizing_requests::inputs(layout, slot);
    let geometry = sizing_requests::child_prefix(layout, slot, rows.len());
    let at = choose |i: int| 0 <= i < geometry.len() && #[trigger] geometry[i] == input;
    assert(0 <= at < requested.len() && requested[at] == input);
    read_dependency(access, slot, input);
}

fn start_children() -> (cursor: Ghost<nat>)
    ensures cursor@ == 0nat,
    no_unwind
{
    Ghost(0nat)
}

fn step_child(cursor: Ghost<nat>) -> (next: Ghost<nat>)
    ensures next@ == cursor@ + 1,
    no_unwind
{
    Ghost(cursor@ + 1)
}

} // verus!

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait IntrinsicRows: IntrinsicContent {
    #[cfg_attr(verus_keep_ghost, verus_spec(layout =>
        ensures layout == self.finish_layout(slot.node).children_layout,
            intrinsic_uses_flow(slot, layout) == (self.topology().intrinsic_flow)(slot),
            intrinsic_tracks_need_other(slot, layout) ==> (self.topology().intrinsic_other)(slot),
        no_unwind
    ))]
    fn intrinsic_layout(&self, slot: Request<Self::Id>) -> ChildrenLayout;

    #[cfg_attr(verus_keep_ghost, verus_spec(child =>
        ensures child == sizing_requests::child_at((self.topology().children)(parent), 0),
        no_unwind
    ))]
    fn first_child(&self, parent: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(row =>
        ensures forall |i: nat|
            #[trigger] sizing_requests::child_at((self.topology().children)(parent), i) == Some(child)
            ==> row == (sizing_requests::child_at((self.topology().children)(parent), i + 1),
                        (self.topology().children)(parent)[i as int].in_flow),
        no_unwind
    ))]
    fn child(&self, parent: Self::Id, child: Self::Id) -> (Option<Self::Id>, bool);

}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires is_intrinsic(access, slot), ready_inputs(access, slot), !(access.topology().intrinsic_flow)(slot),
        child_bound(access, slot, cursor@),
        child == (access.topology().children)(slot.node)[cursor@ as int].node,
        kind is Min || kind is Max,
    ensures result == pre_grow_bound(access, target(child, slot.vertical, kind)),
    no_unwind
))]
fn intrinsic_bound<A: IntrinsicRows>(access: &A, slot: Request<A::Id>, child: A::Id, kind: Kind,
    #[cfg(verus_keep_ghost)] cursor: Ghost<nat>,
) -> Option<f32> {
    let input = target(child, slot.vertical, kind);
    let Some(size) = access.declaration(input) else { return None; };
    if size.is_flex() { return None; }
    #[cfg(verus_keep_ghost)]
    proof! { child_value_ready(access, slot, input, cursor@); }
    Some(read(access, input))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires is_intrinsic(access, slot), ready_inputs(access, slot), !(access.topology().intrinsic_flow)(slot),
        child_bound(access, slot, cursor@),
        child == (access.topology().children)(slot.node)[cursor@ as int].node,
    ensures value == pre_grow_extent(access, target(child, slot.vertical, Kind::Regular)),
    no_unwind
))]
fn pre_grow<A: IntrinsicRows>(access: &A, slot: Request<A::Id>, child: A::Id,
    #[cfg(verus_keep_ghost)] cursor: Ghost<nat>,
) -> f32 {
    let regular = target(child, slot.vertical, Kind::Regular);
    let size = match access.declaration(regular) {
        Some(Size::Fill | Size::Frac(_)) => 0.0,
        _ => {
            #[cfg(verus_keep_ghost)]
            proof! { child_value_ready(access, slot, regular, cursor@); }
            read(access, regular)
        }
    };
    let min = intrinsic_bound(access, slot, child, Kind::Min, #[cfg(verus_keep_ghost)] cursor);
    let max = intrinsic_bound(access, slot, child, Kind::Max, #[cfg(verus_keep_ghost)] cursor);
    clamp::<A::Float>(size, min, max)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
enum Extent {
    Largest { free: bool },
    Grid { tracks: f32, spacing: f32 },
    Stack { estimate: f32 },
}

#[cfg(verus_keep_ghost)]
verus! {
spec fn stack_estimate(measure: Extent) -> f32 {
    match measure { Extent::Stack { estimate } => estimate, _ => 0.0f32 }
}

spec fn free_scan(measure: Extent) -> bool {
    match measure { Extent::Largest { free } => free, _ => false }
}

spec fn grid_scan(measure: Extent) -> (f32, f32) {
    match measure { Extent::Grid { tracks, spacing } => (tracks, spacing), _ => (0.0f32, 0.0f32) }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == with_stack_margin::<F>(size, margin), no_unwind))]
fn add_margin<F: FrameFloat>(size: f32, margin: f32) -> f32 {
    if F::is_zero(margin) { size } else { F::add(size, margin) }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == next_bound::<F>(frac, maximum, wanted, prior), no_unwind))]
fn next_fraction_cap<F: FrameFloat>(frac: f32, maximum: Option<f32>, wanted: f32, prior: Option<f32>) -> Option<f32> {
    let Some(cap) = maximum else { return prior; };
    if !F::less_than(0.0, frac) || !F::less_than(wanted, cap) { return prior; }
    let x = F::divide(cap, frac);
    let probe = if F::less_than(F::multiply(x, frac), cap) {
        F::from_word(F::bits(x).saturating_add(1))
    } else { x };
    if !F::finite(probe) { return prior; }
    Some(match prior { Some(prev) => F::min(prev, probe), None => probe })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires is_intrinsic(access, slot), ready_inputs(access, slot), !(access.topology().intrinsic_flow)(slot),
        child_bound(access, slot, cursor@),
        child == (access.topology().children)(slot.node)[cursor@ as int].node,
    ensures next == stack_row_progress::<A::Float>(stack_rows(access, slot)[cursor@ as int].unwrap(), estimate, current),
    no_unwind
))]
fn scan_stack_child<A: IntrinsicRows>(
    access: &A, slot: Request<A::Id>, child: A::Id, estimate: f32, current: (f32, f32, bool, Option<f32>),
    #[cfg(verus_keep_ghost)] cursor: Ghost<nat>,
) -> (f32, f32, bool, Option<f32>) {
    let (extent, free_frac, has_frac, next_cap) = current;
    let declaration = access.declaration(target(child, slot.vertical, Kind::Regular));
    let [start, end] = A::margins(access.params(child), slot.axis());
    let margin = A::Float::add(start, end);
    #[cfg(verus_keep_ghost)]
    proof! { stack_row_at(access, slot, cursor@); }
    if let Some(Size::Frac(frac)) = declaration {
        let extent = A::Float::add(extent, margin);
        let wanted = A::Float::multiply(estimate, frac);
        let minimum = intrinsic_bound(access, slot, child, Kind::Min, #[cfg(verus_keep_ghost)] cursor);
        let maximum = intrinsic_bound(access, slot, child, Kind::Max, #[cfg(verus_keep_ghost)] cursor);
        let allowed = clamp::<A::Float>(wanted, minimum, maximum);
        let next_cap = next_fraction_cap::<A::Float>(frac, maximum, wanted, next_cap);
        if A::Float::equal_numbers(allowed, wanted) && !matches!(maximum, Some(cap) if A::Float::equal_numbers(wanted, cap)) {
            (extent, A::Float::add(free_frac, frac), true, next_cap)
        } else { (A::Float::add(extent, allowed), free_frac, true, next_cap) }
    } else {
        let size = pre_grow(access, slot, child, #[cfg(verus_keep_ghost)] cursor);
        let footprint = add_margin::<A::Float>(size, margin);
        #[cfg(verus_keep_ghost)]
        proof! { assert(footprint == stack_row_extent::<A::Float>(stack_rows(access, slot)[cursor@ as int].unwrap())); }
        (A::Float::add(extent, footprint), free_frac, has_frac, next_cap)
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires is_intrinsic(access, slot), ready_inputs(access, slot), !(access.topology().intrinsic_flow)(slot),
        child_bound(access, slot, cursor@),
        child == (access.topology().children)(slot.node)[cursor@ as int].node,
    ensures next == A::Float::maximum(extent, largest_row_extent::<A::Float>(stack_rows(access, slot)[cursor@ as int].unwrap(), free)),
    no_unwind
))]
fn scan_largest_child<A: IntrinsicRows>(
    access: &A, slot: Request<A::Id>, child: A::Id, free: bool, extent: f32,
    #[cfg(verus_keep_ghost)] cursor: Ghost<nat>,
) -> f32 {
    let size = pre_grow(access, slot, child, #[cfg(verus_keep_ghost)] cursor);
    let size = if free { size } else {
        let [start, end] = A::margins(access.params(child), slot.axis());
        add_margin::<A::Float>(size, A::Float::add(start, end))
    };
    #[cfg(verus_keep_ghost)]
    proof! { stack_row_at(access, slot, cursor@); }
    A::Float::max(extent, size)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires is_intrinsic(access, slot), ready_inputs(access, slot), !(access.topology().intrinsic_flow)(slot),
        child_bound(access, slot, cursor@),
        child == (access.topology().children)(slot.node)[cursor@ as int].node,
    ensures next == A::Float::maximum(extent,
        grid_cell_extent::<A::Float>(stack_rows(access, slot)[cursor@ as int].unwrap(), tracks, spacing)),
    no_unwind
))]
fn scan_grid_child<A: IntrinsicRows>(
    access: &A, slot: Request<A::Id>, child: A::Id, tracks: f32, spacing: f32, extent: f32,
    #[cfg(verus_keep_ghost)] cursor: Ghost<nat>,
) -> f32 {
    let axis = slot.axis();
    let span = *access.params(child).grid_span.component(axis);
    let span = A::Float::from_count(if span == 0 { 1 } else { span as u32 });
    let span = A::Float::min(span, A::Float::max(tracks, 1.0));
    let [start, end] = A::margins(access.params(child), axis);
    let size = pre_grow(access, slot, child, #[cfg(verus_keep_ghost)] cursor);
    let footprint = add_margin::<A::Float>(size, A::Float::add(start, end));
    let gaps = A::Float::multiply(A::Float::subtract(span, 1.0), spacing);
    let extent = A::Float::max(extent, A::Float::divide(A::Float::subtract(footprint, gaps), span));
    #[cfg(verus_keep_ghost)]
    proof! { stack_row_at(access, slot, cursor@); }
    extent
}

#[cfg_attr(debug_assertions, inline)]
#[cfg_attr(not(debug_assertions), inline(always))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(scan =>
    requires is_intrinsic(access, slot), ready_inputs(access, slot), !(access.topology().intrinsic_flow)(slot),
    ensures no_in_flow_children(access, slot.node) ==> scan == (0.0f32, 0.0f32, false, None),
        measure is Stack ==> {
            let rows = stack_rows(access, slot);
            scan == stack_prefix::<A::Float>(rows, stack_estimate(measure), rows.len())
        },
        measure is Largest ==> {
            let rows = stack_rows(access, slot);
            scan == (largest_prefix::<A::Float>(rows, free_scan(measure), rows.len()), 0.0f32, false, None)
        },
        measure is Grid ==> {
            let rows = stack_rows(access, slot);
            let (tracks, spacing) = grid_scan(measure);
            scan == (grid_prefix::<A::Float>(rows, tracks, spacing, rows.len()), 0.0f32, false, None)
        },
    no_unwind
))]
fn scan_extent<A: IntrinsicRows>(access: &A, slot: Request<A::Id>, measure: Extent) -> (f32, f32, bool, Option<f32>) {
    let mut next = access.first_child(slot.node);
    let mut extent = 0.0f32;
    let mut free_frac = 0.0f32;
    let mut has_frac = false;
    let mut next_cap = None;
    #[cfg(verus_keep_ghost)]
    let mut cursor = start_children();
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(stack_prefix);
        reveal(largest_prefix);
        reveal(grid_prefix);
        stack_rows_count(access, slot);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant is_intrinsic(access, slot), ready_inputs(access, slot),
            !(access.topology().intrinsic_flow)(slot),
            cursor@ <= (access.topology().children)(slot.node).len(),
            next == sizing_requests::child_at((access.topology().children)(slot.node), cursor@),
            no_in_flow_children(access, slot.node) ==> extent == 0.0f32 && free_frac == 0.0f32 && !has_frac && next_cap.is_none(),
            stack_rows(access, slot).len() == (access.topology().children)(slot.node).len(),
            measure is Stack ==> (extent, free_frac, has_frac, next_cap)
                == stack_prefix::<A::Float>(stack_rows(access, slot), stack_estimate(measure), cursor@),
            measure is Largest ==> (extent, free_frac, has_frac, next_cap)
                == (largest_prefix::<A::Float>(stack_rows(access, slot), free_scan(measure), cursor@), 0.0f32, false, None),
            measure is Grid ==> {
                let (tracks, spacing) = grid_scan(measure);
                (extent, free_frac, has_frac, next_cap)
                    == (grid_prefix::<A::Float>(stack_rows(access, slot), tracks, spacing, cursor@), 0.0f32, false, None)
            },
        ensures cursor@ == (access.topology().children)(slot.node).len(),
        decreases (access.topology().children)(slot.node).len() - cursor@,
    ))]
    while let Some(child) = next {
        let (following, in_flow) = access.child(slot.node, child);
        next = following;
        #[cfg(verus_keep_ghost)]
        proof! {
            let rows = (access.topology().children)(slot.node);
            assert(cursor@ < rows.len());
            assert(rows[cursor@ as int].node == child && rows[cursor@ as int].in_flow == in_flow);
        }
        if in_flow {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(cursor@ < (access.topology().children)(slot.node).len());
                assert((access.topology().children)(slot.node)[cursor@ as int].in_flow);
            }

            match measure {
                Extent::Largest { free } => {
                    extent = scan_largest_child(access, slot, child, free, extent, #[cfg(verus_keep_ghost)] cursor);
                }
                Extent::Grid { tracks, spacing } => {
                    extent = scan_grid_child(access, slot, child, tracks, spacing, extent, #[cfg(verus_keep_ghost)] cursor);
                }
                Extent::Stack { estimate } => {
                    let progress = scan_stack_child(
                        access, slot, child, estimate, (extent, free_frac, has_frac, next_cap),
                        #[cfg(verus_keep_ghost)] cursor,
                    );
                    extent = progress.0;
                    free_frac = progress.1;
                    has_frac = progress.2;
                    next_cap = progress.3;
                }
            }
        }
        #[cfg(verus_keep_ghost)]
        {
            proof! {
                if measure is Stack {
                    let ordered = stack_rows(access, slot);
                    stack_row_at(access, slot, cursor@);
                    assert(ordered[cursor@ as int].is_some() == in_flow);
                    stack_step::<A::Float>(ordered, stack_estimate(measure), cursor@);
                    assert((extent, free_frac, has_frac, next_cap) == stack_prefix::<A::Float>(ordered, stack_estimate(measure), cursor@ + 1));
                }
                if measure is Largest {
                    let ordered = stack_rows(access, slot);
                    stack_row_at(access, slot, cursor@);
                    assert(ordered[cursor@ as int].is_some() == in_flow);
                    largest_step::<A::Float>(ordered, free_scan(measure), cursor@);
                    assert(extent == largest_prefix::<A::Float>(ordered, free_scan(measure), cursor@ + 1));
                }
                if measure is Grid {
                    let ordered = stack_rows(access, slot);
                    let (tracks, spacing) = grid_scan(measure);
                    stack_row_at(access, slot, cursor@);
                    assert(ordered[cursor@ as int].is_some() == in_flow);
                    grid_step::<A::Float>(ordered, tracks, spacing, cursor@);
                    assert(extent == grid_prefix::<A::Float>(ordered, tracks, spacing, cursor@ + 1));
                }
            }
            cursor = step_child(cursor);
        }
    }
    (extent, free_frac, has_frac, next_cap)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const MAX_FIT_STACK_STEPS: u64 = 64;
#[cfg_attr(verus_keep_ghost, verus_verify)]
const FIT_STACK_EPSILON: f32 = 1e-6;

#[cfg(verus_keep_ghost)]
verus! {

spec fn fit_iteration<F: FrameFloat>(
    scan: (f32, f32, bool, Option<f32>), estimate: f32, overflow: bool,
) -> ((f32, bool), bool) {
    let (fixed, free_frac, has_frac, next_cap) = scan;
    if !has_frac { ((fixed, false), true) }
    else if F::number_eq(free_frac, 1.0f32) && F::number_eq(fixed, 0.0f32) { ((estimate, false), true) }
    else {
        let within = F::at_most(free_frac, 1.0f32) && !F::number_eq(free_frac, 1.0f32);
        let next = if within { F::quotient(fixed, F::difference(1.0f32, free_frac)) } else { fixed };
        let demand = F::sum(fixed, F::product(estimate, free_frac));
        let positive = F::at_most(0.0f32, fixed) && !F::number_eq(0.0f32, fixed);
        let growing = F::at_most(estimate, demand) && !F::number_eq(estimate, demand);
        if (positive || growing) && next_cap.is_some() && (!within || !F::finite_word(next)) {
            let probe = if F::finite_word(demand) { F::maximum(next_cap.unwrap(), demand) } else { next_cap.unwrap() };
            ((probe, overflow), false)
        } else {
            let settled = F::at_most(F::magnitude(F::difference(next, estimate)),
                F::product(FIT_STACK_EPSILON, F::maximum(F::magnitude(next), 1.0f32)));
            ((next, overflow || !within), settled)
        }
    }
}

#[verifier::opaque]
pub(crate) closed spec fn fit_stack_recipe<F: FrameFloat>(
    rows: Seq<Option<StackRow>>, estimate: f32, overflow: bool, remaining: nat,
) -> (f32, bool)
    decreases remaining,
{
    if remaining == 0 {
        (estimate, overflow)
    } else {
        let scan = stack_prefix::<F>(rows, estimate, rows.len());
        let (next, settled) = fit_iteration::<F>(scan, estimate, overflow);
        if settled { next }
        else { fit_stack_recipe::<F>(rows, next.0, next.1, (remaining - 1) as nat) }
    }
}

proof fn fit_done<F: FrameFloat>(rows: Seq<Option<StackRow>>, estimate: f32, overflow: bool)
    ensures fit_stack_recipe::<F>(rows, estimate, overflow, 0) == (estimate, overflow),
{ reveal(fit_stack_recipe); }

proof fn fit_next<F: FrameFloat>(
    rows: Seq<Option<StackRow>>, estimate: f32, overflow: bool, remaining: nat, scan: (f32, f32, bool, Option<f32>),
)
    requires remaining > 0, scan == stack_prefix::<F>(rows, estimate, rows.len()),
    ensures fit_stack_recipe::<F>(rows, estimate, overflow, remaining) == {
        let (next, settled) = fit_iteration::<F>(scan, estimate, overflow);
        if settled { next }
        else { fit_stack_recipe::<F>(rows, next.0, next.1, (remaining - 1) as nat) }
    },
{ reveal(fit_stack_recipe); }

fn initial_stack_fit<A: FinishModel>(access: &A, slot: Request<A::Id>) -> (program: Ghost<(f32, bool)>)
    ensures program@ == fit_stack_recipe::<A::Float>(stack_rows(access, slot), 0.0f32, false, (MAX_FIT_STACK_STEPS + access.finish_child_count(slot.node)) as nat),
    no_unwind
{
    Ghost(fit_stack_recipe::<A::Float>(stack_rows(access, slot), 0.0f32, false, (MAX_FIT_STACK_STEPS + access.finish_child_count(slot.node)) as nat))
}

}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires is_intrinsic(old(access), slot), ready_inputs(old(access), slot), !(old(access).topology().intrinsic_flow)(slot),
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
        measurement_inputs_stable(old(access), final(access)),
        final(access).finish_child_count(slot.node) == old(access).finish_child_count(slot.node),
        final(access).measurement_requests() == old(access).measurement_requests(),
        final(access).wrap_effects() == old(access).wrap_effects(),
        ({
            let result = fit_stack_recipe::<A::Float>(stack_rows(old(access), slot), 0.0f32, false,
                (MAX_FIT_STACK_STEPS + old(access).finish_child_count(slot.node)) as nat);
            &&& value == result.0
            &&& final(access).finish_effects() == if result.1 {
                old(access).finish_effects().push(FinishEffect::Warning(slot, Warning::ImpossibleFracChildren))
            } else { old(access).finish_effects() }
        }),
    no_unwind
))]
fn fit_stack<A: IntrinsicRows>(access: &mut A, slot: Request<A::Id>) -> f32 {
    let mut estimate = 0.0f32;
    let mut overflow = false;
    // A saturated child can introduce one additional breakpoint.
    let step_limit = MAX_FIT_STACK_STEPS + access.placed_child_count(slot.node) as u64;
    let mut step = 0u64;
    #[cfg(verus_keep_ghost)]
    let program = initial_stack_fit(access, slot);
    #[cfg_attr(verus_keep_ghost, verifier::loop_isolation(false))]
    #[cfg_attr(verus_keep_ghost, verifier::allow_complex_invariants)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant_except_break step <= step_limit, access.topology() == old(access).topology(),
            access.ready() == old(access).ready(), is_intrinsic(access, slot),
            ready_inputs(access, slot), !(access.topology().intrinsic_flow)(slot),
            *access == *old(access),
            program@ == fit_stack_recipe::<A::Float>(stack_rows(access, slot), estimate, overflow,
                (step_limit - step) as nat),
        ensures *access == *old(access), program@ == (estimate, overflow),
        decreases step_limit - step,
    ))]
    loop {
        if step == step_limit {
            #[cfg(verus_keep_ghost)]
            proof! { fit_done::<A::Float>(stack_rows(access, slot), estimate, overflow); }
            break;
        }
        let scan = scan_extent(access, slot, Extent::Stack { estimate });
        let (fixed, free_frac, has_frac, next_cap) = scan;
        #[cfg(verus_keep_ghost)]
        proof! {
            fit_next::<A::Float>(stack_rows(access, slot), estimate, overflow, (step_limit - step) as nat, scan);
        }
        if !has_frac { return fixed; }
        // On this interval the children's total is fixed + free_frac * width.
        // A minimum can bring us to a solution where the equation is W = W.
        if A::Float::equal_numbers(free_frac, 1.0) && A::Float::equal_numbers(fixed, 0.0) {
            return estimate;
        }
        let within = A::Float::less_than(free_frac, 1.0);
        let next = if within {
            A::Float::divide(fixed, A::Float::subtract(1.0, free_frac))
        } else { fixed };
        if !within || !A::Float::finite(next) {
            if let Some(cap) = next_cap {
                // The next cap and the space children already demand both bound
                // the next solution from below. Cross several caps at once when
                // possible, including when the uncapped extrapolation overflowed.
                let demand = A::Float::add(fixed, A::Float::multiply(estimate, free_frac));
                if A::Float::less_than(0.0, fixed) || A::Float::less_than(estimate, demand) {
                    estimate = if A::Float::finite(demand) { A::Float::max(cap, demand) } else { cap };
                    step += 1;
                    continue;
                }
            }
        }
        overflow |= !within;
        let settled = A::Float::less_or_equal(
            A::Float::absolute(A::Float::subtract(next, estimate)),
            A::Float::multiply(FIT_STACK_EPSILON, A::Float::max(A::Float::absolute(next), 1.0)),
        );
        estimate = next;
        if settled { break; }
        step += 1;
    }
    if overflow { access.warn(slot, Warning::ImpossibleFracChildren); }
    estimate
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires is_intrinsic(old(access), slot), ready_inputs(old(access), slot),
    ensures final(access).topology() == old(access).topology(), final(access).ready() == old(access).ready(),
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
pub(super) fn fit_content<A: IntrinsicRows>(access: &mut A, slot: Request<A::Id>) -> f32 {
    let layout = access.intrinsic_layout(slot);
    let axis = slot.axis();
    #[cfg(verus_keep_ghost)]
    proof! {
        if intrinsic_tracks_need_other(slot, layout) { intrinsic_constraint_is_ready(access, slot); }
    }
    let (children, gaps) = match layout {
        ChildrenLayout::Grid { columns, spacing_x, spacing_y, main_axis, .. } => {
            let spacing = if slot.vertical { spacing_y } else { spacing_x };
            let (n, cell) = match columns {
                MainAxisCellSize::Width(width) if axis.index() == main_axis.index() => (1.0, width),
                _ => {
                    let tracks = grid_tracks(access, slot);
                    let (cell, _, _, _) = scan_extent(access, slot, Extent::Grid { tracks, spacing });
                    (tracks, cell)
                }
            };
            let occupied = A::Float::multiply(n, cell);
            let gaps = A::Float::multiply(spacing, A::Float::subtract(n, 1.0));
            (A::Float::max(A::Float::add(occupied, gaps), 0.0), 0.0)
        }
        ChildrenLayout::Stack { axis: main, .. } if main.index() == axis.index() =>
            (fit_stack(access, slot), access.stack_gaps(slot.node, axis)),
        ChildrenLayout::Wrap { axis: main, .. } if main.index() == axis.index() =>
            (fit_stack(access, slot), access.stack_gaps(slot.node, axis)),
        ChildrenLayout::Block if slot.vertical => (read_own_flow(access, slot), 0.0),
        ChildrenLayout::Wrap { .. } => (read_own_flow(access, slot), 0.0),
        _ => {
            let (largest, _, _, _) = scan_extent(access, slot, Extent::Largest { free: matches!(layout, ChildrenLayout::Free) });
            (largest, 0.0)
        }
    };
    intrinsic_content(access, slot, children, gaps)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(value =>
    requires is_intrinsic(access, slot), ready_inputs(access, slot), (access.topology().intrinsic_flow)(slot),
    ensures value == intrinsic_flow_word(access, slot),
    no_unwind
))]
fn read_own_flow<A: IntrinsicRows>(access: &A, slot: Request<A::Id>) -> f32 {
    let flow = target(slot.node, slot.vertical, Kind::Flow);
    #[cfg(verus_keep_ghost)]
    proof! {
        let deps = sizing_requests::inputs(access.topology(), slot);
        assert(deps.len() > 0 && deps[0] == flow);
        read_dependency(access, slot, flow);
    }
    read(access, flow)
}
