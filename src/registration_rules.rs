// Direct numeric inputs read by an acyclic sizing slot, before slot-to-slot propagation.
#![allow(unexpected_cfgs)]
use crate::declarations::{Axis, ChildrenLayout, LayoutParams, MainAxisCellSize, Size, X, Y};
use crate::prepare_frame::FrameFloat;
use crate::node_flags::slot_index;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::{self, Kind};
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::Kind;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns same_sizing_layout(old, current), no_unwind))]
pub(crate) fn same_sizing_layout(old: ChildrenLayout, current: ChildrenLayout) -> bool {
    match (old, current) {
        (ChildrenLayout::Free, ChildrenLayout::Free) | (ChildrenLayout::Block, ChildrenLayout::Block) => true,
        (ChildrenLayout::Stack { axis: left, .. }, ChildrenLayout::Stack { axis: right, .. })
        | (ChildrenLayout::Wrap { axis: left, .. }, ChildrenLayout::Wrap { axis: right, .. }) => left.index() == right.index(),
        (ChildrenLayout::Grid { columns: left, main_axis: axis, backfill, .. },
            ChildrenLayout::Grid { columns: right, main_axis: next_axis, backfill: next_backfill, .. }) => {
            axis.index() == next_axis.index() && backfill == next_backfill && match (left, right) {
                (MainAxisCellSize::Count(a), MainAxisCellSize::Count(b)) => a == b,
                (MainAxisCellSize::Width(_), MainAxisCellSize::Width(_)) => true,
                _ => false,
            }
        },
        _ => false,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns declaration_kind(size), no_unwind))]
pub(crate) fn declaration_kind(size: Option<Size>) -> u8 {
    match size {
        None => 0,
        Some(Size::Fill) => 1,
        Some(Size::FitContent) => 2,
        Some(Size::Auto) => 3,
        Some(Size::Pixels(_)) => 4,
        Some(Size::Frac(_)) => 5,
        Some(Size::AspectRatio(_)) => 6,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns same_axis_declarations(old, current, axis), no_unwind))]
pub(crate) fn same_axis_declarations(old: &LayoutParams, current: &LayoutParams, axis: Axis) -> bool {
    let [regular, minimum, maximum] = match axis {
        X => [(Some(old.size.x), Some(current.size.x)), (old.min_size.x, current.min_size.x),
            (old.max_size.x, current.max_size.x)],
        Y => [(Some(old.size.y), Some(current.size.y)), (old.min_size.y, current.min_size.y),
            (old.max_size.y, current.max_size.y)],
    };
    declaration_kind(regular.0) == declaration_kind(regular.1)
        && declaration_kind(minimum.0) == declaration_kind(minimum.1)
        && declaration_kind(maximum.0) == declaration_kind(maximum.1)
}

/// Report edits that can change dependency edges or a Grid assignment's item order and spans.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns sizing_structure_changed(old, current), no_unwind))]
pub(crate) fn sizing_structure_changed(old: &LayoutParams, current: &LayoutParams) -> bool {
    old.disabled != current.disabled
        || old.free_placement != current.free_placement
        || old.grid_span.x != current.grid_span.x || old.grid_span.y != current.grid_span.y
        || old.text as u8 != current.text as u8
        || old.content_measure as u8 != current.content_measure as u8
        || old.image.is_some() != current.image.is_some()
        || !same_sizing_layout(old.children_layout, current.children_layout)
        || !same_axis_declarations(old, current, X)
        || !same_axis_declarations(old, current, Y)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, Default)]
pub struct AxisEdits {
    pub inner: bool,
    pub other_inner: bool,
    pub content: bool,
    pub margin: bool,
    pub weight: bool,
    pub regular_fraction: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub struct Context {
    pub in_flow: bool,
    pub placed_parent: bool,
    pub parent_stack_axis: bool,
    pub stack_axis: bool,
    pub width_grid: bool,
    pub grid_main: bool,
    pub wraps_text: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, Default)]
pub struct Seeds {
    pub own_intrinsic: bool,
    pub own_fill: bool,
    pub own_final: bool,
    pub own_share: bool,
    pub parent_intrinsic: bool,
    pub parent_share: bool,
    pub child_available: bool,
}

impl AxisEdits {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.seeds(c), no_unwind))]
    pub fn seeds(self, c: Context) -> Seeds {
        let child_available = self.inner || (c.width_grid && self.other_inner);
        let margin = self.margin && c.in_flow && c.placed_parent;
        let weight = self.weight && c.in_flow && c.parent_stack_axis;
        Seeds {
            own_intrinsic: self.content || child_available || (self.other_inner && c.wraps_text),
            own_fill: margin || weight,
            own_final: c.grid_main && (self.inner || self.other_inner),
            own_share: c.stack_axis && self.inner,
            parent_intrinsic: margin || (c.in_flow && self.regular_fraction),
            parent_share: c.parent_stack_axis && (margin || weight),
            child_available,
        }
    }
}

/// Host callbacks see both pixel maxima and the padding used to compute them.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns content_input_changed(image, custom, padding, maximum), no_unwind))]
pub fn content_input_changed(image: bool, custom: bool, padding: bool, maximum: bool) -> bool {
    image || (custom && (padding || maximum))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires index < 8, returns declaration_changed(mask, index), no_unwind
))]
pub fn declaration_changed(mask: u8, index: usize) -> bool {
    mask & (1u8 << index) != 0
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires index < 8,
    ensures forall|i:usize| i < 8 ==> #[trigger] declaration_changed(result, i)
        == (declaration_changed(mask, i) || changed && i == index),
    no_unwind
))]
pub fn register_declaration(mask: u8, index: usize, changed: bool) -> u8 {
    let result = if changed { mask | (1u8 << index) } else { mask };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:usize| i < 8 implies #[trigger] declaration_changed(result, i)
            == (declaration_changed(mask, i) || changed && i == index) by {
            assert(((mask | (1u8 << index)) & (1u8 << i) != 0)
                == (mask & (1u8 << i) != 0 || i == index)) by(bit_vector)
                requires index < 8, i < 8;
        }
    }
    result
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn declaration_input<F: FrameFloat>(size: Option<Size>) -> (u8, u32) {
    match size {
        None => (0, 0),
        Some(Size::Fill) => (1, 0),
        Some(Size::FitContent) => (2, 0),
        Some(Size::Auto) => (3, 0),
        Some(Size::Pixels(value)) => (4, F::word(value)),
        Some(Size::Frac(value)) => (5, F::word(value)),
        Some(Size::AspectRatio(value)) => (6, F::word(value)),
    }
}

pub(crate) open spec fn same_size_words<F: FrameFloat>(a: Option<Size>, b: Option<Size>) -> bool {
    declaration_input::<F>(a) == declaration_input::<F>(b)
}

pub(crate) open spec fn raw_size(params: LayoutParams, axis: Axis, kind: Kind) -> Option<Size> {
    match kind {
        Kind::Regular => Some(if axis is X { params.size.x } else { params.size.y }),
        Kind::Min => if axis is X { params.min_size.x } else { params.min_size.y },
        Kind::Max => if axis is X { params.max_size.x } else { params.max_size.y },
        _ => None,
    }
}

pub(crate) open spec fn changed_on_axis<F: FrameFloat>(
    old: LayoutParams, current: LayoutParams, axis: Axis, index: usize,
) -> bool {
    ||| index == kernel::slot_index(axis.index(), Kind::Regular)
        && !same_size_words::<F>(raw_size(old, axis, Kind::Regular), raw_size(current, axis, Kind::Regular))
    ||| index == kernel::slot_index(axis.index(), Kind::Min)
        && !same_size_words::<F>(raw_size(old, axis, Kind::Min), raw_size(current, axis, Kind::Min))
    ||| index == kernel::slot_index(axis.index(), Kind::Max)
        && !same_size_words::<F>(raw_size(old, axis, Kind::Max), raw_size(current, axis, Kind::Max))
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(word => ensures word == declaration_input::<F>(size), no_unwind))]
fn encoded_declaration<F: FrameFloat>(size: Option<Size>) -> (u8, u32) {
    match size {
        None => (0, 0),
        Some(Size::Fill) => (1, 0),
        Some(Size::FitContent) => (2, 0),
        Some(Size::Auto) => (3, 0),
        Some(Size::Pixels(value)) => (4, F::bits(value)),
        Some(Size::Frac(value)) => (5, F::bits(value)),
        Some(Size::AspectRatio(value)) => (6, F::bits(value)),
    }
}

/// Compare declaration representations, including the sign of zero.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == same_size_words::<F>(a, b), no_unwind))]
pub(crate) fn same_size<F: FrameFloat>(a: Option<Size>, b: Option<Size>) -> bool {
    let (left_kind, left_value) = encoded_declaration::<F>(a);
    let (right_kind, right_value) = encoded_declaration::<F>(b);
    left_kind == right_kind && left_value == right_value
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(mask =>
    ensures forall |index: usize| index < 8 ==> #[trigger] declaration_changed(mask, index)
            == (declaration_changed(previous, index) || changed_on_axis::<F>(*old, *current, axis, index)),
    no_unwind
))]
fn register_axis<F: FrameFloat>(previous: u8, old: &LayoutParams, current: &LayoutParams, axis: Axis) -> u8 {
    let regular = !same_size::<F>(Some(*old.size.component(axis)), Some(*current.size.component(axis)));
    let minimum = !same_size::<F>(*old.min_size.component(axis), *current.min_size.component(axis));
    let maximum = !same_size::<F>(*old.max_size.component(axis), *current.max_size.component(axis));
    let regular_index = slot_index(axis, Kind::Regular);
    let min_index = slot_index(axis, Kind::Min);
    let max_index = slot_index(axis, Kind::Max);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(regular_index < 8 && min_index < 8 && max_index < 8);
    }
    let mask = register_declaration(previous, regular_index, regular);
    let mask = register_declaration(mask, min_index, minimum);
    register_declaration(mask, max_index, maximum)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(mask =>
    ensures forall |index: usize| index < 8 ==> #[trigger] declaration_changed(mask, index)
            == (changed_on_axis::<F>(*old, *current, X, index) || changed_on_axis::<F>(*old, *current, Y, index)),
    no_unwind
))]
pub(crate) fn size_declaration_mask<F: FrameFloat>(old: &LayoutParams, current: &LayoutParams) -> u8 {
    let horizontal = register_axis::<F>(0u8, old, current, X);
    let mask = register_axis::<F>(horizontal, old, current, Y);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |index: usize| index < 8 implies #[trigger] declaration_changed(mask, index)
            == (changed_on_axis::<F>(*old, *current, X, index) || changed_on_axis::<F>(*old, *current, Y, index)) by {
            assert((0u8 & (1u8 << index)) == 0u8) by(bit_vector) requires index < 8;
            assert(!declaration_changed(0, index));
            assert(declaration_changed(horizontal, index) == changed_on_axis::<F>(*old, *current, X, index));
        }
    }
    mask
}

/// A sizing edit either reaches the queue or a solve that already covers it.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Intake { Pending, Cycle, Region, Flow, Budget, Queue }

/// Compare the sum without overflowing on the host's index width.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(exhausted =>
    ensures exhausted == (nodes as int + content >= limit),
    no_unwind
))]
pub fn change_budget_exhausted(nodes: usize, content: usize, limit: usize) -> bool {
    nodes.saturating_add(content) >= limit
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns intake(pending, cyclic, structural, flow, at_limit), no_unwind))]
pub fn intake(pending: bool, cyclic: bool, structural: bool, flow: bool, at_limit: bool) -> Intake {
    if pending { Intake::Pending }
    else if cyclic { Intake::Cycle }
    else if structural { Intake::Region }
    else if flow { Intake::Flow }
    else if at_limit { Intake::Budget }
    else { Intake::Queue }
}
