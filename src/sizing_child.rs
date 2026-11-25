//! Shared ordered reads for Wrap's pre-growth extents and the Fill budget.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use super::sizing_requests;
#[cfg(not(verus_keep_ghost))]
use crate::solve::sizing_requests;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as slots, fill::kernel as fill, stack_share::kernel as collection};
#[cfg(not(verus_keep_ghost))]
use crate::solve::{cycle_rules as slots, fill_compaction as fill, fill_collection as collection};
use crate::declarations::Size;
use fill::{FillChild, FillNumber, FloatOps, Terms};
use sizing_requests::{Declarations, target};
use slots::{Kind, N_SLOTS};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait ValueModel: Declarations {
    spec fn child_words(&self, child: Self::Id) -> [f32; N_SLOTS];
}

pub(crate) struct ChildInputs {
    pub layout: crate::declarations::LayoutParams,
    pub values: [f32; N_SLOTS],
    pub block_item: bool,
    pub block_parent_auto_height: bool,
}

spec fn read_inputs<A: ValueModel + ?Sized>(tree: &A, node: A::Id) -> ChildInputs {
    ChildInputs { layout: tree.layout(node), values: tree.child_words(node),
        block_item: tree.block_item(node), block_parent_auto_height: tree.auto_block_parent(node) }
}

spec fn declaration(inputs: ChildInputs, vertical: bool, kind: Kind) -> Option<Size> {
    sizing_requests::resolved_size(inputs.layout, vertical, kind,
        inputs.block_item, inputs.block_parent_auto_height)
}

pub(crate) open spec fn input_word(inputs: ChildInputs, vertical: bool, kind: Kind) -> f32 {
    inputs.values[slots::slot_index(vertical as usize, kind) as int]
}

spec fn word<A: ValueModel + ?Sized>(tree: &A, node: A::Id, vertical: bool, kind: Kind) -> f32 {
    input_word(read_inputs(tree, node), vertical, kind)
}

spec fn excluded(size: Option<Size>, fractions: bool) -> bool {
    size is Some && (size.unwrap() is Fill || fractions && size.unwrap() is Frac)
}

spec fn bound_input(inputs: ChildInputs, vertical: bool, kind: Kind, fractions: bool) -> Option<f32> {
    if declaration(inputs, vertical, kind).is_some() && !excluded(declaration(inputs, vertical, kind), fractions) {
        Some(input_word(inputs, vertical, kind))
    } else {
        None
    }
}

spec fn bound<A: ValueModel + ?Sized>(
    tree: &A, node: A::Id, vertical: bool, kind: Kind, fractions: bool,
) -> Option<f32> {
    bound_input(read_inputs(tree, node), vertical, kind, fractions)
}

pub(crate) closed spec fn inputs_use_fill(inputs: ChildInputs, vertical: bool) -> bool {
    excluded(declaration(inputs, vertical, Kind::Regular), false) ||
    excluded(declaration(inputs, vertical, Kind::Min), false) ||
    excluded(declaration(inputs, vertical, Kind::Max), false)
}

pub(crate) closed spec fn has_fill<A: ValueModel + ?Sized>(tree: &A, node: A::Id, vertical: bool) -> bool {
    inputs_use_fill(read_inputs(tree, node), vertical)
}

pub(crate) closed spec fn inputs_before_growth<F: fill::FloatModel>(
    inputs: ChildInputs, vertical: bool, fractions: bool,
) -> f32 {
    let size = if excluded(declaration(inputs, vertical, Kind::Regular), fractions) {
        0.0
    } else {
        input_word(inputs, vertical, Kind::Regular)
    };
    let capped = match bound_input(inputs, vertical, Kind::Max, fractions) {
        Some(max) => F::minimum(size, max),
        None => size,
    };
    match bound_input(inputs, vertical, Kind::Min, fractions) {
        Some(min) => F::maximum(capped, min),
        None => capped,
    }
}

pub(crate) closed spec fn before_growth<A: ValueModel + ?Sized, F: fill::FloatModel>(
    tree: &A, node: A::Id, vertical: bool, fractions: bool,
) -> f32 {
    inputs_before_growth::<F>(read_inputs(tree, node), vertical, fractions)
}

pub(crate) closed spec fn inputs_fill_terms<F: fill::FloatModel>(
    inputs: ChildInputs, vertical: bool, weight: f32,
) -> Terms<FillNumber<F>> {
    if inputs_use_fill(inputs, vertical) {
        let content = if excluded(declaration(inputs, vertical, Kind::Regular), false) {
            None
        } else {
            Some(input_word(inputs, vertical, Kind::Regular))
        };
        let min = bound_input(inputs, vertical, Kind::Min, false);
        let max = bound_input(inputs, vertical, Kind::Max, false);
        if content.is_some() || min.is_some() || max.is_some() {
            let capped = content.is_some() && excluded(declaration(inputs, vertical, Kind::Max), false);
            Terms::Constrained(FillNumber::new(weight), FillChild::bounds::<F>(content, min, max, capped, weight))
        } else {
            Terms::Unconstrained(FillNumber::new(weight))
        }
    } else {
        Terms::Fixed(FillNumber::new(input_word(inputs, vertical, Kind::Final)))
    }
}

pub(crate) closed spec fn planned_terms<A: ValueModel + ?Sized, F: fill::FloatModel>(
    tree: &A, node: A::Id, vertical: bool, weight: f32,
) -> Terms<FillNumber<F>> {
    inputs_fill_terms::<F>(read_inputs(tree, node), vertical, weight)
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait ValueModel: Declarations {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Values: ValueModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(words =>
        ensures *words == self.child_words(node),
        no_unwind
    ))]
    fn words(&self, node: Self::Id) -> &[f32; N_SLOTS];
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns word(tree, node, vertical, kind), no_unwind))]
fn read<A: Values + ?Sized>(tree: &A, node: A::Id, vertical: bool, kind: Kind) -> f32 {
    slots::read_slot(tree.words(node), vertical as usize, kind)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns excluded(size, fractions), no_unwind))]
fn skips(size: Option<Size>, fractions: bool) -> bool {
    if let Some(size) = size {
        size.is_fill() || (fractions && matches!(size, Size::Frac(_)))
    } else {
        false
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns bound(tree, node, vertical, kind, fractions), no_unwind))]
fn read_bound<A: Values + ?Sized>(tree: &A, node: A::Id, vertical: bool, kind: Kind, fractions: bool) -> Option<f32> {
    let declared = sizing_requests::read_declaration(tree, target(node, vertical, kind));
    if declared.is_some() && !skips(declared, fractions) {
        Some(read(tree, node, vertical, kind))
    } else {
        None
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns has_fill(tree, node, vertical), no_unwind))]
pub(crate) fn any_fill<A: ValueModel + ?Sized>(tree: &A, node: A::Id, vertical: bool) -> bool {
    skips(sizing_requests::read_declaration(tree, target(node, vertical, Kind::Regular)), false) ||
    skips(sizing_requests::read_declaration(tree, target(node, vertical, Kind::Min)), false) ||
    skips(sizing_requests::read_declaration(tree, target(node, vertical, Kind::Max)), false)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns before_growth::<A, F>(tree, node, vertical, fractions), no_unwind))]
pub(crate) fn pre_growth<A: Values + ?Sized, F: FloatOps>(tree: &A, node: A::Id, vertical: bool, fractions: bool) -> f32 {
    let declared = sizing_requests::read_declaration(tree, target(node, vertical, Kind::Regular));
    let size = if skips(declared, fractions) { 0.0 } else { read(tree, node, vertical, Kind::Regular) };
    let min = read_bound(tree, node, vertical, Kind::Min, fractions);
    let max = read_bound(tree, node, vertical, Kind::Max, fractions);
    let size = match max { Some(max) => F::min(size, max), None => size };
    match min { Some(min) => F::max(size, min), None => size }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns planned_terms::<A, F>(tree, node, vertical, weight), no_unwind))]
pub(crate) fn fill_terms<A: Values + ?Sized, F: FloatOps>(tree: &A, node: A::Id, vertical: bool, weight: f32) -> Terms<FillNumber<F>> {
    if any_fill(tree, node, vertical) {
        let declared = sizing_requests::read_declaration(tree, target(node, vertical, Kind::Regular));
        let content = if skips(declared, false) { None } else { Some(read(tree, node, vertical, Kind::Regular)) };
        let min = read_bound(tree, node, vertical, Kind::Min, false);
        let max = read_bound(tree, node, vertical, Kind::Max, false);
        if collection::has_constraint(content, min, max) {
            let capped = content.is_some() && skips(sizing_requests::read_declaration(tree, target(node, vertical, Kind::Max)), false);
            Terms::Constrained(FillNumber::new(weight), FillChild::new_with::<F>(content, min, max, capped, weight))
        } else {
            Terms::Unconstrained(FillNumber::new(weight))
        }
    } else {
        Terms::Fixed(FillNumber::new(read(tree, node, vertical, Kind::Final)))
    }
}
