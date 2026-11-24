//! Preparation of leaf slots that need no further read from the solver.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, LayoutParams, Size, X, Y};
use crate::node_data::NodeLayoutData;
use crate::prepare_frame::FrameFloat;
#[cfg(not(verus_keep_ghost))]
use crate::solve::sizing_finish::inside_margins;
#[cfg(verus_keep_ghost)]
use crate::{prepare_frame::FrameWords, placement::geometry::FloatClassification,
    dependencies::sizing_finish::{inside_margins, margin_pair, subtract_margins}};

#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules;
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::{StructuralChange, flow::wrap_metrics, solve::{dependency_rules::Form, leaf_retention}};
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, dependencies::rules::Form, leaf::kernel as leaf_retention,
    structural::kernel::StructuralChange, wrap_metrics::kernel as wrap_metrics};
use cycle_rules::{Kind, SOLVED};
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::node_flags::{NodeFlags, slot_index};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn on_axis<T>(pair: crate::declarations::Xy<T>, axis: Axis) -> T {
    if axis is X { pair.x } else { pair.y }
}

pub(crate) open spec fn other_axis(axis: Axis) -> Axis {
    if axis is X { Y } else { X }
}

pub(crate) open spec fn aspect<F: FrameFloat>(main: Axis, cross: f32, ratio: f32) -> f32 {
    if main is X { F::product(cross, ratio) } else { F::quotient(cross, ratio) }
}

pub(crate) open spec fn cross_regular<F: FrameFloat>(params: LayoutParams, cross: Axis, inner: f32) -> Option<f32> {
    match on_axis(params.size, cross) {
        Size::Fill => Some(if params.free_placement { inner } else { subtract_margins::<F>(inner, margin_pair::<F>(params, cross)) }),
        Size::Frac(fraction) => Some(F::product(inner, fraction)),
        _ => None,
    }
}

pub(crate) open spec fn stack_regular<F: FrameFloat>(params: LayoutParams, main: Axis, cross: f32) -> Option<(f32, bool)> {
    match on_axis(params.size, main) {
        Size::Pixels(size) => Some((size, true)),
        Size::AspectRatio(ratio) => Some((aspect::<F>(main, cross, ratio), false)),
        _ => None,
    }
}

pub(crate) open spec fn solved_axis_pair(data: NodeLayoutData, axis: Axis, size: f32, level: u16) -> bool {
    let regular = cycle_rules::slot_index(axis.index(), Kind::Regular) as int;
    let resolved = cycle_rules::slot_index(axis.index(), Kind::Final) as int;
    &&& data.values@[regular] == size && data.values@[resolved] == size
    &&& data.levels@[regular] == level && data.levels@[resolved] == crate::dependencies::rules::next_level(level)
    &&& cycle_rules::read_state(data.flags.0, regular as u32) == SOLVED
    &&& cycle_rules::read_state(data.flags.0, resolved as u32) == SOLVED
}

pub(crate) open spec fn publish_stack_pairs(flags: u32) -> u32 {
    cycle_rules::phase_word(cycle_rules::phase_word(
        cycle_rules::phase_word(cycle_rules::phase_word(flags, 0, SOLVED), 2, SOLVED), 1, SOLVED), 3, SOLVED)
}

pub(crate) open spec fn no_bounds(params: LayoutParams, axis: Axis) -> bool {
    on_axis(params.min_size, axis).is_none() && on_axis(params.max_size, axis).is_none()
}

pub(crate) open spec fn axis_lane(axis: Axis, kind: Kind) -> int {
    cycle_rules::slot_index(axis.index(), kind) as int
}

pub(crate) open spec fn solved_axis_bits(axis: Axis) -> u32 {
    cycle_rules::phase_word(cycle_rules::phase_word(0, axis_lane(axis, Kind::Regular) as u32, SOLVED),
        axis_lane(axis, Kind::Final) as u32, SOLVED)
}

pub(crate) open spec fn can_reset_intrinsic_fill<F: FrameFloat>(prior: NodeLayoutData, intrinsic: Axis) -> bool {
    &&& prior.structural_change is Clean
    &&& prior.flags.0 & !NodeFlags::WRAP_LINE_START == solved_axis_bits(X) | solved_axis_bits(Y)
    &&& prior.n_placed_children == 0
    &&& F::finite_word(prior.values@[axis_lane(intrinsic, Kind::Final)])
}

pub(crate) open spec fn intrinsic_fill_axis(params: LayoutParams) -> Option<Axis> {
    match (params.size.x, params.size.y) {
        (Size::FitContent, Size::Fill) => Some(X),
        (Size::Fill, Size::FitContent) => Some(Y),
        _ => None,
    }
}

pub(crate) open spec fn intrinsic_fill_admitted<F: FrameFloat>(prior: NodeLayoutData, params: LayoutParams, axis: Axis) -> bool {
    &&& intrinsic_fill_axis(params) == Some(axis)
    &&& !params.intrinsic_reads_other_axis(axis)
    &&& no_bounds(params, X) && no_bounds(params, Y)
    &&& can_reset_intrinsic_fill::<F>(prior, axis)
}

pub(crate) open spec fn reset_keeps_intrinsic(prior: NodeLayoutData, after: NodeLayoutData, intrinsic: Axis) -> bool {
    let other = other_axis(intrinsic);
    let reg = axis_lane(other, Kind::Regular);
    let fin = axis_lane(other, Kind::Final);
    &&& after.flags.0 == solved_axis_bits(intrinsic)
    &&& after.parent_flow == wrap_metrics::INITIAL_WORDS
    &&& after.values@ == prior.values@.update(reg, 0.0).update(fin, 0.0)
    &&& after.levels@ == prior.levels@.update(reg, 0).update(fin, 0)
    &&& after == (NodeLayoutData {
        values: after.values, levels: after.levels, flags: after.flags, parent_flow: after.parent_flow, ..prior
    })
}

pub(crate) proof fn intrinsic_fill_keeps_axis(prior: NodeLayoutData, after: NodeLayoutData, axis: Axis)
    requires reset_keeps_intrinsic(prior, after, axis),
    ensures
        after.values@[axis_lane(axis, Kind::Regular)] == prior.values@[axis_lane(axis, Kind::Regular)],
        after.values@[axis_lane(axis, Kind::Final)] == prior.values@[axis_lane(axis, Kind::Final)],
        after.levels@[axis_lane(axis, Kind::Regular)] == prior.levels@[axis_lane(axis, Kind::Regular)],
        after.levels@[axis_lane(axis, Kind::Final)] == prior.levels@[axis_lane(axis, Kind::Final)],
        cycle_rules::read_state(after.flags.0, axis_lane(axis, Kind::Regular) as u32) == SOLVED,
        cycle_rules::read_state(after.flags.0, axis_lane(axis, Kind::Final) as u32) == SOLVED,
        cycle_rules::read_state(after.flags.0, axis_lane(other_axis(axis), Kind::Regular) as u32) == cycle_rules::UNSOLVED,
        cycle_rules::read_state(after.flags.0, axis_lane(other_axis(axis), Kind::Final) as u32) == cycle_rules::UNSOLVED,
{
    if axis is X {
        assert(axis_lane(X, Kind::Regular) == 0 && axis_lane(Y, Kind::Regular) == 1
            && axis_lane(X, Kind::Final) == 2 && axis_lane(Y, Kind::Final) == 3) by (compute_only);
        assert(solved_axis_bits(X) == 0x22u32) by (compute_only);
        assert(cycle_rules::read_state(0x22u32, 0) == SOLVED
            && cycle_rules::read_state(0x22u32, 2) == SOLVED
            && cycle_rules::read_state(0x22u32, 1) == cycle_rules::UNSOLVED
            && cycle_rules::read_state(0x22u32, 3) == cycle_rules::UNSOLVED) by (compute_only);
    } else {
        assert(axis_lane(X, Kind::Regular) == 0 && axis_lane(Y, Kind::Regular) == 1
            && axis_lane(X, Kind::Final) == 2 && axis_lane(Y, Kind::Final) == 3) by (compute_only);
        assert(solved_axis_bits(Y) == 0x88u32) by (compute_only);
        assert(cycle_rules::read_state(0x88u32, 1) == SOLVED
            && cycle_rules::read_state(0x88u32, 3) == SOLVED
            && cycle_rules::read_state(0x88u32, 0) == cycle_rules::UNSOLVED
            && cycle_rules::read_state(0x88u32, 2) == cycle_rules::UNSOLVED) by (compute_only);
    }
}

/// Both receipts bind the packed lanes of the previous full solve to the
/// native producers. The fresh producer needs the same own-content inputs,
/// even when the opposite Fill axis will receive a different extent.
pub(crate) proof fn retained_free_intrinsic_fill_matches_full<A: crate::dependencies::sizing_finish::FinishModel>(
    prior: NodeLayoutData, after: NodeLayoutData, axis: Axis,
    old_regular: crate::dependencies::sizing_finish::StoredSize<A::Id>,
    old_final: crate::dependencies::sizing_finish::StoredSize<A::Id>,
    before_regular: &A, before_final: &A, fresh_regular: &A, fresh_final: &A,
)
    requires
        reset_keeps_intrinsic(prior, after, axis),
        ({
            use crate::dependencies::sizing_finish as finish;
            use crate::dependencies::sizing_requests::target;
            let regular = old_regular.slot;
            let final_slot = target(regular.node, regular.vertical, Kind::Final);
            let style = before_regular.finish_layout(regular.node);
            &&& regular.kind is Regular && regular.axis() == axis && old_final.slot == final_slot
            &&& before_final.finish_layout(regular.node) == style
            &&& fresh_final.finish_layout(regular.node) == style
            &&& !style.intrinsic_reads_other_axis(axis)
            &&& finish::free_intrinsic(before_regular, regular) && finish::free_intrinsic(fresh_regular, regular)
            &&& finish::canonical_direct_final(before_final, final_slot)
            &&& finish::canonical_direct_final(fresh_final, final_slot)
            &&& finish::same_intrinsic_leaf_inputs(before_regular, fresh_regular, regular)
            &&& old_regular.value == finish::free_intrinsic_value(before_regular, regular)
            &&& old_final.value == finish::direct_regular(before_final, final_slot)
            &&& finish::direct_regular(before_final, final_slot) == old_regular.value
            &&& finish::direct_regular(fresh_final, final_slot) == finish::free_intrinsic_value(fresh_regular, regular)
            &&& prior.values@[axis_lane(axis, Kind::Regular)] == old_regular.value
            &&& prior.values@[axis_lane(axis, Kind::Final)] == old_final.value
        }),
    ensures ({
        use crate::dependencies::sizing_finish as finish;
        &&& after.values@[axis_lane(axis, Kind::Regular)] == finish::free_intrinsic_value(fresh_regular, old_regular.slot)
        &&& after.values@[axis_lane(axis, Kind::Final)] == finish::direct_regular(fresh_final, old_final.slot)
    }),
{
    use crate::dependencies::sizing_finish as finish;
    finish::matching_own_content(before_regular, fresh_regular, old_regular.slot);
    intrinsic_fill_keeps_axis(prior, after, axis);
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(size =>
    ensures size == match cross_regular::<F>(*params, cross, inner) {
        Some(value) if F::finite_word(value) => Some(value), _ => None,
    },
    no_unwind
))]
fn stack_leaf_cross<F: FrameFloat>(params: &LayoutParams, cross: Axis, inner: f32) -> Option<f32> {
    let size = match *params.size.component(cross) {
        Size::Fill if params.free_placement => inner,
        Size::Fill => {
            let [start, end] = *params.margin.component(cross);
            inside_margins::<F>(inner, [F::margin(start), F::margin(end)])
        }
        Size::Frac(fraction) => F::multiply(inner, fraction),
        _ => return None,
    };
    if F::finite(size) { Some(size) } else { None }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == aspect::<F>(main, cross, ratio), no_unwind))]
pub(crate) fn aspect_size<F: FrameFloat>(main: Axis, cross: f32, ratio: f32) -> f32 {
    if matches!(main, X) { F::multiply(cross, ratio) } else { F::divide(cross, ratio) }
}

impl NodeLayoutData {
    /// Prepare both axes of a leaf in a stack with a fixed cross extent.
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures match out {
            None => *final(self) == *old(self),
            Some((size, pixel)) => ({
                let main = other_axis(cross);
                let resolved_cross = cross_regular::<F>(*params, cross, inner_cross);
                &&& no_bounds(*params, main) && no_bounds(*params, cross)
                &&& resolved_cross.is_some() && F::finite_word(resolved_cross.unwrap())
                &&& stack_regular::<F>(*params, main, resolved_cross.unwrap()) == Some((size, pixel))
                &&& F::finite_word(size)
                &&& ({
                    let x = if cross is X { resolved_cross.unwrap() } else { size };
                    let y = if cross is X { size } else { resolved_cross.unwrap() };
                    let regular = if pixel { 0u16 } else { 4u16 };
                    let rx = if cross is X { 2u16 } else { regular };
                    let ry = if cross is X { regular } else { 2u16 };
                    &&& final(self).values@ == old(self).values@.update(0, x).update(2, x).update(1, y).update(3, y)
                    &&& final(self).levels@ == old(self).levels@.update(0, rx)
                        .update(2, crate::dependencies::rules::next_level(rx)).update(1, ry)
                        .update(3, crate::dependencies::rules::next_level(ry))
                    &&& final(self).flags.0 == publish_stack_pairs(old(self).flags.0)
                })
            }),
        },
        no_unwind
    ))]
    pub(crate) fn seed_ready_stack_leaf<F: FrameFloat>(
        &mut self, params: &LayoutParams, cross: Axis, inner_cross: f32,
    ) -> Option<(f32, bool)> {
        let main = cross.other();
        let main_size = *params.size.component(main);
        if !matches!(main_size, Size::Pixels(_) | Size::AspectRatio(_))
            || params.min_size.x.is_some() || params.min_size.y.is_some()
            || params.max_size.x.is_some() || params.max_size.y.is_some()
        {
            return None;
        }
        let cross_size = stack_leaf_cross::<F>(params, cross, inner_cross)?;
        let (size, level, pixel) = match main_size {
            Size::Pixels(size) => (size, 0, true),
            Size::AspectRatio(ratio) => {
                let size = aspect_size::<F>(main, cross_size, ratio);
                (size, 4, false)
            }
            _ => return None,
        };
        if !F::finite(size) { return None; }
        let (x, y, x_level, y_level) = match cross {
            X => (cross_size, size, 2, level),
            Y => (size, cross_size, level, 2),
        };
        self.publish_axis(X, x, x, x_level);
        self.publish_axis(Y, y, y, y_level);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(main == other_axis(cross));
            assert(no_bounds(*params, main) && no_bounds(*params, cross));
            assert(cross_regular::<F>(*params, cross, inner_cross) == Some(cross_size));
            assert(stack_regular::<F>(*params, main, cross_size) == Some((size, pixel)));
            assert(F::finite_word(cross_size) && F::finite_word(size));
            assert(level == if pixel { 0u16 } else { 4u16 });
            assert(cycle_rules::slot_index(0, Kind::Regular) == 0 && cycle_rules::slot_index(0, Kind::Final) == 2
                && cycle_rules::slot_index(1, Kind::Regular) == 1 && cycle_rules::slot_index(1, Kind::Final) == 3) by (compute_only);
        }
        Some((size, pixel))
    }

    /// Resolve a leaf against its stack's fixed cross-axis extent.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn seed_stack_leaf<F: FrameFloat>(&mut self, params: &LayoutParams, cross: Axis, inner_cross: f32) -> bool {
        if params.min_size.component(cross).is_some() || params.max_size.component(cross).is_some() { return false; }
        let Some(cross_size) = stack_leaf_cross::<F>(params, cross, inner_cross) else { return false; };
        // The parent's pixel Regular and Final have levels zero and one.
        self.publish_axis(cross, cross_size, cross_size, 2);
        let main = cross.other();
        if let Size::AspectRatio(ratio) = *params.size.component(main) {
            if params.min_size.component(main).is_none() && params.max_size.component(main).is_none() {
                let size = aspect_size::<F>(main, cross_size, ratio);
                if F::finite(size) { self.publish_axis(main, size, size, 4); }
            }
        }
        self.flags.check_state(main, Kind::Final) == SOLVED
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn declaration(params: &LayoutParams, axis: Axis, kind: Kind) -> Option<Size> {
    match kind {
        Kind::Regular => Some(*params.size.component(axis)),
        Kind::Min => *params.min_size.component(axis),
        Kind::Max => *params.max_size.component(axis),
        _ => None,
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn block_auto(size: Size, axis: Axis, kind: Kind, block_item: bool) -> bool {
    matches!(size, Size::Auto) && matches!(axis, X) && matches!(kind, Kind::Regular) && block_item
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn stable(params: &LayoutParams, axis: Axis, kind: Kind, size: Size, block_item: bool, other_known: bool) -> bool {
    let form = if block_auto(size, axis, kind, block_item) { Form::Fill } else { size.dependency_form() };
    leaf_retention::input(form, matches!(form, Form::Intrinsic) && params.intrinsic_reads_other_axis(axis)).stable(other_known)
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn independent_decl(params: &LayoutParams, axis: Axis, kind: Kind, block_item: bool) -> bool {
    match declaration(params, axis, kind) {
        Some(size) => stable(params, axis, kind, size, block_item, false),
        None => true,
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
impl NodeLayoutData {
    /// Keep declarations whose complete dependency chain stays inside this leaf.
    #[cfg_attr(verus_keep_ghost, verus_spec(count => ensures count <= 8, no_unwind))]
    pub(crate) fn retain_leaf_slots<F: FrameFloat>(&mut self, old: &Self, params: &LayoutParams) -> u32 {
        let block_context = NodeFlags::BLOCK_ITEM | NodeFlags::BLOCK_PARENT_AUTO_HEIGHT;
        if !matches!(old.structural_change, StructuralChange::Clean | StructuralChange::Moved)
            || old.has_in_flow_children()
            || old.flags.has_cycle() || (old.flags.0 ^ self.flags.0) & block_context != 0
            || old.flags.check_state(X, Kind::Final) != SOLVED || old.flags.check_state(Y, Kind::Final) != SOLVED
        {
            return 0;
        }
        let block_item = self.flags.is_block_item();
        let x = independent_decl(params, X, Kind::Regular, block_item)
            && independent_decl(params, X, Kind::Min, block_item) && independent_decl(params, X, Kind::Max, block_item);
        let y = independent_decl(params, Y, Kind::Regular, block_item)
            && independent_decl(params, Y, Kind::Min, block_item) && independent_decl(params, Y, Kind::Max, block_item);
        let retained_x = self.retain_axis::<F>(old, params, X, block_item, y);
        let retained_y = self.retain_axis::<F>(old, params, Y, block_item, x);
        retained_x + retained_y
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(count => ensures count <= 4, no_unwind))]
    fn retain_axis<F: FrameFloat>(&mut self, old: &Self, params: &LayoutParams, axis: Axis, block_item: bool, other_known: bool) -> u32 {
        let (regular, kept_regular) = self.retain_decl(old, params, axis, Kind::Regular, block_item, other_known);
        let (min, kept_min) = self.retain_decl(old, params, axis, Kind::Min, block_item, other_known);
        let (max, kept_max) = self.retain_decl(old, params, axis, Kind::Max, block_item, other_known);
        // Leave warning-producing Final slots to the solver so it emits them again.
        let resolved = if kept_regular && kept_min && kept_max
            && F::finite(old.values[slot_index(axis, Kind::Final)])
            && old.values[slot_index(axis, Kind::Min)] <= old.values[slot_index(axis, Kind::Max)]
        {
            self.retain_slot(old, axis, Kind::Final)
        } else { 0 };
        regular + min + max + resolved
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires kind is Regular || kind is Min || kind is Max,
        ensures out.0 <= 1,
            !out.1 ==> *final(self) == *old(self) || ({
                let index = cycle_rules::slot_index(axis.index(), kind) as int;
                let opposite = cycle_rules::slot_index((1 - axis.index()) as usize, Kind::Final) as int;
                let flow = cycle_rules::slot_index(1, Kind::Flow) as int;
                &&& final(self).values@ == old(self).values@.update(flow, prior.values[opposite]).update(index, prior.values[index])
                &&& cycle_rules::read_state(final(self).flags.0, index as u32) == cycle_rules::CHECK_INTRINSIC
                &&& *final(self) == (NodeLayoutData { flags: final(self).flags, values: final(self).values, ..*old(self) })
            }),
        no_unwind
    ))]
    fn retain_decl(&mut self, prior: &Self, params: &LayoutParams, axis: Axis, kind: Kind, block_item: bool, other_known: bool) -> (u32, bool) {
        let Some(size) = declaration(params, axis, kind) else { return (0, true); };
        if stable(params, axis, kind, size, block_item, other_known) && prior.flags.check_state(axis, kind) == SOLVED {
            return (self.retain_slot(prior, axis, kind), true);
        }
        let other = axis.other();
        if matches!(size, Size::FitContent | Size::Auto) && params.intrinsic_reads_other_axis(axis)
            && !params.intrinsic_reads_other_axis(other) && !block_auto(size, axis, kind, block_item)
            && prior.flags.check_state(axis, kind) == SOLVED
        {
            // Preserve the old constraint word until the new parent supplies its available space.
            self.values[slot_index(Y, Kind::Flow)] = prior.values[slot_index(other, Kind::Final)];
            let index = slot_index(axis, kind);
            self.values[index] = prior.values[index];
            self.flags.set_state(axis, kind, cycle_rules::CHECK_INTRINSIC);
        }
        (0, false)
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out <= 1,
            out == 0 ==> *final(self) == *old(self),
            out == 1 ==> ({
                let index = cycle_rules::slot_index(axis.index(), kind) as int;
                &&& final(self).values@ == old(self).values@.update(index, prior.values[index])
                &&& final(self).levels@ == old(self).levels@.update(index, prior.levels[index])
                &&& cycle_rules::read_state(final(self).flags.0, index as u32) == cycle_rules::SOLVED
                &&& *final(self) == (NodeLayoutData { flags: final(self).flags, values: final(self).values,
                    levels: final(self).levels, ..*old(self) })
            }),
        no_unwind
    ))]
    fn retain_slot(&mut self, prior: &Self, axis: Axis, kind: Kind) -> u32 {
        if self.flags.check_state(axis, kind) == SOLVED { return 0; }
        let index = slot_index(axis, kind);
        self.publish_slot(index, prior.values[index]);
        self.levels[index] = prior.levels[index];
        1
    }

    #[cfg_attr(verus_keep_ghost, verus_spec(kept =>
        ensures kept == can_reset_intrinsic_fill::<F>(*old(self), intrinsic),
            if kept { reset_keeps_intrinsic(*old(self), *final(self), intrinsic) }
            else { *final(self) == *old(self) },
        no_unwind
    ))]
    pub(crate) fn reset_intrinsic_fill_leaf<F: FrameFloat>(&mut self, intrinsic: Axis) -> bool {
        let solved_x = solved_axis(X);
        let solved_y = solved_axis(Y);
        if !matches!(self.structural_change, StructuralChange::Clean)
            || self.flags.0 & !NodeFlags::WRAP_LINE_START != (solved_x | solved_y)
            || self.n_placed_children != 0 || !F::finite(self.values[slot_index(intrinsic, Kind::Final)])
        {
            return false;
        }
        self.flags = NodeFlags(if matches!(intrinsic, X) { solved_x } else { solved_y });
        self.parent_flow = wrap_metrics::INITIAL_WORDS;
        let regular = slot_index(intrinsic.other(), Kind::Regular);
        let resolved = slot_index(intrinsic.other(), Kind::Final);
        self.values[regular] = 0.0;
        self.values[resolved] = 0.0;
        self.levels[regular] = 0;
        self.levels[resolved] = 0;
        true
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(bits => ensures bits == solved_axis_bits(axis), no_unwind))]
fn solved_axis(axis: Axis) -> u32 {
    let regular = cycle_rules::write_state(0, slot_index(axis, Kind::Regular) as u32, SOLVED);
    cycle_rules::write_state(regular, slot_index(axis, Kind::Final) as u32, SOLVED)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Margin, placement_geometry::RustFloat, prepare_nodes::seed_pixels};

    #[test]
    fn pixel_stack_leaf_matches_general_sizing_slots() {
        let margins = [Margin::px(0.25).unwrap(), Margin::px(3.5).unwrap()];
        for cross in [X, Y] {
            for (rule, free) in [(Size::Fill, false), (Size::Fill, true), (Size::Frac(-0.0), false)] {
                let mut params = LayoutParams::DEFAULT;
                params.size[cross] = rule;
                params.size[cross.other()] = Size::Pixels(-0.0);
                params.margin[cross] = margins;
                params.free_placement = free;

                let mut expected = NodeLayoutData::new();
                assert!(!seed_pixels::<RustFloat>(&mut expected, &params, false, None));
                assert!(expected.seed_stack_leaf::<RustFloat>(&params, cross, 3.0));

                let mut actual = NodeLayoutData::new();
                let (pixels, independent) = actual.seed_ready_stack_leaf::<RustFloat>(&params, cross, 3.0).unwrap();
                assert!(independent);
                assert_eq!(pixels.to_bits(), (-0.0f32).to_bits());
                assert_eq!(actual.flags, expected.flags);
                assert_eq!(actual.values.map(f32::to_bits), expected.values.map(f32::to_bits));
                #[cfg(feature = "incremental")]
                assert_eq!(actual.levels, expected.levels);
            }
        }
    }
}
