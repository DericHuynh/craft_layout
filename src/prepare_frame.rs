//! Shared data and arithmetic for the production postorder preparation.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, ChildrenLayout, ContentMeasure, LayoutParams, MainAxisCellSize, Margin, Size, TextContent, Xy, X, Y};
use crate::node_flags::{NodeFlags, slot_index};
#[cfg(not(verus_keep_ghost))]
use crate::{placement_geometry::{FloatBounds, RustFloat}, solve::cycle_rules};
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::solve::dependency_rules;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, dependencies::rules as dependency_rules, placement::geometry::FloatBounds};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use cycle_rules::{Kind, N_SLOTS};

#[cfg(verus_keep_ghost)]
verus! {
#[verifier::reject_recursive_types(I)]
pub(crate) struct Order<I> {
    pub live: spec_fn(I) -> bool,
    pub interval: spec_fn(I) -> (nat, nat),
    pub depth: spec_fn(I) -> nat,
    pub parent: spec_fn(I) -> Option<I>,
    pub first: spec_fn(I) -> Option<I>,
    pub sibling: spec_fn(I) -> Option<I>,
}

impl<I> Order<I> {
    pub(crate) open spec fn inside(self, root: I, node: I) -> bool {
        &&& (self.live)(node)
        &&& (self.interval)(root).0 <= (self.interval)(node).0 < (self.interval)(node).1
        &&& (self.interval)(node).1 <= (self.interval)(root).1
    }

    pub(crate) open spec fn child(self, parent: I, node: I) -> bool {
        &&& (self.live)(node)
        &&& (self.parent)(node) == Some(parent)
        &&& (self.interval)(parent).0 < (self.interval)(node).0 < (self.interval)(node).1
        &&& (self.interval)(node).1 <= (self.interval)(parent).1
        &&& (self.depth)(parent) < (self.depth)(node)
    }

    pub(crate) open spec fn ordered(self) -> bool {
        forall |node: I| #[trigger] (self.live)(node) ==> {
            &&& (self.interval)(node).0 < (self.interval)(node).1
            &&& match (self.first)(node) {
                Some(child) => self.child(node, child),
                None => true,
            }
            &&& match (self.parent)(node) {
                Some(parent) => (self.live)(parent) && self.child(parent, node)
                    && match (self.sibling)(node) {
                        Some(next) => self.child(parent, next) && (self.interval)(node).1 <= (self.interval)(next).0,
                        None => true,
                    },
                None => (self.sibling)(node).is_none(),
            }
        }
    }

    /// An interval for a subtree contains its live nodes and only their
    /// in-scope parent and sibling links. The root's outside links are excluded.
    pub(crate) open spec fn closed_subtrees(self) -> bool {
        forall |root: I, node: I| #[trigger] self.inside(root, node) && (self.live)(root) && node != root ==> {
            &&& (self.parent)(node).is_some() && self.inside(root, (self.parent)(node).unwrap())
            &&& (self.sibling)(node).is_some() ==> self.inside(root, (self.sibling)(node).unwrap())
        }
    }

    pub(crate) proof fn node_facts(self, node: I)
        requires self.ordered(), (self.live)(node),
        ensures (self.interval)(node).0 < (self.interval)(node).1,
            (self.first)(node).is_some() ==> self.child(node, (self.first)(node).unwrap()),
            (self.parent)(node).is_some() && (self.sibling)(node).is_some()
                ==> self.child((self.parent)(node).unwrap(), (self.sibling)(node).unwrap())
                    && (self.interval)(node).1 <= (self.interval)((self.sibling)(node).unwrap()).0,
    {}
}

pub(crate) open spec fn frame_live<I>(frame: PrepareFrame<I>, order: Order<I>) -> bool {
    &&& frame.order@ == order
    &&& order.ordered()
    &&& (order.live)(frame.node)
    &&& frame.next.is_some() ==> order.child(frame.node, frame.next.unwrap())
}

pub(crate) open spec fn remaining<I>(frame: PrepareFrame<I>) -> nat {
    match frame.next {
        Some(cursor) => (3 * ((frame.order@.interval)(frame.node).1 - (frame.order@.interval)(cursor).0)) as nat,
        None => 0,
    }
}
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait FrameWords {
    spec fn word(value: f32) -> u32;
    spec fn decode(word: u32) -> f32;

    // RustFloat's bitcasts satisfy this law for every binary32 representation.
    // proofs/frame_float_native.py checks the concrete native implementation.
    proof fn word_roundtrip(value: f32)
        ensures Self::decode(Self::word(value)) == value;

    spec fn count_value(count: u32) -> f32;
    spec fn margin_value(value: Margin) -> f32;
    spec fn sum(left: f32, right: f32) -> f32;
    spec fn difference(left: f32, right: f32) -> f32;
    spec fn product(left: f32, right: f32) -> f32;
    spec fn quotient(left: f32, right: f32) -> f32;
    spec fn number_eq(left: f32, right: f32) -> bool;
    spec fn at_most(left: f32, right: f32) -> bool;
    spec fn magnitude(value: f32) -> f32;
}

pub(crate) proof fn same_float_word<F: FrameWords>(left: f32, right: f32)
    requires F::word(left) == F::word(right),
    ensures left == right,
{
    F::word_roundtrip(left);
    F::word_roundtrip(right);
}

}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait FrameWords {}
#[cfg(not(verus_keep_ghost))]
impl<T> FrameWords for T {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FrameFloat: FloatBounds + FrameWords {
    #[cfg_attr(verus_keep_ghost, verus_spec(pixels => ensures pixels == Self::margin_value(value), no_unwind))]
    fn margin(value: Margin) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == Self::sum(left, right), no_unwind))]
    fn add(left: f32, right: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == Self::difference(left, right), no_unwind))]
    fn subtract(left: f32, right: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == Self::product(left, right), no_unwind))]
    fn multiply(left: f32, right: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == Self::quotient(left, right), no_unwind))]
    fn divide(left: f32, right: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(zero => ensures zero == (Self::word(value) & 0x7fff_ffffu32 == 0), no_unwind))]
    fn is_zero(value: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(nonzero =>
        ensures nonzero == (0u32 < Self::word(value) <= 0x7f80_0000u32), no_unwind))]
    fn positive(value: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(finite => ensures finite == Self::finite_word(value), no_unwind))]
    fn finite(value: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(bits => ensures bits == Self::word(value), no_unwind))]
    fn bits(value: f32) -> u32;

    #[cfg_attr(verus_keep_ghost, verus_spec(value =>
        ensures Self::word(value) == word, value == Self::decode(word), no_unwind
    ))]
    fn from_word(word: u32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(value => ensures value == Self::count_value(count), no_unwind))]
    fn from_count(count: u32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(equal => ensures equal == Self::number_eq(left, right), no_unwind))]
    fn equal_numbers(left: f32, right: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(within => ensures within == Self::at_most(left, right), no_unwind))]
    fn less_or_equal(left: f32, right: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(before =>
        ensures before == (Self::at_most(left, right) && !Self::number_eq(left, right)), no_unwind
    ))]
    fn less_than(left: f32, right: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(abs => ensures abs == Self::magnitude(value), no_unwind))]
    fn absolute(value: f32) -> f32;
}

#[cfg(not(verus_keep_ghost))]
impl FrameFloat for RustFloat {
    #[inline(always)]
    fn margin(value: Margin) -> f32 { value.pixels() }

    #[inline(always)]
    fn add(left: f32, right: f32) -> f32 { left + right }

    #[inline(always)]
    fn subtract(left: f32, right: f32) -> f32 { left - right }

    #[inline(always)]
    fn multiply(left: f32, right: f32) -> f32 { left * right }

    #[inline(always)]
    fn divide(left: f32, right: f32) -> f32 { left / right }

    #[inline(always)]
    fn is_zero(value: f32) -> bool { value == 0.0 }

    #[inline(always)]
    fn positive(value: f32) -> bool { value > 0.0 }

    #[inline(always)]
    fn finite(value: f32) -> bool { value.is_finite() }

    #[inline(always)]
    fn bits(value: f32) -> u32 { value.to_bits() }

    #[inline(always)]
    fn from_word(word: u32) -> f32 { f32::from_bits(word) }

    #[inline(always)]
    fn from_count(count: u32) -> f32 { count as f32 }

    #[inline(always)]
    fn equal_numbers(left: f32, right: f32) -> bool { left == right }

    #[inline(always)]
    fn less_or_equal(left: f32, right: f32) -> bool { left <= right }

    #[inline(always)]
    fn less_than(left: f32, right: f32) -> bool { left < right }

    #[inline(always)]
    fn absolute(value: f32) -> f32 { value.abs() }
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct KnownAxis {
    pub axis: Axis,
    pub size: f32,
    // Dependency rank of the Regular slot.
    pub rank: u16,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct KnownStack {
    pub own: KnownAxis,
    // The main-axis Fill share or the available cross-axis extent.
    pub child_space: Option<f32>,
}

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
pub(crate) struct PrepareFrame<I> {
    pub(crate) node: I,
    pub(crate) next: Option<I>,
    pub(crate) retain: bool,
    pub(crate) block_parent: Option<bool>,
    pub(crate) block_children: Option<bool>,
    pub(crate) stack_axis: Option<Axis>,
    pub(crate) spacing: f32,
    pub(crate) pixel_fit_axis: Option<Axis>,
    pub(crate) extent: f32,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    pub(crate) fit_level: u16,
    pub(crate) fixed_cross: Option<(Axis, f32)>,
    pub(crate) known: Option<KnownStack>,
    pub(crate) n_placed_children: u32,
    pub(crate) n_nodes: u32,
    pub(crate) flags: u32,
    #[cfg(verus_keep_ghost)]
    pub(crate) order: Ghost<Order<I>>,
}

impl<I> PrepareFrame<I> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).node == old(self).node, final(self).next == old(self).next,
            final(self).order@ == old(self).order@,
            final(self).n_nodes == if old(self).n_nodes + child_nodes <= u32::MAX {
                old(self).n_nodes + child_nodes
            } else { u32::MAX as int },
        no_unwind
    ))]
    pub(crate) fn include_child<F: FrameFloat>(&mut self, params: &LayoutParams, child_nodes: u32, needs_solve: bool,
        fit_child: Option<(f32, u16)>,
    ) {
        self.n_nodes = cycle_rules::add_count(self.n_nodes, child_nodes);
        if needs_solve {
            self.flags |= NodeFlags::DESCENDANTS_NEED_SOLVE;
        }
        if let Some(axis) = self.pixel_fit_axis {
            if !params.disabled && !params.free_placement {
                let extent = if params.min_size.component(axis).is_none() && params.max_size.component(axis).is_none() {
                    match *params.size.component(axis) {
                        Size::Pixels(size) => Some((size, 0)),
                        Size::FitContent => fit_child,
                        _ => None,
                    }
                } else { None };
                match extent {
                    Some((size, _level)) => {
                        let [start, end] = *params.margin.component(axis);
                        let margin = F::margin(start) + F::margin(end);
                        let child_extent = if margin == 0.0 { size } else { size + margin };
                        self.extent = match self.stack_axis {
                            Some(main) if main.index() == axis.index() => self.extent + child_extent,
                            _ => F::max(self.extent, child_extent),
                        };
                        #[cfg(any(feature = "incremental", verus_keep_ghost))]
                        { self.fit_level = dependency_rules::include_level(self.fit_level, _level); }
                    }
                    _ => self.pixel_fit_axis = None,
                }
            }
        }
        summarize_child(params, &mut self.n_placed_children, &mut self.flags);
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns child_flag_mask(params), no_unwind))]
pub(crate) fn child_flag_mask(params: &LayoutParams) -> u32 {
    let x = if params.size.x.is_flex() { NodeFlags::FLEX_CHILD_X } else { 0 };
    let y = if params.size.y.is_flex() { NodeFlags::FLEX_CHILD_Y } else { 0 };
    let spans = if params.grid_span.x > 1 || params.grid_span.y > 1 { NodeFlags::GRID_SPANS } else { 0 };
    x | y | spans
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures
        *final(n_placed) == if !params.disabled && !params.free_placement && *old(n_placed) < u32::MAX {
            *old(n_placed) + 1
        } else { *old(n_placed) as int },
        *final(flags) == if !params.disabled && !params.free_placement {
            *old(flags) | child_flag_mask(params)
        } else { *old(flags) },
    no_unwind
))]
pub(crate) fn summarize_child(params: &LayoutParams, n_placed: &mut u32, flags: &mut u32) {
    if !params.disabled && !params.free_placement {
        *n_placed = cycle_rules::add_count(*n_placed, 1);
        *flags |= child_flag_mask(params);
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn pixel_decl(params: LayoutParams, axis: Axis) -> Option<f32> {
    match if axis is X { params.size.x } else { params.size.y } {
        Size::Pixels(pixels) => Some(pixels),
        _ => None,
    }
}

pub(crate) open spec fn pixel_final<F: FrameFloat>(
    params: LayoutParams, axis: Axis, block_item: bool, width_grid_axis: Option<Axis>,
) -> bool {
    let declaration = pixel_decl(params, axis);
    declaration.is_some() && cycle_rules::ready_pixel_finals(
        F::finite_word(declaration.unwrap()),
        (if axis is X { params.min_size.x } else { params.min_size.y }).is_some(),
        (if axis is X { params.max_size.x } else { params.max_size.y }).is_some(),
        block_item, width_grid_axis.is_some() && width_grid_axis.unwrap().index() == axis.index(),
    )
}

pub(crate) open spec fn pixel_slots<F: FrameFloat>(values: [f32; N_SLOTS], axis: Axis) -> (u32, u32) {
    (F::word(values[cycle_rules::slot_index(axis.index(), Kind::Regular) as int]),
     F::word(values[cycle_rules::slot_index(axis.index(), Kind::Final) as int]))
}

proof fn pixel_write_preserves_upper(before: u32, after: u32, index: usize)
    requires index < 4, after & !(3u32 << (2 * index)) == before & !(3u32 << (2 * index)),
    ensures after & !0xffu32 == before & !0xffu32,
{
    assert(after & !0xffu32 == before & !0xffu32) by (bit_vector)
        requires index < 4, after & !(3u32 << (2 * index)) == before & !(3u32 << (2 * index));
}
}

/// Initial preparation of an independent, explicitly declared pixel slot.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(ready =>
    ensures ready == pixel_final::<F>(*params, axis, block_item, width_grid_axis),
        ({
            let reg = cycle_rules::slot_index(axis.index(), Kind::Regular) as int;
            let fin = cycle_rules::slot_index(axis.index(), Kind::Final) as int;
            let value = pixel_decl(*params, axis);
            let regular = if value.is_some() { old(values)@.update(reg, value.unwrap()) } else { old(values)@ };
            &&& final(values)@ == if ready { regular.update(fin, value.unwrap()) } else { regular }
            &&& final(levels)@ == if ready { old(levels)@.update(fin, 1u16) } else { old(levels)@ }
            &&& *final(flags) & !0xffu32 == *old(flags) & !0xffu32
            &&& value.is_some() ==> cycle_rules::read_state(*final(flags), reg as u32) == cycle_rules::SOLVED
            &&& ready ==> cycle_rules::read_state(*final(flags), fin as u32) == cycle_rules::SOLVED
            &&& forall |i: u32| i < N_SLOTS && (i != reg || value.is_none()) && (i != fin || !ready) ==>
                #[trigger] cycle_rules::read_state(*final(flags), i) == cycle_rules::read_state(*old(flags), i)
        }),
    no_unwind
))]
fn seed_axis<F: FrameFloat>(
    params: &LayoutParams, axis: Axis, block_item: bool, width_grid_axis: Option<Axis>,
    flags: &mut u32, values: &mut [f32; N_SLOTS],
    #[cfg(any(feature = "incremental", verus_keep_ghost))] levels: &mut [u16; N_SLOTS],
) -> bool {
    let Size::Pixels(pixels) = *params.size.component(axis) else { return false; };
    let regular = slot_index(axis, Kind::Regular);
    #[cfg(verus_keep_ghost)]
    let before = *flags;
    cycle_rules::publish_finished_slot(flags, values, regular, pixels);
    #[cfg(verus_keep_ghost)]
    proof! { pixel_write_preserves_upper(before, *flags, regular); }
    let grid_depends_on_axis = match width_grid_axis {
        Some(main) => main.index() == axis.index(),
        None => false,
    };
    if !cycle_rules::ready_pixel_finals(
        F::finite(pixels), params.min_size.component(axis).is_some(), params.max_size.component(axis).is_some(),
        block_item, grid_depends_on_axis,
    ) {
        return false;
    }
    let final_index = slot_index(axis, Kind::Final);
    #[cfg(verus_keep_ghost)]
    let previous = *flags;
    cycle_rules::publish_finished_slot(flags, values, final_index, pixels);
    #[cfg(verus_keep_ghost)]
    proof! { pixel_write_preserves_upper(previous, *flags, final_index); }
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { levels[final_index] = 1; }
    true
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(ready =>
    ensures ready == (pixel_final::<F>(*params, X, block_item, width_grid_axis)
                       && pixel_final::<F>(*params, Y, block_item, width_grid_axis)),
        ready ==> ({
            let x = F::word(pixel_decl(*params, X).unwrap());
            let y = F::word(pixel_decl(*params, Y).unwrap());
            &&& pixel_slots::<F>(*final(values), X) == (x, x)
            &&& pixel_slots::<F>(*final(values), Y) == (y, y)
            &&& final(levels)@[0] == old(levels)@[0] && final(levels)@[1] == old(levels)@[1]
            &&& final(levels)@[2] == 1 && final(levels)@[3] == 1
            &&& *final(flags) == (*old(flags) & !0xffu32) | 0xaau32
        }),
    no_unwind
))]
pub(crate) fn seed_pixels<F: FrameFloat>(
    params: &LayoutParams, block_item: bool, width_grid_axis: Option<Axis>,
    flags: &mut u32, values: &mut [f32; N_SLOTS],
    #[cfg(any(feature = "incremental", verus_keep_ghost))] levels: &mut [u16; N_SLOTS],
) -> bool {
    let x = seed_axis::<F>(params, X, block_item, width_grid_axis, flags, values,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] levels);
    let y = seed_axis::<F>(params, Y, block_item, width_grid_axis, flags, values,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] levels);
    #[cfg(verus_keep_ghost)]
    proof! {
        if x && y {
            let result = *flags;
            let before = *old(flags);
            assert(cycle_rules::read_state(result, 0) == cycle_rules::SOLVED);
            assert(cycle_rules::read_state(result, 1) == cycle_rules::SOLVED);
            assert(cycle_rules::read_state(result, 2) == cycle_rules::SOLVED);
            assert(cycle_rules::read_state(result, 3) == cycle_rules::SOLVED);
            assert(cycle_rules::SOLVED == 2) by (compute_only);
            assert(cycle_rules::read_state(result, 0) == (result >> 0u32) & 3);
            assert((result >> 0u32) == result) by (bit_vector);
            assert(result & 3 == 2);
            assert(cycle_rules::read_state(result, 1) == (result >> 2u32) & 3);
            assert(cycle_rules::read_state(result, 2) == (result >> 4u32) & 3);
            assert(cycle_rules::read_state(result, 3) == (result >> 6u32) & 3);
            assert(result == (before & !0xffu32) | 0xaau32) by (bit_vector) requires
                result & !0xffu32 == before & !0xffu32, result & 3 == 2,
                (result >> 2) & 3 == 2, (result >> 4) & 3 == 2, (result >> 6) & 3 == 2;
        }
    }
    x && y
}

/// Determine which axis can be resolved by folding independent pixel children.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn pixel_fit(params: &LayoutParams, stack_axis: Option<Axis>) -> Option<Axis> {
    let Some(main) = stack_axis else { return None; };
    if !matches!(params.text, TextContent::None) || !matches!(params.content_measure, ContentMeasure::None) {
        return None;
    }
    let cross = main.other();
    if matches!(*params.size.component(cross), Size::FitContent) { Some(cross) }
    else if matches!(*params.size.component(main), Size::FitContent) { Some(main) }
    else { None }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn stack_cross_pixels<F: FrameFloat>(
    params: &LayoutParams, mode: ChildrenLayout, retain: bool, block_parent: Option<bool>,
) -> Option<(Axis, f32)> {
    if retain || block_parent.is_some() { return None; }
    let ChildrenLayout::Stack { axis, .. } = mode else { return None; };
    let cross = axis.other();
    match *params.size.component(cross) {
        Size::Pixels(size) if F::finite(size) && params.min_size.component(cross).is_none()
            && params.max_size.component(cross).is_none() => Some((cross, size)),
        _ => None,
    }
}

impl<I> PrepareFrame<I> {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn mode_flags(&self, children_layout: ChildrenLayout) -> (u32, u32, Option<Axis>) {
        let mut flags = self.flags;
        if let Some(auto_height) = self.block_parent {
            flags |= NodeFlags::BLOCK_ITEM;
            if auto_height { flags |= NodeFlags::BLOCK_PARENT_AUTO_HEIGHT; }
        }
        let count = if self.block_children.is_some() {
            flags |= NodeFlags::BLOCK_CONTAINER;
            if self.n_placed_children != 0 { 1 } else { 0 }
        } else { self.n_placed_children };
        if matches!(children_layout, ChildrenLayout::Wrap { .. }) {
            flags |= NodeFlags::WRAP_CONTAINER;
        }
        let width_grid_axis = match children_layout {
            ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } => Some(main_axis),
            _ => None,
        };
        (flags, count, width_grid_axis)
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn publish_fit<F: FrameFloat>(
    axis: Axis, child_extent: f32, image: Option<Xy<f32>>, stack_axis: Option<Axis>,
    spacing: f32, count: u32, padding: f32, flags: &mut u32, values: &mut [f32; N_SLOTS],
    #[cfg(any(feature = "incremental", verus_keep_ghost))] levels: &mut [u16; N_SLOTS],
    #[cfg(any(feature = "incremental", verus_keep_ghost))] level: u16,
) {
    let own = match image { Some(extent) => F::max(0.0, *extent.component(axis)), None => 0.0 };
    let gaps = match stack_axis {
        Some(main) if main.index() == axis.index() => spacing * F::max(count as f32 - 1.0, 0.0),
        _ => 0.0,
    };
    let index = slot_index(axis, Kind::Regular);
    cycle_rules::publish_finished_slot(flags, values, index, F::max(child_extent, own) + gaps + padding);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { levels[index] = level; }
}
