//! Fast sizing of unbounded Fill axes and compatible sibling batches.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, ChildrenLayout, LayoutParams, MainAxisCellSize, Size, X, Y, Xy};
use crate::node_data::NodeLayoutData;
use crate::node_flags::{NodeFlags, slot_index};
use crate::prepare_frame::FrameFloat;
use crate::prepare_nodes::Records;
use crate::sizing_pass;
#[cfg(not(verus_keep_ghost))]
use super::{cycle_rules, fill_compaction as fill, sizing_finish};
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use super::dependency_rules;
#[cfg(not(verus_keep_ghost))]
use crate::{fill_budget, flow::wrap_metrics};
#[cfg(not(verus_keep_ghost))]
use crate::placement_geometry::FloatBounds;
#[cfg(verus_keep_ghost)]
use crate::placement::geometry::FloatBounds;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, dependencies::{rules as dependency_rules, sizing_finish},
    fill::{budget as fill_budget, kernel as fill}, prepare_nodes::live,
    wrap_metrics::kernel as wrap_metrics};
#[cfg(verus_keep_ghost)]
use crate::{placement::geometry::FloatClassification, prepare_frame::FrameWords,
    prepare_leaf::{axis_lane, no_bounds, on_axis, solved_axis_pair}, prepare_nodes::RecordModel};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use cycle_rules::{Kind, SOLVED, UNSOLVED};
use fill::FloatOps;
use sizing_finish::{GridTrack, clamp, inner, inside_margins, padding};

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait BoundRecords: Records {
    type BoundFloat: fill::FloatOps;
}

#[cfg(not(verus_keep_ghost))]
impl<T: crate::TreeAdapter + ?Sized> BoundRecords for T {
    type BoundFloat = fill::RustFloat;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: sizing_pass::Access + BoundRecords {
    #[cfg_attr(verus_keep_ghost, verus_spec(requires live(self, node), no_unwind))]
    fn declaration(&self, node: Self::Id, axis: Axis, kind: Kind) -> Option<Size>;

    // The Fill collector shares the stable suffix and addressable scratch premises.
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires first.is_some() ==> live(old(self), first.unwrap()),
        ensures final(self).order() == old(self).order(),
        no_unwind
    ))]
    fn bounded_share(&mut self, axis: Axis, budget: f32, first: Option<Self::Id>) -> f32;
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(pair =>
    ensures pair == sizing_finish::margin_pair::<F>(*params, axis), no_unwind
))]
fn margins<F: FrameFloat>(params: &LayoutParams, axis: Axis) -> [f32; 2] {
    let [start, end] = *params.margin.component(axis);
    [F::margin(start), F::margin(end)]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(requires live(tree, node), no_unwind))]
fn value<A: Records + ?Sized>(tree: &A, node: A::Id, axis: Axis, kind: Kind) -> f32 {
    cycle_rules::read_slot(&tree.record(node).values, axis.index(), kind)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(requires live(tree, node), no_unwind))]
fn bound<A: Access + ?Sized>(tree: &A, node: A::Id, axis: Axis, kind: Kind) -> Option<f32> {
    if tree.declaration(node, axis, kind).is_some() { Some(value(tree, node, axis, kind)) }
    else { None }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(level =>
    ensures level == dependency_rules::next_level(data.levels@[axis_lane(axis, kind)]),
    no_unwind
))]
fn dependency_level(data: &NodeLayoutData, axis: Axis, kind: Kind) -> u16 {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { dependency_rules::next_level(data.levels[slot_index(axis, kind)]) }
    #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
    { let _ = (data, axis, kind); 0 }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn publish_share(data: &mut NodeLayoutData, axis: Axis, share: f32) -> u16 {
    let index = slot_index(axis, Kind::EvenShare);
    data.publish_slot(index, share);
    let level = dependency_level(data, axis, Kind::Final);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { data.levels[index] = level; }
    level
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) struct WrappedFill<I> {
    pub parent: I,
    pub child_style: LayoutParams,
    pub parent_style: LayoutParams,
    pub child_flags: NodeFlags,
    pub flow_flags: NodeFlags,
    pub cross_word: u32,
    pub size: f32,
    pub level: u16,
}

impl<I> WrappedFill<I> {
    pub(crate) open spec fn valid<F: FrameFloat>(self, cross: Axis) -> bool {
        &&& on_axis(self.child_style.size, cross) is Fill
        &&& !self.child_style.free_placement && no_bounds(self.child_style, cross)
        &&& matches!(self.child_style.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        &&& phase(self.child_flags, cross, Kind::Regular) == UNSOLVED
        &&& phase(self.child_flags, cross, Kind::Final) == UNSOLVED
        &&& phase(self.flow_flags, cross, Kind::Flow) == SOLVED
        &&& matches!(self.parent_style.children_layout, ChildrenLayout::Wrap { axis, .. } if axis.index() != cross.index())
        &&& self.size == sizing_finish::subtract_margins::<F>(
            F::decode(self.cross_word), sizing_finish::margin_pair::<F>(self.child_style, cross),
        )
        &&& F::finite_word(self.size)
    }
}

pub(crate) open spec fn phase(flags: NodeFlags, axis: Axis, kind: Kind) -> u32 {
    cycle_rules::read_state(flags.0, axis_lane(axis, kind) as u32)
}

pub(crate) open spec fn wrapped_fill_at<A: RecordModel + ?Sized>(tree: &A, child: A::Id, cross: Axis) -> Option<WrappedFill<A::Id>> {
    let params = tree.layout_params(child);
    let data = tree.layout_record(child);
    if !(on_axis(params.size, cross) is Fill) || params.free_placement || !no_bounds(params, cross)
        || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        || (tree.order().first)(child).is_some()
        || phase(data.flags, cross, Kind::Regular) != UNSOLVED || phase(data.flags, cross, Kind::Final) != UNSOLVED
    {
        None
    } else if let Some(parent) = (tree.order().parent)(child) {
        let parent_data = tree.layout_record(parent);
        let parent_style = tree.layout_params(parent);
        let cross_word = data.parent_flow@[wrap_metrics::Metric::Cross.word() as int];
        let size = sizing_finish::subtract_margins::<A::Float>(
            A::Float::decode(cross_word), sizing_finish::margin_pair::<A::Float>(params, cross),
        );
        if phase(parent_data.flags, cross, Kind::Flow) == SOLVED
            && matches!(parent_style.children_layout, ChildrenLayout::Wrap { axis, .. } if axis.index() != cross.index())
            && A::Float::finite_word(size)
        {
            Some(WrappedFill {
                parent, child_style: params, parent_style, child_flags: data.flags, flow_flags: parent_data.flags,
                cross_word, size, level: dependency_rules::next_level(parent_data.levels@[axis_lane(cross, Kind::Flow)]),
            })
        } else { None }
    } else { None }
}

pub(crate) open spec fn published_line_fill<I>(record: NodeLayoutData, cross: Axis, work: WrappedFill<I>) -> bool {
    solved_axis_pair(record, cross, work.size, work.level)
}

/// When the reference's native Flow producer supplies the same packed
/// Cross observation, its scalar Regular and direct Final publish these
/// shortcut words, without relying on any equality of computed size outputs.
pub(crate) proof fn wrapped_fill_matches_declared_scalar<A: sizing_finish::FinishModel>(
    work: WrappedFill<A::Id>, child: A::Id, cross: Axis,
    reference: &A, with_regular: &A, published: NodeLayoutData,
)
    requires
        work.valid::<A::Float>(cross), published_line_fill(published, cross, work),
        reference.finish_layout(child) == work.child_style,
        reference.finish_layout(work.parent) == work.parent_style,
        (reference.topology().parent)(child) == Some(work.parent),
        ({
            let regular = crate::dependencies::sizing_requests::target(child, cross is Y, Kind::Regular);
            (reference.topology().stack_parent)(regular).is_none()
        }),
        reference.finish_flags(child).0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT == 0,
        phase(reference.finish_flags(work.parent), cross, Kind::Flow) == SOLVED,
        reference.wrap_words().contains_key(child),
        reference.wrap_words()[child].1 == work.cross_word,
        with_regular.finish_layout(child) == work.child_style,
        !with_regular.finish_flags(child).is_block_item(),
        ({
            let regular = crate::dependencies::sizing_requests::target(child, cross is Y, Kind::Regular);
            sizing_finish::declared_scalar(reference, regular)
                == Some(with_regular.finish_values(child)[axis_lane(cross, Kind::Regular)])
        }),
    ensures ({
        let regular = crate::dependencies::sizing_requests::target(child, cross is Y, Kind::Regular);
        let final_slot = crate::dependencies::sizing_requests::target(child, cross is Y, Kind::Final);
        &&& sizing_finish::declared_scalar(reference, regular) == Some(published.values@[axis_lane(cross, Kind::Regular)])
        &&& sizing_finish::canonical_direct_final(with_regular, final_slot)
        &&& sizing_finish::direct_regular(with_regular, final_slot) == published.values@[axis_lane(cross, Kind::Final)]
    }),
{
    use crate::dependencies::sizing_requests::{resolved_size, target};
    let regular = target(child, cross is Y, Kind::Regular);
    let final_slot = target(child, cross is Y, Kind::Final);
    let flow = target(work.parent, cross is Y, Kind::Flow);
    let flags = reference.finish_flags(child);
    assert(regular.axis() == cross);
    assert(axis_lane(cross, Kind::Flow) == sizing_finish::key(flow).1);
    assert(sizing_finish::producer_phase(reference, flow) == SOLVED);
    assert(resolved_size(work.child_style, cross is Y, Kind::Regular, flags.is_block_item(), false) == Some(Size::Fill));
    assert(sizing_finish::scalar_declaration(reference, regular) == Some(Size::Fill));
    assert(sizing_finish::parent_extent(reference, regular, true) == work.size);
    assert(sizing_finish::has_unbounded_final_inputs(work.child_style, cross, false));
    assert(sizing_finish::permits_direct_final(work.child_style, cross, with_regular.finish_flags(child)));
}
}

/// A wrapped leaf can read its line extent directly once the flow slot solves.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(published =>
    requires live(old(tree), child),
    ensures final(tree).order() == old(tree).order(), final(tree).root_calls() == old(tree).root_calls(),
        published == wrapped_fill_at(old(tree), child, cross).is_some(),
        if published {
            let work = wrapped_fill_at(old(tree), child, cross).unwrap();
            &&& work.valid::<A::Float>(cross)
            &&& published_line_fill(final(tree).layout_record(child), cross, work)
            &&& final(tree).layout_record(child).parent_flow == old(tree).layout_record(child).parent_flow
        } else { final(tree).layout_record(child) == old(tree).layout_record(child) },
    no_unwind
))]
pub(crate) fn wrapped<A: sizing_pass::Access + ?Sized>(tree: &mut A, child: A::Id, cross: Axis) -> bool {
    let params = tree.params(child);
    if !matches!(params.size.component(cross), Size::Fill) || params.free_placement
        || params.min_size.component(cross).is_some() || params.max_size.component(cross).is_some()
        || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        || tree.first(child).is_some()
    {
        return false;
    }
    let data = tree.record(child);
    if data.flags.check_state(cross, Kind::Regular) != UNSOLVED
        || data.flags.check_state(cross, Kind::Final) != UNSOLVED
    {
        return false;
    }
    let Some(parent) = tree.parent_id(child) else { return false; };
    let parent_data = tree.record(parent);
    if parent_data.flags.check_state(cross, Kind::Flow) != SOLVED
        || !matches!(tree.params(parent).children_layout, ChildrenLayout::Wrap { axis, .. } if axis.index() != cross.index())
    {
        return false;
    }
    let extent = A::Float::from_word(wrap_metrics::read_metric(&data.parent_flow, wrap_metrics::Metric::Cross));
    let size = inside_margins::<A::Float>(extent, margins::<A::Float>(params, cross));
    // The ordinary finish emits the warning for a non-finite size.
    if !A::Float::finite(size) { return false; }
    let level = dependency_level(parent_data, cross, Kind::Flow);
    tree.edit(child).publish_axis(cross, size, size, level);
    true
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(first =>
    requires live(tree, parent), tree.order().ordered(),
    ensures first.is_some() ==> tree.order().child(parent, first.unwrap()),
    no_unwind
))]
fn first_child<A: Records + ?Sized>(tree: &A, parent: A::Id) -> Option<A::Id> {
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(parent); }
    tree.first(parent)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires tree.order().child(parent, child), tree.order().ordered(),
    ensures next.is_some() ==> tree.order().child(parent, next.unwrap()),
        sizing_pass::remaining(tree.order(), parent, next) < sizing_pass::remaining(tree.order(), parent, Some(child)),
    no_unwind
))]
fn following<A: Records + ?Sized>(tree: &A, parent: A::Id, child: A::Id) -> Option<A::Id> {
    let _ = parent;
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(child); }
    tree.sibling(child)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(requires live(tree, node), no_unwind))]
fn track<A: Access + ?Sized>(tree: &A, node: A::Id, axis: Axis, count: f32, spacing: f32) -> GridTrack {
    let size = value(tree, node, axis, Kind::Final);
    GridTrack::new::<A::Float>(inner::<A::Float>(size, padding(tree.params(node), axis)), count, spacing)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn grid<A: Access + ?Sized>(tree: &mut A, node: A::Id, spacing: Xy<f32>) -> bool {
    let parent = tree.record(node);
    let flex = NodeFlags::FLEX_CHILD_X | NodeFlags::FLEX_CHILD_Y;
    if parent.flags.0 & flex != flex { return false; }
    let x = parent.values[slot_index(X, Kind::EvenShare)];
    let y = parent.values[slot_index(Y, Kind::Flow)];
    let width_track = track(tree, node, X, x, spacing.x);
    let height_track = track(tree, node, Y, y, spacing.y);
    let level_x = dependency_level(parent, X, Kind::Final);
    let level_y = dependency_level(parent, Y, Kind::Final);

    let mut next = first_child(tree, node);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(), live(tree, node),
            next.is_some() ==> tree.order().child(node, next.unwrap()),
        decreases sizing_pass::remaining(tree.order(), node, next),
    ))]
    while let Some(child) = next {
        next = following(tree, node, child);
        if tree.params(child).disabled { continue; }
        let params = tree.params(child);
        if params.free_placement || !matches!(params.size.x, Size::Fill) || !matches!(params.size.y, Size::Fill)
            || params.min_size.x.is_some() || params.min_size.y.is_some()
            || params.max_size.x.is_some() || params.max_size.y.is_some()
            || !matches!(params.children_layout, ChildrenLayout::Stack { .. } | ChildrenLayout::Free)
            || tree.first(child).is_some() || tree.record(child).flags.0 != NodeFlags::EMPTY.0
        {
            return false;
        }
        // Leave any already published prefix for the ordinary traversal to reuse.
        let width = inside_margins::<A::Float>(width_track.extent::<A::Float>(params.grid_span.x), margins::<A::Float>(params, X));
        let height = inside_margins::<A::Float>(height_track.extent::<A::Float>(params.grid_span.y), margins::<A::Float>(params, Y));
        if !A::Float::finite(width) || !A::Float::finite(height) { return false; }
        let data = tree.edit(child);
        data.publish_axis(X, width, width, level_x);
        data.publish_axis(Y, height, height, level_y);
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
enum Batch { Solved, General, PixelBounds }

#[cfg_attr(verus_keep_ghost, verus_verify)]
const LOCAL_BOUNDS: usize = 4;

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
enum LocalSize {
    Pixels { regular: f32, capped: bool },
    Fill { min: Option<f32>, max: Option<f32> },
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
struct LocalChild<I> {
    node: I,
    size: LocalSize,
    weight: f32,
    margins: [f32; 2],
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(item =>
    requires live(tree, node),
    ensures item.is_some() ==> item.unwrap().node == node,
    no_unwind
))]
fn local_child<A: Records + ?Sized>(tree: &A, node: A::Id, axis: Axis, cross: Axis) -> Option<LocalChild<A::Id>> {
    let params = tree.params(node);
    if params.disabled || params.free_placement || !A::Float::finite(params.fill_weight)
        || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
    {
        return None;
    }
    let data = tree.record(node);
    let flags = data.flags;
    if flags.0 & (NodeFlags::DESCENDANTS_NEED_SOLVE | NodeFlags::BLOCK_ITEM | NodeFlags::BLOCK_PARENT_AUTO_HEIGHT
        | NodeFlags::BLOCK_CONTAINER | NodeFlags::WRAP_CONTAINER) != 0
        || flags.check_state(cross, Kind::Final) != SOLVED || flags.check_state(axis, Kind::Final) != UNSOLVED
        || flags.check_state(axis, Kind::Min) != UNSOLVED || flags.check_state(axis, Kind::Max) != UNSOLVED
    {
        return None;
    }
    let min = *params.min_size.component(axis);
    let max = *params.max_size.component(axis);
    let size = match *params.size.component(axis) {
        Size::Pixels(_) => {
            let capped = match (min, max) {
                (Some(Size::Fill), None) => false,
                (None, Some(Size::Fill)) => true,
                _ => return None,
            };
            if flags.check_state(axis, Kind::Regular) != SOLVED { return None; }
            let regular_index = slot_index(axis, Kind::Regular);
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            if data.levels[regular_index] != 0 { return None; }
            let regular = data.values[regular_index];
            if !A::Float::finite(regular) { return None; }
            LocalSize::Pixels { regular, capped }
        }
        Size::Fill => {
            if flags.check_state(axis, Kind::Regular) != UNSOLVED { return None; }
            let min = match min {
                None => None,
                Some(Size::Pixels(value)) if A::Float::finite(value) => Some(value),
                _ => return None,
            };
            let max = match max {
                None => None,
                Some(Size::Pixels(value)) if A::Float::finite(value) => Some(value),
                _ => return None,
            };
            if matches!((min, max), (Some(a), Some(b)) if a > b) { return None; }
            LocalSize::Fill { min, max }
        }
        _ => return None,
    };
    Some(LocalChild { node, size, weight: params.fill_weight, margins: margins::<A::Float>(params, axis) })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn publish_local(data: &mut NodeLayoutData, axis: Axis, size: LocalSize, value: f32, final_size: f32, _share_level: u16) {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    let level = dependency_rules::next_level(_share_level);
    #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
    let level = 0;
    match size {
        LocalSize::Pixels { capped, .. } => {
            let bound = if capped { Kind::Max } else { Kind::Min };
            let bound_index = slot_index(axis, bound);
            let final_index = slot_index(axis, Kind::Final);
            cycle_rules::publish_finished_pair(&mut data.flags.0, &mut data.values, (bound_index, value), (final_index, final_size));
            #[cfg(any(feature = "incremental", verus_keep_ghost))]
            {
                data.levels[bound_index] = level;
                data.levels[final_index] = dependency_rules::next_level(level);
            }
        }
        LocalSize::Fill { min, max } => {
            if let Some(minimum) = min {
                let index = slot_index(axis, Kind::Min);
                data.publish_slot(index, minimum);
                #[cfg(any(feature = "incremental", verus_keep_ghost))]
                { data.levels[index] = 0; }
            }
            if let Some(maximum) = max {
                let index = slot_index(axis, Kind::Max);
                data.publish_slot(index, maximum);
                #[cfg(any(feature = "incremental", verus_keep_ghost))]
                { data.levels[index] = 0; }
            }
            data.publish_axis(axis, value, final_size, level);
        }
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires count <= LOCAL_BOUNDS,
    no_unwind
))]
fn local_results<A: Records + ?Sized>(children: &[Option<LocalChild<A::Id>>; LOCAL_BOUNDS], count: usize, share: f32,
    results: &mut [(f32, f32); LOCAL_BOUNDS],
) -> Option<bool> {
    if !A::Float::finite(share) { return None; }
    let mut constrained = false;
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant index <= count <= LOCAL_BOUNDS, decreases count-index))]
    while index < count {
        let item = children[index]?;
        let bound = share * item.weight;
        if !A::Float::finite(bound) { return None; }
        let final_size = match item.size {
            LocalSize::Pixels { regular, capped: false } => {
                constrained |= bound < regular;
                A::Float::max(regular, bound)
            }
            LocalSize::Pixels { regular, capped: true } => {
                constrained |= regular < bound;
                A::Float::min(regular, bound)
            }
            LocalSize::Fill { min, max } => {
                constrained |= matches!(min, Some(min) if bound < min) || matches!(max, Some(max) if max < bound);
                clamp::<A::Float>(bound, min, max)
            }
        };
        results[index] = (bound, final_size);
        index += 1;
    }
    Some(constrained)
}

#[cold]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(requires count <= LOCAL_BOUNDS, no_unwind))]
fn resolve_local_bounds<A: BoundRecords + ?Sized>(children: &[Option<LocalChild<A::Id>>; LOCAL_BOUNDS], count: usize, budget: f32,
    weight: f32,
) -> Option<f32> {
    let empty = fill::empty_fill();
    let mut fills = [empty, empty, empty, empty];
    let mut index = 0;
    let mut used = 0;
    let mut widest = None;
    #[cfg_attr(verus_keep_ghost, verus_spec(invariant used <= index <= count <= LOCAL_BOUNDS, decreases count-index))]
    while index < count {
        let item = children[index]?;
        index += 1;
        let (content, min, max, capped) = match item.size {
            LocalSize::Pixels { regular, capped } => (Some(regular), None, None, capped),
            LocalSize::Fill { min: None, max: None } => {
                let weight = A::BoundFloat::abs(item.weight);
                widest = Some(if let Some(old) = widest { <A::BoundFloat as FloatOps>::max(old, weight) } else { weight });
                continue;
            }
            LocalSize::Fill { min, max } => (None, min, max, false),
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(used < index); }
        fills[used] = fill::FillChild::new_with::<A::BoundFloat>(content, min, max, capped, item.weight);
        used += 1;
    }
    let fills: &mut [fill::FillChild] = &mut fills;
    Some(fill::resolve_fill_share_with::<A::BoundFloat>(fills.split_at_mut(used).0, budget, weight, widest))
}

/// A short list of ready pixel and Fill children can publish its bounds together.
/// The general path handles any child that needs additional sizing work.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn local_bounds<A: BoundRecords + ?Sized>(tree: &mut A, node: A::Id, axis: Axis) -> bool {
    let cross = axis.other();
    let mut next = first_child(tree, node);
    let own = inner::<A::Float>(value(tree, node, axis, Kind::Final), padding(tree.params(node), axis));
    let mut budget = fill_budget::after_gaps(own, stack_gaps(tree, node, axis));
    let mut weight = 0.0;
    let mut children: [Option<LocalChild<A::Id>>; LOCAL_BOUNDS] = [None, None, None, None];
    let mut count = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(), live(tree, node), count <= LOCAL_BOUNDS,
            next.is_some() ==> tree.order().child(node, next.unwrap()),
            forall |i: int| 0 <= i < count ==> (#[trigger] children[i]).is_some() && live(tree, children[i].unwrap().node),
        decreases LOCAL_BOUNDS-count,
    ))]
    while let Some(child) = next {
        if count == LOCAL_BOUNDS { return false; }
        next = following(tree, node, child);
        let Some(item) = local_child(tree, child, axis, cross) else { return false; };
        budget = fill_budget::charge(budget, item.margins[0] + item.margins[1]);
        weight += item.weight;
        children[count] = Some(item);
        count += 1;
    }
    if count == 0 { return false; }
    let budget = fill_budget::nonnegative(budget);
    let mut share = fill_budget::share(budget, 0.0, weight);
    let mut results = [(0.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.0, 0.0)];
    let Some(constrained) = local_results::<A>(&children, count, share, &mut results) else { return false; };
    // If every target already fits, every violation in the ordinary fold is
    // positive zero and it returns this exact first share.
    if constrained {
        let Some(adjusted) = resolve_local_bounds::<A>(&children, count, budget, weight) else { return false; };
        share = adjusted;
        if local_results::<A>(&children, count, share, &mut results).is_none() { return false; }
    }
    let share_level = publish_share(tree.edit(node), axis, share);
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= count <= LOCAL_BOUNDS, tree.order() == old(tree).order(),
            forall |i: int| 0 <= i < count ==> (#[trigger] children[i]).is_some() && live(tree, children[i].unwrap().node),
        decreases count-index,
    ))]
    while index < count {
        let Some(item) = children[index] else { return false; };
        let (bound, final_size) = results[index];
        publish_local(tree.edit(item.node), axis, item.size, bound, final_size, share_level);
        index += 1;
    }
    true
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(requires live(tree, node), no_unwind))]
fn stack_gaps<A: Records + ?Sized>(tree: &A, node: A::Id, axis: Axis) -> f32 {
    let (ChildrenLayout::Stack { axis: main, spacing, .. } | ChildrenLayout::Wrap { axis: main, spacing, .. })
        = tree.params(node).children_layout else { return 0.0; };
    if main.index() != axis.index() { return 0.0; }
    let n = tree.record(node).n_placed_children as f32;
    spacing * A::Float::max(n - 1.0, 0.0)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn seed_bound<A: Access + ?Sized>(tree: &mut A, node: A::Id, axis: Axis, kind: Kind, bound: Option<Size>) -> bool {
    let Some(bound) = bound else { return true; };
    let Size::Pixels(pixels) = bound else { return false; };
    let data = tree.edit(node);
    let index = slot_index(axis, kind);
    data.publish_slot(index, pixels);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { data.levels[index] = 0; }
    true
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn stack<A: Access + ?Sized, const PIXEL_BOUNDS: bool>(tree: &mut A, node: A::Id, axis: Axis) -> Batch {
    let first = first_child(tree, node);
    let own = inner::<A::Float>(value(tree, node, axis, Kind::Final), padding(tree.params(node), axis));
    let mut budget = fill_budget::after_gaps(own, stack_gaps(tree, node, axis));
    let mut total_weight = 0.0;
    let mut needs_cross = false;
    let cross = axis.other();
    let mut next = first;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(), live(tree, node),
            first.is_some() ==> tree.order().child(node, first.unwrap()),
            next.is_some() ==> tree.order().child(node, next.unwrap()),
        decreases sizing_pass::remaining(tree.order(), node, next),
    ))]
    while let Some(child) = next {
        next = following(tree, node, child);
        if tree.params(child).disabled { continue; }
        let params = tree.params(child);
        let flags = tree.record(child).flags;
        if params.free_placement || !matches!(params.size.component(axis), Size::Fill)
            || flags.0 & (NodeFlags::DESCENDANTS_NEED_SOLVE | NodeFlags::BLOCK_CONTAINER | NodeFlags::WRAP_CONTAINER) != 0
            || matches!(tree.params(child).children_layout,
                ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } if main_axis.index() == axis.index())
        {
            return Batch::General;
        }
        let min = *params.min_size.component(axis);
        let max = *params.max_size.component(axis);
        if !PIXEL_BOUNDS && (min.is_some() || max.is_some()) { return Batch::PixelBounds; }

        needs_cross |= flags.check_state(cross, Kind::Final) != SOLVED;
        if PIXEL_BOUNDS {
            // A pixel declaration has no dependencies or measurement callbacks.
            if !seed_bound(tree, child, axis, Kind::Min, min) || !seed_bound(tree, child, axis, Kind::Max, max) {
                return Batch::General;
            }
        } else {
            let [start, end] = margins::<A::Float>(params, axis);
            budget = fill_budget::charge(budget, start + end);
            total_weight += params.fill_weight;
        }
    }

    let share = if PIXEL_BOUNDS { tree.bounded_share(axis, budget, first) }
        else { fill_budget::share(fill_budget::nonnegative(budget), 0.0, total_weight) };
    let share_level = publish_share(tree.edit(node), axis, share);
    let mut next = first;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), tree.order().ordered(),
            next.is_some() ==> tree.order().child(node, next.unwrap()),
        decreases sizing_pass::remaining(tree.order(), node, next),
    ))]
    while let Some(child) = next {
        next = following(tree, node, child);
        if tree.params(child).disabled { continue; }
        let regular = share * tree.params(child).fill_weight;
        let (min, max) = if PIXEL_BOUNDS {
            (bound(tree, child, axis, Kind::Min), bound(tree, child, axis, Kind::Max))
        } else { (None, None) };
        let final_size = clamp::<A::Float>(regular, min, max);
        if !A::Float::finite(final_size) || matches!((min, max), (Some(a), Some(b)) if a > b) {
            // Exceptional values retain ordinary warning and measurement order.
            tree.slot(child, X, Kind::Final);
            tree.slot(child, Y, Kind::Final);
            continue;
        }
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        let level = dependency_rules::next_level(share_level);
        #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
        let level = { let _ = share_level; 0 };
        let data = tree.edit(child);
        data.publish_axis(axis, regular, final_size, level);
        if needs_cross && data.flags.check_state(cross, Kind::Final) != SOLVED {
            tree.slot(child, cross, Kind::Final);
        }
    }
    Batch::Solved
}

/// Publish a small, ready Fill batch without invoking the ordinary slot driver.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
pub(crate) fn ready_bounded_children<A: BoundRecords + ?Sized>(tree: &mut A, node: A::Id) -> bool {
    let ChildrenLayout::Stack { axis, .. } = tree.params(node).children_layout else { return false; };
    ready_bounds_on_axis(tree, node, axis)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn ready_bounds_on_axis<A: BoundRecords + ?Sized>(tree: &mut A, node: A::Id, axis: Axis) -> bool {
    let data = tree.record(node);
    let flags = data.flags;
    data.n_placed_children > 0 && data.n_placed_children <= LOCAL_BOUNDS as u32
        && flags.0 & (NodeFlags::BLOCK_CONTAINER | NodeFlags::WRAP_CONTAINER) == 0
        && flags.check_state(axis, Kind::Final) == SOLVED
        && flags.check_state(axis, Kind::EvenShare) == UNSOLVED
        && local_bounds(tree, node, axis)
}

/// Resolve a compatible group once the parent's geometry is ready.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
pub(crate) fn children<A: Access + ?Sized>(tree: &mut A, node: A::Id) -> bool {
    let axis = match tree.params(node).children_layout {
        ChildrenLayout::Stack { axis, .. } => axis,
        ChildrenLayout::Grid { columns: MainAxisCellSize::Count(_), spacing_x, spacing_y, .. } => {
            return grid(tree, node, Xy::new(spacing_x, spacing_y));
        }
        _ => return false,
    };
    let data = tree.record(node);
    let flags = data.flags;
    if flags.check_state(axis, Kind::EvenShare) != UNSOLVED {
        return false;
    }
    if ready_bounds_on_axis(tree, node, axis) { return true; }
    if flags.0 & NodeFlags::flex_child(axis) == 0 { return false; }
    match stack::<A, false>(tree, node, axis) {
        Batch::Solved => true,
        Batch::General => false,
        Batch::PixelBounds => matches!(stack::<A, true>(tree, node, axis), Batch::Solved),
    }
}
