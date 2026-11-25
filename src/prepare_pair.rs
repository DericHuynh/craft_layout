//! Complete small stacks with ready pixel and Fill leaves.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, ChildrenLayout, ContentMeasure, LayoutParams, Size, TextContent};
#[cfg(not(verus_keep_ghost))]
use crate::fill_budget;
use crate::node_data::NodeLayoutData;
use crate::node_flags::{NodeFlags, slot_index};
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::Pos;
use crate::prepare_frame::{self, FrameFloat};
use crate::prepare_nodes::Records;
#[cfg(not(verus_keep_ghost))]
use crate::{placement_geometry::FloatBounds, solve::{
    cycle_rules::Kind, fill_compaction as fill, sizing_fill::BoundRecords,
    sizing_finish::{clamp, inner, padding},
}};
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel::Kind, dependencies::sizing_finish::{clamp, inner, padding},
    fill::{budget as fill_budget, kernel as fill}, placement::geometry::FloatBounds,
    prepare_nodes::live, sizing_fill::BoundRecords};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use fill::FloatOps;

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn ready_pair_records<T: Records + ?Sized>(tree: &T, parent: T::Id) -> bool {
    let links = crate::placement::node::PlacementLinks::from_order(tree.order());
    match links.leaf_pair(parent) {
        Some((first, second)) => tree.layout_record(first).placement == crate::placement::kernel::PlacementWork::Clean
            && tree.layout_record(second).placement == crate::placement::kernel::PlacementWork::Clean,
        None => false,
    }
}

pub(crate) open spec fn pair_marker<T: Records + ?Sized>(tree: &T, parent: T::Id) -> bool {
    tree.layout_record(parent).prepared_placement & NodeLayoutData::PREPARED_PAIR != 0
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct BoundedLeaf {
    main: f32,
    cross: f32,
    margins: f32,
    outer_cross: f32,
    weight: f32,
    bound: Kind,
    spans: bool,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    start: bool,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn leaf<F: FrameFloat>(params: &LayoutParams, axis: Axis) -> Option<BoundedLeaf> {
    let cross = axis.other();
    let Size::Pixels(main) = *params.size.component(axis) else { return None; };
    let Size::Pixels(cross_size) = *params.size.component(cross) else { return None; };
    let bound = match (*params.min_size.component(axis), *params.max_size.component(axis)) {
        (Some(Size::Fill), None) => Kind::Min,
        (None, Some(Size::Fill)) => Kind::Max,
        _ => return None,
    };
    if params.disabled || params.free_placement
        || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        || params.min_size.component(cross).is_some() || params.max_size.component(cross).is_some()
        || !F::finite(main) || !F::finite(cross_size) || !F::finite(params.fill_weight)
    {
        return None;
    }
    let [main_start, main_end] = *params.margin.component(axis);
    let [cross_start, cross_end] = *params.margin.component(cross);
    let margins = F::margin(main_start) + F::margin(main_end);
    let cross_margins = F::margin(cross_start) + F::margin(cross_end);
    let outer_cross = if cross_margins == 0.0 { cross_size } else { cross_size + cross_margins };
    Some(BoundedLeaf {
        main, cross: cross_size, margins, outer_cross, weight: params.fill_weight, bound,
        spans: params.grid_span.x > 1 || params.grid_span.y > 1,
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        start: matches!(*params.position.component(cross), Pos::Start)
            && main_start.is_zero() && main_end.is_zero() && cross_start.is_zero() && cross_end.is_zero(),
    })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn target<F: FrameFloat>(leaf: &BoundedLeaf, share: f32) -> Option<(f32, f32)> {
    let bound = share * leaf.weight;
    if !F::finite(bound) { return None; }
    let final_size = match leaf.bound {
        Kind::Min if bound >= leaf.main => F::max(leaf.main, bound),
        Kind::Max if bound <= leaf.main => F::min(leaf.main, bound),
        _ => return None,
    };
    Some((bound, final_size))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(data =>
    ensures data.placement == crate::placement::kernel::PlacementWork::Clean,
    no_unwind
))]
fn publish_leaf<T: Records + ?Sized>(axis: Axis, leaf: &BoundedLeaf, bound: f32, size: f32) -> NodeLayoutData {
    let mut data = T::empty_record();
    let bound_index = slot_index(axis, leaf.bound);
    data.publish_axis(axis, leaf.main, size, 0);
    data.publish_axis(axis.other(), leaf.cross, leaf.cross, 0);
    data.publish_slot(bound_index, bound);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    {
        data.levels[bound_index] = 3;
        data.levels[slot_index(axis, Kind::Final)] = 4;
    }
    data
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
        result.is_some() && pair_marker(final(tree), node) ==> ready_pair_records(final(tree), node),
    no_unwind
))]
pub(crate) fn ready<T: BoundRecords + ?Sized>(tree: &mut T, node: T::Id) -> Option<(Axis, f32)> {
    let params = tree.params(node);
    let ChildrenLayout::Stack { axis, spacing, .. } = params.children_layout else { return None; };
    match axis {
        Axis::X => ready_on_axis::<T, true>(tree, node, spacing),
        Axis::Y => ready_on_axis::<T, false>(tree, node, spacing),
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
        result.is_some() && pair_marker(final(tree), node) ==> ready_pair_records(final(tree), node),
    no_unwind
))]
fn ready_on_axis<T: BoundRecords + ?Sized, const HORIZONTAL: bool>(
    tree: &mut T, node: T::Id, spacing: f32,
) -> Option<(Axis, f32)> {
    let axis = if HORIZONTAL { Axis::X } else { Axis::Y };
    let cross = axis.other();
    let params = tree.params(node);
    let Size::Pixels(main) = *params.size.component(axis) else { return None; };
    if !matches!(*params.size.component(cross), Size::FitContent)
        || params.disabled || !matches!(params.text, TextContent::None)
        || !matches!(params.content_measure, ContentMeasure::None)
        || params.min_size.x.is_some() || params.max_size.x.is_some()
        || params.min_size.y.is_some() || params.max_size.y.is_some()
        || !T::Float::finite(main) || !T::Float::finite(spacing)
    {
        return None;
    }

    let first = tree.first(node)?;
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(node); }
    let first_params = tree.params(first);
    if matches!(*first_params.size.component(axis), Size::Fill) {
        return regular_fill(tree, node, first, axis, spacing, main);
    }
    let a = leaf::<T::Float>(first_params, axis)?;
    let second = tree.sibling(first)?;
    let b = leaf::<T::Float>(tree.params(second), axis)?;
    if tree.sibling(second).is_some() || tree.first(first).is_some() || tree.first(second).is_some() {
        return None;
    }
    let main_padding = padding(params, axis);
    let cross_padding = padding(params, cross);
    if !T::Float::finite(main_padding) || !T::Float::finite(cross_padding) { return None; }
    let available = fill_budget::after_gaps(inner::<T::Float>(main, main_padding), spacing);
    let available = fill_budget::charge(fill_budget::charge(available, a.margins), b.margins);
    let weight = (0.0 + a.weight) + b.weight;
    let share = fill_budget::share(fill_budget::nonnegative(available), 0.0, weight);
    if !T::Float::finite(share) { return None; }
    // If neither tentative target crosses its opposite pixel limit,
    // the ordered Fill resolver returns this first share unchanged.
    let (a_bound, a_size) = target::<T::Float>(&a, share)?;
    let (b_bound, b_size) = target::<T::Float>(&b, share)?;
    let max_cross = T::Float::max(T::Float::max(0.0, a.outer_cross), b.outer_cross);
    let flags = if a.spans || b.spans { NodeFlags::GRID_SPANS } else { 0 };
    #[allow(unused_mut)]
    let mut data = publish_parent::<T>(params, axis, main, spacing, cross_padding, max_cross, flags, share)?;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if a.start && b.start { data.prepared_placement |= NodeLayoutData::PREPARED_PAIR; }
    *tree.edit(first) = publish_leaf::<T>(axis, &a, a_bound, a_size);
    *tree.edit(second) = publish_leaf::<T>(axis, &b, b_bound, b_size);
    let cross = axis.other();
    let fit = data.values[slot_index(cross, Kind::Regular)];
    *tree.edit(node) = data;
    Some((cross, fit))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.is_some() ==> result.unwrap().prepared_placement == 0,
    no_unwind
))]
fn publish_parent<T: Records + ?Sized>(params: &LayoutParams, axis: Axis, main: f32, spacing: f32,
    cross_padding: f32, max_cross: f32, flags: u32, share: f32,
) -> Option<NodeLayoutData> {
    let cross = axis.other();
    let mut data = T::empty_record();
    data.flags.0 = flags;
    data.n_placed_children = 2;
    data.publish_axis(axis, main, main, 0);
    prepare_frame::publish_fit::<T::Float>(cross, max_cross, params.image, Some(axis), spacing, 2, cross_padding,
        &mut data.flags.0, &mut data.values,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] &mut data.levels,
        #[cfg(any(feature = "incremental", verus_keep_ghost))] 1);
    let fit = data.values[slot_index(cross, Kind::Regular)];
    if !T::Float::finite(fit) { return None; }
    data.publish_axis(cross, fit, fit, 1);
    let share_index = slot_index(axis, Kind::EvenShare);
    data.publish_slot(share_index, share);
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { data.levels[share_index] = 2; }
    Some(data)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct FillLeaf {
    min: Option<f32>,
    max: Option<f32>,
    cross: f32,
    margins: f32,
    outer_cross: f32,
    weight: f32,
    spans: bool,
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    start: bool,
}
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn pixel_bound<F: FrameFloat>(size: Option<Size>) -> Option<Option<f32>> {
    match size {
        None => Some(None),
        Some(Size::Pixels(value)) if F::finite(value) => Some(Some(value)),
        _ => None,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn fill_leaf<F: FrameFloat>(params: &LayoutParams, axis: Axis) -> Option<FillLeaf> {
    let cross = axis.other();
    if !matches!(*params.size.component(axis), Size::Fill) { return None; }
    let Size::Pixels(cross_size) = *params.size.component(cross) else { return None; };
    if params.disabled || params.free_placement
        || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        || params.min_size.component(cross).is_some() || params.max_size.component(cross).is_some()
        || !F::finite(cross_size) || !F::finite(params.fill_weight)
    {
        return None;
    }
    let min = pixel_bound::<F>(*params.min_size.component(axis))?;
    let max = pixel_bound::<F>(*params.max_size.component(axis))?;
    if matches!((min, max), (Some(a), Some(b)) if a > b) { return None; }
    let [main_start, main_end] = *params.margin.component(axis);
    let [cross_start, cross_end] = *params.margin.component(cross);
    let margins = F::margin(main_start) + F::margin(main_end);
    let cross_margins = F::margin(cross_start) + F::margin(cross_end);
    let outer_cross = if cross_margins == 0.0 { cross_size } else { cross_size + cross_margins };
    Some(FillLeaf {
        min, max, cross: cross_size, margins, outer_cross, weight: params.fill_weight,
        spans: params.grid_span.x > 1 || params.grid_span.y > 1,
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        start: matches!(*params.position.component(cross), Pos::Start)
            && main_start.is_zero() && main_end.is_zero() && cross_start.is_zero() && cross_end.is_zero(),
    })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(data =>
    ensures data.placement == crate::placement::kernel::PlacementWork::Clean,
    no_unwind
))]
fn filled_leaf<T: Records + ?Sized>(axis: Axis, leaf: &FillLeaf, regular: f32) -> NodeLayoutData {
    let mut data = T::empty_record();
    if let Some(min) = leaf.min { data.publish_slot(slot_index(axis, Kind::Min), min); }
    if let Some(max) = leaf.max { data.publish_slot(slot_index(axis, Kind::Max), max); }
    let size = clamp::<T::Float>(regular, leaf.min, leaf.max);
    data.publish_axis(axis, regular, size, 3);
    data.publish_axis(axis.other(), leaf.cross, leaf.cross, 0);
    data
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), node), live(old(tree), first), old(tree).order().ordered(),
        (old(tree).order().first)(node) == Some(first),
    ensures final(tree).order() == old(tree).order(),
        result.is_some() && pair_marker(final(tree), node) ==> ready_pair_records(final(tree), node),
    no_unwind
))]
fn regular_fill<T: BoundRecords + ?Sized>(tree: &mut T, node: T::Id, first: T::Id, axis: Axis, spacing: f32, main: f32) -> Option<(Axis, f32)> {
    let second = tree.sibling(first)?;
    if tree.sibling(second).is_some() || tree.first(first).is_some() || tree.first(second).is_some() {
        return None;
    }
    let a = fill_leaf::<T::Float>(tree.params(first), axis)?;
    let b = fill_leaf::<T::Float>(tree.params(second), axis)?;
    let a_bound = a.min.is_some() || a.max.is_some();
    let b_bound = b.min.is_some() || b.max.is_some();
    let params = tree.params(node);
    let main_padding = padding(params, axis);
    let cross_padding = padding(params, axis.other());
    if !T::Float::finite(main_padding) || !T::Float::finite(cross_padding) { return None; }
    let available = fill_budget::after_gaps(inner::<T::Float>(main, main_padding), spacing);
    let available = fill_budget::nonnegative(fill_budget::charge(fill_budget::charge(available, a.margins), b.margins));
    let weight = (0.0 + a.weight) + b.weight;
    let share = match (a_bound, b_bound) {
        (true, true) => return None,
        (false, false) => fill_budget::share(available, 0.0, weight),
        _ => {
            let (bounded, other) = if a_bound { (&a, &b) } else { (&b, &a) };
            let terms = fill::FillChild::new_with::<T::BoundFloat>(None, bounded.min, bounded.max, false, bounded.weight);
            fill::single_constraint_share::<T::BoundFloat>(terms, available, weight, Some(T::BoundFloat::abs(other.weight)))?
        }
    };

    let a_size = share * a.weight;
    let b_size = share * b.weight;
    if !T::Float::finite(a_size) || !T::Float::finite(b_size) { return None; }
    let max_cross = T::Float::max(T::Float::max(0.0, a.outer_cross), b.outer_cross);
    let spans = if a.spans || b.spans { NodeFlags::GRID_SPANS } else { 0 };
    #[allow(unused_mut)]
    let mut data = publish_parent::<T>(params, axis, main, spacing, cross_padding, max_cross, spans | NodeFlags::flex_child(axis), share)?;
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    if a.start && b.start { data.prepared_placement |= NodeLayoutData::PREPARED_PAIR; }
    *tree.edit(first) = filled_leaf::<T>(axis, &a, a_size);
    *tree.edit(second) = filled_leaf::<T>(axis, &b, b_size);
    let cross = axis.other();
    let fit = data.values[slot_index(cross, Kind::Regular)];
    *tree.edit(node) = data;
    Some((cross, fit))
}

#[cfg(all(test, feature = "incremental", not(verus_keep_ghost)))]
#[test]
fn ready_fill_pair_preserves_resolver_values_and_ranks() {
    use crate::{Arrange, LayoutData, TreeAdapter, XyRect, declarations::{Margin, X, Xy, Y},
        prepare_nodes::RetainedSizing, solve::Solve};

    #[derive(Clone)]
    struct Fixture {
        params: [LayoutParams; 3],
        records: [NodeLayoutData; 3],
        layout: LayoutData<usize>,
    }

    impl TreeAdapter for Fixture {
        type NodeId = usize;
        fn root(&self) -> usize { 0 }
        fn parent(&self, node: usize) -> Option<usize> { (node != 0).then_some(0) }
        fn first_child(&self, node: usize) -> Option<usize> { (node == 0).then_some(1) }
        fn next_sibling(&self, node: usize) -> Option<usize> { (node == 1).then_some(2) }
        fn node_layout_params(&self, node: usize) -> &LayoutParams { &self.params[node] }
        fn node_layout_data(&self, node: usize) -> &NodeLayoutData { &self.records[node] }
        fn node_layout_data_mut(&mut self, node: usize) -> &mut NodeLayoutData { &mut self.records[node] }
        fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }
        fn write_output_rect(&mut self, _: usize, _: XyRect, _: XyRect) {}
    }

    for axis in [X, Y] {
        for (minimum, maximum) in [(Some(91.25), None), (None, Some(26.5))] {
            let mut root = LayoutParams {
                size: Xy::new_symm(Size::FitContent),
                children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: 1.25 },
                ..LayoutParams::DEFAULT
            };
            root.size[axis] = Size::Pixels(108.5);
            root.padding[axis] = [2.25, 1.75];
            let mut first = LayoutParams { size: Xy::new_symm(Size::Fill), fill_weight: 1.25, ..LayoutParams::DEFAULT };
            first.size[axis.other()] = Size::Pixels(16.25);
            first.margin[axis] = [Margin::px(-0.25).unwrap(), Margin::px(0.75).unwrap()];
            let mut second = first;
            second.fill_weight = 2.5;
            second.size[axis.other()] = Size::Pixels(13.5);
            second.min_size[axis] = minimum.map(Size::Pixels);
            second.max_size[axis] = maximum.map(Size::Pixels);
            let mut tree = Fixture {
                params: [root, first, second], records: [NodeLayoutData::new(); 3], layout: LayoutData::new(),
            };
            let mut ordinary = tree.clone();

            assert!(ready(&mut tree, 0).is_some());
            ordinary.prepare::<true, false>(0, None, &mut RetainedSizing::default());
            for node in 0..3 {
                ordinary.solve_slot(node, X, Kind::Final);
                ordinary.solve_slot(node, Y, Kind::Final);
            }
            for (actual, expected) in tree.records.iter().zip(&ordinary.records) {
                // The pair has already finished its children.
                assert_eq!(actual.flags.0, expected.flags.0 & !NodeFlags::DESCENDANTS_NEED_SOLVE);
                assert_eq!(actual.values.map(f32::to_bits), expected.values.map(f32::to_bits));
                assert_eq!(actual.levels, expected.levels);
            }
        }
    }
}

#[cfg(all(test, feature = "incremental", not(verus_keep_ghost)))]
#[test]
fn ready_pair_placement_matches_the_general_write_order_and_rectangle_bits() {
    use crate::{Arrange, LayoutData, PixelScale, Place, TreeAdapter, XyRect, declarations::{X, Xy, Y}};

    struct Fixture {
        params: [LayoutParams; 6],
        records: [NodeLayoutData; 6],
        layout: LayoutData<usize>,
        writes: Vec<(usize, Xy<[u32; 2]>, Xy<[u32; 2]>)>,
    }

    impl TreeAdapter for Fixture {
        type NodeId = usize;

        fn root(&self) -> usize { 0 }
        fn parent(&self, node: usize) -> Option<usize> { [None, Some(0), Some(0), Some(2), Some(2), Some(0)][node] }
        fn first_child(&self, node: usize) -> Option<usize> { [Some(1), None, Some(3), None, None, None][node] }
        fn next_sibling(&self, node: usize) -> Option<usize> { [None, Some(2), Some(5), Some(4), None, None][node] }
        fn node_layout_params(&self, node: usize) -> &LayoutParams { &self.params[node] }
        fn node_layout_data(&self, node: usize) -> &NodeLayoutData { &self.records[node] }
        fn node_layout_data_mut(&mut self, node: usize) -> &mut NodeLayoutData { &mut self.records[node] }
        fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }
        fn write_output_rect(&mut self, node: usize, rect: XyRect, local: XyRect) {
            let bits = |rect: XyRect| Xy::new(rect.x.map(f32::to_bits), rect.y.map(f32::to_bits));
            self.writes.push((node, bits(rect), bits(local)));
        }
    }

    for axis in [X, Y] {
        let mode = ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: 1.25 };
        let root = LayoutParams { size: Xy::new_symm(Size::Pixels(250.0)), children_layout: mode, ..LayoutParams::DEFAULT };
        let leading = LayoutParams { size: Xy::new_symm(Size::Pixels(13.5)), ..LayoutParams::DEFAULT };
        let mut parent = LayoutParams { size: Xy::new_symm(Size::FitContent), children_layout: mode, ..LayoutParams::DEFAULT };
        parent.size[axis] = Size::Pixels(100.0);
        parent.padding[axis] = [2.25, 1.0];
        parent.padding[axis.other()] = [-0.0, 0.25];
        let mut first = LayoutParams {
            size: Xy::new_symm(Size::Pixels(10.0)), position: Xy::new_symm(Pos::Start), ..LayoutParams::DEFAULT
        };
        first.min_size[axis] = Some(Size::Fill);
        let mut second = first;
        second.size[axis.other()] = Size::Pixels(-0.0);
        let mut tree = Fixture {
            params: [root, leading, parent, first, second, leading],
            records: [NodeLayoutData::new(); 6],
            layout: LayoutData::new(),
            writes: Vec::new(),
        };

        for scale in [None, PixelScale::new(1.25)] {
            tree.layout.set_pixel_scale(scale);
            tree.solve_layout(Xy::new_symm(250.0));
            assert_ne!(tree.records[2].prepared_placement & NodeLayoutData::PREPARED_PAIR, 0);
            assert!(tree.writes.iter().map(|item| item.0).eq(0..6));
            let fresh = std::mem::take(&mut tree.writes);
            tree.place_nodes::<false>();
            assert_eq!(fresh, tree.writes);
            tree.writes.clear();
        }
    }
}
