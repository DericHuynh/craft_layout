//! Translate measured native box declarations into a flexible formatting context.
use super::driver::Frame;
use crate::flex::{FlexBasis, FlexLayout, FlexMetrics};
use crate::{Axis, ChildrenLayout, Size, Xy};

pub(super) fn bound(
    size: Size,
    axis: Axis,
    inner: Xy<f32>,
    natural: Xy<f32>,
    allocated: Xy<f32>,
) -> f32 {
    match size {
        Size::Pixels(value) => value,
        Size::Frac(fraction) => inner[axis] * fraction,
        Size::Fill => inner[axis],
        Size::Auto | Size::FitContent => natural[axis],
        Size::AspectRatio(ratio) => match axis {
            Axis::X => allocated.y * ratio,
            Axis::Y => allocated.x / ratio,
        },
    }
}

pub(super) fn apply(frame: &mut Frame<'_>, parent: usize, layout: FlexLayout) {
    let axis = layout.axis;
    let cross = axis.other();
    let inner = frame.content_size(parent);
    let mut children = Vec::new();
    let mut metrics = Vec::new();
    for &id in &frame.nodes[parent].children {
        let node = &frame.nodes[id];
        let p = &node.base;
        if p.disabled || p.free_placement || node.rule.placement.out_of_flow() {
            continue;
        }
        let mut preferred = node.natural;
        let mut min = Xy::new_symm(0.0);
        let mut max = Xy::new_symm(f32::INFINITY);
        for a in [Axis::X, Axis::Y] {
            preferred[a] = match p.size[a] {
                Size::FitContent | Size::Auto | Size::Fill if a == cross => node.measured[a],
                Size::Fill => node.natural[a],
                other => bound(other, a, inner, node.natural, super::size(node.rect)),
            };
            if let Some(s) = p.min_size[a] {
                min[a] = bound(s, a, inner, node.natural, super::size(node.rect));
            }
            if let Some(s) = p.max_size[a] {
                max[a] = bound(s, a, inner, node.natural, super::size(node.rect));
            }
        }
        let mut item = node.rule.flex_item;
        if matches!(p.size[axis], Size::Fill)
            && item.basis == FlexBasis::Preferred
            && item.grow == 0.0
            && item.shrink == 0.0
        {
            item.basis = FlexBasis::Pixels(0.0);
            item.grow = p.fill_weight;
        }
        children.push(id);
        metrics.push(FlexMetrics {
            item,
            preferred,
            content_main: node.natural[axis],
            min,
            max,
            padding: p.padding,
            margin: p.margin,
            stretch_cross: matches!(p.size[cross], Size::Auto | Size::Fill),
            first_baseline: node.rule.baselines.x,
            last_baseline: node.rule.baselines.y,
        });
    }
    let mut intrinsic = inner;
    intrinsic[axis] = layout.intrinsic_main(&metrics);
    frame.set_intrinsic(parent, intrinsic);
    let inner = frame.content_size(parent);
    let (mut rects, natural_cross) = layout.resolve_and_measure(inner, &metrics);
    intrinsic[cross] = natural_cross;
    frame.set_intrinsic(parent, intrinsic);
    let adjusted = frame.content_size(parent);
    if adjusted != inner {
        rects = layout.resolve(adjusted, &metrics);
    }
    frame.nodes[parent].effective.children_layout = ChildrenLayout::Free;
    for (child, rect) in children.into_iter().zip(rects) {
        frame.place(child, parent, rect);
    }
}
