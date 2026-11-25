//! Vertical writing uses the same scalar collapsing-margin and inline-position
//! kernels as horizontal block flow, with each request made on the context's
//! block and inline axes. The public physical Block format remains unchanged.
use super::driver::{Frame, FrameNode};
use crate::flow::{
    BlockFlow, BlockItem, BlockMargins, block_can_collapse, item_adjoins, zero_minimum,
};
use crate::placement_geometry::{RustFloat, block_inline_edges};
use crate::{
    Axis, ChildrenLayout, LogicalAxis, Margin, Size, TextContent, WritingMode, Xy, XyRect,
};

pub(super) fn vertical(node: &FrameNode) -> bool {
    node.base.children_layout == ChildrenLayout::Block
        && node.context.writing_mode != WritingMode::HorizontalTb
        && node.rule.flex.is_none()
        && node.rule.grid.is_none()
}

#[derive(Clone, Copy, Default)]
pub(super) struct Summary {
    margins: BlockMargins,
    content: Xy<f32>,
}

fn reversed<T>(mut pair: [T; 2], reverse: bool) -> [T; 2] {
    if reverse {
        pair.swap(0, 1);
    }
    pair
}

fn metric(value: Size, axis: Axis, available: f32, intrinsic: f32, other: f32) -> f32 {
    match value {
        Size::Pixels(length) => length,
        Size::Frac(fraction) => fraction * available,
        Size::Auto | Size::FitContent => intrinsic,
        Size::Fill => available,
        Size::AspectRatio(ratio) => {
            if axis == Axis::X {
                other * ratio
            } else {
                other / ratio
            }
        }
    }
}

fn constrain(
    node: &FrameNode,
    axis: Axis,
    value: f32,
    available: f32,
    intrinsic: f32,
    other: f32,
) -> f32 {
    let p = &node.base;
    let mut value = value.max(0.);
    if let Some(max) = p.max_size[axis] {
        value = value.min(metric(max, axis, available, intrinsic, other));
    }
    if let Some(min) = p.min_size[axis] {
        value = value.max(metric(min, axis, available, intrinsic, other));
    }
    value.max(p.padding[axis].iter().sum())
}

fn in_flow(node: &FrameNode) -> bool {
    !node.base.disabled && !node.base.free_placement
}

fn collapse_with(node: &FrameNode, parent: &FrameNode) -> bool {
    node.context.writing_mode == parent.context.writing_mode
        && block_can_collapse(&node.base)
        && node.rule.flex.is_none()
        && node.rule.grid.is_none()
}

fn replay(
    frame: &Frame<'_>,
    parent: usize,
    summaries: &[Summary],
    mut emit: impl FnMut(usize, XyRect),
) -> Summary {
    let node = &frame.nodes[parent];
    let block = node.context.axis(LogicalAxis::Block);
    let inline = block.other();
    let p = &node.base;
    let flip = p.children_origin_flipped;
    let available = frame.content_size(parent);
    let collapse = in_flow(node)
        && node.parent.is_some_and(|i| {
            let outer = &frame.nodes[i];
            vertical(outer) && collapse_with(node, outer)
        });
    let [pad_before, pad_after] = reversed(p.padding[block], flip[block]);
    let fit = matches!(p.size[block], Size::Auto | Size::FitContent);
    let mut flow = BlockFlow::from_edges(
        collapse && pad_before == 0.,
        collapse && pad_after == 0. && fit,
    );
    let mut intrinsic_inline = 0f32;
    for &id in &node.children {
        let child = &frame.nodes[id];
        if !in_flow(child) {
            continue;
        }
        let cp = &child.base;
        let inline_margin = cp.margin[inline].map(|m| m.as_px().unwrap_or(0.));
        let margin_sum: f32 = inline_margin.iter().sum();
        let mut natural = child.measured;
        if vertical(child) {
            for a in [Axis::X, Axis::Y] {
                natural[a] = summaries[id].content[a] + cp.padding[a].iter().sum::<f32>();
            }
        }
        let inline_available = available[inline] - margin_sum;
        let mut inline_size = match cp.size[inline] {
            Size::Auto | Size::Fill => inline_available,
            value => metric(
                value,
                inline,
                inline_available,
                natural[inline],
                natural[block],
            ),
        };
        inline_size = constrain(
            child,
            inline,
            inline_size,
            inline_available,
            natural[inline],
            natural[block],
        );
        let mut block_size = match cp.size[block] {
            Size::Fill if fit => natural[block],
            value => metric(value, block, available[block], natural[block], inline_size),
        };
        block_size = constrain(
            child,
            block,
            block_size,
            available[block],
            natural[block],
            inline_size,
        );
        if matches!(cp.size[inline], Size::AspectRatio(_)) {
            let candidate = metric(
                cp.size[inline],
                inline,
                inline_available,
                natural[inline],
                block_size,
            );
            inline_size = constrain(
                child,
                inline,
                candidate,
                inline_available,
                natural[inline],
                block_size,
            );
        }
        let independent = match cp.size[inline] {
            Size::Auto | Size::Frac(_) | Size::Fill => {
                constrain(child, inline, 0., 0., natural[inline], block_size)
            }
            _ => inline_size,
        };
        intrinsic_inline = intrinsic_inline.max(independent + margin_sum);
        let edges = reversed(
            cp.margin[block].map(|m| m.as_px().unwrap_or(0.)),
            flip[block],
        );
        let adjoining = item_adjoins(
            block_size == 0.,
            cp.padding[block].map(|v| v == 0.),
            collapse_with(child, node),
            zero_minimum(cp.min_size[block]),
        );
        let empty = !child.children.iter().any(|&i| in_flow(&frame.nodes[i]));
        let nested =
            (vertical(child) && collapse_with(child, node)).then_some(summaries[id].margins);
        let start = flow.push(BlockItem::from_edges(
            edges[0], edges[1], block_size, adjoining, empty, nested,
        ));
        let mut rect = Xy::new_symm([0.; 2]);
        rect[inline] = block_inline_edges::<RustFloat>(
            [0., available[inline]],
            inline_size,
            inline_margin,
            cp.margin[inline].map(|m| m == Margin::AUTO),
            flip[inline],
        );
        rect[block] = if flip[block] {
            [
                available[block] - start - block_size,
                available[block] - start,
            ]
        } else {
            [start, start + block_size]
        };
        emit(id, rect);
    }
    // A positive minimum separates the final child margin only when it binds.
    if let Some(minimum) = p.min_size[block] {
        let min = metric(minimum, block, available[block], 0., available[inline]);
        flow.collapse_bottom &= min <= pad_before + flow.end;
    }
    let (extent, margins) = flow.finish();
    let mut content = Xy::new_symm(0.);
    content[block] = extent;
    content[inline] = intrinsic_inline;
    if p.text != TextContent::None
        || p.image.is_some()
        || p.content_measure != crate::ContentMeasure::None
    {
        for a in [Axis::X, Axis::Y] {
            content[a] = content[a].max(node.natural[a] - p.padding[a].iter().sum::<f32>());
        }
    }
    Summary { margins, content }
}

pub(super) fn measure(frame: &mut Frame<'_>) -> Vec<Summary> {
    if !frame.nodes.iter().any(vertical) {
        return Vec::new();
    }
    let mut summaries = vec![Summary::default(); frame.nodes.len()];
    for i in (0..frame.nodes.len()).rev() {
        if frame.nodes[i].base.disabled || !vertical(&frame.nodes[i]) {
            continue;
        }
        let summary = replay(frame, i, &summaries, |_, _| {});
        summaries[i] = summary;
        frame.set_intrinsic(i, summary.content);
    }
    summaries
}

pub(super) fn place(frame: &mut Frame<'_>, parent: usize, summaries: &[Summary]) {
    let mut children = Vec::with_capacity(frame.nodes[parent].children.len());
    replay(frame, parent, summaries, |id, rect| {
        children.push((id, rect))
    });
    for (id, rect) in children {
        frame.place(id, parent, rect);
    }
}
