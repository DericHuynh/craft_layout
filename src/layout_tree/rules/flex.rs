//! Translate measured native box declarations into a flexible formatting context.
use super::driver::Frame;
use crate::flex::{FlexAlign, FlexBasis, FlexLayout, FlexMetrics};
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

pub(super) fn uses_baseline(rule: &super::NodeRules) -> bool {
    use crate::tracks::{GridAlign, TrackGrid};
    let flex = |a: FlexAlign| matches!(a, FlexAlign::FirstBaseline | FlexAlign::LastBaseline);
    let grid = |a: GridAlign| matches!(a, GridAlign::FirstBaseline | GridAlign::LastBaseline);
    let grid_uses = |g: &TrackGrid| grid(g.align_items.x) || grid(g.align_items.y);
    rule.flex.is_some_and(|f| flex(f.align_items))
        || rule.flex_item.align_self.is_some_and(flex)
        || rule.grid.as_ref().is_some_and(grid_uses)
        || rule.grid_item.align.x.is_some_and(grid)
        || rule.grid_item.align.y.is_some_and(grid)
        || rule.queries.iter().any(|q| match &q.style.layout {
            Some(super::QueryLayout::Flex(f)) => flex(f.align_items),
            Some(super::QueryLayout::Grid(g)) => grid_uses(g),
            _ => false,
        })
}

/// A block can forward a descendant's baseline. A flex line or grid track
/// can also synthesize one from its chosen child's far border. Keep this
/// distinction while computing each descendant exactly once in reverse order.
pub(super) fn collect_baselines(frame: &mut Frame<'_>) -> bool {
    let mut changed = false;
    for i in (0..frame.nodes.len()).rev() {
        let node = &frame.nodes[i];
        let mut baselines = Xy::new_symm([None; 2]);
        for axis in [Axis::X, Axis::Y] {
            for last in [false, true] {
                let edge = usize::from(last);
                let offset = |child: usize| {
                    let c = &frame.nodes[child];
                    c.allocation_origin
                        .map_or(c.rect[axis][0] - node.rect[axis][0], |p| p[axis])
                };
                let inherited = |child: usize| {
                    let c = &frame.nodes[child];
                    offset(child)
                        + c.exported_baselines[axis][edge]
                            .unwrap_or_else(|| super::size(c.rect)[axis])
                };
                let eligible = |&&child: &&usize| {
                    let c = &frame.nodes[child];
                    !c.base.disabled && !c.base.free_placement && !c.rule.placement.out_of_flow()
                };
                let supplied = if last {
                    node.rule.baselines.y
                } else {
                    node.rule.baselines.x
                };
                let value = supplied.or_else(|| {
                    if node.rule.block_flow.contain_layout {
                        return None;
                    }
                    if let Some(layout) = node.rule.flex {
                        let main = node
                            .rule
                            .logical
                            .main_axis
                            .map_or(layout.axis, |a| node.context.axis(a));
                        return node
                            .flex_baseline_items
                            .map(|items| inherited(items[usize::from(main != axis)][edge]));
                    }
                    if node.rule.grid.is_some()
                        && let Some(items) = node.grid_baseline_items
                    {
                        return Some(inherited(items[axis][edge]));
                    }
                    if node.base.children_layout == ChildrenLayout::Block {
                        let baseline = |&child: &usize| {
                            frame.nodes[child].exported_baselines[axis][edge]
                                .map(|v| offset(child) + v)
                        };
                        return if last {
                            node.children
                                .iter()
                                .rev()
                                .filter(eligible)
                                .find_map(baseline)
                        } else {
                            node.children.iter().filter(eligible).find_map(baseline)
                        };
                    }
                    let reverse = match node.base.children_layout {
                        ChildrenLayout::Stack { axis: main, .. }
                        | ChildrenLayout::Wrap { axis: main, .. }
                            if axis == main =>
                        {
                            node.base.children_origin_flipped[axis]
                        }
                        _ => false,
                    };
                    if last ^ reverse {
                        node.children.iter().rev().find(eligible)
                    } else {
                        node.children.iter().find(eligible)
                    }
                    .copied()
                    .map(inherited)
                });
                baselines[axis][edge] = if matches!(
                    node.rule.scroll.overflow[axis],
                    super::Overflow::Hidden | super::Overflow::Scroll | super::Overflow::Auto
                ) {
                    value.map(|v| v.clamp(0., super::size(node.rect)[axis].max(0.)))
                } else {
                    value
                };
            }
        }
        changed |= baselines != node.exported_baselines;
        frame.nodes[i].exported_baselines = baselines;
    }
    changed
}

pub(super) fn exported_baseline(
    frame: &Frame<'_>,
    node: usize,
    axis: Axis,
    last: bool,
) -> Option<f32> {
    frame.nodes[node].exported_baselines[axis][usize::from(last)]
}

pub(super) fn apply(frame: &mut Frame<'_>, parent: usize, layout: FlexLayout) {
    let axis = layout.axis;
    let cross = axis.other();
    let inner = frame.content_size(parent);
    let container = &frame.nodes[parent];
    // An explicitly sized ancestor can allocate flex space in two phases.
    // Follow the assigned flex chain until the first definite declaration;
    // otherwise a percentage basis would depend on the line it is creating.
    let mut owner = parent;
    let intrinsic_basis = loop {
        let n = &frame.nodes[owner];
        if !frame.is_intrinsic(owner, axis, n.base.size[axis])
            || matches!(n.base.min_size[axis], Some(Size::Pixels(_) | Size::Frac(_)))
        {
            break false;
        }
        if let Some(outer) = n.parent
            && n.assigned
            && frame.nodes[outer].rule.flex.is_some()
        {
            owner = outer;
        } else {
            break true;
        }
    };
    let auto_cross = !matches!(
        container.base.size[cross],
        Size::Pixels(_) | Size::AspectRatio(_)
    );
    let mut relative_preferences = Vec::new();
    let mut intrinsic_cross_corrections = Vec::new();
    let mut children = Vec::new();
    let mut metrics = Vec::new();
    for &id in &frame.nodes[parent].children {
        let node = &frame.nodes[id];
        let p = &node.base;
        if p.disabled || p.free_placement || node.rule.placement.out_of_flow() {
            continue;
        }
        let mut natural = node.natural;
        if node.content_dependency[axis] {
            natural[axis] = node.measured[axis];
        }
        let mut preferred = natural;
        let mut min = Xy::new_symm(0.0);
        let mut max = Xy::new_symm(f32::INFINITY);
        for a in [Axis::X, Axis::Y] {
            preferred[a] = match p.size[a] {
                Size::FitContent | Size::Auto | Size::Fill if a == cross => node.measured[a],
                Size::Fill => node.natural[a],
                other => bound(other, a, inner, natural, super::size(node.rect)),
            };
            if let Some(s) = p.min_size[a] {
                min[a] = bound(s, a, inner, natural, super::size(node.rect));
            }
            if let Some(s) = p.max_size[a] {
                max[a] = bound(s, a, inner, natural, super::size(node.rect));
            }
        }
        if let Some(floor) = node.rule.flex_fit_cross
            && p.size[cross] == Size::FitContent
        {
            let line_count = match layout.wrap {
                crate::flex::FlexWrap::Balance { lines, .. } => f32::from(lines.max(1)),
                _ => 1.,
            };
            if !frame.is_intrinsic(parent, cross, frame.nodes[parent].base.size[cross])
                || frame.nodes[parent].assigned
            {
                let room = (inner[cross] - layout.line_gap * (line_count - 1.)) / line_count;
                let margins = p.margin[cross]
                    .iter()
                    .filter_map(|m| m.as_px())
                    .sum::<f32>();
                preferred[cross] = preferred[cross].min((room - margins).max(floor));
            }
        }
        // A ratio reads its resolved opposite dimension. Percentages may change
        // without changing this node's previous allocated rectangle.
        if let Size::AspectRatio(ratio) = p.size[axis] {
            let driving = preferred[cross].min(max[cross]).max(min[cross]);
            preferred[axis] = if axis == Axis::X {
                driving * ratio
            } else {
                driving / ratio
            };
        }
        let mut item = node.rule.flex_item;
        if intrinsic_basis
            && matches!(
                item.basis,
                FlexBasis::Fraction(_) | FlexBasis::FractionPlus(_, _)
            )
        {
            item.basis = FlexBasis::Content;
        }
        if auto_cross && node.relative_size(cross) && preferred[cross] != natural[cross] {
            intrinsic_cross_corrections.push((metrics.len(), natural[cross]));
        }
        if matches!(p.size[axis], Size::Fill)
            && item.basis == FlexBasis::Preferred
            && item.grow == 0.0
            && item.shrink == 0.0
        {
            item.basis = FlexBasis::Pixels(0.0);
            item.grow = p.fill_weight;
        }
        if node.relative_size(axis) && preferred[axis] != natural[axis] {
            relative_preferences.push((metrics.len(), preferred[axis], natural[axis]));
        }
        children.push(id);
        metrics.push(FlexMetrics {
            item,
            preferred,
            content_main: natural[axis],
            min,
            max,
            // Scrollbars reserve inner space, but are allowed to be clipped
            // when the allocated outer box is smaller than one scrollbar.
            padding: Xy::new(
                [p.padding.x[0], p.padding.x[1] - node.gutter.x],
                [p.padding.y[0], p.padding.y[1] - node.gutter.y],
            ),
            margin: p.margin,
            stretch_cross: matches!(p.size[cross], Size::Auto | Size::Fill),
            first_baseline: if item.align_self.unwrap_or(layout.align_items)
                == FlexAlign::FirstBaseline
            {
                exported_baseline(frame, id, cross, false)
            } else {
                None
            },
            last_baseline: if item.align_self.unwrap_or(layout.align_items)
                == FlexAlign::LastBaseline
            {
                exported_baseline(frame, id, cross, true)
            } else {
                None
            },
        });
    }
    let mut intrinsic = inner;
    let box_rule = &frame.nodes[parent];
    let mut layout = layout;
    let mut intrinsic_layout = layout;
    if let Some(declared) = box_rule.rule.flex {
        intrinsic_layout.gap = declared.gap;
        // An indefinite cross size has no percentage basis while collecting
        // lines, including when those lines establish the final cross size.
        if !box_rule.assigned && frame.is_intrinsic(parent, cross, box_rule.base.size[cross]) {
            layout.line_gap = declared.line_gap;
        }
    }
    // A percentage preferred size becomes definite after the container has
    // been measured. Its unwrapped content contributes during intrinsic sizing.
    for &(i, _, natural) in &relative_preferences {
        metrics[i].preferred[axis] = natural;
    }
    intrinsic[axis] = intrinsic_layout.intrinsic_main(&metrics);
    for (i, preferred, _) in relative_preferences {
        metrics[i].preferred[axis] = preferred;
    }
    frame.set_intrinsic(parent, intrinsic);
    let inner = frame.content_size(parent);
    let mut geometry = layout.geometry(inner, &metrics, frame.export_baselines);
    intrinsic[cross] = if intrinsic_cross_corrections.is_empty() {
        geometry.natural_cross
    } else {
        let mut contributions = metrics.clone();
        for (i, value) in intrinsic_cross_corrections {
            contributions[i].preferred[cross] = value;
        }
        layout.geometry(inner, &contributions, false).natural_cross
    };
    frame.set_intrinsic(parent, intrinsic);
    let adjusted = frame.content_size(parent);
    if adjusted != inner {
        geometry = layout.geometry(adjusted, &metrics, frame.export_baselines);
    }
    frame.nodes[parent].effective.children_layout = ChildrenLayout::Free;
    frame.nodes[parent].flex_baseline_items = geometry
        .baseline_items
        .map(|axes| axes.map(|pair| pair.map(|i| children[i])));
    for (child, rect) in children.into_iter().zip(geometry.rects) {
        frame.place(child, parent, rect);
    }
}
