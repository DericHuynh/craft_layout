//! Scroll geometry and placement relative to a containing box.
use super::TreeIdentity;
use super::{RuleIssue, driver::Frame, size};
use crate::{Axis, LayoutParams, NodeId, Size, Xy, XyRect};
use std::sync::Arc;

/// A length measured as a fraction of a reference box plus logical pixels.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Length {
    /// Proportion of the reference dimension.
    pub fraction: f32,
    /// Constant distance in logical pixels.
    pub pixels: f32,
}
impl Length {
    /// A fixed distance.
    pub const fn px(pixels: f32) -> Self {
        Self {
            fraction: 0.,
            pixels,
        }
    }
    /// Evaluate against the reference dimension.
    pub fn resolve(self, extent: f32) -> f32 {
        self.fraction * extent + self.pixels
    }
}
/// Physical left/right and top/bottom insets. An absent edge is unconstrained.
pub type Edges = Xy<[Option<Length>; 2]>;

/// The box used for positioned layout.
#[derive(Clone, Debug, Default, PartialEq)]
pub enum BoxReference {
    /// Immediate parent's padding box.
    #[default]
    Parent,
    /// Root viewport.
    Window,
    /// Explicit node's padding box.
    Node(NodeId),
}
/// Preferred side for an anchor-relative popup, aligned to the low perpendicular edge.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    /// Below the anchor.
    Below,
    /// Above the anchor.
    Above,
    /// To the left.
    Left,
    /// To the right.
    Right,
}
/// Optional placement behavior for a node.
#[derive(Clone, Debug, Default, PartialEq)]
pub enum Placement {
    /// Use native flow or free placement unchanged.
    #[default]
    Flow,
    /// Translate the rendered subtree while reserving its original slot.
    Relative(Xy<Length>),
    /// Take the node out of flow and place against a containing box. Opposing
    /// insets stretch a dimension declared Auto or Fill.
    Absolute {
        /// Reference padding box.
        containing: BoxReference,
        /// Insets from physical edges.
        insets: Edges,
    },
    /// Pin a node to the viewport across ancestor scrolling.
    Fixed(Edges),
    /// Keep the normal slot and constrain the visual box to its nearest
    /// scrollport, stopping at its parent's trailing edge.
    Sticky(Edges),
    /// Place a popup next to another box using ordered fallback sides.
    Anchor {
        /// Stable reference to another live node.
        target: NodeId,
        /// Preferred side followed by fallback placements.
        sides: Vec<Side>,
        /// Space between the anchor and popup.
        gap: f32,
    },
}
impl Placement {
    pub(super) fn target(&self) -> Option<&NodeId> {
        match self {
            Self::Anchor { target, .. }
            | Self::Absolute {
                containing: BoxReference::Node(target),
                ..
            } => Some(target),
            _ => None,
        }
    }
    pub(super) fn rebind(&mut self, owner: &Arc<TreeIdentity>) {
        match self {
            Self::Anchor { target, .. }
            | Self::Absolute {
                containing: BoxReference::Node(target),
                ..
            } => *target = NodeId::new(owner, target.key(), target.incarnation()),
            _ => {}
        }
    }
    pub(super) fn out_of_flow(&self) -> bool {
        matches!(
            self,
            Self::Absolute { .. } | Self::Fixed(_) | Self::Anchor { .. }
        )
    }
}

/// Per-axis overflow policy. Hidden allows programmatic scroll; Clip does not.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Overflow {
    /// Propagate overflow to the parent.
    #[default]
    Visible,
    /// Clip descendants, with no scrolling.
    Clip,
    /// Clip descendants and permit programmatic scrolling.
    Hidden,
    /// Scroll when content overflows.
    Auto,
    /// Always reserve the configured scrollbar and enable scrolling.
    Scroll,
}
impl Overflow {
    fn scrolls(self) -> bool {
        matches!(self, Self::Auto | Self::Hidden | Self::Scroll)
    }
}
/// Scroll and scrollbar policy. Zero-width bars are overlays.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct ScrollStyle {
    /// Overflow behavior per axis.
    pub overflow: Xy<Overflow>,
    /// Thickness of each axis's scrollbar, taken from the other dimension.
    pub scrollbar: Xy<f32>,
    /// Reserve the scrollbar gutter even before content overflows.
    pub stable_gutter: bool,
}
/// Published, physical viewport geometry. Scroll offsets are measured in the
/// same coordinate system as the layout rectangles.
#[derive(Clone, Debug, PartialEq)]
pub struct ViewGeometry {
    /// Visual border box after scroll and positioning.
    pub rect: XyRect,
    /// Clip inherited from ancestor scrollports, in window coordinates.
    pub clip: XyRect,
    /// This node's scrollport, in window coordinates.
    pub scrollport: XyRect,
    /// Scrollable bounds relative to the scrollport origin, before scrolling.
    pub content: XyRect,
    /// Inclusive allowed scroll offsets, per axis.
    pub scroll_range: XyRect,
    /// Actual clamped offset.
    pub offset: Xy<f32>,
}
impl ViewGeometry {
    pub(super) fn plain(rect: XyRect, window: Xy<f32>) -> Self {
        let s = size(rect);
        Self {
            rect,
            clip: viewport(window),
            scrollport: rect,
            content: viewport(s),
            scroll_range: Xy::new_symm([0.; 2]),
            offset: Xy::new_symm(0.),
        }
    }
}
fn viewport(size: Xy<f32>) -> XyRect {
    Xy::new([0., size.x], [0., size.y])
}
fn shifted(mut r: XyRect, d: Xy<f32>) -> XyRect {
    for a in [Axis::X, Axis::Y] {
        r[a][0] += d[a];
        r[a][1] += d[a];
    }
    r
}
pub(super) fn gutter(style: ScrollStyle, overflowing: Xy<bool>) -> Xy<f32> {
    let width = |a: Axis| match style.overflow[a] {
        Overflow::Scroll => style.scrollbar[a].max(0.),
        Overflow::Auto if style.stable_gutter || overflowing[a] => style.scrollbar[a].max(0.),
        Overflow::Hidden if style.stable_gutter => style.scrollbar[a].max(0.),
        _ => 0.,
    };
    Xy::new(width(Axis::Y), width(Axis::X))
}
fn inset_box(mut rect: XyRect, edges: Xy<[f32; 2]>) -> XyRect {
    for a in [Axis::X, Axis::Y] {
        rect[a][0] += edges[a][0];
        rect[a][1] = (rect[a][1] - edges[a][1]).max(rect[a][0]);
    }
    rect
}

fn static_box(parent: XyRect, padding: Xy<[f32; 2]>, block_offset: f32) -> XyRect {
    let mut rect = inset_box(parent, padding);
    rect.y[0] += block_offset;
    rect
}

fn positioned(
    reference: XyRect,
    insets: &Edges,
    style: &LayoutParams,
    initial: Xy<f32>,
    model: super::BoxStyle,
    static_box: XyRect,
) -> XyRect {
    let available = size(reference);
    let mut length = initial;
    let mut rect = reference;
    // Resolve percentages against the explicit containing box. The native
    // measuring parent may be an unrelated, smaller wrapper.
    let bound = |value: Size, axis: Axis, other: f32| match value {
        Size::Pixels(value) => value,
        Size::Frac(fraction) => available[axis] * fraction,
        Size::Fill => available[axis],
        Size::Auto | Size::FitContent => initial[axis],
        Size::AspectRatio(ratio) => {
            if axis == Axis::X {
                other * ratio
            } else {
                other / ratio
            }
        }
    };
    let clamp = |mut value: f32, axis: Axis, other: f32| {
        if let Some(max) = style.max_size[axis] {
            value = value.min(bound(max, axis, other));
        }
        if let Some(min) = style.min_size[axis] {
            value = value.max(bound(min, axis, other));
        }
        value.max(0.)
    };
    for a in [Axis::X, Axis::Y] {
        let [low, high] = insets[a].map(|v| v.map(|v| v.resolve(available[a])));
        let [before, after] = style.margin[a].map(|m| m.as_px().unwrap_or(0.));
        let candidate = match (style.size[a], low, high) {
            (Size::Auto | Size::Fill, Some(lo), Some(hi)) => {
                available[a] - lo - hi - before - after
            }
            (Size::Fill, lo, hi) => {
                available[a] - lo.unwrap_or(0.) - hi.unwrap_or(0.) - before - after
            }
            (Size::FitContent, lo, hi) if let Some(min) = model.positioned_fit_min[a] => {
                let available = available[a] - lo.unwrap_or(0.) - hi.unwrap_or(0.) - before - after;
                initial[a].min(available).max(min)
            }
            (size, _, _) => bound(size, a, initial[a.other()]),
        };
        length[a] = clamp(candidate, a, initial[a.other()]);
    }
    for a in [Axis::X, Axis::Y] {
        if let Size::AspectRatio(_) = style.size[a] {
            length[a] = clamp(
                bound(style.size[a], a, length[a.other()]),
                a,
                length[a.other()],
            );
        }
        let [low, high] = insets[a].map(|v| v.map(|v| v.resolve(available[a])));
        let [before, after] = style.margin[a].map(|m| m.as_px().unwrap_or(0.));
        let start = match (low, high) {
            (Some(lo), Some(hi)) => {
                let free = available[a] - lo - hi - before - after - length[a];
                let [auto_before, auto_after] = style.margin[a].map(|m| m.as_px().is_none());
                let shift = match (auto_before, auto_after) {
                    (true, false) => free,
                    (true, true) if free >= 0. => free * 0.5,
                    (false, false) | (true, true) if model.reverse_insets[a] => free,
                    _ => 0.,
                };
                reference[a][0] + lo + before + shift
            }
            (Some(lo), _) => reference[a][0] + lo + before,
            (_, Some(hi)) => reference[a][1] - hi - after - length[a],
            _ if let Some(f) = model.absolute_static[a] => {
                let candidate = static_box[a][0]
                    + before
                    + f * (static_box[a][1] - static_box[a][0] - before - after - length[a]);
                if model.safe_static[a] {
                    let lower = reference[a][0] + before;
                    let upper = reference[a][1] - after - length[a];
                    if model.reverse_insets[a] {
                        candidate.max(lower).min(upper)
                    } else {
                        candidate.min(upper).max(lower)
                    }
                } else {
                    candidate
                }
            }
            _ => reference[a][0] + before,
        };
        rect[a] = [start, start + length[a]];
    }
    rect
}
pub(super) fn apply(frame: &mut Frame<'_>, i: usize, issues: &mut Vec<RuleIssue>) {
    let Some(parent) = frame.nodes[i].parent else {
        return;
    };
    let p = &frame.nodes[i].rule.placement;
    let window = viewport(frame.window);
    let (reference, insets) = match p {
        Placement::Absolute { containing, insets } => {
            let rect = match containing {
                BoxReference::Window => window,
                BoxReference::Parent => port(&frame.nodes[parent]),
                BoxReference::Node(target) => match frame.reference(i, target) {
                    Some(j) => {
                        if let Some(area) = super::grid::ancestor_area(frame, j, i) {
                            let origin = frame.nodes[j].rect;
                            let local = shifted(area, Xy::new(-origin.x[0], -origin.y[0]));
                            frame
                                .grid_positioned_areas
                                .insert(frame.nodes[i].id.key(), (j, local));
                            area
                        } else {
                            port(&frame.nodes[j])
                        }
                    }
                    None => {
                        issues.push(RuleIssue::MissingReference(frame.nodes[i].id.clone()));
                        return;
                    }
                },
            };
            (rect, insets)
        }
        Placement::Fixed(insets) => (window, insets),
        Placement::Anchor { .. } => {
            frame.nodes[i].effective.free_placement = true;
            return;
        }
        _ => return,
    };
    let rect = positioned(
        reference,
        insets,
        &frame.nodes[i].base,
        if frame.nodes[i].assigned {
            size(frame.nodes[i].rect)
        } else {
            frame.nodes[i].measured
        },
        frame.nodes[i].rule.box_model,
        static_box(
            frame.nodes[parent].rect,
            frame.nodes[parent].effective.padding,
            frame.nodes[i].block_static_y,
        ),
    );
    let parent_rect = frame.nodes[parent].rect;
    let pad = frame.nodes[parent].effective.padding;
    let local = shifted(
        rect,
        Xy::new(-parent_rect.x[0] - pad.x[0], -parent_rect.y[0] - pad.y[0]),
    );
    frame.place(i, parent, local);
}

fn port(node: &super::driver::FrameNode) -> XyRect {
    let mut edges = node.rule.box_model.border;
    for a in [Axis::X, Axis::Y] {
        let flip = node
            .rule
            .box_model
            .scroll_origin
            .is_some_and(|origin| origin[a]);
        edges[a][usize::from(!flip)] += node.gutter[a];
    }
    inset_box(node.rect, edges)
}

fn delta(to: XyRect, from: XyRect) -> Xy<f32> {
    Xy::new(to.x[0] - from.x[0], to.y[0] - from.y[0])
}

fn clip_interval(bounds: [f32; 2], new: [f32; 2]) -> [f32; 2] {
    let low = bounds[0].max(new[0]);
    [low, bounds[1].min(new[1]).max(low)]
}

fn anchored(target: XyRect, extent: Xy<f32>, sides: &[Side], gap: f32, clip: XyRect) -> XyRect {
    let at = |side| {
        let origin = match side {
            Side::Below => Xy::new(target.x[0], target.y[1] + gap),
            Side::Above => Xy::new(target.x[0], target.y[0] - extent.y - gap),
            Side::Left => Xy::new(target.x[0] - extent.x - gap, target.y[0]),
            Side::Right => Xy::new(target.x[1] + gap, target.y[0]),
        };
        shifted(viewport(extent), origin)
    };
    for &side in sides {
        let rect = at(side);
        if [Axis::X, Axis::Y]
            .iter()
            .all(|&a| rect[a][0] >= clip[a][0] && rect[a][1] <= clip[a][1])
        {
            return rect;
        }
    }
    // As in native free placement, keep the preferred side when neither side
    // fits, then shift it into the available clip on each physical axis.
    let mut rect = at(sides.first().copied().unwrap_or(Side::Below));
    for a in [Axis::X, Axis::Y] {
        let start = rect[a][0].clamp(clip[a][0], (clip[a][1] - extent[a]).max(clip[a][0]));
        rect[a] = [start, start + extent[a]];
    }
    rect
}

#[derive(Clone, Copy)]
struct ScrollFrame {
    port: XyRect,
    content: XyRect,
    range: XyRect,
    offset: Xy<f32>,
}

// Propagate visible descendant bounds only as far as their first clipping
// ancestor. The containing scrollport includes its own trailing padding.
fn scroll_frames(
    frame: &mut Frame<'_>,
    offsets: &std::collections::HashMap<super::NodeKey, Xy<f32>>,
) -> Vec<ScrollFrame> {
    let mut frames: Vec<_> = frame
        .nodes
        .iter()
        .map(|node| {
            let port = port(node);
            ScrollFrame {
                port,
                content: port,
                range: Xy::new_symm([0.; 2]),
                offset: Xy::new_symm(0.),
            }
        })
        .collect();
    // The positioning grid also owns this descendant's scrollable overflow.
    // A static wrapper in between cannot acquire a spurious scroll range.
    let mut hoisted = std::collections::HashMap::<usize, Vec<usize>>::new();
    if !frame.grid_positioned_areas.is_empty() {
        for (i, node) in frame.nodes.iter().enumerate() {
            if let Some(&(target, _)) = frame.grid_positioned_areas.get(&node.id.key())
                && node.parent != Some(target)
            {
                hoisted.entry(target).or_default().push(i);
            }
        }
    }
    for i in (0..frame.nodes.len()).rev() {
        let node = &frame.nodes[i];
        let port = frames[i].port;
        let mut content = port;
        let origin = node
            .rule
            .box_model
            .scroll_origin
            .unwrap_or(node.context.origins());
        let mut trailing = Xy::new_symm(0.);
        for a in [Axis::X, Axis::Y] {
            let end = usize::from(!origin[a]);
            trailing[a] = node.effective.padding[a][end]
                - node.rule.box_model.border[a][end]
                - node.gutter[a];
            let extent = node.rule.box_model.content_extent[a];
            if extent > 0. {
                let start_pad =
                    node.effective.padding[a][1 - end] - node.rule.box_model.border[a][1 - end];
                let required = start_pad + extent + trailing[a];
                if origin[a] {
                    content[a][0] = content[a][0].min(port[a][1] - required);
                } else {
                    content[a][1] = content[a][1].max(port[a][0] + required);
                }
            }
        }
        for &c in node
            .children
            .iter()
            .chain(hoisted.get(&i).into_iter().flatten())
        {
            let child = &frame.nodes[c];
            if frame
                .grid_positioned_areas
                .get(&child.id.key())
                .is_some_and(|(target, _)| *target != i)
                || child.base.disabled
                || matches!(
                    child.rule.placement,
                    Placement::Fixed(_)
                        | Placement::Anchor { .. }
                        | Placement::Absolute {
                            containing: BoxReference::Window,
                            ..
                        }
                )
            {
                continue;
            }
            let relative = match &child.rule.placement {
                Placement::Relative(offset) => Xy::new(
                    offset.x.resolve(frame.content_size(i).x),
                    offset.y.resolve(frame.content_size(i).y),
                ),
                _ => Xy::new_symm(0.),
            };
            for a in [Axis::X, Axis::Y] {
                let mut child_bounds = child.rect[a];
                if child.rule.scroll.overflow[a] == Overflow::Visible {
                    child_bounds[0] = child_bounds[0].min(frames[c].content[a][0]);
                    child_bounds[1] = child_bounds[1].max(frames[c].content[a][1]);
                }
                let pad = if child.base.free_placement {
                    0.
                } else {
                    trailing[a]
                };
                let before = if origin[a] { pad } else { 0. };
                let after = if origin[a] { 0. } else { pad };
                content[a][0] = content[a][0].min(child_bounds[0] + relative[a] - before);
                content[a][1] = content[a][1].max(child_bounds[1] + relative[a] + after);
            }
        }
        let asked = offsets.get(&node.id.key()).copied().unwrap_or_default();
        let mut overflowing = Xy::new_symm(false);
        for a in [Axis::X, Axis::Y] {
            let mut range = [content[a][0] - port[a][0], content[a][1] - port[a][1]];
            if let Some(origin) = node.rule.box_model.scroll_origin {
                range[usize::from(origin[a])] = 0.;
            }
            overflowing[a] = range[0] < 0. || range[1] > 0.;
            if node.rule.scroll.overflow[a].scrolls() {
                frames[i].range[a] = range;
                let offset = if asked[a].is_nan() { 0. } else { asked[a] };
                frames[i].offset[a] = offset.clamp(range[0], range[1]);
            }
        }
        frames[i].content = content;
        frame.nodes[i].overflowing = overflowing;
    }
    frames
}

fn stick(
    mut rect: XyRect,
    insets: &Edges,
    nearest: Xy<Option<usize>>,
    parent: usize,
    views: &[ViewGeometry],
    window: XyRect,
) -> XyRect {
    for a in [Axis::X, Axis::Y] {
        let [before, after] = insets[a];
        if before.is_none() && after.is_none() {
            continue;
        }
        let scrollport = nearest[a].map_or(window[a], |i| views[i].scrollport[a]);
        let available = scrollport[1] - scrollport[0];
        let length = rect[a][1] - rect[a][0];
        let low = before.map_or(f32::NEG_INFINITY, |v| scrollport[0] + v.resolve(available));
        let high = after.map_or(f32::INFINITY, |v| {
            scrollport[1] - v.resolve(available) - length
        });
        let mut start = rect[a][0].clamp(low, high.max(low));
        let containing = &views[parent];
        let mut bounds = containing.rect[a];
        if nearest[a] == Some(parent) {
            for side in 0..2 {
                bounds[side] = containing.scrollport[a][0] + containing.content[a][side]
                    - containing.offset[a];
            }
        }
        start = start.clamp(bounds[0], (bounds[1] - length).max(bounds[0]));
        rect[a] = [start, start + length];
    }
    rect
}

pub(super) fn publish(
    frame: &mut Frame<'_>,
    offsets: &std::collections::HashMap<super::NodeKey, Xy<f32>>,
    issues: &mut Vec<RuleIssue>,
) -> std::collections::HashMap<super::NodeKey, ViewGeometry> {
    use std::collections::VecDeque;
    let scroll = scroll_frames(frame, offsets);
    let n = frame.nodes.len();
    let window = viewport(frame.window);
    let mut views = vec![ViewGeometry::plain(window, frame.window); n];
    let mut nearest = vec![Xy::new_symm(None); n];
    let mut dependencies = vec![0u8; n];
    let mut targets = vec![None; n];
    let mut dependents = vec![Vec::new(); n];
    let mut queue = VecDeque::new();
    for (i, node) in frame.nodes.iter().enumerate() {
        if node.parent.is_some() {
            dependencies[i] += 1;
        }
        if !node.base.disabled
            && let Some(target) = node.rule.placement.target()
        {
            if let Some(j) = frame.reference(i, target) {
                dependencies[i] += 1;
                targets[i] = Some(j);
                dependents[j].push(i);
            } else {
                issues.push(RuleIssue::MissingReference(node.id.clone()));
            }
        }
        if dependencies[i] == 0 {
            queue.push_back(i);
        }
    }
    let mut done = vec![false; n];
    let mut count = 0;
    while count < n {
        let i = match queue.pop_front() {
            Some(i) => i,
            None => {
                // Parent links cannot cycle. Break only a positioning reference
                // whose parent is already resolved, preserving the rest of the tree.
                let Some(i) =
                    (0..n).find(|&i| !done[i] && frame.nodes[i].parent.is_none_or(|p| done[p]))
                else {
                    break;
                };
                issues.push(RuleIssue::CyclicReference(frame.nodes[i].id.clone()));
                targets[i] = None;
                i
            }
        };
        let node = &frame.nodes[i];
        let mut clip = window;
        let mut containing_scroll = Xy::new_symm(None);
        let mut rect = node.rect;
        if let Some(p) = node.parent {
            let parent = &views[p];
            let parent_node = &frame.nodes[p];
            let movement = delta(parent.rect, parent_node.rect);
            rect = shifted(
                rect,
                Xy::new(movement.x - parent.offset.x, movement.y - parent.offset.y),
            );
            clip = parent.clip;
            containing_scroll = nearest[p];
            for a in [Axis::X, Axis::Y] {
                let overflow = parent_node.rule.scroll.overflow[a];
                if overflow != Overflow::Visible {
                    clip[a] = clip_interval(clip[a], parent.scrollport[a]);
                }
                if overflow.scrolls() {
                    containing_scroll[a] = Some(p);
                }
            }
            match &node.rule.placement {
                Placement::Flow => {}
                Placement::Relative(offset) => {
                    let parent_extent = frame.content_size(p);
                    rect = shifted(
                        rect,
                        Xy::new(
                            offset.x.resolve(parent_extent.x),
                            offset.y.resolve(parent_extent.y),
                        ),
                    );
                }
                Placement::Sticky(insets) => {
                    rect = stick(rect, insets, containing_scroll, p, &views, window)
                }
                Placement::Fixed(insets) => {
                    rect = positioned(
                        window,
                        insets,
                        &node.base,
                        size(node.rect),
                        node.rule.box_model,
                        static_box(
                            parent.rect,
                            parent_node.effective.padding,
                            node.block_static_y,
                        ),
                    );
                    clip = window;
                    containing_scroll = Xy::new_symm(None);
                }
                Placement::Absolute { containing, insets } => {
                    // Static alignment moves with the immediate parent's
                    // scrolling content; explicit insets use their reference.
                    let origin = shifted(parent.rect, Xy::new(-parent.offset.x, -parent.offset.y));
                    let local_static =
                        static_box(origin, parent_node.effective.padding, node.block_static_y);
                    let reference = match containing {
                        BoxReference::Parent => Some(p),
                        BoxReference::Node(_) => targets[i],
                        BoxReference::Window => None,
                    };
                    if let Some(j) = reference {
                        let reference = &views[j];
                        let target = if let Some(&(_, area)) =
                            frame.grid_positioned_areas.get(&node.id.key())
                        {
                            // Like its reference coordinates, clipping and sticky ancestry
                            // follow the positioning grid across intervening static wrappers.
                            clip = reference.clip;
                            containing_scroll = nearest[j];
                            for a in [Axis::X, Axis::Y] {
                                let overflow = frame.nodes[j].rule.scroll.overflow[a];
                                if overflow != Overflow::Visible {
                                    clip[a] = clip_interval(clip[a], reference.scrollport[a]);
                                }
                                if overflow.scrolls() {
                                    containing_scroll[a] = Some(j);
                                }
                            }
                            shifted(area, Xy::new(reference.rect.x[0], reference.rect.y[0]))
                        } else {
                            reference.scrollport
                        };
                        rect = positioned(
                            shifted(target, Xy::new(-reference.offset.x, -reference.offset.y)),
                            insets,
                            &node.base,
                            size(node.rect),
                            node.rule.box_model,
                            local_static,
                        );
                    } else if matches!(containing, BoxReference::Window) {
                        rect = positioned(
                            window,
                            insets,
                            &node.base,
                            size(node.rect),
                            node.rule.box_model,
                            local_static,
                        );
                    }
                }
                Placement::Anchor { sides, gap, .. } => {
                    if let Some(j) = targets[i] {
                        rect = anchored(views[j].rect, size(node.rect), sides, *gap, clip);
                    }
                }
            }
        }
        nearest[i] = containing_scroll;
        let own = &scroll[i];
        views[i] = ViewGeometry {
            rect,
            clip,
            scrollport: shifted(own.port, delta(rect, node.rect)),
            content: shifted(own.content, Xy::new(-own.port.x[0], -own.port.y[0])),
            scroll_range: own.range,
            offset: own.offset,
        };
        done[i] = true;
        count += 1;
        for &child in node.children.iter().chain(&dependents[i]) {
            if done[child] {
                continue;
            }
            dependencies[child] -= 1;
            if dependencies[child] == 0 {
                queue.push_back(child);
            }
        }
    }
    frame
        .nodes
        .iter()
        .zip(views)
        .filter(|(node, _)| !node.base.disabled)
        .map(|(node, view)| (node.id.key(), view))
        .collect()
}
