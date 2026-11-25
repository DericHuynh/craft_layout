//! Horizontal block formatting contexts with float exclusion rectangles. All
//! exclusions use the same coordinates within their independent context. An
//! ordinary nested block retains the context of its parent.
use super::driver::{Frame, FrameNode};
use super::viewport::Overflow;
use crate::flow::{BlockFlow, BlockItem, BlockMargins, zero_minimum};
use crate::{Axis, ChildrenLayout, Margin, Size, TextContent, WritingMode, Xy};

/// Physical side of a floated box in horizontal block flow.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Float {
    /// Participate in normal flow.
    #[default]
    None,
    /// Float against the left edge or preceding floats.
    Left,
    /// Float against the right edge or preceding floats.
    Right,
}

/// Sides whose earlier floats must end before the box can start.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Clear {
    /// Allow neighboring floats.
    #[default]
    None,
    /// Clear left floats.
    Left,
    /// Clear right floats.
    Right,
    /// Clear both sides.
    Both,
}
impl Clear {
    fn matches(self, side: Float) -> bool {
        self == Self::Both
            || matches!(
                (self, side),
                (Self::Right, Float::Right) | (Self::Left, Float::Left)
            )
    }
}

/// Alignment of a block's content group or one normal-flow child.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BlockAlignment {
    /// Use the parent's alignment, or start when there is no override.
    #[default]
    Normal,
    /// Logical start.
    Start,
    /// Logical end.
    End,
    /// Start edge in the aligned child's own inline direction.
    SelfStart,
    /// End edge in the aligned child's own inline direction.
    SelfEnd,
    /// Stretch an automatic inline size.
    Stretch,
    /// Center, allowing overflow on both sides.
    Center,
    /// Center, keeping overflowing content at start.
    SafeCenter,
    /// End, keeping overflowing content at start.
    SafeEnd,
    /// Physical left.
    Left,
    /// Physical right.
    Right,
}
impl BlockAlignment {
    fn offset(self, spare: f32, rtl: bool) -> f32 {
        match self {
            Self::Left => 0.,
            Self::Right => spare,
            Self::Center => spare / 2.,
            Self::SafeCenter if spare >= 0. => spare / 2.,
            Self::End | Self::SafeEnd if !rtl && (self == Self::End || spare >= 0.) => spare,
            Self::End | Self::SafeEnd if rtl && (self == Self::End || spare >= 0.) => 0.,
            _ if rtl => spare,
            _ => 0.,
        }
    }
}

/// Optional box declarations for float-aware block layout.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct BlockStyle {
    /// Float side, applied when the box participates in a block context.
    pub float: Float,
    /// Float clearance applied before this box.
    pub clear: Clear,
    /// Vertical alignment of the complete group of children.
    pub align_content: BlockAlignment,
    /// Default horizontal alignment of normal-flow children.
    pub justify_items: BlockAlignment,
    /// Horizontal alignment override when this node is a block child.
    pub justify_self: BlockAlignment,
    /// Physical alignment inherited from legacy text alignment. Unlike
    /// justify-items, this preserves the normal fill width of an automatic box.
    pub legacy_justify: BlockAlignment,
    /// For a stretching block height, subtract only margins that cannot
    /// collapse through the parent's corresponding edge.
    pub stretch_block_margins: bool,
    /// Anchor an out-of-flow child at its source position in the block flow.
    pub static_block_position: bool,
    /// Establish layout containment, including an independent fallback baseline.
    pub contain_layout: bool,
}

fn block(n: &FrameNode) -> bool {
    n.base.children_layout == ChildrenLayout::Block
        && !n.base.disabled
        && n.context.writing_mode == WritingMode::HorizontalTb
        && n.rule.flex.is_none()
        && n.rule.grid.is_none()
}
fn requested_alignment(parent: &FrameNode, child: &FrameNode) -> BlockAlignment {
    let align = child.rule.block_flow.justify_self;
    if align == BlockAlignment::Normal {
        parent.rule.block_flow.justify_items
    } else {
        align
    }
}
pub(super) fn intrinsic_inline(parent: &FrameNode, child: &FrameNode) -> bool {
    block(parent)
        && (child.rule.block_flow.float != Float::None
            || !matches!(
                requested_alignment(parent, child),
                BlockAlignment::Normal | BlockAlignment::Stretch
            ))
}
fn independent(n: &FrameNode) -> bool {
    !block(n)
        || n.base.free_placement
        || n.base.isolate_block_margins
        || n.rule.block_flow.float != Float::None
        || n.rule.block_flow.contain_layout
        || n.rule.block_flow.align_content != BlockAlignment::Normal
        || [n.rule.scroll.overflow.x, n.rule.scroll.overflow.y]
            .iter()
            .any(|v| matches!(v, Overflow::Scroll | Overflow::Hidden | Overflow::Auto))
}
fn in_flow(n: &FrameNode) -> bool {
    !n.base.disabled && !n.base.free_placement
}
fn axis_size(value: Size, available: f32, pref: f32, other: f32, axis: Axis) -> f32 {
    match value {
        Size::Pixels(s) => s,
        Size::Frac(f) => available * f,
        Size::Fill => available,
        Size::Auto | Size::FitContent => pref,
        Size::AspectRatio(r) => {
            if axis == Axis::X {
                other * r
            } else {
                other / r
            }
        }
    }
}
fn bounded(n: &FrameNode, a: Axis, value: f32, available: f32) -> f32 {
    let resolve = |v| axis_size(v, available, n.measured[a], n.measured[a.other()], a);
    value
        .min(n.base.max_size[a].map_or(f32::INFINITY, resolve))
        .max(n.base.min_size[a].map_or(0., resolve))
        .max(n.base.padding[a].iter().sum())
}
fn margin(n: &FrameNode, a: Axis) -> [f32; 2] {
    n.base.margin[a].map(|m| m.as_px().unwrap_or(0.))
}

#[derive(Clone, Copy, Default)]
struct Intrinsic {
    width: f32,
    margins: BlockMargins,
    floats: bool,
    empty: bool,
}

pub(super) struct Plan {
    roots: Vec<bool>,
    intrinsic: Vec<Intrinsic>,
}
impl Plan {
    pub(super) fn new(frame: &Frame<'_>) -> Self {
        if !frame
            .nodes
            .iter()
            .any(|n| n.rule.block_flow != BlockStyle::default())
        {
            return Self {
                roots: Vec::new(),
                intrinsic: Vec::new(),
            };
        }
        let nodes = &frame.nodes;
        let mut group = vec![None; nodes.len()];
        let mut roots = vec![false; nodes.len()];
        for (i, n) in nodes.iter().enumerate() {
            let parent_group = n.parent.and_then(|p| group[p]);
            if block(n) {
                group[i] = if in_flow(n) {
                    parent_group.or(Some(i))
                } else {
                    Some(i)
                };
            }
            if n.rule.block_flow != BlockStyle::default() {
                if let Some(root) = parent_group {
                    roots[root] = true;
                }
                let style = n.rule.block_flow;
                // A free child's static source position belongs to its parent.
                // It does not opt the child's own descendants into float layout.
                let layout_children = in_flow(n)
                    || [
                        style.align_content,
                        style.justify_items,
                        style.legacy_justify,
                    ]
                    .iter()
                    .any(|&value| value != BlockAlignment::Normal);
                if layout_children && let Some(root) = group[i] {
                    roots[root] = true;
                }
            }
        }
        let mut intrinsic = vec![Intrinsic::default(); nodes.len()];
        for (i, n) in nodes.iter().enumerate().rev() {
            if !block(n) || !group[i].is_some_and(|root| roots[root]) {
                continue;
            }
            let collapse = n.parent.is_some_and(|p| block(&nodes[p])) && !independent(n);
            let mut flow = BlockFlow::from_edges(
                collapse && n.base.padding.y[0] == 0.,
                collapse
                    && n.base.padding.y[1] == 0.
                    && matches!(n.base.size.y, Size::FitContent | Size::Auto),
            );
            let mut width = 0f32;
            let mut row = 0f32;
            let mut floats = false;
            let mut empty = true;
            for &id in &n.children {
                let child = &nodes[id];
                if !in_flow(child) {
                    continue;
                }
                let calc = intrinsic[id];
                let m = margin(child, Axis::X);
                let pref = if block(child) {
                    calc.width
                } else {
                    child.measured.x
                };
                let w = match child.base.size.x {
                    Size::Pixels(w) => w,
                    Size::Frac(_) => 0.,
                    _ => pref,
                };
                let w = bounded(child, Axis::X, w, 0.) + m[0] + m[1];
                if child.rule.block_flow.clear != Clear::None {
                    row = 0.;
                }
                if child.rule.block_flow.float != Float::None {
                    floats = true;
                    row += w;
                    width = width.max(row);
                    continue;
                }
                empty = false;
                width = width.max(w);
                row = 0.;
                let h = child.measured.y;
                let [top, bottom] = margin(child, Axis::Y);
                let separates =
                    floats && (child.rule.block_flow.clear != Clear::None || independent(child));
                let nested = (block(child) && !independent(child)).then_some(calc.margins);
                let mut item = BlockItem::from_edges(
                    top,
                    bottom,
                    h,
                    !independent(child)
                        && h == 0.
                        && child.base.padding.y == [0.; 2]
                        && zero_minimum(child.base.min_size.y),
                    calc.empty,
                    nested,
                );
                if separates && flow.outgoing.all_through {
                    flow.collapse_top = false;
                    item.through = false;
                }
                if separates && child.rule.block_flow.clear != Clear::None && h == 0. {
                    flow.collapse_bottom = false;
                }
                flow.push(item);
                floats |= !independent(child) && calc.floats;
            }
            if n.base.text != TextContent::None || n.base.image.is_some() {
                width = width.max(n.natural.x - n.base.padding.x.iter().sum::<f32>());
            }
            intrinsic[i] = Intrinsic {
                width: width + n.base.padding.x.iter().sum::<f32>(),
                margins: flow.finish().1,
                floats,
                empty,
            };
        }
        Self { roots, intrinsic }
    }
    pub(super) fn is_root(&self, id: usize) -> bool {
        self.roots.get(id) == Some(&true)
    }
}

#[derive(Clone, Copy)]
struct Obstacle {
    side: Float,
    x: [f32; 2],
    y: [f32; 2],
}
#[derive(Default)]
struct Space {
    floats: Vec<Obstacle>,
}
impl Space {
    fn clear(&self, clear: Clear) -> Option<f32> {
        self.floats
            .iter()
            .filter(|f| clear.matches(f.side))
            .map(|f| f.y[1])
            .reduce(f32::max)
    }
    fn band(&self, bounds: [f32; 2], top: f32, h: f32) -> ([f32; 2], Option<f32>) {
        let mut region = bounds;
        let mut next = None::<f32>;
        for f in &self.floats {
            if f.y[1] <= top
                || (if h > 0. {
                    f.y[0] >= top + h
                } else {
                    f.y[0] > top
                })
            {
                continue;
            }
            if f.side == Float::Left {
                region[0] = region[0].max(f.x[1]);
            } else {
                region[1] = region[1].min(f.x[0]);
            }
            next = Some(next.map_or(f.y[1], |n| n.min(f.y[1])));
        }
        (region, next)
    }
}

struct BoxFlow {
    id: usize,
    origin: Xy<f32>,
    width: f32,
    flow: BlockFlow,
    space: usize,
    owns: bool,
    next: usize,
    float_start: usize,
    placed: Vec<(usize, Xy<[f32; 2]>)>,
}
impl BoxFlow {
    fn new(
        frame: &Frame<'_>,
        id: usize,
        origin: Xy<f32>,
        space: usize,
        owns: bool,
        prior: usize,
    ) -> Self {
        let n = &frame.nodes[id];
        let collapse = !owns && !independent(n);
        Self {
            id,
            origin,
            width: frame.content_size(id).x,
            flow: BlockFlow::from_edges(
                collapse && n.base.padding.y[0] == 0.,
                collapse
                    && n.base.padding.y[1] == 0.
                    && matches!(n.base.size.y, Size::FitContent | Size::Auto),
            ),
            space,
            owns,
            next: 0,
            float_start: prior,
            placed: Vec::new(),
        }
    }
}

impl Plan {
    pub(super) fn layout(&self, frame: &mut Frame<'_>, root: usize) {
        let mut spaces = vec![Space::default()];
        let mut stack = vec![BoxFlow::new(frame, root, Xy::new_symm(0.), 0, true, 0)];
        while let Some(row) = stack.last_mut() {
            let parent = row.id;
            let node = &frame.nodes[parent];
            if let Some(&id) = node.children.get(row.next) {
                row.next += 1;
                let child = &frame.nodes[id];
                if !in_flow(child) {
                    if child.rule.block_flow.static_block_position && !child.base.disabled {
                        // The hypothetical box sees the preceding in-flow cursor
                        // and its pending collapsed edge, without advancing either.
                        let y = row.flow.end
                            + if row.flow.collapse_top && row.flow.outgoing.all_through {
                                0.
                            } else {
                                row.flow.pending.positive + row.flow.pending.negative
                            };
                        let margin = child.base.margin.y[0].as_px().unwrap_or(0.);
                        let child = &mut frame.nodes[id];
                        child.block_static_y = y;
                        child.effective.position.y = crate::Pos::Pixels(y + margin);
                        child.effective.anchor.y = crate::Anchor::Start;
                    }
                    continue;
                }
                let style = child.rule.block_flow;
                let nested = block(child);
                let owns = independent(child);
                let floating = style.float != Float::None;
                let space = &mut spaces[row.space];
                let [mt, mb] = margin(child, Axis::Y);
                let [ml, mr] = margin(child, Axis::X);
                let rtl = node.base.children_origin_flipped.x;
                let width = row.width;
                let cm = self.intrinsic[id];
                let pref = if nested { cm.width } else { child.measured.x };
                let requested = requested_alignment(node, child);
                let fit_inline = intrinsic_inline(node, child);
                let align = match requested {
                    BlockAlignment::SelfStart if child.base.children_origin_flipped.x => {
                        BlockAlignment::Right
                    }
                    BlockAlignment::SelfStart => BlockAlignment::Left,
                    BlockAlignment::SelfEnd if child.base.children_origin_flipped.x => {
                        BlockAlignment::Left
                    }
                    BlockAlignment::SelfEnd => BlockAlignment::Right,
                    BlockAlignment::Normal => node.rule.block_flow.legacy_justify,
                    value => value,
                };
                let auto = matches!(child.base.size.x, Size::Fill | Size::Auto);
                let choose_width = |room: f32| {
                    let inline = if fit_inline && (auto || child.base.size.x == Size::FitContent) {
                        pref.min(room.max(0.))
                    } else if auto {
                        room
                    } else {
                        axis_size(child.base.size.x, width, pref, child.measured.y, Axis::X)
                    };
                    bounded(child, Axis::X, inline, width)
                };
                let mut w = choose_width(width - ml - mr);
                let available = frame.content_size(parent);
                let height = if style.stretch_block_margins && child.base.size.y == Size::Fill {
                    let parent_is_bfc = row.owns || floating;
                    let top = if parent_is_bfc || node.base.padding.y[0] != 0. {
                        mt
                    } else {
                        0.
                    };
                    let bottom = if parent_is_bfc || node.base.padding.y[1] != 0. {
                        mb
                    } else {
                        0.
                    };
                    available.y - top - bottom
                } else {
                    axis_size(child.base.size.y, available.y, child.measured.y, w, Axis::Y)
                };
                let mut h = bounded(child, Axis::Y, height, available.y);
                let mut item = BlockItem::from_edges(
                    mt,
                    mb,
                    h,
                    !owns
                        && h == 0.
                        && child.base.padding.y == [0.; 2]
                        && zero_minimum(child.base.min_size.y),
                    cm.empty,
                    (nested && !owns).then_some(cm.margins),
                );
                let leading = row.flow.outgoing.all_through && row.flow.collapse_top;
                let pending = row.flow.pending.positive + row.flow.pending.negative;
                let before = if floating {
                    row.flow.end + if leading { 0. } else { pending }
                } else {
                    let mut f = row.flow;
                    f.push(item_copy(&item))
                };
                let clear = space.clear(style.clear);
                let force_clear = clear.is_some_and(|edge| edge > before + row.origin.y);
                let mut y = if force_clear {
                    clear.unwrap() - row.origin.y
                } else {
                    before
                };
                let bounds = [row.origin.x, row.origin.x + width];
                let mut region = bounds;
                if floating {
                    if let Some(last) = space.floats.last() {
                        y = y.max(last.y[0] - row.origin.y);
                    }
                    loop {
                        let (band, next) = space.band(bounds, row.origin.y + y, 0.);
                        region = band;
                        if next.is_none() || w + ml + mr <= region[1] - region[0] + 0.0005 {
                            break;
                        }
                        y = next.unwrap() - row.origin.y;
                    }
                } else if owns {
                    loop {
                        let (band, next) = space.band(bounds, row.origin.y + y, h);
                        if next.is_none() {
                            break;
                        }
                        let start = if band[0] > bounds[0] {
                            band[0].max(bounds[0] + ml)
                        } else {
                            bounds[0] + ml
                        };
                        let end = if band[1] < bounds[1] {
                            band[1].min(bounds[1] - mr)
                        } else {
                            bounds[1] - mr
                        };
                        let fit = choose_width(end - start);
                        let negative_fits =
                            ml >= -(band[1] - band[0]) && mr >= -(band[1] - band[0]);
                        let fits_from_origin = if rtl {
                            end - fit >= band[0] - 0.0005
                        } else {
                            start + fit <= band[1] + 0.0005
                        };
                        if fits_from_origin && negative_fits {
                            region = [start, end];
                            w = fit;
                            break;
                        }
                        y = next.unwrap() - row.origin.y;
                    }
                }
                let x = if floating {
                    if style.float == Float::Left {
                        region[0] + ml
                    } else {
                        region[1] - mr - w
                    }
                } else {
                    let (start, end) = if region == bounds {
                        (bounds[0] + ml, bounds[1] - mr)
                    } else {
                        (region[0], region[1])
                    };
                    let spare = end - start - w;
                    let m = child.base.margin.x;
                    let offset = if spare >= 0. && (m[0] == Margin::AUTO || m[1] == Margin::AUTO) {
                        if m[0] == Margin::AUTO {
                            if m[1] == Margin::AUTO {
                                spare / 2.
                            } else {
                                spare
                            }
                        } else {
                            0.
                        }
                    } else {
                        align.offset(spare, rtl)
                    };
                    start + offset
                };
                if matches!(child.base.size.y, Size::AspectRatio(_)) {
                    h = bounded(
                        child,
                        Axis::Y,
                        axis_size(child.base.size.y, available.y, child.measured.y, w, Axis::Y),
                        available.y,
                    );
                    item.size = h;
                }
                if floating {
                    space.floats.push(Obstacle {
                        side: style.float,
                        x: [x - ml, x + w + mr],
                        y: [row.origin.y + y, row.origin.y + y + mt + h + mb],
                    });
                    y += mt;
                } else {
                    if y != before || force_clear {
                        row.flow.outgoing.all_through = false;
                        row.flow.collapse_top = false;
                        row.flow.end = y + h;
                        row.flow.pending = item.after;
                        if h == 0. {
                            row.flow.end -= mt;
                            row.flow.pending.merge(item.before);
                            row.flow.collapse_bottom = false;
                        }
                    } else {
                        row.flow.push(item);
                    }
                }
                let child_origin = Xy::new(
                    x + child.base.padding.x[0],
                    row.origin.y + y + child.base.padding.y[0],
                );
                let rect = Xy::new([x - row.origin.x, x - row.origin.x + w], [y, y + h]);
                let space = row.space;
                if node.rule.block_flow.align_content != BlockAlignment::Normal {
                    row.placed.push((id, rect));
                }
                frame.place(id, parent, rect);
                if nested {
                    let space = if owns {
                        spaces.push(Space::default());
                        spaces.len() - 1
                    } else {
                        space
                    };
                    stack.push(BoxFlow::new(
                        frame,
                        id,
                        child_origin,
                        space,
                        owns,
                        spaces[space].floats.len(),
                    ));
                }
            } else {
                let row = stack.pop().unwrap();
                let (normal, _) = row.flow.finish();
                let extent = if row.owns {
                    spaces[row.space].floats[row.float_start..]
                        .iter()
                        .fold(normal, |h, f| h.max(f.y[1] - row.origin.y))
                } else {
                    normal
                };
                let n = &frame.nodes[row.id];
                let inline = self.intrinsic[row.id].width - n.base.padding.x.iter().sum::<f32>();
                let natural_height = if n.base.text != TextContent::None {
                    extent.max(n.measured.y - n.base.padding.y.iter().sum::<f32>())
                } else {
                    extent
                };
                let align = n.rule.block_flow.align_content;
                frame.set_intrinsic(row.id, Xy::new(inline, natural_height));
                let offset = align.offset(frame.content_size(row.id).y - natural_height, false);
                if offset != 0. {
                    for (id, mut rect) in row.placed {
                        rect.y = rect.y.map(|x| x + offset);
                        frame.place(id, row.id, rect);
                    }
                }
                // Every planned normal child now has a physical assignment.
                frame.nodes[row.id].effective.children_layout = ChildrenLayout::Free;
                frame.nodes[row.id].managed_block = true;
            }
        }
    }
}

fn item_copy(item: &BlockItem) -> BlockItem {
    BlockItem {
        before: item.before,
        after: item.after,
        size: item.size,
        through: item.through,
    }
}
