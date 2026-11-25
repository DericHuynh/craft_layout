//! Opt-in flexible rows and columns. Sizes and offsets use logical pixels.
//!
//! A flex item can have a preferred size, a separate starting basis, and independent
//! permission to grow or shrink. The default item preserves its preferred size.
//! The existing `Stack` and `Wrap` declarations keep their original sizing rules.

use crate::place::stack_line;
use crate::placement_geometry::{RustFloat, line_start_and_gap};
use crate::{Arrange, Axis, Margin, Xy, XyRect};
use std::ops::Range;

#[path = "flex_balance.rs"]
mod balance;

/// The outer main-axis size from which flexible sizing begins.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub enum FlexBasis {
    /// Use the item's preferred outer size.
    #[default]
    Preferred,
    /// Use the item's intrinsic content contribution, including its padding.
    Content,
    /// A fixed outer size in logical pixels.
    Pixels(f32),
    /// A fraction of the container's full inner main size, before gaps.
    Fraction(f32),
    /// Fraction of the inner main size plus a fixed outer-box adjustment.
    FractionPlus(f32, f32),
    /// Fill available space after the item's main-axis margins.
    Stretch,
    /// Size to the available space within the content minimum and preferred size.
    FitContent(f32),
}

/// Whether to collect items into one line or successive lines.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum FlexWrap {
    /// Always collect one line, allowing main-axis overflow.
    #[default]
    NoWrap,
    /// Start a new line when the next item and gap exceed the available space.
    Wrap,
    /// Wrap, with lines advancing from the opposite cross edge.
    WrapReverse,
    /// Balance widths of consecutive lines, requesting at least this many nonempty lines.
    Balance {
        /// Minimum number of lines, limited by the number of items.
        lines: u16,
        /// Advance lines from the opposite cross edge.
        reverse: bool,
    },
}

/// Alignment within a flex line. Safe alignment falls back to Start on overflow.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum FlexAlign {
    /// Align the margin box to the cross-start edge.
    Start,
    /// Align the margin box to the cross-end edge.
    End,
    /// Center the margin box on the cross axis.
    Center,
    /// Expand an eligible item to fill the cross size within its bounds.
    #[default]
    Stretch,
    /// Align first baselines toward the cross-start edge.
    FirstBaseline,
    /// Align last baselines toward the cross-end edge.
    LastBaseline,
    /// Center when the item fits, otherwise use Start.
    SafeCenter,
    /// Use End when the item fits, otherwise use Start.
    SafeEnd,
}

/// Distribution of flex lines along the cross axis of a wrapping container.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum LineAlign {
    /// Pack lines against the cross-start edge.
    Start,
    /// Pack lines against the cross-end edge.
    End,
    /// Center the group of lines.
    Center,
    /// Add an equal share of positive free space to each line.
    #[default]
    Stretch,
    /// Distribute spare space equally between lines.
    SpaceBetween,
    /// Give every line equal spare space on both sides.
    SpaceAround,
    /// Use equal spare space between lines and at the edges.
    SpaceEvenly,
    /// Center the group when it fits, otherwise use Start.
    SafeCenter,
    /// Use End when the group fits, otherwise use Start.
    SafeEnd,
}

/// Independent flex parameters for one in-flow child. Bounds and margins come
/// from its ordinary layout declarations. Equal order values preserve input order.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct FlexItem {
    /// Starting size on the main axis.
    pub basis: FlexBasis,
    /// Nonnegative share of positive free space. Defaults to zero.
    pub grow: f32,
    /// Nonnegative shrink factor, weighted by the inner basis. Defaults to zero.
    pub shrink: f32,
    /// Visual sort key. Smaller keys appear first.
    pub order: i32,
    /// Individual cross alignment. An absent override inherits the container policy.
    pub align_self: Option<FlexAlign>,
}

impl FlexItem {
    /// The CSS initial flexibility policy, `flex: 0 1 auto`.
    pub fn css() -> Self {
        Self {
            shrink: 1.0,
            ..Self::default()
        }
    }
}

/// Formatting policy for a row or column.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FlexLayout {
    /// Physical axis after resolving the container's writing direction.
    pub axis: Axis,
    /// Place the first item against the far edge of the main axis.
    pub reverse: bool,
    /// Begin at the far cross edge. WrapReverse reverses this direction again.
    pub cross_reverse: bool,
    /// Line collection and cross direction.
    pub wrap: FlexWrap,
    /// Minimum spacing between neighboring items on a line.
    pub gap: f32,
    /// Minimum spacing between adjacent lines.
    pub line_gap: f32,
    /// Distribution of unused main-axis space after flexible sizing and margins.
    pub justify: Arrange,
    /// Fall back to Start when Center or End would overflow the main-start edge.
    pub safe_justify: bool,
    /// Default cross alignment for children.
    pub align_items: FlexAlign,
    /// Distribution of wrapped lines across the container.
    pub align_content: LineAlign,
}

impl Default for FlexLayout {
    fn default() -> Self {
        Self {
            axis: Axis::X,
            reverse: false,
            cross_reverse: false,
            wrap: FlexWrap::NoWrap,
            gap: 0.0,
            line_gap: 0.0,
            justify: Arrange::Start,
            safe_justify: false,
            align_items: FlexAlign::Stretch,
            align_content: LineAlign::Stretch,
        }
    }
}

/// Measurement inputs for one in-flow item in physical X/Y coordinates. Supply
/// finite dimensions, with positive infinity permitted for an absent maximum.
/// All sizes include padding. A baseline is a distance from the physical start
/// (left or top) edge on the cross axis. An omitted baseline uses the far border edge.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct FlexMetrics {
    /// Flex declarations of this child.
    pub item: FlexItem,
    /// Preferred outer width and height, including padding.
    pub preferred: Xy<f32>,
    /// Measured intrinsic outer size along the main axis.
    pub content_main: f32,
    /// Minimum outer dimensions.
    pub min: Xy<f32>,
    /// Maximum outer dimensions. A conflicting minimum takes precedence.
    pub max: Xy<f32>,
    /// Physical padding on each axis in low-to-high order.
    pub padding: Xy<[f32; 2]>,
    /// Physical margins on each axis in low-to-high order.
    pub margin: Xy<[Margin; 2]>,
    /// Whether Stretch may change this child’s cross size.
    pub stretch_cross: bool,
    /// Optional first baseline in the physical cross axis.
    pub first_baseline: Option<f32>,
    /// Optional last baseline in the physical cross axis.
    pub last_baseline: Option<f32>,
}

impl Default for FlexMetrics {
    fn default() -> Self {
        Self {
            item: FlexItem::default(),
            preferred: Xy::new_symm(0.0),
            content_main: 0.0,
            min: Xy::new_symm(0.0),
            max: Xy::new_symm(f32::INFINITY),
            padding: Xy::new_symm([0.0; 2]),
            margin: Xy::new_symm([Margin::ZERO; 2]),
            stretch_cross: true,
            first_baseline: None,
            last_baseline: None,
        }
    }
}

impl FlexMetrics {
    fn padding_sum(&self, axis: Axis) -> f64 {
        self.padding[axis]
            .into_iter()
            .map(|p| f64::from(p.max(0.0)))
            .sum()
    }

    fn bounded(&self, value: f64, axis: Axis) -> f64 {
        value
            .min(f64::from(self.max[axis]))
            .max(f64::from(self.min[axis]))
            .max(self.padding_sum(axis))
    }

    fn margin_sum(&self, axis: Axis) -> f32 {
        self.margin[axis]
            .into_iter()
            .filter_map(Margin::as_px)
            .sum()
    }
}

/// Children supplying the container's first/last baselines along the main and
/// cross directions. These are indices in the original input order.
#[derive(Default)]
pub(crate) struct FlexGeometry {
    pub(crate) rects: Vec<XyRect>,
    pub(crate) natural_cross: f32,
    #[cfg(feature = "incremental")]
    pub(crate) baseline_items: Option<[[usize; 2]; 2]>,
}

struct WorkingItem<'a> {
    input: &'a FlexMetrics,
    index: usize,
    basis: f64,
    hypothetical: f64,
    target: f64,
    frozen: bool,
    violation: f64,
}

impl WorkingItem<'_> {
    fn factor(&self, grow: bool) -> f64 {
        let factor = if grow {
            self.input.item.grow
        } else {
            self.input.item.shrink
        };
        if factor.is_finite() {
            f64::from(factor.max(0.0))
        } else {
            0.0
        }
    }

    fn weight(&self, grow: bool, axis: Axis) -> f64 {
        if grow {
            self.factor(true)
        } else {
            self.factor(false) * (self.basis - self.input.padding_sum(axis)).max(0.0)
        }
    }
}

struct BaselineGroup {
    before: f32,
    after: f32,
}

impl Default for BaselineGroup {
    fn default() -> Self {
        // Either margin can be negative, even for the first participant.
        Self {
            before: f32::NEG_INFINITY,
            after: f32::NEG_INFINITY,
        }
    }
}

#[derive(Default)]
struct Line {
    items: Range<usize>,
    cross_size: f32,
    first: BaselineGroup,
    last: BaselineGroup,
}

fn alignment(item: &FlexMetrics, parent: &FlexLayout) -> FlexAlign {
    item.item.align_self.unwrap_or(parent.align_items)
}

fn cross_margins(item: &FlexMetrics, axis: Axis, reverse: bool) -> [Option<f32>; 2] {
    let [a, b] = item.margin[axis].map(Margin::as_px);
    if reverse { [b, a] } else { [a, b] }
}

fn baseline(item: &FlexMetrics, align: FlexAlign, size: f32, reversed: bool) -> f32 {
    let value = if align == FlexAlign::FirstBaseline {
        item.first_baseline
    } else {
        item.last_baseline
    };
    let from_start = value.unwrap_or(size);
    if reversed {
        size - from_start
    } else {
        from_start
    }
}

fn line_cross(items: &[WorkingItem], layout: &FlexLayout, reversed: bool, line: &mut Line) {
    let axis = layout.axis.other();
    for state in items {
        let item = state.input;
        let size = item.bounded(f64::from(item.preferred[axis]), axis) as f32;
        let margins = cross_margins(item, axis, reversed);
        line.cross_size = line.cross_size.max(size + item.margin_sum(axis));
        let align = alignment(item, layout);
        let group = match align {
            FlexAlign::FirstBaseline => &mut line.first,
            FlexAlign::LastBaseline => &mut line.last,
            _ => continue,
        };
        if let [Some(before), Some(after)] = margins {
            let offset = baseline(item, align, size, reversed);
            group.before = group.before.max(before + offset);
            group.after = group.after.max(size - offset + after);
        }
    }
    line.cross_size = line
        .cross_size
        .max(line.first.before + line.first.after)
        .max(line.last.before + line.last.after);
}

// Resolve flexible lengths against this line's budget. Only the sign of the
// total bound violation determines which side freezes: a lower and an upper
// bound can be violated in the same provisional distribution.
fn distribute(items: &mut [WorkingItem], axis: Axis, inner: f32, gap: f32) {
    let margins: f64 = items
        .iter()
        .map(|s| f64::from(s.input.margin_sum(axis)))
        .sum();
    let budget = f64::from(inner) - margins - f64::from(gap) * items.len().saturating_sub(1) as f64;
    let grow = items.iter().map(|s| s.hypothetical).sum::<f64>() < budget;
    for s in items.iter_mut() {
        s.frozen = s.factor(grow) == 0.0
            || if grow {
                s.basis > s.hypothetical
            } else {
                s.basis < s.hypothetical
            };
        s.target = if s.frozen { s.hypothetical } else { s.basis };
    }
    let initial = budget - items.iter().map(|s| s.target).sum::<f64>();
    loop {
        let mut factors = 0.0;
        let mut weights = 0.0;
        let mut remaining = budget;
        for s in items.iter() {
            if s.frozen {
                remaining -= s.target;
            } else {
                remaining -= s.basis;
                factors += s.factor(grow);
                weights += s.weight(grow, axis);
            }
        }
        if factors == 0.0 {
            break;
        }
        if factors < 1.0 && (initial * factors).abs() < remaining.abs() {
            remaining = initial * factors;
        }
        let delta = if grow { remaining } else { -remaining.abs() };
        let mut total_violation = 0.0;
        for s in items.iter_mut().filter(|s| !s.frozen) {
            let proposed = if weights > 0.0 {
                s.basis + delta * (s.weight(grow, axis) / weights)
            } else {
                s.basis
            };
            s.target = s.input.bounded(proposed, axis);
            s.violation = s.target - proposed;
            total_violation += s.violation;
        }
        if total_violation == 0.0 || !total_violation.is_finite() {
            break;
        }
        for s in items.iter_mut().filter(|s| !s.frozen) {
            s.frozen = if total_violation > 0.0 {
                s.violation > 0.0
            } else {
                s.violation < 0.0
            };
        }
    }
}

fn line_distribution(
    align: LineAlign,
    extent: f32,
    total: f32,
    n: u32,
    gap: f32,
) -> (f32, f32, f32) {
    let arrange = match align {
        LineAlign::Stretch => return (0.0, gap, (extent - total).max(0.0) / n as f32),
        LineAlign::Start => Arrange::Start,
        LineAlign::SafeCenter | LineAlign::SafeEnd if total > extent => Arrange::Start,
        LineAlign::Center | LineAlign::SafeCenter => Arrange::Center,
        LineAlign::End | LineAlign::SafeEnd => Arrange::End,
        LineAlign::SpaceBetween => Arrange::SpaceBetween,
        LineAlign::SpaceAround => Arrange::SpaceAround,
        LineAlign::SpaceEvenly => Arrange::SpaceEvenly,
    };
    let (start, gap) = line_start_and_gap::<RustFloat>(arrange, [0.0, extent], total, n, gap);
    (start, gap, 0.0)
}

fn cross_edges(item: &FlexMetrics, layout: &FlexLayout, line: &Line, reversed: bool) -> [f32; 2] {
    let axis = layout.axis.other();
    let [before, after] = cross_margins(item, axis, reversed);
    let auto = before.is_none() || after.is_none();
    let before_px = before.unwrap_or(0.0);
    let room = line.cross_size - before_px - after.unwrap_or(0.0);
    let align = alignment(item, layout);
    let stretch = !auto && align == FlexAlign::Stretch && item.stretch_cross;
    let preferred = if stretch { room } else { item.preferred[axis] };
    let size = item.bounded(f64::from(preferred), axis) as f32;
    let free = room - size;
    let start = if auto {
        let auto_count = u8::from(before.is_none()) + u8::from(after.is_none());
        before.unwrap_or(free.max(0.0) / f32::from(auto_count))
    } else {
        match align {
            FlexAlign::SafeCenter | FlexAlign::SafeEnd if free < 0.0 => before_px,
            FlexAlign::Center | FlexAlign::SafeCenter => before_px + free / 2.0,
            FlexAlign::End | FlexAlign::SafeEnd => before_px + free,
            FlexAlign::FirstBaseline => line.first.before - baseline(item, align, size, reversed),
            FlexAlign::LastBaseline => {
                line.cross_size - line.last.after - baseline(item, align, size, reversed)
            }
            FlexAlign::Start | FlexAlign::Stretch => before_px,
        }
    };
    [start, start + size]
}

impl FlexLayout {
    /// Compute outer rectangles relative to the container's content origin.
    /// The returned vector follows tree order even when the visual order differs.
    /// Supply only in-flow children. Margins stay outside the returned rectangles.
    pub fn resolve(&self, inner: Xy<f32>, items: &[FlexMetrics]) -> Vec<XyRect> {
        self.resolve_and_measure(inner, items).0
    }

    /// The natural single-line main extent before a containing size is known.
    /// A growable child contributes its preferred size even when growth starts
    /// at a smaller basis. A percentage basis has no reference yet and uses
    /// the content contribution at this phase.
    pub fn intrinsic_main(&self, items: &[FlexMetrics]) -> f32 {
        let axis = self.axis;
        let gap = f64::from(self.gap.max(0.0));
        let contribution = |item: &FlexMetrics| {
            let preferred = item.preferred[axis];
            let basis = match item.item.basis {
                FlexBasis::Preferred => preferred,
                FlexBasis::Content
                | FlexBasis::Fraction(_)
                | FlexBasis::FractionPlus(_, _)
                | FlexBasis::FitContent(_)
                | FlexBasis::Stretch => item.content_main,
                FlexBasis::Pixels(px) => px,
            };
            let contribution = if item.item.grow > 0.0 {
                basis.max(preferred)
            } else {
                basis
            };
            item.bounded(f64::from(contribution), axis) + f64::from(item.margin_sum(axis))
        };
        if let FlexWrap::Balance { lines, .. } = self.wrap
            && lines > 1
        {
            let sizes: Vec<_> = items.iter().map(contribution).collect();
            return balance::ranges(&sizes, gap, f64::INFINITY, lines)
                .into_iter()
                .map(|r| {
                    sizes[r.clone()].iter().sum::<f64>() + gap * r.len().saturating_sub(1) as f64
                })
                .fold(0., f64::max) as f32;
        }
        let extents: f64 = items.iter().map(contribution).sum();
        (extents + gap * items.len().saturating_sub(1) as f64).max(0.0) as f32
    }

    /// Compute rectangles and the natural cross extent of the collected lines,
    /// before cross-axis alignment consumes the container's unused space.
    pub fn resolve_and_measure(&self, inner: Xy<f32>, items: &[FlexMetrics]) -> (Vec<XyRect>, f32) {
        let geometry = self.geometry(inner, items, false);
        (geometry.rects, geometry.natural_cross)
    }

    pub(crate) fn geometry(
        &self,
        inner: Xy<f32>,
        items: &[FlexMetrics],
        _export_baselines: bool,
    ) -> FlexGeometry {
        if items.is_empty() {
            return FlexGeometry::default();
        }
        let main = self.axis;
        let cross = main.other();
        let limit = inner[main].max(0.0);
        let cross_limit = inner[cross].max(0.0);
        let cross_reverse = self.cross_reverse
            ^ matches!(
                self.wrap,
                FlexWrap::WrapReverse | FlexWrap::Balance { reverse: true, .. }
            );
        let gap = self.gap.max(0.0);
        let line_gap = self.line_gap.max(0.0);
        let mut states: Vec<_> = items
            .iter()
            .enumerate()
            .map(|(index, input)| {
                let basis = match input.item.basis {
                    FlexBasis::Preferred => f64::from(input.preferred[main]),
                    FlexBasis::Content => f64::from(input.content_main),
                    FlexBasis::Pixels(px) => f64::from(px),
                    FlexBasis::Fraction(f) => f64::from(limit) * f64::from(f),
                    FlexBasis::FractionPlus(f, p) => f64::from(limit) * f64::from(f) + f64::from(p),
                    FlexBasis::Stretch => f64::from(limit - input.margin_sum(main)),
                    FlexBasis::FitContent(min) => f64::from(
                        input
                            .content_main
                            .min((limit - input.margin_sum(main)).max(min)),
                    ),
                }
                .max(input.padding_sum(main));
                WorkingItem {
                    input,
                    index,
                    basis,
                    hypothetical: input.bounded(basis, main),
                    target: basis,
                    frozen: false,
                    violation: 0.0,
                }
            })
            .collect();
        if !states
            .windows(2)
            .all(|pair| pair[0].input.item.order <= pair[1].input.item.order)
        {
            states.sort_by_key(|state| state.input.item.order);
        }
        let mut lines = Vec::new();
        let mut start = 0;
        let mut used = 0.0f64;
        if let FlexWrap::Balance { lines: minimum, .. } = self.wrap {
            let widths: Vec<_> = states
                .iter()
                .map(|s| s.hypothetical + f64::from(s.input.margin_sum(main)))
                .collect();
            lines.extend(
                balance::ranges(&widths, f64::from(gap), f64::from(limit), minimum)
                    .into_iter()
                    .map(|items| Line {
                        items,
                        ..Default::default()
                    }),
            );
        } else if self.wrap != FlexWrap::NoWrap {
            for (i, state) in states.iter().enumerate() {
                let extent = state.hypothetical + f64::from(state.input.margin_sum(main));
                if i > start && used + f64::from(gap) + extent > f64::from(limit) {
                    lines.push(Line {
                        items: start..i,
                        ..Line::default()
                    });
                    start = i;
                    used = 0.0;
                }
                used += extent + if i > start { f64::from(gap) } else { 0.0 };
            }
        }
        if !matches!(self.wrap, FlexWrap::Balance { .. }) {
            lines.push(Line {
                items: start..states.len(),
                ..Line::default()
            });
        }
        for line in &mut lines {
            let slice = &mut states[line.items.clone()];
            distribute(slice, main, limit, gap);
            line_cross(slice, self, cross_reverse, line);
        }
        #[cfg(feature = "incremental")]
        let baseline_items = _export_baselines.then(|| {
            let wrap_reverse = matches!(
                self.wrap,
                FlexWrap::WrapReverse | FlexWrap::Balance { reverse: true, .. }
            );
            let line_sources = |last: bool| {
                let line = if last ^ wrap_reverse {
                    &lines[lines.len() - 1]
                } else {
                    &lines[0]
                };
                let group = &states[line.items.clone()];
                let edge = |end| {
                    if end {
                        group.last().unwrap()
                    } else {
                        &group[0]
                    }
                };
                let kind = if last {
                    FlexAlign::LastBaseline
                } else {
                    FlexAlign::FirstBaseline
                };
                let eligible = |s: &&WorkingItem| {
                    alignment(s.input, self) == kind
                        && s.input.margin[cross].iter().all(|m| m.as_px().is_some())
                };
                let participant = if last {
                    group.iter().rev().find(eligible)
                } else {
                    group.iter().find(eligible)
                };
                (
                    edge(last ^ self.reverse).index,
                    participant.unwrap_or_else(|| edge(last)).index,
                )
            };
            let (main_first, cross_first) = line_sources(false);
            let (main_last, cross_last) = line_sources(true);
            [[main_first, main_last], [cross_first, cross_last]]
        });
        let natural_cross =
            lines.iter().map(|l| l.cross_size).sum::<f32>() + line_gap * (lines.len() - 1) as f32;
        let (mut line_start, line_step, stretch) = if self.wrap == FlexWrap::NoWrap {
            lines[0].cross_size = cross_limit;
            (0.0, 0.0, 0.0)
        } else {
            line_distribution(
                self.align_content,
                cross_limit,
                natural_cross,
                lines.len() as u32,
                line_gap,
            )
        };
        let mut result = vec![Xy::new_symm([0.0; 2]); items.len()];
        for line in &mut lines {
            line.cross_size += stretch;
            let slice = &states[line.items.clone()];
            let n = slice.len();
            let total = slice
                .iter()
                .map(|s| s.target as f32 + s.input.margin_sum(main))
                .sum::<f32>()
                + gap * (n - 1) as f32;
            let autos = slice
                .iter()
                .flat_map(|s| s.input.margin[main])
                .filter(|m| m.as_px().is_none())
                .count();
            let free = limit - total;
            let auto = if autos > 0 {
                free.max(0.0) / autos as f32
            } else {
                0.0
            };
            let arrange = if auto > 0.0 || self.safe_justify && free < 0.0 {
                Arrange::Start
            } else {
                self.justify
            };
            let (mut cursor, step) =
                line_start_and_gap::<RustFloat>(arrange, [0.0, limit], total, n as u32, gap);
            for state in slice {
                let margins = state.input.margin[main].map(|m| m.as_px().unwrap_or(auto));
                let rect = &mut result[state.index];
                rect[main] = stack_line::place(
                    &mut cursor,
                    self.reverse,
                    [0.0, limit],
                    state.target as f32,
                    margins,
                    step,
                );
                let [lo, hi] = cross_edges(state.input, self, line, cross_reverse);
                rect[cross] = if cross_reverse {
                    [
                        cross_limit - (line_start + hi),
                        cross_limit - (line_start + lo),
                    ]
                } else {
                    [line_start + lo, line_start + hi]
                };
            }
            line_start += line.cross_size + line_step;
        }
        FlexGeometry {
            rects: result,
            natural_cross,
            #[cfg(feature = "incremental")]
            baseline_items,
        }
    }
}
