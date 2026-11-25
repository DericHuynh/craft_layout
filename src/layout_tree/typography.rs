//! Measured horizontal text and control baselines for the owned layout tree.
use super::*;
use std::collections::HashMap;

/// Horizontal content-box contributions supplied by the text or widget host.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct IntrinsicWidths {
    minimum: f32,
    maximum: f32,
}

impl IntrinsicWidths {
    /// Build an ordered pair of finite, nonnegative advances, in logical pixels.
    /// A zero-width glyph run is valid.
    pub fn new(minimum: f32, maximum: f32) -> Option<Self> {
        (minimum.is_finite() && maximum.is_finite() && 0.0 <= minimum && minimum <= maximum)
            .then_some(Self { minimum, maximum })
    }
    /// The widest contribution under the host's available line-breaking opportunities.
    pub fn min_content(self) -> f32 {
        self.minimum
    }
    /// The unwrapped contribution, respecting forced breaks.
    pub fn max_content(self) -> f32 {
        self.maximum
    }
}

/// An intrinsic contribution to use for a measured leaf's horizontal size or bound.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum IntrinsicWidth {
    /// The host's smallest intrinsic content-box width.
    MinContent,
    /// The host's largest intrinsic content-box width.
    MaxContent,
    /// Fit to the supplied content-box limit, clamped between both intrinsic widths.
    FitContent(f32),
}

impl IntrinsicWidth {
    fn width(self, widths: IntrinsicWidths) -> f32 {
        match self {
            Self::MinContent => widths.minimum,
            Self::MaxContent => widths.maximum,
            Self::FitContent(limit) => limit.clamp(widths.minimum, widths.maximum),
        }
    }
}

/// Select which horizontal declarations should use intrinsic content metrics.
/// An unspecified field retains the corresponding authored size or bound.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct IntrinsicSizing {
    /// Preferred width contribution.
    pub preferred: Option<IntrinsicWidth>,
    /// Minimum width contribution.
    pub minimum: Option<IntrinsicWidth>,
    /// Maximum width contribution.
    pub maximum: Option<IntrinsicWidth>,
}

/// A horizontal line layout's extent and baselines in logical pixels.
/// Baselines are measured downwards from the content-box top.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct InlineMetrics {
    height: f32,
    first: f32,
    last: f32,
}

impl InlineMetrics {
    /// Construct finite line metrics. Negative baseline offsets are permitted.
    pub fn new(height: f32, first: f32, last: f32) -> Option<Self> {
        (height.is_finite()
            && height >= 0.0
            && first.is_finite()
            && last.is_finite()
            && first <= last)
            .then_some(Self {
                height,
                first,
                last,
            })
    }
    /// Total laid-out content height at the requested width.
    pub fn height(self) -> f32 {
        self.height
    }
    /// First line baseline offset from the content-box top.
    pub fn first_baseline(self) -> f32 {
        self.first
    }
    /// Last line baseline offset from the content-box top.
    pub fn last_baseline(self) -> f32 {
        self.last
    }
}

/// Rich text or atomic-control measurement. All inputs affecting returned metrics
/// (including font, language, and breaking policy) belong to the host. Report
/// content changes to the tree, and invalidate the tree on a global font change.
pub trait InlineMeasurer<T> {
    /// Minimum and maximum content-box widths, before padding.
    fn intrinsic_widths(&mut self, node: &NodeId, content: Option<&T>) -> IntrinsicWidths;
    /// Measure height and both baseline offsets at the supplied content-box width.
    /// `None` requests the unwrapped layout. Atomic boxes without typography use
    /// their bottom border-box edge as a synthesized baseline.
    fn measure_lines(
        &mut self,
        node: &NodeId,
        content: Option<&T>,
        width: Option<f32>,
    ) -> InlineMetrics;
}

/// The baselines to share between in-flow siblings in a horizontal stack or wrap line.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Baseline {
    /// Align first baselines and pack the group against the top of the line.
    First,
    /// Align last baselines and pack the group against the bottom of the line.
    Last,
}

/// Errors encountered when applying measured typography.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TypographyError {
    /// A fit-content limit must be finite and nonnegative.
    InvalidLimit,
    /// The registered alignment parent must be a horizontal stack or wrapping row.
    ExpectedHorizontalRow,
    /// A changed width and a changed baseline repeatedly fed back into one another.
    UnstableMeasurements,
    /// An edit used a foreign or removed handle.
    Tree(TreeError),
}

impl From<TreeError> for TypographyError {
    fn from(error: TreeError) -> Self {
        Self::Tree(error)
    }
}
impl std::fmt::Display for TypographyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for TypographyError {}

#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub(crate) struct TypographyPatch {
    widths: [Option<f32>; 3],
    placement: Option<(Pos, usize, f32)>,
    baselines: Xy<Option<f32>>,
}

impl TypographyPatch {
    pub(crate) fn apply(&self, params: &mut LayoutParams) {
        let padding = params.padding.x[0] + params.padding.x[1];
        if let Some(width) = self.widths[0] {
            params.size.x = Size::Pixels(width + padding);
        }
        if let Some(width) = self.widths[1] {
            params.min_size.x = Some(Size::Pixels(width + padding));
        }
        if let Some(width) = self.widths[2] {
            params.max_size.x = Some(Size::Pixels(width + padding));
        }
        if let Some((position, edge, extra)) = self.placement {
            params.position.y = position;
            let prior = params.margin.y[edge].as_px().unwrap_or(0.0);
            params.margin.y[edge] = Margin::px(prior + extra).unwrap_or(params.margin.y[edge]);
        }
    }

    pub(crate) fn baselines(&self) -> Xy<Option<f32>> {
        self.baselines
    }
}

#[derive(Clone, Debug, Default)]
struct CacheEntry {
    widths: Option<IntrinsicWidths>,
    last_layout: Option<(Option<u32>, InlineMetrics)>,
}

impl CacheEntry {
    fn widths<T>(
        &mut self,
        measurer: &mut impl InlineMeasurer<T>,
        id: &NodeId,
        context: Option<&T>,
    ) -> IntrinsicWidths {
        *self
            .widths
            .get_or_insert_with(|| measurer.intrinsic_widths(id, context))
    }

    fn lines<T>(
        &mut self,
        measurer: &mut impl InlineMeasurer<T>,
        id: &NodeId,
        context: Option<&T>,
        width: Option<f32>,
    ) -> InlineMetrics {
        let bits = width.map(f32::to_bits);
        if let Some((key, metrics)) = self.last_layout
            && key == bits
        {
            return metrics;
        }
        let metrics = measurer.measure_lines(id, context, width);
        self.last_layout = Some((bits, metrics));
        metrics
    }
}

#[derive(Debug, Default)]
pub(super) struct TypographyState {
    widths: HashMap<NodeKey, IntrinsicSizing>,
    rows: HashMap<NodeKey, Baseline>,
    cache: HashMap<NodeKey, CacheEntry>,
    patches: HashMap<NodeKey, TypographyPatch>,
}

impl TypographyState {
    pub(super) fn for_clone(&self) -> Self {
        Self {
            widths: self.widths.clone(),
            rows: self.rows.clone(),
            patches: self.patches.clone(),
            cache: HashMap::new(),
        }
    }
    pub(super) fn invalidate_node(&mut self, id: NodeKey) {
        self.cache.remove(&id);
    }
    pub(super) fn invalidate(&mut self) {
        self.cache.clear();
    }
}

impl<T> LayoutTree<T> {
    /// Set intrinsic width contributions for a horizontal text or atomic control.
    /// Padding is added once. Pass the default binding to return to authored widths.
    pub fn set_intrinsic_sizing(
        &mut self,
        id: &NodeId,
        sizing: IntrinsicSizing,
    ) -> Result<(), TypographyError> {
        self.resolve_node(id)?;
        for size in [sizing.preferred, sizing.minimum, sizing.maximum]
            .into_iter()
            .flatten()
        {
            if let IntrinsicWidth::FitContent(limit) = size
                && (!limit.is_finite() || limit < 0.0)
            {
                return Err(TypographyError::InvalidLimit);
            }
        }
        let state = self.typography.get_or_insert_with(Default::default);
        if sizing == IntrinsicSizing::default() {
            state.widths.remove(&id.key());
        } else {
            state.widths.insert(id.key(), sizing);
        }
        Ok(())
    }

    /// Align all in-flow children of a horizontal stack or wrap row. Hidden and
    /// free-positioned children are excluded. Baselines are scoped to each wrap line.
    /// Use `TextContent::Wrapping` or `Fixed` for text; a plain widget aligns on
    /// its bottom edge. Pass `None` to restore every child's authored placement.
    pub fn set_baseline_alignment(
        &mut self,
        row: &NodeId,
        which: Option<Baseline>,
    ) -> Result<(), TypographyError> {
        let layout = self.params(row)?.children_layout;
        if which.is_some() && !horizontal_row(layout) {
            return Err(TypographyError::ExpectedHorizontalRow);
        }
        let state = self.typography.get_or_insert_with(Default::default);
        if let Some(baseline) = which {
            state.rows.insert(row.key(), baseline);
        } else {
            state.rows.remove(&row.key());
        }
        Ok(())
    }

    /// Return cached intrinsic content-box widths when this node has been measured.
    pub fn measured_widths(&self, id: &NodeId) -> Result<Option<IntrinsicWidths>, TreeError> {
        self.resolve_node(id)?;
        Ok(self
            .typography
            .as_ref()
            .and_then(|s| s.cache.get(&id.key())?.widths))
    }

    /// Resolve intrinsic widths, wrapped heights and first/last baselines using the
    /// ordinary retained layout path. Use this entry point consistently for scenes
    /// with rich text, and call `invalidate` if the host replaces the measurer.
    pub fn solve_layout_with_typography(
        &mut self,
        window: Xy<f32>,
        measurer: &mut impl InlineMeasurer<T>,
    ) -> Result<IncrementalRelayoutOutcome, TypographyError> {
        self.solve_layout_with_typography_and_content(window, measurer, super::zero_content::<T>)
    }

    /// The measured solve with an additional content callback for non-text widgets.
    pub fn solve_layout_with_typography_and_content(
        &mut self,
        window: Xy<f32>,
        measurer: &mut impl InlineMeasurer<T>,
        mut content: impl FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
    ) -> Result<IncrementalRelayoutOutcome, TypographyError> {
        let mut state = self.typography.take().unwrap_or_default();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            state.solve(self, window, measurer, &mut content)
        }));
        self.typography = Some(state);
        result.unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    }
}

fn horizontal_row(layout: ChildrenLayout) -> bool {
    matches!(
        layout,
        ChildrenLayout::Stack { axis: Axis::X, .. } | ChildrenLayout::Wrap { axis: Axis::X, .. }
    )
}

impl TypographyState {
    fn solve<T>(
        &mut self,
        tree: &mut LayoutTree<T>,
        window: Xy<f32>,
        measurer: &mut impl InlineMeasurer<T>,
        mut content: impl FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
    ) -> Result<IncrementalRelayoutOutcome, TypographyError> {
        self.widths.retain(|k, _| tree.nodes.contains_key(*k));
        self.rows.retain(|k, _| tree.nodes.contains_key(*k));
        self.cache.retain(|k, _| tree.nodes.contains_key(*k));
        self.patches.retain(|k, _| tree.nodes.contains_key(*k));

        let mut next = HashMap::<NodeKey, TypographyPatch>::new();
        for (&key, &sizing) in &self.widths {
            let node = &tree.nodes[key];
            if node.params.disabled {
                continue;
            }
            let id = tree.node_id(key);
            let metrics =
                self.cache
                    .entry(key)
                    .or_default()
                    .widths(measurer, &id, tree.context(node));
            let widths = [sizing.preferred, sizing.minimum, sizing.maximum]
                .map(|v| v.map(|s| s.width(metrics)));
            next.entry(key).or_default().widths = widths;
        }
        for &key in self.rows.keys() {
            if !horizontal_row(tree.params(&tree.node_id(key))?.children_layout) {
                return Err(TypographyError::ExpectedHorizontalRow);
            }
        }
        // Preserve the last baseline estimate while solving the current widths.
        // This lets an idle solve take the normal no-change path.
        for (&key, old) in &self.patches {
            let patch = next.entry(key).or_default();
            patch.baselines = old.baselines;
            patch.placement = old.placement;
        }
        self.install(tree, &next)?;
        let managed_rows = tree.rules_state.possible_baseline_contexts();
        let mut first = None;
        for _ in 0..(self.rows.len() + managed_rows)
            .saturating_mul(2)
            .saturating_add(4)
        {
            let outcome = tree.solve_layout_with_measurers(
                window,
                |id, ctx, width| {
                    let cache = self.cache.entry(id.key()).or_default();
                    let ctx = ctx.as_deref();
                    let x = cache.widths(measurer, &id, ctx).maximum;
                    let y = cache.lines(measurer, &id, ctx, width).height;
                    Xy::new(x, y)
                },
                &mut content,
            );
            first.get_or_insert(outcome);
            for patch in next.values_mut() {
                patch.placement = None;
                patch.baselines = Xy::new_symm(None);
            }
            for (&row, &align) in &self.rows {
                if tree.nodes[row].params.disabled {
                    continue;
                }
                let mut line = Vec::new();
                let parent = &tree.nodes[row];
                let wraps = matches!(parent.params.children_layout, ChildrenLayout::Wrap { .. });
                let mut cursor = parent.first_child;
                while let Some(key) = cursor {
                    let node = &tree.nodes[key];
                    cursor = node.next_sibling;
                    if node.params.disabled || node.params.free_placement {
                        continue;
                    }
                    if wraps && node.layout.flags.starts_wrap_line() && !line.is_empty() {
                        align_line(
                            &mut line,
                            align,
                            parent.params.children_origin_flipped.y,
                            &mut next,
                        );
                    }
                    let item = Self::line_item(&mut self.cache, tree, key, measurer)?;
                    next.entry(key).or_default().baselines =
                        Xy::new(Some(item.metric[0]), Some(item.metric[1]));
                    line.push(item);
                }
                align_line(
                    &mut line,
                    align,
                    parent.params.children_origin_flipped.y,
                    &mut next,
                );
            }
            for (&row, &alignment) in &tree.rules_state.baseline_contexts {
                let parent = &tree.nodes[row];
                if parent.params.disabled {
                    continue;
                }
                let mut cursor = parent.first_child;
                while let Some(key) = cursor {
                    let node = &tree.nodes[key];
                    cursor = node.next_sibling;
                    let style = tree.params(&tree.node_id(key))?;
                    if style.disabled || style.free_placement || style.text == TextContent::None {
                        continue;
                    }
                    let rule = tree.rules(&tree.node_id(key))?;
                    if !alignment.aligns(rule) {
                        continue;
                    }
                    let item = Self::line_item(&mut self.cache, tree, key, measurer)?;
                    next.entry(key).or_default().baselines =
                        Xy::new(Some(item.metric[0]), Some(item.metric[1]));
                }
            }
            next.retain(|_, p| *p != TypographyPatch::default());
            if !self.install(tree, &next)? {
                return Ok(first.unwrap_or(outcome));
            }
        }
        Err(TypographyError::UnstableMeasurements)
    }

    fn line_item<T>(
        cache: &mut HashMap<NodeKey, CacheEntry>,
        tree: &LayoutTree<T>,
        key: NodeKey,
        measurer: &mut impl InlineMeasurer<T>,
    ) -> Result<LineItem, TreeError> {
        let id = tree.node_id(key);
        let node = &tree.nodes[key];
        let size = tree.published_size(key, node);
        let style = tree.params(&id)?;
        let metric = if style.text == TextContent::None {
            [size.y; 2]
        } else {
            let width = (size.x - style.padding.x[0] - style.padding.x[1]).max(0.0);
            let constraint = style.text_wraps_on(Axis::Y).then_some(width);
            let m =
                cache
                    .entry(key)
                    .or_default()
                    .lines(measurer, &id, tree.context(node), constraint);
            [m.first + style.padding.y[0], m.last + style.padding.y[0]]
        };
        Ok(LineItem {
            key,
            height: size.y,
            metric,
            margin: style.margin.y.map(|m| m.as_px().unwrap_or(0.0)),
        })
    }

    fn install<T>(
        &mut self,
        tree: &mut LayoutTree<T>,
        next: &HashMap<NodeKey, TypographyPatch>,
    ) -> Result<bool, TreeError> {
        let mut changed = false;
        for &key in self.patches.keys().filter(|k| !next.contains_key(*k)) {
            tree.set_typography_patch(&tree.node_id(key), TypographyPatch::default())?;
            changed = true;
        }
        for (&key, &patch) in next {
            if self.patches.get(&key) != Some(&patch) {
                tree.set_typography_patch(&tree.node_id(key), patch)?;
                changed = true;
            }
        }
        if changed {
            self.patches.clone_from(next);
        }
        Ok(changed)
    }
}

struct LineItem {
    key: NodeKey,
    height: f32,
    metric: [f32; 2],
    margin: [f32; 2],
}

fn align_line(
    line: &mut Vec<LineItem>,
    align: Baseline,
    flipped: bool,
    patches: &mut HashMap<NodeKey, TypographyPatch>,
) {
    let (index, position) = match align {
        Baseline::First => (0, if flipped { Pos::End } else { Pos::Start }),
        Baseline::Last => (1, if flipped { Pos::Start } else { Pos::End }),
    };
    let reach = |item: &LineItem| {
        item.margin[index]
            + if index == 0 {
                item.metric[0]
            } else {
                item.height - item.metric[1]
            }
    };
    let extent = line.iter().map(&reach).fold(f32::NEG_INFINITY, f32::max);
    for item in line.drain(..) {
        let extra = extent - reach(&item);
        patches.entry(item.key).or_default().placement = Some((position, index, extra));
    }
}
