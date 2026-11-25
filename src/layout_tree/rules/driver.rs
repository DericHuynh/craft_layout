//! Lower optional constraints to the same physical declarations consumed by
//! both owned schedulers. Keep author declarations separate from allocations.
use super::{
    BaselineContext, NodeRules, QueryLayout, RuleIssue, State, block, flex, grid, responsive,
    viewport,
};
use crate::flex::{FlexBasis, FlexLayout};
use crate::incremental::SameInput;
use crate::layout_tree::{NodeKey, typography::TypographyPatch};
use crate::logical::WritingContext;
use crate::{
    Anchor, Axis, ChildrenLayout, LayoutParams, LayoutTree, NodeId, Pos, Size, Xy, XyRect,
};
use std::collections::HashMap;
use std::ops::Range;

pub(super) struct FrameNode {
    pub(super) id: NodeId,
    pub(super) parent: Option<usize>,
    pub(super) children: Vec<usize>,
    authored: LayoutParams,
    pub(super) base: LayoutParams,
    pub(super) effective: LayoutParams,
    pub(super) rule: NodeRules,
    layout_query: Option<usize>,
    pub(super) context: WritingContext,
    pub(super) rect: XyRect,
    pub(super) query_content: Option<Xy<f32>>,
    pub(super) natural: Xy<f32>,
    pub(super) measured: Xy<f32>,
    pub(super) overflowing: Xy<bool>,
    pub(super) gutter: Xy<f32>,
    assigned: bool,
    intrinsic_proposal: Xy<Option<f32>>,
}

pub(super) struct Frame<'a> {
    pub(super) nodes: Vec<FrameNode>,
    pub(super) window: Xy<f32>,
    indices: HashMap<NodeKey, usize>,
    patches: &'a HashMap<NodeKey, TypographyPatch>,
    styles: &'a HashMap<NodeKey, NodeRules>,
    pub(super) grid_tracks: HashMap<NodeKey, Xy<Vec<[f32; 2]>>>,
    pub(super) grid_baselines: HashMap<usize, Xy<Vec<[Option<f32>; 2]>>>,
    pub(super) grid_cells: HashMap<usize, Xy<Range<usize>>>,
}

impl<'a> Frame<'a> {
    fn new<T>(
        tree: &LayoutTree<T>,
        window: Xy<f32>,
        styles: &'a HashMap<NodeKey, NodeRules>,
        authored: &HashMap<NodeKey, LayoutParams>,
        patches: &'a HashMap<NodeKey, TypographyPatch>,
    ) -> Self {
        let mut nodes: Vec<FrameNode> = Vec::with_capacity(tree.nodes.len());
        let mut indices = HashMap::with_capacity(tree.nodes.len());
        let mut stack = vec![(tree.root, None::<usize>)];
        while let Some((key, parent)) = stack.pop() {
            let record = &tree.nodes[key];
            let mut params = authored.get(&key).copied().unwrap_or(record.params);
            params.disabled = record.params.disabled;
            let index = nodes.len();
            let mut rule = styles.get(&key).cloned().unwrap_or_default();
            if let Some(patch) = patches.get(&key) {
                let measured = patch.baselines();
                rule.baselines.x = rule.baselines.x.or(measured.x);
                rule.baselines.y = rule.baselines.y.or(measured.y);
            }
            let inherited = parent.map_or_else(WritingContext::default, |p| nodes[p].context);
            let context = rule.logical.context(inherited);
            nodes.push(FrameNode {
                id: tree.node_id(key),
                parent,
                children: Vec::new(),
                authored: params,
                base: params,
                effective: params,
                rule,
                layout_query: None,
                context,
                rect: record.rect,
                query_content: None,
                natural: Xy::new_symm(0.),
                measured: Xy::new_symm(0.),
                overflowing: Xy::new_symm(false),
                gutter: Xy::new_symm(0.),
                assigned: false,
                intrinsic_proposal: Xy::new_symm(None),
            });
            indices.insert(key, index);
            if let Some(p) = parent {
                nodes[p].children.push(index);
            }
            let mut child = record.last_child;
            while let Some(c) = child {
                stack.push((c, Some(index)));
                child = tree.nodes[c].prev_sibling;
            }
        }
        Self {
            window,
            nodes,
            indices,
            patches,
            styles,
            grid_cells: HashMap::new(),
            grid_tracks: HashMap::new(),
            grid_baselines: HashMap::new(),
        }
    }

    pub(super) fn reference(&self, node: usize, target: &NodeId) -> Option<usize> {
        let idx = *self.indices.get(&target.key())?;
        if &self.nodes[idx].id != target || self.nodes[idx].base.disabled {
            return None;
        }
        let mut parent = Some(idx);
        while let Some(i) = parent {
            if i == node {
                return None;
            }
            parent = self.nodes[i].parent;
        }
        Some(idx)
    }

    pub(super) fn content_size(&self, i: usize) -> Xy<f32> {
        let n = &self.nodes[i];
        let mut extent = super::size(n.rect);
        for a in [Axis::X, Axis::Y] {
            if let Size::Pixels(v) = n.effective.size[a] {
                extent[a] = v;
            }
            extent[a] = (extent[a] - n.effective.padding[a].iter().sum::<f32>()).max(0.);
        }
        extent
    }

    pub(super) fn is_intrinsic(&self, i: usize, axis: Axis, size: Size) -> bool {
        match size {
            Size::FitContent => true,
            Size::Auto => self.nodes[i].parent.is_none_or(|p| {
                let parent = &self.nodes[p];
                if let Some(flex) = self.flex_layout(p) {
                    return axis == flex.axis;
                }
                if parent.rule.grid.is_some() {
                    return false;
                }
                match parent.base.children_layout {
                    ChildrenLayout::Block => axis == parent.context.axis(crate::LogicalAxis::Block),
                    _ => true,
                }
            }),
            _ => false,
        }
    }
    fn flex_layout(&self, i: usize) -> Option<FlexLayout> {
        let n = &self.nodes[i];
        let mut f = n.rule.flex?;
        if let Some(main) = n.rule.logical.main_axis {
            f.axis = n.context.axis(main);
        }
        f.reverse ^= n.base.children_origin_flipped[f.axis];
        f.cross_reverse ^= n.base.children_origin_flipped[f.axis.other()];
        Some(f)
    }
    pub(super) fn set_intrinsic(&mut self, i: usize, content: Xy<f32>) {
        for a in [Axis::X, Axis::Y] {
            let p = self.nodes[i].base;
            if matches!(p.size[a], Size::FitContent | Size::Auto | Size::Fill) {
                let mut outer = content[a].max(0.) + p.padding[a].iter().sum::<f32>();
                if let Some(Size::Pixels(max)) = p.max_size[a] {
                    outer = outer.min(max);
                }
                if let Some(Size::Pixels(min)) = p.min_size[a] {
                    outer = outer.max(min);
                }
                self.nodes[i].intrinsic_proposal[a] = Some(outer);
                if !self.nodes[i].assigned && self.is_intrinsic(i, a, p.size[a]) {
                    self.nodes[i].effective.size[a] = Size::Pixels(outer);
                }
            }
        }
    }
    pub(super) fn place(&mut self, i: usize, parent: usize, rect: XyRect) {
        let inner = self.content_size(parent);
        let flipped = self.nodes[parent].effective.children_origin_flipped;
        let n = &mut self.nodes[i];
        n.assigned = true;
        n.effective.free_placement = true;
        for a in [Axis::X, Axis::Y] {
            n.effective.size[a] = Size::Pixels((rect[a][1] - rect[a][0]).max(0.));
            // The formatting context has already applied its item's bounds.
            n.effective.min_size[a] = None;
            n.effective.max_size[a] = None;
            n.effective.position[a] = Pos::Pixels(if flipped[a] {
                inner[a] - rect[a][0]
            } else {
                rect[a][0]
            });
            n.effective.anchor[a] = if flipped[a] {
                Anchor::End
            } else {
                Anchor::Start
            };
        }
    }
    fn prepare(&mut self, issues: &mut Vec<RuleIssue>) {
        self.grid_tracks.clear();
        self.grid_baselines.clear();
        self.grid_cells.clear();
        for i in 0..self.nodes.len() {
            let n = &self.nodes[i];
            let mut p = n.rule.logical.project(n.context, n.authored);
            if let Some(patch) = self.patches.get(&n.id.key()) {
                patch.apply(&mut p);
            }
            let layout_query = if p.disabled {
                None
            } else {
                responsive::apply(self, i, &mut p, issues)
            };
            let gutter = viewport::gutter(n.rule.scroll, n.overflowing);
            p.padding.x[1] += gutter.x;
            p.padding.y[1] += gutter.y;
            if n.rule.placement.out_of_flow() {
                p.free_placement = true;
            }
            let n = &mut self.nodes[i];
            if n.layout_query != layout_query {
                // Only the frame changes. Nested grids, vertical blocks, flex placement
                // and intrinsic probes all read this same selection on this pass.
                (n.rule.flex, n.rule.grid) = match layout_query {
                    Some(index) => match &n.rule.queries[index].style.layout {
                        Some(QueryLayout::Flex(flex)) => (Some(*flex), None),
                        Some(QueryLayout::Grid(grid)) => (None, Some(grid.clone())),
                        _ => (None, None),
                    },
                    None => {
                        let authored = &self.styles[&n.id.key()];
                        (authored.flex, authored.grid.clone())
                    }
                };
                n.layout_query = layout_query;
            }
            n.gutter = gutter;
            p.isolate_block_margins |= n.rule.flex.is_some() || n.rule.grid.is_some();
            n.base = p;
            n.effective = p;
            n.assigned = false;
            if block::vertical(n) {
                n.effective.children_layout = ChildrenLayout::Free;
            }
        }
    }
    fn plan(&mut self, issues: &mut Vec<RuleIssue>) {
        let blocks = block::measure(self);
        for i in 0..self.nodes.len() {
            if self.nodes[i].base.disabled {
                continue;
            }
            viewport::apply(self, i, issues);
            let n = &self.nodes[i];
            if n.rule.flex.is_some() && n.rule.grid.is_some() {
                issues.push(RuleIssue::ConflictingFormattingContexts(n.id.clone()));
            }
            if let Some(g) = &n.rule.grid {
                for a in [Axis::X, Axis::Y] {
                    if matches!(g.tracks[a], crate::tracks::TrackAxis::Subgrid)
                        && !self.grid_cells.contains_key(&i)
                    {
                        issues.push(RuleIssue::MissingParentTracks(n.id.clone(), a));
                    }
                }
            }
            if let Some(layout) = self.flex_layout(i) {
                flex::apply(self, i, layout);
            } else if let Some(layout) = self.nodes[i].rule.grid.clone() {
                grid::apply(self, i, &layout);
            } else if block::vertical(&self.nodes[i]) {
                block::place(self, i, &blocks);
            }
        }
    }
    fn sync<T>(
        &self,
        tree: &mut LayoutTree<T>,
        authored: &mut HashMap<NodeKey, LayoutParams>,
    ) -> bool {
        let mut changed = false;
        for n in &self.nodes {
            let k = n.id.key();
            if !n.effective.same_input(&n.authored) {
                authored.insert(k, n.authored);
            } else {
                authored.remove(&k);
            }
            if !tree.nodes[k].params.same_input(&n.effective) {
                tree.update_effective(&n.id, n.effective)
                    .expect("live frame handle");
                changed = true;
            }
        }
        changed
    }
    fn read<T>(&mut self, tree: &LayoutTree<T>, rounded: bool) {
        for n in &mut self.nodes {
            let k = n.id.key();
            let record = &tree.nodes[k];
            n.rect = record.rect;
            if !rounded {
                let s = tree.published_size(k, record);
                if n.rule.container.is_some() {
                    let content =
                        |a: Axis| (s[a] - record.params.padding[a].iter().sum::<f32>()).max(0.);
                    n.query_content = Some(Xy::new(content(Axis::X), content(Axis::Y)));
                }
                for a in [Axis::X, Axis::Y] {
                    n.rect[a][1] = n.rect[a][0] + s[a];
                }
            }
        }
    }
}

impl State {
    fn run<T, E>(
        &mut self,
        tree: &mut LayoutTree<T>,
        window: Xy<f32>,
        solve: &mut dyn FnMut(&mut LayoutTree<T>) -> Result<(), E>,
    ) -> Result<(), E> {
        if !self.dirty && self.window == Some(window) {
            solve(tree)?;
            let mut frame = Frame::new(tree, window, &self.styles, &self.authored, &self.patches);
            frame.read(tree, true);
            for n in &mut frame.nodes {
                n.effective = tree.nodes[n.id.key()].params;
                // Positioning still evaluates insets against the moving reference box.
                // Its sizes, bounds and margins come from the same resolved style that
                // produced the last layout, including queries and typography.
                n.base = self
                    .positioned_styles
                    .get(&n.id.key())
                    .copied()
                    .unwrap_or(n.effective);
                if let Some(previous) = self.outputs.get(&n.id.key()) {
                    let rect = super::size(previous.rect);
                    let port = super::size(previous.scrollport);
                    n.gutter = Xy::new((rect.x - port.x).max(0.), (rect.y - port.y).max(0.));
                }
            }
            let mut issues = Vec::new();
            self.outputs = viewport::publish(&mut frame, &self.offsets, &mut issues);
            self.view_dirty = false;
            return Ok(());
        }
        self.dirty = true;
        self.styles.retain(|k, _| tree.nodes.contains_key(*k));
        self.patches.retain(|k, _| tree.nodes.contains_key(*k));
        self.authored.retain(|k, _| tree.nodes.contains_key(*k));
        self.offsets.retain(|k, _| tree.nodes.contains_key(*k));
        let visual = self.styles.values().any(|s| {
            s.scroll != super::ScrollStyle::default() || s.placement != super::Placement::Flow
        });
        let mut frame = Frame::new(tree, window, &self.styles, &self.authored, &self.patches);
        // Only conditional, space-consuming scrollbars feed visual overflow
        // back into native sizing. Overlay and stable bars need one visual pass.
        let dynamic_gutter = self.styles.values().any(|s| {
            !s.scroll.stable_gutter
                && [Axis::X, Axis::Y].iter().any(|&a| {
                    s.scroll.overflow[a] == super::Overflow::Auto && s.scroll.scrollbar[a] > 0.0
                })
        });
        let mut issues = Vec::new();
        frame.prepare(&mut issues);
        // An allocated query container can cross a breakpoint after the first
        // flex/grid pass. Capture the children's intrinsic contributions for
        // every context that may subsequently consume them.
        for parent in 0..frame.nodes.len() {
            let node = &frame.nodes[parent];
            let Some(style) = frame.styles.get(&node.id.key()) else {
                continue;
            };
            let mut managed = style.grid.is_some() || style.flex.is_some();
            let mut content_basis = Xy::new_symm(false);
            let axis = |f: FlexLayout| {
                style
                    .logical
                    .main_axis
                    .map_or(f.axis, |a| node.context.axis(a))
            };
            if let Some(flex) = style.flex {
                content_basis[axis(flex)] = true;
            }
            for query in &style.queries {
                match &query.style.layout {
                    Some(QueryLayout::Flex(flex)) => {
                        managed = true;
                        content_basis[axis(*flex)] = true;
                    }
                    Some(QueryLayout::Grid(_)) => managed = true,
                    _ => {}
                }
            }
            if !managed {
                continue;
            }
            for index in 0..frame.nodes[parent].children.len() {
                let child = frame.nodes[parent].children[index];
                let item = &mut frame.nodes[child];
                for a in [Axis::X, Axis::Y] {
                    if matches!(item.effective.size[a], Size::Auto | Size::Fill)
                        || content_basis[a] && item.rule.flex_item.basis == FlexBasis::Content
                    {
                        item.effective.size[a] = Size::FitContent;
                    }
                }
            }
        }
        frame.sync(tree, &mut self.authored);
        solve(tree)?;
        frame.read(tree, false);
        for n in &mut frame.nodes {
            n.natural = super::size(n.rect);
            n.measured = n.natural;
        }
        // A chain of nested content-dependent containers can communicate a
        // measured size one level per iteration. Keep oscillations bounded.
        let limit = frame.nodes.len().saturating_add(4);
        let mut settled = false;
        for _ in 0..limit {
            issues.clear();
            frame.prepare(&mut issues);
            frame.plan(&mut issues);
            let mut metrics_changed = false;
            for n in &mut frame.nodes {
                for a in [Axis::X, Axis::Y] {
                    if let Some(value) = n.intrinsic_proposal[a].take() {
                        metrics_changed |= n.natural[a] != value;
                        n.natural[a] = value;
                        n.measured[a] = value;
                    }
                }
            }
            let mut probes = Vec::new();
            for i in 0..frame.nodes.len() {
                if !frame.nodes[i].assigned {
                    continue;
                }
                let p = frame.nodes[i].base;
                for a in [Axis::X, Axis::Y] {
                    if p.intrinsic_reads_other_axis(a)
                        && matches!(p.size[a], Size::Auto | Size::Fill | Size::FitContent)
                    {
                        probes.push((i, a, frame.nodes[i].effective.size[a]));
                        frame.nodes[i].effective.size[a] = Size::FitContent;
                    }
                }
            }
            if !probes.is_empty() {
                frame.sync(tree, &mut self.authored);
                solve(tree)?;
                for (i, a, allocated) in probes {
                    frame.nodes[i].effective.size[a] = allocated;
                    let key = frame.nodes[i].id.key();
                    let v = tree.published_size(key, &tree.nodes[key])[a];
                    metrics_changed |= frame.nodes[i].measured[a] != v;
                    frame.nodes[i].measured[a] = v;
                }
            }
            let prior_geometry: Vec<_> = frame
                .nodes
                .iter()
                .map(|n| (n.rect, n.overflowing, n.query_content))
                .collect();
            let changed = frame.sync(tree, &mut self.authored);
            if changed {
                solve(tree)?;
            }
            frame.read(tree, false);
            if dynamic_gutter {
                let _ = viewport::publish(&mut frame, &self.offsets, &mut issues);
            }
            if !metrics_changed
                && frame
                    .nodes
                    .iter()
                    .zip(&prior_geometry)
                    .all(|(n, (r, o, c))| {
                        n.rect == *r && n.overflowing == *o && n.query_content == *c
                    })
            {
                settled = true;
                break;
            }
        }
        if !settled {
            issues.push(RuleIssue::UnstableLayout);
        }
        frame.read(tree, true);
        self.outputs = if visual {
            viewport::publish(&mut frame, &self.offsets, &mut issues)
        } else {
            HashMap::new()
        };
        // Publish the same tracks used for item placement and subgrid inheritance.
        // Idle and scroll-only solves keep this geometry, as does a rejected Batch solve.
        self.grid_tracks = std::mem::take(&mut frame.grid_tracks);
        self.positioned_styles.clear();
        self.positioned_styles
            .extend(frame.nodes.iter().filter_map(|n| {
                matches!(
                    n.rule.placement,
                    super::Placement::Fixed(_) | super::Placement::Absolute { .. }
                )
                .then_some((n.id.key(), n.base))
            }));
        self.baseline_contexts.clear();
        self.baseline_contexts
            .extend(frame.nodes.iter().enumerate().filter_map(|(i, n)| {
                let context = if let Some(flex) = frame.flex_layout(i) {
                    (flex.axis == Axis::X).then_some(BaselineContext::Flex(flex.align_items))
                } else {
                    n.rule
                        .grid
                        .as_ref()
                        .map(|grid| BaselineContext::Grid(grid.align_items.y))
                };
                context.map(|context| (n.id.key(), context))
            }));
        // A projected allocation pins the native box to pixels after its
        // formatting context has enforced bounds. Retain the diagnostic from
        // the authored constraints even when that final pin has no bounds.
        for node in frame
            .nodes
            .iter()
            .filter(|n| n.assigned && !n.base.disabled)
        {
            for axis in [Axis::X, Axis::Y] {
                if let (Some(Size::Pixels(min)), Some(Size::Pixels(max))) =
                    (node.base.min_size[axis], node.base.max_size[axis])
                    && min > max
                    && !tree.warnings.iter().any(|w| matches!(w,
                        crate::LayoutWarning::MinAboveMax { node: id, axis: a } if *id == node.id && *a == axis))
                {
                    tree.warnings.push(crate::LayoutWarning::MinAboveMax {node: node.id.clone(), axis});
                }
            }
        }
        self.issues.clear();
        for issue in issues {
            if !self.issues.contains(&issue) {
                self.issues.push(issue);
            }
        }
        self.window = (!self.styles.is_empty() || !self.patches.is_empty()).then_some(window);
        self.dirty = false;
        self.view_dirty = false;
        Ok(())
    }
}

impl<T> LayoutTree<T> {
    pub(in crate::layout_tree) fn run_rules<E>(
        &mut self,
        window: Xy<f32>,
        solve: &mut dyn FnMut(&mut Self) -> Result<(), E>,
    ) -> Result<(), E> {
        // Restore authored inputs even when a host's measurement callback unwinds.
        let mut state = std::mem::take(&mut self.rules_state);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            state.run(self, window, solve)
        }));
        self.rules_state = state;
        result.unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    }
}
