use crate::*;

#[path = "placement_walk.rs"]
mod placement_walk;

#[path = "stack_line.rs"]
pub(crate) mod stack_line;

#[derive(Clone, Copy)]
pub(crate) struct ParentFrame<'a> {
    rect: XyRect,
    output_origin: Xy<f32>,
    padding: Xy<[f32; 2]>,
    flipped: Xy<bool>,
    snapper: Option<&'a Snapper>,
}

/// The parent has been visited. Its first child is next in preorder.
#[derive(Clone, Copy)]
pub(crate) struct Branch<I> {
    parent: I,
    first: I,
    rect: XyRect,
    origin: Xy<f32>,
    partial: bool,
}

#[derive(Clone, Copy)]
pub(crate) struct Siblings<'a, I> {
    next: Option<I>,
    frame: ParentFrame<'a>,
    partial: bool,
    mode: SiblingMode<I>,
}

#[derive(Clone, Copy)]
enum SiblingMode<I> {
    Free,
    Stack { axis: Axis, position: f32, gap: f32, batch: bool },
    Wrap(WrapCursor<I>),
    Block(BlockFlow),
    Grid { parent: I, spacing_x: f32, spacing_y: f32 },
}

#[derive(Clone, Copy)]
pub(crate) struct WrapCursor<I> {
    axis: Axis,
    arrange: Arrange,
    spacing: f32,
    line_spacing: f32,
    next_line: Option<I>,
    cross_position: f32,
    cross_edges: [f32; 2],
    main_position: f32,
    gap: f32,
}

#[path = "placement_batch.rs"]
mod placement_batch;

struct LeafBatch<'a, I> {
    buffer: placement_batch::Buffer<I, [f32; 4]>,
    snapper: &'a Snapper,
}

impl<'a, I: Copy> LeafBatch<'a, I> {
    fn new(first: I, snapper: &'a Snapper) -> Self {
        Self { buffer: placement_batch::empty_buffer(first, [0.0; 4]), snapper }
    }

    #[inline]
    fn push<T: TreeAdapter<NodeId = I> + ?Sized>(&mut self, tree: &mut T, frame: &ParentFrame, id: I, rect: XyRect, dirty: bool) {
        let edges = [rect.x[0], rect.x[1], rect.y[0], rect.y[1]];
        if let Some(run) = self.buffer.push(id, edges, dirty) {
            self.publish(tree, frame, run);
        }
    }

    fn flush<T: TreeAdapter<NodeId = I> + ?Sized>(&mut self, tree: &mut T, frame: &ParentFrame) {
        let run = self.buffer.drain();
        if run.len != 0 { self.publish(tree, frame, run); }
    }

    fn publish<T: TreeAdapter<NodeId = I> + ?Sized>(&mut self, tree: &mut T, frame: &ParentFrame, run: placement_batch::Run) {
        let ids = run.ids(&self.buffer.ids);
        let edges = run.edges(&mut self.buffer.edges);
        self.snapper.snap_many(edges);
        let parent = frame.output_origin;
        #[cfg(feature = "incremental")]
        let mut dirty = run.dirty;
        for (&node, &[left, right, top, bottom]) in ids.iter().zip(edges.iter()) {
            #[cfg(feature = "incremental")]
            {
                if placement_batch::pop_dirty(&mut dirty) {
                    tree.node_layout_data_mut(node).placement = PlacementWork::Clean;
                }
            }
            let rect = Xy::new([left, right], [top, bottom]);
            let local = Xy::new([left - parent.x, right - parent.x], [top - parent.y, bottom - parent.y]);
            tree.write_output_rect(node, rect, local);
        }
    }
}

/// The placement part of the layout. Every `TreeAdapter` gets it from the blanket impl.
pub(crate) trait Place: Solve {
    fn solve_full<const REGISTERED_PIXELS: bool>(&mut self, window_size: Xy<f32>) {
        #[cfg(feature = "incremental")]
        self.layout_data().clear();
        self.measure_sizes::<REGISTERED_PIXELS>(window_size);
        self.place_nodes::<false>();
        #[cfg(feature = "incremental")]
        {
            if self.retains_output_rects() { self.layout_data().track_topology = true; }
            self.remember_topology();
        }
    }

    fn place_nodes<const PARTIAL: bool>(&mut self) {
        #[cfg(feature = "incremental")]
        { self.layout_data().placement_scale_changed = false; }
        let root = self.root();
        if self.node_layout_params(root).disabled { return; }
        let size = self.node_layout_data(root).size();
        let rect = Xy::new([0.0, size.x], [0.0, size.y]);
        let snapper = self.layout_data().pixel_scale.map(Snapper::new);
        self.place::<PARTIAL>(root, rect, Xy::new_symm(0.0), snapper.as_ref());
    }

    fn place<const PARTIAL: bool>(&mut self, node: Self::NodeId, rect: XyRect, origin: Xy<f32>, snapper: Option<&Snapper>) {
        if let Some(branch) = self.publish_node::<PARTIAL>(node, rect, origin, snapper) {
            self.walk_placement(branch, snapper);
        }
    }

    /// Publish one node. Its children are visited by the outer work loop.
    #[inline(always)]
    fn publish_node<const PARTIAL: bool>(&mut self, node: Self::NodeId, rect: XyRect, parent_origin: Xy<f32>, snapper: Option<&Snapper>) -> Option<Branch<Self::NodeId>> {
        #[cfg(feature = "incremental")]
        let write = {
            let work = self.node_layout_data(node).placement;
            if !work.visits(!PARTIAL) { return None; }
            if work != PlacementWork::Clean {
                self.node_layout_data_mut(node).placement = PlacementWork::Clean;
            }
            work.writes(!PARTIAL)
        };
        #[cfg(not(feature = "incremental"))]
        let write = true;

        let output = snapper.map_or(rect, |snapper| snap_rect(rect, snapper));
        if write {
            let local = Xy::new(
                [output.x[0] - parent_origin.x, output.x[1] - parent_origin.x],
                [output.y[0] - parent_origin.y, output.y[1] - parent_origin.y],
            );
            self.write_output_rect(node, output, local);
        }
        let first = self.first_child(node)?;
        Some(Branch {
            parent: node, first, rect, origin: Xy::new(output.x[0], output.y[0]),
            // A changed frame forces all its descendants to publish.
            partial: PARTIAL && !write,
        })
    }

    #[cfg(feature = "incremental")]
    fn place_children<const PARTIAL: bool>(&mut self, parent: Self::NodeId, first: Self::NodeId, rect: XyRect, origin: Xy<f32>, snapper: Option<&Snapper>) {
        self.walk_placement(Branch { parent, first, rect, origin, partial: PARTIAL }, snapper);
    }

    fn walk_placement(&mut self, start: Branch<Self::NodeId>, snapper: Option<&Snapper>) {
        let mut pending = crate::work_stack::work_stack::<_, 4>(Vec::new());
        let mut siblings = self.placement_cursor(start, snapper);
        loop {
            let branch = if siblings.partial {
                self.place_siblings::<true>(&mut siblings)
            } else {
                self.place_siblings::<false>(&mut siblings)
            };
            let child = branch.map(|branch| self.placement_cursor(branch, snapper));
            let Some(next) = placement_walk::next(&mut pending, child, &siblings, siblings.next.is_some()) else { return };
            siblings = next;
        }
    }

    fn placement_cursor<'a>(&self, branch: Branch<Self::NodeId>, snapper: Option<&'a Snapper>) -> Siblings<'a, Self::NodeId> {
        let Branch { parent, first, rect, origin, partial } = branch;
        let (layout, frame) = self.parent_frame(parent, rect, origin, snapper);
        let mode = match layout {
            ChildrenLayout::Free => SiblingMode::Free,
            ChildrenLayout::Stack { axis, arrange, spacing } => {
                let (position, gap) = self.stack_start(first, &frame, axis, arrange, spacing);
                let batch = !partial && snapper.is_some_and(Snapper::prefers_batch)
                    && self.node_layout_data(parent).n_placed_children >= placement_batch::CAPACITY as u32;
                SiblingMode::Stack { axis, position, gap, batch }
            }
            ChildrenLayout::Wrap { axis, arrange, spacing, line_spacing } => SiblingMode::Wrap(WrapCursor {
                axis, arrange, spacing, line_spacing, next_line: Some(first),
                cross_position: inner_range(&frame, axis.other())[0],
                cross_edges: [0.0; 2], main_position: 0.0, gap: 0.0,
            }),
            ChildrenLayout::Block => SiblingMode::Block(self.block_flow(parent)),
            ChildrenLayout::Grid { spacing_x, spacing_y, .. } => SiblingMode::Grid { parent, spacing_x, spacing_y },
        };
        Siblings { next: Some(first), frame, partial, mode }
    }

    fn place_siblings<const PARTIAL: bool>(&mut self, siblings: &mut Siblings<Self::NodeId>) -> Option<Branch<Self::NodeId>> {
        let Siblings { next, frame, mode, .. } = siblings;
        match mode {
            SiblingMode::Free => self.place_children_free::<PARTIAL>(next, frame),
            SiblingMode::Block(flow) => self.place_children_block::<PARTIAL>(next, frame, flow),
            SiblingMode::Wrap(line) => self.place_children_wrap::<PARTIAL>(next, frame, line),
            SiblingMode::Grid { parent, spacing_x, spacing_y } =>
                self.place_children_grid::<PARTIAL>(*parent, next, frame, *spacing_x, *spacing_y),
            SiblingMode::Stack { axis, position, gap, batch } => {
                if *batch {
                    self.place_stack_items::<false, true>(next, frame, *axis, position, *gap)
                } else {
                    self.place_stack_items::<PARTIAL, false>(next, frame, *axis, position, *gap)
                }
            }
        }
    }

    fn free_placement_parent(&self, node: Self::NodeId) -> Result<Self::NodeId, FreePlacementError> {
        let root = self.root();
        if node == root { return Err(FreePlacementError::Root); }
        let parent = self.parent(node).ok_or(FreePlacementError::Detached)?;
        let params = self.node_layout_params(node);
        if params.disabled { return Err(FreePlacementError::Disabled); }

        // Custom adapters can hide a subtree by disabling only its ancestor.
        let mut ancestor = parent;
        loop {
            if self.node_layout_params(ancestor).disabled { return Err(FreePlacementError::Disabled); }
            if ancestor == root { break; }
            ancestor = self.parent(ancestor).ok_or(FreePlacementError::Detached)?;
        }
        if !params.free_placement && self.node_layout_params(parent).children_layout != ChildrenLayout::Free {
            return Err(FreePlacementError::InFlow);
        }
        let mut next = Some(node);
        while let Some(item) = next {
            let visible = !self.node_layout_params(item).disabled;
            if visible {
                let flags = self.node_layout_data(item).flags;
                if flags.check_state(X, Kind::Final) != SOLVED || flags.check_state(Y, Kind::Final) != SOLVED {
                    return Err(FreePlacementError::Unsolved);
                }
            }
            next = self.traversal_next(node, item, visible);
        }
        Ok(parent)
    }

    fn place_free_node(&mut self, node: Self::NodeId, parent_rect: XyRect) -> Result<(), FreePlacementError> {
        let parent = self.free_placement_parent(node)?;
        let snapper = self.layout_data().pixel_scale.map(Snapper::new);
        let output = snapper.as_ref().map_or(parent_rect, |snapper| snap_rect(parent_rect, snapper));
        let parent_origin = Xy::new(output.x[0], output.y[0]);
        let (_, frame) = self.parent_frame(parent, parent_rect, parent_origin, snapper.as_ref());
        let rect = self.free_child_rect(node, &frame, self.node_layout_data(node).size());
        self.place::<false>(node, rect, frame.output_origin, frame.snapper);
        #[cfg(feature = "incremental")]
        self.node_layout_data_mut(node).mark_placement_changed();
        Ok(())
    }

    /// Place an appended leaf when the preceding stack items retain their sizes and
    /// positions. Both cached rectangles must be unrounded. The previous item, if
    /// present, is the last enabled, in-flow sibling.
    #[cfg(feature = "incremental")]
    fn place_appended_stack_leaf(&mut self, parent: Self::NodeId, child: Self::NodeId, parent_rect: XyRect,
        previous: Option<(Self::NodeId, XyRect)>) -> bool
    {
        if self.layout_data().pixel_scale.is_some() || self.first_child(child).is_some() { return false; }
        let origin = Xy::new(parent_rect.x[0], parent_rect.y[0]);
        let (layout, frame) = self.parent_frame(parent, parent_rect, origin, None);
        let ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing } = layout else { return false };
        let params = self.node_layout_params(child);
        if frame.flipped[axis] || params.disabled || params.free_placement { return false; }

        let range = inner_range(&frame, axis);
        let mut cursor = if let Some((sibling, rect)) = previous {
            let sibling_params = self.node_layout_params(sibling);
            if sibling_params.disabled || sibling_params.free_placement { return false; }
            // Match place_in_line's addition order. Adding the gap to the cached
            // trailing edge would round at a different step for fractional sizes.
            let trailing = sibling_params.margin[axis][1].pixels();
            stack_line::after_item(rect[axis][0], self.node_layout_data(sibling).size()[axis], trailing, spacing)
        } else {
            range[0]
        };
        let size = self.node_layout_data(child).size();
        let rect = self.stack_item_rect(&frame, params, size, axis, &mut cursor, spacing);
        self.publish_node::<false>(child, rect, origin, None);
        true
    }

    #[inline(always)]
    fn parent_frame<'a>(&self, i: Self::NodeId, rect: XyRect, output_origin: Xy<f32>, snapper: Option<&'a Snapper>) -> (ChildrenLayout, ParentFrame<'a>) {
        let params = self.node_layout_params(i);
        (params.children_layout, ParentFrame {
            rect,
            output_origin,
            padding: params.padding,
            flipped: params.children_origin_flipped,
            snapper,
        })
    }

    fn stack_start(&self, first: Self::NodeId, frame: &ParentFrame, main: Axis, arrange: Arrange, spacing: f32) -> (f32, f32) {
        let (total_size, n) = if arrange == Arrange::Start {
            (0.0, 0)
        } else {
            let mut n: u32 = 0;
            let mut children_size = 0.0;
            for_each_layout_child!(@from self, Some(first), child, {
                if ! self.node_layout_params(child).free_placement {
                    let [start, end] = margins(self.node_layout_params(child), main);
                    children_size += with_margin(self.node_layout_data(child).size()[main], start + end);
                    n = crate::solve::cycle_rules::add_count(n, 1);
                }
            });
            let total = if n > 0 { children_size + spacing * (n - 1) as f32 } else { children_size };
            (total, n)
        };
        line_start_and_gap(arrange, inner_range(frame, main), total_size, n, spacing)
    }

    fn place_stack_items<const PARTIAL: bool, const BATCH: bool>(&mut self, next: &mut Option<Self::NodeId>, frame: &ParentFrame, main: Axis, position: &mut f32, gap: f32) -> Option<Branch<Self::NodeId>> {
        let cross = main.other();
        let cross_start = inner_range(frame, cross)[0];
        let forward = !frame.flipped.x && !frame.flipped.y;
        let first = (*next)?;
        // The cursor still advances in sibling order. Only rounding and output
        // for leaf runs can be deferred, since adapter callbacks keep inputs stable.
        let mut batch = if BATCH { frame.snapper.map(|snapper| LeafBatch::new(first, snapper)) } else { None };
        #[cfg(feature = "incremental")]
        // The owned tree supplies prepared styles. Adapters without retained
        // output can skip checking for them in the sibling loop.
        let use_prepared_styles = !PARTIAL && forward && self.retains_output_rects();
        walk_siblings!(; (*next, child); {
            let child_data = self.node_layout_data(child);
            #[cfg(feature = "incremental")]
            let cached = use_prepared_styles && child_data.cached_stack_start();
            #[cfg(not(feature = "incremental"))]
            let cached = false;
            let params = (!cached).then(|| self.node_layout_params(child));
        }; self.next_sibling(child); params.is_some_and(|p| p.disabled); {
            let child_size = child_data.size();
            let rect = match params {
                Some(p) if p.free_placement => {
                    if let Some(batch) = &mut batch { batch.flush(self, frame); }
                    self.free_child_rect(child, frame, child_size)
                }
                _ => {
                    let rect = match params {
                        Some(p) if !forward || p.position[cross] != Pos::Start
                            || p.margin != Xy::new_symm([Margin::ZERO; 2]) =>
                            self.stack_item_rect(frame, p, child_size, main, position, gap),
                        _ => {
                            let [x, y] = stack_line::place_start(position, cross_start, main == X, [child_size.x, child_size.y], gap);
                            Xy::new(x, y)
                        }
                    };
                    if let Some(batch) = &mut batch {
                        if self.first_child(child).is_none() {
                            #[cfg(feature = "incremental")]
                            let dirty = child_data.placement != PlacementWork::Clean;
                            #[cfg(not(feature = "incremental"))]
                            let dirty = false;
                            batch.push(self, frame, child, rect, dirty);
                            continue;
                        }
                        batch.flush(self, frame);
                    }
                    rect
                }
            };
            if let Some(branch) = self.publish_node::<PARTIAL>(child, rect, frame.output_origin, frame.snapper) {
                return Some(branch);
            }
        });
        if let Some(batch) = &mut batch { batch.flush(self, frame); }
        None
    }

    #[inline(always)]
    fn stack_item_rect(&self, frame: &ParentFrame, params: &LayoutParams, size: Xy<f32>, main: Axis, cursor: &mut f32, gap: f32) -> XyRect {
        let cross = main.other();
        let mut rect = Xy::new_symm([0.0; 2]);
        rect[cross] = self.resolve_pos_on_axis(frame, params, cross, size[cross], margins(params, cross));
        rect[main] = place_in_line(frame, main, inner_range(frame, main), cursor, size[main], margins(params, main), gap);
        rect
    }

    fn place_children_wrap<const PARTIAL: bool>(&mut self, next: &mut Option<Self::NodeId>, frame: &ParentFrame, cursor: &mut WrapCursor<Self::NodeId>) -> Option<Branch<Self::NodeId>> {
        let axis = cursor.axis;
        let cross = axis.other();
        let main_range = inner_range(frame, axis);
        let cross_range = inner_range(frame, cross);
        while let Some(child) = *next {
            if cursor.next_line == Some(child) {
                let line = self.wrap_line::<true>(*next, axis, None, cursor.spacing);
                (cursor.main_position, cursor.gap) = line_start_and_gap(cursor.arrange, main_range, line.main, line.count, cursor.spacing);
                cursor.cross_edges = place_in_line(frame, cross, cross_range, &mut cursor.cross_position, line.cross, [0.0; 2], cursor.line_spacing);
                cursor.next_line = line.next;
            }
            *next = self.next_sibling(child);
            let params = self.node_layout_params(child);
            if params.disabled { continue; }
            let size = self.node_layout_data(child).size();
            let rect = if params.free_placement {
                self.free_child_rect(child, frame, size)
            } else {
                let mut line_frame = *frame;
                line_frame.rect[cross] = cursor.cross_edges;
                line_frame.padding[cross] = [0.0; 2];
                let mut rect = Xy::new_symm([0.0; 2]);
                rect[axis] = place_in_line(frame, axis, main_range, &mut cursor.main_position, size[axis], margins(params, axis), cursor.gap);
                rect[cross] = self.resolve_pos_on_axis(&line_frame, params, cross, size[cross], margins(params, cross));
                rect
            };
            if let Some(branch) = self.publish_node::<PARTIAL>(child, rect, frame.output_origin, frame.snapper) {
                return Some(branch);
            }
        }
        None
    }

    fn place_children_block<const PARTIAL: bool>(&mut self, next: &mut Option<Self::NodeId>, frame: &ParentFrame, flow: &mut BlockFlow) -> Option<Branch<Self::NodeId>> {
        let [left, right] = inner_range(frame, X);
        let [top, _] = inner_range(frame, Y);
        walk_siblings!(; (*next, child); {}; self.next_sibling(child); self.node_layout_params(child).disabled; {
            let params = self.node_layout_params(child);
            let size = self.node_layout_data(child).size();
            let rect = if params.free_placement {
                self.free_child_rect(child, frame, size)
            } else {
                let [inline_left, inline_right] = params.margin.x;
                let spare = (right - left - size.x - inline_left.pixels() - inline_right.pixels()).max(0.0);
                let auto_count = usize::from(inline_left == Margin::AUTO) + usize::from(inline_right == Margin::AUTO);
                let leading = if frame.flipped.x { inline_right } else { inline_left };
                let leading = if leading == Margin::AUTO { spare / auto_count as f32 } else { leading.pixels() };
                let inline = if frame.flipped.x {
                    let end = right - leading;
                    [end - size.x, end]
                } else {
                    let start = left + leading;
                    [start, start + size.x]
                };
                let y = top + flow.push(self.block_item(child));
                Xy::new(inline, [y, y + size.y])
            };
            if let Some(branch) = self.publish_node::<PARTIAL>(child, rect, frame.output_origin, frame.snapper) {
                return Some(branch);
            }
        });
        None
    }

    fn place_children_grid<const PARTIAL: bool>(&mut self, i: Self::NodeId, next: &mut Option<Self::NodeId>, frame: &ParentFrame, spacing_x: f32, spacing_y: f32) -> Option<Branch<Self::NodeId>> {
        let lines = self.node_layout_data(i).grid_lines();

        let spacing = Xy::new(spacing_x, spacing_y);
        let size = self.node_layout_data(i).size();
        let mut cell = Xy::new(0.0, 0.0);
        for axis in [X, Y] {
            let n = lines[axis];
            let [pad_start, pad_end] = frame.padding[axis];
            cell[axis] = ((size[axis] - pad_start - pad_end - spacing[axis] * (n - 1.0)) / n.max(1.0)).max(0.0);
        }

        let [left, _] = inner_range(frame, X);
        let [top, _] = inner_range(frame, Y);
        let step = Xy::new(cell.x + spacing_x, cell.y + spacing_y);
        let forward = !frame.flipped.x && !frame.flipped.y;
        walk_siblings!(; (*next, child); {}; self.next_sibling(child); self.node_layout_params(child).disabled; {
            let child_size = self.node_layout_data(child).size();
            let params = self.node_layout_params(child);
            let rect = if params.free_placement {
                self.free_child_rect(child, frame, child_size)
            } else {
                let child_cell = self.node_layout_data(child).grid_cell();
                if forward && params.position == Xy::new_symm(Pos::Start)
                    && params.margin == Xy::new_symm([Margin::ZERO; 2])
                {
                    grid_start_rect(Xy::new(left, top), step, child_cell, child_size)
                } else {
                    let span = params.grid_span;
                    // The child is positioned inside the rect of its cells, as if the cells were its parent.
                    let mut cell_frame = ParentFrame { rect: Xy::new_symm([0.0; 2]), padding: Xy::new_symm([0.0; 2]), ..*frame };
                    for axis in [X, Y] {
                        let span = f32::from(span[axis].max(1)).min(lines[axis].max(1.0));
                        let offset = child_cell[axis] * (cell[axis] + spacing[axis]);
                        let length = span * cell[axis] + (span - 1.0) * spacing[axis];
                        cell_frame.rect[axis] = if ! frame.flipped[axis] {
                            let start = frame.rect[axis][0] + frame.padding[axis][0] + offset;
                            [start, start + length]
                        } else {
                            let end = frame.rect[axis][1] - frame.padding[axis][1] - offset;
                            [end - length, end]
                        };
                    }
                    let mut child_rect = Xy::new([0.0, 0.0], [0.0, 0.0]);
                    for axis in [X, Y] {
                        child_rect[axis] = self.resolve_pos_on_axis(&cell_frame, params, axis, child_size[axis], margins(params, axis));
                    }
                    child_rect
                }
            };
            if let Some(branch) = self.publish_node::<PARTIAL>(child, rect, frame.output_origin, frame.snapper) {
                return Some(branch);
            }
        });
        None
    }

    #[inline(always)]
    fn resolve_pos_on_axis(&self, frame: &ParentFrame, params: &LayoutParams, axis: Axis, child_size: f32, margin: [f32; 2]) -> [f32; 2] {
        let [inner_start, inner_end] = inner_range(frame, axis);
        let inner_start = with_margin(inner_start, margin[0]);
        let inner_end = with_margin(inner_end, -margin[1]);
        let flipped = frame.flipped[axis];

        let place_at = |reference: f32| {
            let anchor_frac = anchor_frac(params.anchor[axis]);
            if ! flipped {
                let low = reference - anchor_frac * child_size;
                [low, low + child_size]
            } else {
                let high = reference + anchor_frac * child_size;
                [high - child_size, high]
            }
        };

        let origin_edge = if ! flipped { inner_start } else { inner_end };
        let far_edge = if ! flipped { inner_end } else { inner_start };

        match params.position[axis] {
            Pos::Start => {
                if ! flipped { [origin_edge, origin_edge + child_size] } else { [origin_edge - child_size, origin_edge] }
            }
            Pos::End => {
                if ! flipped { [far_edge - child_size, far_edge] } else { [far_edge, far_edge + child_size] }
            }
            Pos::Pixels(pixels) => place_at(if ! flipped { origin_edge + pixels } else { origin_edge - pixels }),
            Pos::Frac(frac) => {
                let static_pos = frac * (inner_end - inner_start);
                place_at(if ! flipped { origin_edge + static_pos } else { origin_edge - static_pos })
            }
            Pos::Center => centered_range(inner_start, inner_end, child_size),
        }
    }

    #[inline(always)]
    fn free_child_rect(&mut self, child: Self::NodeId, frame: &ParentFrame, child_size: Xy<f32>) -> XyRect {
        let params = self.node_layout_params(child);
        if params.position == Xy::new_symm(Pos::Center) && params.window_overflow == Xy::new_symm(WindowOverflow::Ignore) {
            // Keeping both axes together lets the compiler vectorize the centered arithmetic.
            Xy::new(
                centered_range(frame.rect.x[0] + frame.padding.x[0], frame.rect.x[1] - frame.padding.x[1], child_size.x),
                centered_range(frame.rect.y[0] + frame.padding.y[0], frame.rect.y[1] - frame.padding.y[1], child_size.y),
            )
        } else {
            let overflow = params.window_overflow;
            let anchors = params.anchor;
            let mut rect = Xy::new(
                self.resolve_pos_on_axis(frame, params, X, child_size.x, [0.0; 2]),
                self.resolve_pos_on_axis(frame, params, Y, child_size.y, [0.0; 2]),
            );
            for axis in [X, Y] {
                if overflow[axis] != WindowOverflow::Ignore {
                    let window_size = self.layout_data().window_size[axis];
                    rect[axis] = self.apply_window_overflow(window_size, overflow[axis], frame.flipped[axis], anchors[axis], rect[axis]);
                }
            }
            rect
        }
    }

    fn apply_window_overflow(&self, win_high: f32, behavior: WindowOverflow, flipped: bool, anchor: Anchor, rect: [f32; 2]) -> [f32; 2] {
        let win_low = 0.0;
        let [lo, hi] = rect;
        let size = hi - lo;

        // If the node is larger than the window, just give up.
        if size >= (win_high - win_low) {
            return [win_low, win_low + size];
        }

        let mut out = rect;
        if behavior == WindowOverflow::Flip {
            // The anchor point (in absolute coords) is the point that should stay fixed, e.g. the cursor.
            let anchor_frac = anchor_frac(anchor);
            let a = if ! flipped { lo + anchor_frac * size } else { hi - anchor_frac * size };

            let reflected = [2.0 * a - hi, 2.0 * a - lo];
            let should_reflect = hi > win_high && reflected[0] >= win_low || lo < win_low && reflected[1] <= win_high;
            if should_reflect {
                out = reflected;
            }
        }

        // Clamp (also the fallback when a flip wouldn't fit either).
        let [mut lo, mut hi] = out;
        let size = hi - lo;
        if hi > win_high {
            hi = win_high;
            lo = hi - size;
        }
        if lo < win_low {
            lo = win_low;
            hi = lo + size;
        }
        [lo, hi]
    }

    fn place_children_free<const PARTIAL: bool>(&mut self, next: &mut Option<Self::NodeId>, frame: &ParentFrame) -> Option<Branch<Self::NodeId>> {
        walk_siblings!(; (*next, child); {}; self.next_sibling(child); self.node_layout_params(child).disabled; {
            #[cfg(feature = "incremental")]
            if PARTIAL && !self.node_layout_data(child).placement.visits(false) { continue; }
            let child_size = self.node_layout_data(child).size();
            let rect = self.free_child_rect(child, frame, child_size);
            if let Some(branch) = self.publish_node::<PARTIAL>(child, rect, frame.output_origin, frame.snapper) {
                return Some(branch);
            }
        });
        None
    }
}

impl<T: TreeAdapter + ?Sized> Place for T {}

#[inline]
fn grid_start_rect(origin: Xy<f32>, step: Xy<f32>, cell: Xy<f32>, size: Xy<f32>) -> XyRect {
    // Entering the cell's inner range adds its zero padding before sizing.
    #[cfg(target_arch = "x86_64")]
    {
        use std::arch::x86_64::*;
        // SAFETY: SSE2 is part of x86-64 and the array has four lanes.
        unsafe {
            let pack = |value: Xy<f32>| _mm_setr_ps(value.x, value.y, 0.0, 0.0);
            let offset = _mm_mul_ps(pack(cell), pack(step));
            let start = _mm_add_ps(_mm_add_ps(pack(origin), offset), _mm_setzero_ps());
            let end = _mm_add_ps(start, pack(size));
            let mut edges = [0.0; 4];
            _mm_storeu_ps(edges.as_mut_ptr(), _mm_unpacklo_ps(start, end));
            let [left, right, top, bottom] = edges;
            Xy::new([left, right], [top, bottom])
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        let x = (origin.x + cell.x * step.x) + 0.0;
        let y = (origin.y + cell.y * step.y) + 0.0;
        Xy::new([x, x + size.x], [y, y + size.y])
    }
}

#[inline]
fn snap_rect(rect: XyRect, snapper: &Snapper) -> XyRect {
    let [left, right, top, bottom] = snapper.snap([rect.x[0], rect.x[1], rect.y[0], rect.y[1]]);
    Xy::new([left, right], [top, bottom])
}

#[path = "pixel_grid.rs"]
mod pixel_grid;
use pixel_grid::Snapper;


#[inline]
fn inner_range(frame: &ParentFrame, axis: Axis) -> [f32; 2] {
    let [start, end] = frame.rect[axis];
    let [pad_start, pad_end] = frame.padding[axis];
    [start + pad_start, end - pad_end]
}

fn line_start_and_gap(arrange: Arrange, [start, end]: [f32; 2], total: f32, n: u32, spacing: f32) -> (f32, f32) {
    let free = ((end - start) - total).max(0.0);
    match arrange {
        Arrange::Start => (start, spacing),
        Arrange::End => (end - total, spacing),
        Arrange::Center => ((start + end) / 2.0 - total / 2.0, spacing),
        Arrange::SpaceBetween => {
            let extra = if n > 1 { free / (n - 1) as f32 } else { 0.0 };
            (start, spacing + extra)
        }
        Arrange::SpaceAround => {
            let extra = if n > 0 { free / n as f32 } else { 0.0 };
            (start + extra / 2.0, spacing + extra)
        }
        Arrange::SpaceEvenly => {
            let extra = if n > 0 { free / stack_line::evenly_spaced_gaps(n) as f32 } else { 0.0 };
            (start + extra, spacing + extra)
        }
    }
}

#[inline]
fn place_in_line(frame: &ParentFrame, axis: Axis, range: [f32; 2], cursor: &mut f32, size: f32, margin: [f32; 2], gap: f32) -> [f32; 2] {
    stack_line::place(cursor, frame.flipped[axis], range, size, margin, gap)
}

#[inline(always)]
fn centered_range(start: f32, end: f32, size: f32) -> [f32; 2] {
    let center = (start + end) / 2.0;
    [center - size / 2.0, center + size / 2.0]
}

/// The anchor point of a node, as a fraction of its size from its origin-side edge.
#[inline(always)]
fn anchor_frac(anchor: Anchor) -> f32 {
    match anchor {
        Anchor::Start => 0.0,
        Anchor::Center => 0.5,
        Anchor::End => 1.0,
        Anchor::Frac(f) => f,
    }
}

#[cfg(test)]
#[path = "placement_depth_tests.rs"]
mod placement_depth_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grid_start_rect_preserves_scalar_coordinates() {
        #[inline(never)]
        fn reference(origin: f32, step: f32, cell: f32, size: f32) -> [f32; 2] {
            let start = (origin + cell * step) + 0.0;
            [start, start + size]
        }

        let coordinates = [
            0.0, -0.0, f32::from_bits(1), -f32::from_bits(1), 0.25, -8.75,
            16_777_216.0, f32::MAX, f32::MIN, f32::INFINITY, f32::NEG_INFINITY, f32::NAN,
        ];
        for origin in coordinates {
            for step in coordinates {
                for size in coordinates {
                    let actual = grid_start_rect(Xy::new(origin, step), Xy::new(step, origin),
                        Xy::new(-0.0, 3.0), Xy::new(size, -size));
                    let expected = Xy::new(reference(origin, step, -0.0, size),
                        reference(step, origin, 3.0, -size));
                    for (actual, expected) in actual.x.into_iter().chain(actual.y)
                        .zip(expected.x.into_iter().chain(expected.y))
                    {
                        if expected.is_nan() { assert!(actual.is_nan()); }
                        else { assert_eq!(actual.to_bits(), expected.to_bits()); }
                    }
                }
            }
        }
    }
    use rand::{Rng, SeedableRng};

    #[test]
    fn evenly_spaced_lines_use_the_full_gap_count() {
        // The integer denominator is exact before conversion to f32, including
        // counts that would round down if converted before adding the extra gap.
        for count in [16_777_217, u32::MAX - 1, u32::MAX] {
            let expected = 4_294_967_296.0 / (u64::from(count) + 1) as f32;
            let (start, gap) = line_start_and_gap(Arrange::SpaceEvenly, [0.0, 4_294_967_296.0], 0.0, count, 0.0);
            assert_eq!((start, gap), (expected, expected));
        }
    }

    #[test]
    fn resuming_a_stack_preserves_cursor_rounding() {
        // The first rectangle's end rounds down to its start. Its size and trailing
        // gap still advance the cursor together by one representable coordinate.
        let start = (1_u32 << 24) as f32;
        let range = [start, start + 8.0];
        let frame = ParentFrame {
            rect: Xy::new_symm(range), padding: Xy::new_symm([0.0; 2]),
            output_origin: Xy::new_symm(start), flipped: Xy::new_symm(false), snapper: None,
        };
        let mut cursor = start;
        let first = place_in_line(&frame, X, range, &mut cursor, 1.0, [0.0; 2], 1.0);
        assert_eq!(first, [start; 2]);
        assert_eq!(cursor, start + 2.0);
        assert_eq!(stack_line::after_item(first[0], 1.0, 0.0, 1.0), cursor);
    }

    #[test]
    fn packed_snapping_matches_scalar_rounding() {
        let check = |edges: [f32; 4], scale: f32| {
            let snapped = snap_rect(Xy::new([edges[0], edges[1]], [edges[2], edges[3]]), &Snapper::new(scale));
            let actual = [snapped.x[0], snapped.x[1], snapped.y[0], snapped.y[1]];
            for (edge, actual) in edges.into_iter().zip(actual) {
                let expected = ((f64::from(edge) * f64::from(scale)).round() / f64::from(scale)) as f32;
                if expected.is_nan() {
                    assert!(actual.is_nan());
                } else {
                    assert_eq!(actual.to_bits(), expected.to_bits(), "edge={edge}, scale={scale}");
                }
            }
        };

        for scale in [0.125, 0.75, 1.0, 1.5, 2.0, f32::MIN_POSITIVE, f32::MAX] {
            for half_pixel in [0.5, 1.5, 2.5, 127.5, 4095.5, 8_388_607.5] {
                let edge = (half_pixel / f64::from(scale)) as f32;
                check([edge.next_down(), edge, edge.next_up(), -edge], scale);
            }
            check([-0.0, f32::from_bits(1), f32::INFINITY, f32::NEG_INFINITY], scale);
            check([f32::MAX, -f32::MAX, (1_u64 << 47) as f32, f32::NAN], scale);
        }

        let mut rng = rand::rngs::StdRng::seed_from_u64(0x52_47);
        for _ in 0..10_000 {
            let scale = f32::from_bits(rng.random_range(1..=f32::MAX.to_bits()));
            check(std::array::from_fn(|_| f32::from_bits(rng.random())), scale);
        }
    }
}
