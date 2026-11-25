//! A resident schedule can retain a tail subtree when its parent has no
//! producers that read child sizes. The two boundary Final producers can
//! feed the subtree. All other new edges stay inside it.

use super::super::LayoutNode;
use super::{
    ABSENT, Adjacency, Axis, BatchLayoutError, CaptureTask, ChildrenLayout, Dependencies, Frame,
    Host, Kind, N_SLOTS, Node, NodeKey, NodeLayoutData, Request, Requests, RustFloat, SOLVED, Size,
    State, TreeAdapter, WalkNode, enqueue, push, refill, sizing_requests, slot_index,
};
use crate::SameInput;
use slotmap::SlotMap;

#[derive(Clone, Copy, Debug)]
pub(in crate::layout_tree) struct Tail {
    root: NodeKey,
    parent: NodeKey,
    previous: Option<NodeKey>,
}

#[derive(Debug, Default)]
pub(super) enum TailEdit {
    #[default]
    None,
    Append(Tail),
    Remove(Tail),
}

#[derive(Debug, Default)]
pub(super) struct TailCapture {
    rows: Vec<WalkNode>,
    requests: Vec<Option<CaptureTask>>,
    pending: Vec<usize>,
    inputs: Vec<Request<usize>>,
    edges: Vec<(usize, usize)>,
    backward: Vec<(usize, usize)>,
    shape: Vec<TailShape>,
}

#[derive(Debug)]
struct TailShape {
    links: [usize; 3],
    style: super::LayoutParams,
}

#[derive(Debug, Default)]
pub(super) struct TailEdges {
    live: bool,
    span: usize,
    outgoing: Vec<Vec<usize>>,
    boundary: [usize; 2],
    external: [Vec<usize>; 2],
    edges: usize,
}

impl TailEdges {
    pub(super) fn vertex_count(&self) -> usize {
        self.span
    }

    pub(super) fn edge_count(&self) -> usize {
        if self.live { self.edges } else { 0 }
    }

    pub(super) fn remove(&mut self) {
        self.live = false;
    }

    pub(super) fn forget(&mut self) {
        self.live = false;
        self.span = 0;
    }

    pub(super) fn successors(&self, vertex: usize, base: usize) -> Option<&[usize]> {
        if vertex >= base {
            return Some(if self.live {
                &self.outgoing[vertex - base]
            } else {
                &[]
            });
        }
        if self.live {
            if vertex == self.boundary[0] {
                return Some(&self.external[0]);
            }
            if vertex == self.boundary[1] {
                return Some(&self.external[1]);
            }
        }
        None
    }
}

impl State {
    pub(in crate::layout_tree) fn can_record_tail(&self) -> bool {
        self.frame.is_some() && !self.graph_dirty
    }

    pub(in crate::layout_tree) fn record_local_append(
        &mut self,
        was_clean: bool,
        records: &SlotMap<NodeKey, LayoutNode>,
        key: NodeKey,
        parent: NodeKey,
        previous: Option<NodeKey>,
    ) {
        if !was_clean {
            return;
        }
        if let TailEdit::Append(tail) = self.tail_edit {
            // All subsequent created nodes must descend from the pending root.
            let mut next = Some(parent);
            for _ in 0..records.len() {
                let Some(node) = next else { return };
                if node == tail.root {
                    self.graph_dirty = false;
                    return;
                }
                next = records.get(node).and_then(|record| record.parent);
            }
        } else if matches!(self.tail_edit, TailEdit::None)
            && self
                .frame
                .as_ref()
                .is_some_and(|frame| frame.tail.is_none())
        {
            self.tail_edit = TailEdit::Append(Tail {
                root: key,
                parent,
                previous,
            });
            self.graph_dirty = false;
        }
    }

    pub(in crate::layout_tree) fn removable_tail(&self, root: NodeKey) -> Option<Tail> {
        if self.can_record_tail() && matches!(self.tail_edit, TailEdit::None) {
            self.frame.as_ref()?.tail.filter(|tail| tail.root == root)
        } else {
            None
        }
    }

    pub(in crate::layout_tree) fn record_local_removal(&mut self, tail: Tail) {
        self.tail_edit = TailEdit::Remove(tail);
        self.graph_dirty = false;
    }

    pub(super) fn apply_tail_edit<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        population: usize,
    ) -> Option<usize> {
        let edit = std::mem::take(&mut self.tail_edit);
        if self.graph_dirty || matches!(edit, TailEdit::None) {
            return None;
        }
        self.viewport_memo.invalidate();
        let frame = self.frame.as_mut()?;
        frame.grid_memo.clear();
        frame.parked_visibility = None;
        let (result, tail, appended) = match edit {
            TailEdit::None => return None,
            TailEdit::Append(tail) => {
                let result = frame
                    .append_tail(
                        source,
                        population,
                        tail,
                        self.order.positions(),
                        &mut self.tail_capture,
                    )
                    .and_then(|()| {
                        let repair = self.order.repair_with_appended(
                            &frame.graph,
                            &self.tail_capture.backward,
                            &mut self.repair,
                        )?;
                        let base = frame.graph.base_vertex_count();
                        frame.install_tail(self.order.suffix(base), &self.tail_capture, tail);
                        Ok(repair.regions)
                    });
                (result, tail, true)
            }
            TailEdit::Remove(tail) => (frame.remove_tail(source, tail).map(|()| 0), tail, false),
        };
        match result {
            Ok(regions) => {
                let style = source.node_layout_params(tail.parent);
                let prefix_stays = match style.children_layout {
                    ChildrenLayout::Free => true,
                    ChildrenLayout::Stack {
                        axis,
                        arrange: crate::Arrange::Start,
                        ..
                    } => !style.children_origin_flipped[axis],
                    _ => false,
                };
                let mark = if prefix_stays {
                    if appended {
                        frame.initial_tail_from = Some(frame.graph.base_vertex_count() / N_SLOTS);
                    }
                    appended.then_some(tail.root)
                } else {
                    Some(tail.parent)
                };
                if let Some(key) = mark
                    && push(&mut self.placement_edits, key).is_err()
                {
                    self.output_dirty = true;
                }
                Some(regions)
            }
            Err(_) => {
                // The ordinary capture retries from the live document. No
                // output or new measurement was published by this attempt.
                self.graph_dirty = true;
                None
            }
        }
    }
}

impl Frame {
    fn anchor<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &A,
        tail: Tail,
    ) -> Result<(usize, Option<usize>), BatchLayoutError> {
        let parent = self
            .indices
            .get(&tail.parent)
            .copied()
            .ok_or(BatchLayoutError::InvalidGraph)?;
        let style = source.node_layout_params(tail.parent);
        if self.data.has_flow
            || style.disabled
            || super::placement::has_intrinsic_declaration(style)
        {
            return Err(BatchLayoutError::InvalidGraph);
        }
        let stack_axis = match style.children_layout {
            ChildrenLayout::Free => None,
            ChildrenLayout::Stack { axis, .. } => Some(axis),
            _ => return Err(BatchLayoutError::InvalidGraph),
        };
        let mut child_count = 0;
        let mut child_flags = 0;
        let mut child = source.first_child(tail.parent);
        while let Some(key) = child {
            let style = source.node_layout_params(key);
            // Stack Frac reads the gap count, and Fill adds a share
            // producer that folds the complete sibling list.
            if !style.free_placement
                && let Some(axis) = stack_axis
                && [
                    Some(style.size[axis]),
                    style.min_size[axis],
                    style.max_size[axis],
                ]
                .into_iter()
                .any(|size| matches!(size, Some(Size::Fill | Size::Frac(_))))
            {
                return Err(BatchLayoutError::InvalidGraph);
            }
            crate::prepare_frame::summarize_child(style, &mut child_count, &mut child_flags);
            child = source.next_sibling(key);
        }
        let record = &mut self.records[parent];
        record.n_placed_children = child_count;
        let mask = super::NodeFlags::FLEX_CHILD_X
            | super::NodeFlags::FLEX_CHILD_Y
            | super::NodeFlags::GRID_SPANS;
        record.flags.0 = (record.flags.0 & !mask) | child_flags;
        let previous = tail
            .previous
            .map(|key| {
                self.indices
                    .get(&key)
                    .copied()
                    .ok_or(BatchLayoutError::InvalidGraph)
            })
            .transpose()?;
        Ok((parent, previous))
    }

    fn append_tail<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        population: usize,
        tail: Tail,
        positions: &[usize],
        capture: &mut TailCapture,
    ) -> Result<(), BatchLayoutError> {
        let (parent, previous) = self.anchor(source, tail)?;
        if source.parent(tail.root) != Some(tail.parent)
            || source.next_sibling(tail.root).is_some()
            || tail.previous.map_or_else(
                || source.first_child(tail.parent) != Some(tail.root),
                |before| source.next_sibling(before) != Some(tail.root),
            )
        {
            return Err(BatchLayoutError::InvalidGraph);
        }
        let first_vertex = self.graph.base_vertex_count();
        let first_row = first_vertex / N_SLOTS;
        let new_nodes = population
            .checked_sub(self.indices.len())
            .ok_or(BatchLayoutError::InvalidGraph)?;
        capture.walk(source, tail.root, new_nodes)?;
        let row_end = first_row
            .checked_add(new_nodes)
            .ok_or(BatchLayoutError::Capacity)?;
        let new_vertices = new_nodes
            .checked_mul(N_SLOTS)
            .ok_or(BatchLayoutError::Capacity)?;
        let vertices = first_vertex
            .checked_add(new_vertices)
            .ok_or(BatchLayoutError::Capacity)?
            .max(self.graph.vertex_count());
        self.extend_tail_storage(vertices / N_SLOTS, new_nodes)?;
        self.base_execution = self.execution.len();

        for (offset, row) in capture.rows.iter().enumerate() {
            let index = first_row + offset;
            let first = (row.first != usize::MAX).then(|| first_row + row.first);
            let next = (row.next != usize::MAX).then(|| first_row + row.next);
            let parent_id = if offset == 0 {
                parent
            } else {
                first_row + row.parent
            };
            self.nodes[index] = Some(Node::new(row.key, Some(parent_id), first, next)?);
            let style = source.node_layout_params(row.key);
            self.params[index] = *style;
            let record = &mut self.records[index];
            crate::prepare_nodes::seed_pixels::<RustFloat>(record, style, false, None);
            if parent_id >= first_row {
                let parent_record = &mut self.records[parent_id];
                crate::prepare_frame::summarize_child(
                    style,
                    &mut parent_record.n_placed_children,
                    &mut parent_record.flags.0,
                );
            }
        }
        self.replace_tail_link(parent, previous, Some(first_row))?;
        let local_vertices = vertices - first_vertex;
        let tail_graph = &self.graph.tail;
        let boundary = parent * N_SLOTS + slot_index(Axis::X, Kind::Final);
        // Removal leaves the suffix ranks and reader rows isolated. An
        // exact shape match can reconnect them at the same parent boundary.
        // The new rows still measure and resolve under their new node IDs.
        let reuse = tail_graph.span != 0
            && tail_graph.span == local_vertices
            && tail_graph.boundary[0] == boundary
            && capture.matches_shape(&self.params[first_row..row_end]);
        if reuse {
            self.graph.tail.live = true;
            capture.backward.clear();
        } else {
            let host = Host::new(
                source,
                &self.nodes,
                &self.params,
                &mut self.records,
                &mut self.data,
                self.root,
            );
            capture.capture(&host, first_row, row_end)?;
            self.graph
                .pack_tail(parent, local_vertices, &capture.edges)?;
            let rank = |vertex: usize| positions.get(vertex).copied().unwrap_or(vertex);
            for &(from, to) in &capture.edges {
                if rank(from) >= rank(to) {
                    push(&mut capture.backward, (from, to))?;
                }
            }
            capture.remember_shape(&self.params[first_row..row_end]);
        }
        self.ready
            .try_reserve(vertices.saturating_sub(self.ready.len()))?;
        self.ready.resize(vertices, false);
        for &local in &capture.pending {
            let task = capture.requests[local]
                .ok_or(BatchLayoutError::InvalidGraph)?
                .request(first_vertex + local);
            self.ready[first_vertex + local] = self.records[task.node]
                .flags
                .check_state(task.axis(), task.kind)
                == SOLVED;
        }
        self.execution.try_reserve(capture.pending.len())?;
        self.execution_ranks
            .try_reserve(vertices.saturating_sub(self.execution_ranks.len()))?;
        self.execution_ranks.resize(vertices, usize::MAX);
        let words = (self.execution.len() + capture.pending.len()).div_ceil(super::DIRTY_WORD_BITS);
        self.dirty
            .try_reserve(words.saturating_sub(self.dirty.len()))?;
        self.dirty.resize(words, 0);
        Ok(())
    }

    fn extend_tail_storage(
        &mut self,
        rows: usize,
        new_nodes: usize,
    ) -> Result<(), BatchLayoutError> {
        self.indices.try_reserve(new_nodes)?;
        self.visible.try_reserve(new_nodes)?;
        self.nodes
            .try_reserve(rows.saturating_sub(self.nodes.len()))?;
        self.params
            .try_reserve(rows.saturating_sub(self.params.len()))?;
        self.records
            .try_reserve(rows.saturating_sub(self.records.len()))?;
        self.text_widths
            .try_reserve(rows.saturating_sub(self.text_widths.len()))?;
        self.visibility_marks
            .try_reserve(rows.saturating_sub(self.visibility_marks.len()))?;
        // Previously removed rows are still isolated in the order.
        self.nodes.resize(rows, None);
        self.params.resize(rows, ABSENT);
        self.records.resize(rows, NodeLayoutData::new());
        self.text_widths.resize(rows, None);
        self.visibility_marks.resize(rows, 0);
        Ok(())
    }

    fn replace_tail_link(
        &mut self,
        parent: usize,
        previous: Option<usize>,
        following: Option<usize>,
    ) -> Result<(), BatchLayoutError> {
        let row = previous.unwrap_or(parent);
        let old = self.nodes[row].ok_or(BatchLayoutError::InvalidGraph)?;
        let (first, next) = if previous.is_some() {
            (old.first(), following)
        } else {
            (following, old.next())
        };
        self.nodes[row] = Some(Node::new(old.key, old.parent(), first, next)?);
        Ok(())
    }

    fn install_tail(
        &mut self,
        order: impl Iterator<Item = usize>,
        capture: &TailCapture,
        tail: Tail,
    ) {
        let base = self.graph.base_vertex_count();
        for vertex in order {
            if let Some(CaptureTask { kind, vertical }) =
                capture.requests.get(vertex - base).copied().flatten()
            {
                self.execution_ranks[vertex] = self.execution.len();
                let slot = self.scheduled_slot(vertex, vertical, kind);
                self.execution.push(slot);
            }
        }
        let first = base / N_SLOTS;
        for (offset, row) in capture.rows.iter().enumerate() {
            let index = first + offset;
            self.indices.insert(row.key, index);
            self.visible.push(index);
        }
        self.active_nodes += capture.rows.len();
        self.tail = Some(tail);
        self.stack_placement.invalidate();
    }

    pub(super) fn mark_new_tail(&mut self) {
        if self.tail.is_some() {
            let first = self.graph.base_vertex_count() / N_SLOTS;
            for row in first..self.nodes.len() {
                self.mark_node(row);
            }
        }
    }

    fn remove_tail<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &A,
        tail: Tail,
    ) -> Result<(), BatchLayoutError> {
        let (parent, previous) = self.anchor(source, tail)?;
        let root = self
            .indices
            .get(&tail.root)
            .copied()
            .ok_or(BatchLayoutError::InvalidGraph)?;
        let was_last = self.nodes[root].is_some_and(|node| node.next().is_none());
        let linked = if let Some(previous) = previous {
            self.nodes[previous].and_then(Node::next)
        } else {
            self.nodes[parent].and_then(Node::first)
        };
        if !was_last || linked != Some(root) {
            return Err(BatchLayoutError::InvalidGraph);
        }

        if tail.previous.map_or_else(
            || source.first_child(tail.parent).is_some(),
            |before| source.next_sibling(before).is_some(),
        ) {
            return Err(BatchLayoutError::InvalidGraph);
        }
        self.replace_tail_link(parent, previous, None)?;
        let base = self.graph.base_vertex_count();
        for row in base / N_SLOTS..self.nodes.len() {
            if let Some(node) = self.nodes[row].take() {
                self.indices.remove(&node.key);
                if !self.params[row].disabled {
                    self.active_nodes -= 1;
                }
            }
            self.params[row] = ABSENT;
            self.records[row] = NodeLayoutData::new();
            self.text_widths[row] = None;
        }
        self.visible.retain(|&node| node < base / N_SLOTS);
        self.execution.truncate(self.base_execution);
        self.execution_ranks[base..].fill(usize::MAX);
        self.ready[base..].fill(false);
        self.graph.tail.remove();
        self.tail = None;
        self.stack_placement.invalidate();
        Ok(())
    }
}

impl TailCapture {
    fn matches_shape(&self, styles: &[super::LayoutParams]) -> bool {
        self.shape.len() == self.rows.len()
            && self
                .shape
                .iter()
                .zip(&self.rows)
                .zip(styles)
                .all(|((saved, row), style)| {
                    saved.links == [row.parent, row.first, row.next]
                        && saved.style.same_input(style)
                })
    }

    fn remember_shape(&mut self, styles: &[super::LayoutParams]) {
        self.shape.clear();
        if self.shape.try_reserve_exact(self.rows.len()).is_ok() {
            self.shape
                .extend(self.rows.iter().zip(styles).map(|(row, style)| TailShape {
                    links: [row.parent, row.first, row.next],
                    style: *style,
                }));
        }
    }

    fn walk<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &A,
        root: NodeKey,
        count: usize,
    ) -> Result<(), BatchLayoutError> {
        self.rows.clear();
        self.rows.try_reserve(count)?;
        push(
            &mut self.rows,
            WalkNode {
                key: root,
                parent: usize::MAX,
                first: usize::MAX,
                next: usize::MAX,
                dense: usize::MAX,
            },
        )?;
        let mut cursor = 0;
        while let Some(item) = self.rows.get(cursor) {
            let parent = item.key;
            let style = source.node_layout_params(parent);
            if style.disabled
                || !matches!(
                    style.children_layout,
                    ChildrenLayout::Stack { .. } | ChildrenLayout::Free
                )
            {
                return Err(BatchLayoutError::InvalidGraph);
            }
            let start = self.rows.len();
            let mut next = source.first_child(parent);
            while let Some(key) = next {
                if self.rows.len() >= count || source.parent(key) != Some(parent) {
                    return Err(BatchLayoutError::InvalidGraph);
                }
                next = source.next_sibling(key);
                let next_row = if next.is_some() {
                    self.rows.len() + 1
                } else {
                    usize::MAX
                };
                self.rows.push(WalkNode {
                    key,
                    parent: cursor,
                    first: usize::MAX,
                    next: next_row,
                    dense: usize::MAX,
                });
            }
            if self.rows.len() > start {
                self.rows[cursor].first = start;
            }
            cursor += 1;
        }
        if self.rows.len() != count {
            return Err(BatchLayoutError::InvalidGraph);
        }
        Ok(())
    }

    fn capture<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        host: &Host<'_, A>,
        first_row: usize,
        end_row: usize,
    ) -> Result<(), BatchLayoutError> {
        let base = first_row * N_SLOTS;
        refill(&mut self.requests, (end_row - first_row) * N_SLOTS, None)?;
        self.pending.clear();
        self.edges.clear();
        self.backward.clear();
        // Keep the ordinary request definitions and exact packed slot IDs.
        for row in first_row..end_row {
            for vertical in [false, true] {
                enqueue(
                    &mut self.requests,
                    &mut self.pending,
                    Request {
                        node: row - first_row,
                        vertical,
                        kind: Kind::Final,
                    },
                )?;
            }
        }
        let mut cursor = 0;
        while let Some(&reader) = self.pending.get(cursor) {
            cursor += 1;
            let task = self.requests[reader]
                .ok_or(BatchLayoutError::InvalidGraph)?
                .request(base + reader);
            if host
                .node_layout_data(task.node)
                .flags
                .check_state(task.axis(), task.kind)
                == SOLVED
            {
                continue;
            }
            self.inputs.clear();
            let requests = sizing_requests::request_inputs(
                Requests {
                    host,
                    inputs: &mut self.inputs,
                    failed: false,
                },
                task,
            );
            if requests.failed {
                return Err(BatchLayoutError::Capacity);
            }
            for &producer in &self.inputs {
                let from = if producer.node < first_row {
                    producer.node * N_SLOTS + slot_index(producer.axis(), producer.kind)
                } else {
                    enqueue(
                        &mut self.requests,
                        &mut self.pending,
                        Request {
                            node: producer.node - first_row,
                            ..producer
                        },
                    )? + base
                };
                push(&mut self.edges, (from, reader + base))?;
            }
        }
        Ok(())
    }
}

impl Dependencies {
    fn pack_tail(
        &mut self,
        parent: usize,
        vertices: usize,
        edges: &[(usize, usize)],
    ) -> Result<(), BatchLayoutError> {
        let base = self.base_vertex_count();
        let tail = &mut self.tail;
        tail.outgoing
            .try_reserve(vertices.saturating_sub(tail.outgoing.len()))?;
        if vertices > tail.outgoing.len() {
            tail.outgoing.resize_with(vertices, Vec::new);
        }
        for row in &mut tail.outgoing[..vertices] {
            row.clear();
        }
        tail.edges = 0;
        tail.boundary =
            [Axis::X, Axis::Y].map(|axis| parent * N_SLOTS + slot_index(axis, Kind::Final));
        for (axis, vertex) in tail.boundary.into_iter().enumerate() {
            let existing = self.base.successors(vertex);
            let row = &mut tail.external[axis];
            row.clear();
            row.try_reserve(existing.len())?;
            row.extend_from_slice(existing);
        }
        for &(from, to) in edges {
            let row = if from >= base {
                tail.outgoing
                    .get_mut(from - base)
                    .ok_or(BatchLayoutError::InvalidGraph)?
            } else {
                let axis = tail
                    .boundary
                    .iter()
                    .position(|&vertex| vertex == from)
                    .ok_or(BatchLayoutError::InvalidGraph)?;
                &mut tail.external[axis]
            };
            if row.last().copied() != Some(to) {
                push(row, to)?;
                tail.edges += 1;
            }
        }
        tail.span = vertices;
        tail.live = true;
        Ok(())
    }
}

#[cfg(test)]
mod sparse_row_tests {
    use super::super::*;

    fn pack(
        edges: &[(usize, usize)],
        ranks: &[usize],
        sparse: bool,
    ) -> (Dependencies, Vec<(usize, usize)>) {
        let mut out = Dependencies::default();
        capture(&mut out.base, edges, ranks.len(), sparse);
        let mut seeds = Vec::new();
        out.base.pack(edges, ranks, &mut seeds).unwrap();
        (out, seeds)
    }

    fn capture(rows: &mut BaseRows, edges: &[(usize, usize)], n: usize, adaptive: bool) {
        rows.begin(n).unwrap();
        if !adaptive {
            rows.offsets.resize(n + 1, 0);
        }
        for (index, &(producer, _)) in edges.iter().enumerate() {
            rows.count_edge(producer, &edges[..=index]).unwrap();
        }
        assert_eq!(
            rows.offsets.is_empty(),
            adaptive && edges.len() <= SPARSE_EDGE_LIMIT
        );
    }

    #[test]
    fn base_rows_can_promote_and_return_to_sparse() {
        let mut reused = BaseRows::default();
        let n = 300;
        let edges: Vec<_> = (0..40).map(|i| (149 + i / 5, i % 5)).collect();
        let mut seeds = Vec::new();
        for count in [0, 32, 33, 40, 1, 0] {
            let subset = &edges[..count];
            capture(&mut reused, subset, n, true);
            reused.pack(subset, &[], &mut seeds).unwrap();
            let mut reference = BaseRows::default();
            capture(&mut reference, subset, n, false);
            let mut expected = Vec::new();
            reference.pack(subset, &[], &mut expected).unwrap();
            assert_eq!(seeds, expected);
            for vertex in 0..n {
                assert_eq!(reused.successors(vertex), reference.successors(vertex));
            }
        }
    }

    #[test]
    fn tiny_graph_rows_and_tail_boundary_match_csr() {
        let n = 1010;
        let ranks: Vec<_> = (0..n).map(|vertex| (vertex * 13) % n).collect();
        let mut random = 9663u64;
        for len in 0..=SPARSE_EDGE_LIMIT + 7 {
            for _ in 0..169 {
                let mut edges = Vec::new();
                for _ in 0..len {
                    random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                    let producer = (random >> 32) as usize % (if random & 4 == 0 { 11 } else { n });
                    random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                    let reader = (random >> 32) as usize % (if random & 16 == 0 { 7 } else { n });
                    if random & 3 == 0 && !edges.is_empty() {
                        edges.push(edges[edges.len() / 2]);
                    } else {
                        edges.push((producer, reader));
                    }
                }
                let (mut csr, old) = pack(&edges, &ranks, false);
                let (mut sparse, new) = pack(&edges, &ranks, true);
                assert_eq!(old, new);
                let tail = [
                    (slot_index(Axis::X, Kind::Final), n + 2),
                    (slot_index(Axis::Y, Kind::Final), n + 4),
                    (n + 1, n + 2),
                ];
                for phase in 0..3 {
                    if phase == 1 {
                        csr.pack_tail(0, 10, &tail).unwrap();
                        sparse.pack_tail(0, 10, &tail).unwrap();
                    }
                    if phase == 2 {
                        csr.tail.remove();
                        sparse.tail.remove();
                    }
                    assert_eq!(csr.base_vertex_count(), sparse.base_vertex_count());
                    assert_eq!(csr.vertex_count(), sparse.vertex_count());
                    assert_eq!(csr.edge_count(), sparse.edge_count());
                    for vertex in 0..csr.vertex_count() {
                        assert_eq!(csr.successors(vertex), sparse.successors(vertex));
                    }
                }
            }
        }
    }
}
