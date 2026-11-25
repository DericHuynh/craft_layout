//! The first view uses the owned solver. When a subsequent solve needs work,
//! the pilot captures the current graph and takes over with batch Pearce–Kelly.

use super::NodeKey;
use crate::batch_order::{Adjacency, RepairError, RepairScratch};
use crate::incremental::{NodeChange, readers, tape_plan};
use crate::place::Place;
use crate::placement_geometry::RustFloat;
use crate::solve::sizing_requests::{self, Request, RequestAccess, RequestModel};
use crate::solve::{Kind, N_SLOTS, NodeFlags, SOLVED, Slot, Solve, UNSOLVED, slot_index};
use crate::solve::{block_schedule, sizing_finish};
use crate::{
    Axis, ChildrenLayout, ContentMeasureInput, LayoutData, LayoutParams, LayoutWarning,
    MainAxisCellSize, NodeLayoutData, SameInput, Size, TreeAdapter, Xy, XyRect,
};
use std::collections::{HashMap, TryReserveError};
use std::num::NonZeroU32;

mod block;
mod grid_memo;
mod memo;
mod order;
mod placement;
mod stack_fit;
mod stack_placement;
mod stack_shares;
mod structural_delta;
mod warm;
mod wrap_leaves;
mod wrap_placement;
pub(super) use memo::MemoSource;

/// Failure to admit a layout to the batch solver. A rejected frame leaves
/// its preceding published layout available.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BatchLayoutError {
    /// The requested sizing slots form a cycle.
    Cycle,
    /// The captured slots or physical links are inconsistent.
    InvalidGraph,
    /// The pilot could not reserve its graph or repair storage.
    Capacity,
}

impl std::fmt::Display for BatchLayoutError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Cycle => "the sizing graph contains a cycle",
            Self::InvalidGraph => "the sizing graph has inconsistent slots or links",
            Self::Capacity => "the batch solver could not reserve storage",
        })
    }
}

impl std::error::Error for BatchLayoutError {}

impl From<TryReserveError> for BatchLayoutError {
    fn from(_: TryReserveError) -> Self {
        Self::Capacity
    }
}

impl From<RepairError> for BatchLayoutError {
    fn from(error: RepairError) -> Self {
        match error {
            RepairError::Cycle => Self::Cycle,
            RepairError::Allocation => Self::Capacity,
            _ => Self::InvalidGraph,
        }
    }
}

/// Work performed by the batch scheduler. The initial default solve reports zero Batch work.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct BatchLayoutStats {
    /// Packed sizing slots in the retained execution schedule.
    pub slots: usize,
    /// Distinct producer-to-reader dependencies.
    pub edges: usize,
    /// Sizing producers evaluated, excluding prepared constants.
    pub computed: usize,
    /// Affected topological intervals repaired this frame.
    pub repaired_intervals: usize,
    /// Whether the dependency graph was captured again.
    pub rebuilt_graph: bool,
}

#[derive(Debug, Default)]
pub(super) struct State {
    frame: Option<Frame>,
    order: order::Order,
    repair: RepairScratch,
    capture: CaptureScratch,
    tail_edit: structural_delta::TailEdit,
    tail_capture: structural_delta::TailCapture,
    graph_dirty: bool,
    visibility_dirty: bool,
    visibility_roots: Vec<NodeKey>,
    values_dirty: bool,
    output_dirty: bool,
    content: Vec<NodeKey>,
    declarations: Vec<(NodeKey, NodeChange)>,
    reordered: Vec<NodeKey>,
    placement_edits: Vec<NodeKey>,
    viewport_memo: memo::ViewportMemo,
}

impl State {
    pub(super) fn graph_changed(&mut self) {
        self.graph_dirty = true;
        self.viewport_memo.invalidate();
        if let Some(frame) = &mut self.frame {
            frame.grid_memo.clear();
        }
    }

    pub(super) fn invalidate(&mut self) {
        self.values_dirty = true;
        self.viewport_memo.invalidate();
        if let Some(frame) = &mut self.frame {
            frame.grid_memo.invalidate();
        }
    }

    pub(super) fn output_changed(&mut self) {
        self.output_dirty = true;
    }

    /// The window of the last frame this scheduler solved.
    pub(super) fn published_window(&self) -> Option<Xy<f32>> {
        self.frame.as_ref().map(|frame| frame.data.window_size)
    }

    /// The unsnapped final size this scheduler last computed for `key`.
    pub(super) fn published_size(&self, key: NodeKey) -> Option<Xy<f32>> {
        let frame = self.frame.as_ref()?;
        let &index = frame.indices.get(&key)?;
        frame.nodes.get(index)?.as_ref().filter(|node| node.key == key)?;
        Some(frame.records.get(index)?.size())
    }

    pub(super) fn content_changed(&mut self, key: NodeKey) {
        self.viewport_memo.invalidate();
        if let Some(frame) = &mut self.frame {
            frame.invalidate_grid_memo(key);
        }
        if self.frame.is_none() || self.graph_dirty || self.values_dirty {
            return;
        }
        if let Some(frame) = &mut self.frame
            && let Some(&row) = frame.indices.get(&key)
        {
            frame.text_widths[row] = None;
        }
        if self.content.try_reserve(1).is_ok() {
            self.content.push(key);
        } else {
            self.values_dirty = true;
        }
    }

    pub(super) fn parameters_changed(
        &mut self,
        key: NodeKey,
        old: &LayoutParams,
        new: &LayoutParams,
    ) {
        if self.frame.is_none() || self.graph_dirty {
            return;
        }
        if old.disabled != new.disabled {
            self.viewport_memo.invalidate();
        } else {
            self.viewport_memo.edit_style(key);
        }
        if let Some(frame) = &mut self.frame {
            frame.stack_placement.invalidate();
            frame.stack_fit.invalidate();
            frame.warm_runs.invalidate();
            frame.ready_wrap_placement = false;
            frame.stack_shares.invalidate();
            if !(LayoutParams {
                disabled: new.disabled,
                ..*old
            })
            .same_input(new)
            {
                frame.invalidate_grid_memo(key);
            }
        }
        if self.note_visibility(key, old, new) {
            return;
        }
        // Visibility edits can update inherited flags across a subtree.
        // The capture or visibility refresh reads those rows from the tree.
        if old.disabled == new.disabled
            && let Some(frame) = &mut self.frame
            && let Some(&node) = frame.indices.get(&key)
        {
            frame.params[node] = LayoutParams {
                disabled: frame.params[node].disabled,
                ..*new
            };
        }
        if self.note_placement(key, old, new) {
            return;
        }
        let Some(change) = NodeChange::between(old, new, true) else {
            self.graph_changed();
            return;
        };
        // Finite pixel declarations can be prepared constants. A change in
        // their readiness requires recapturing their incoming requests.
        if [Axis::X, Axis::Y].into_iter().any(|axis| {
            matches!(old.size[axis], Size::Pixels(value) if value.is_finite())
                != matches!(new.size[axis], Size::Pixels(value) if value.is_finite())
        }) {
            self.graph_changed();
        } else if change == NodeChange::default() {
            self.output_changed();
        } else if push(&mut self.declarations, (key, change)).is_err() {
            self.graph_changed();
        }
    }

    pub(super) fn solve<A: MemoSource>(
        &mut self,
        source: &mut A,
        population: usize,
        window: Xy<f32>,
        scale: Option<f32>,
    ) -> Result<BatchLayoutStats, BatchLayoutError> {
        let local_repair = self.apply_tail_edit(source, population);
        let window_changed = self
            .frame
            .as_ref()
            .is_none_or(|frame| !frame.data.window_size.same_input(&window));
        let sizing_inputs_changed = local_repair.is_some()
            || self.values_dirty
            || window_changed
            || !self.content.is_empty()
            || !self.reordered.is_empty()
            || !self.declarations.is_empty();
        let sizing_changed = sizing_inputs_changed || self.visibility_dirty;
        // Block declarations can change adjoining edges independently of the
        // size words. Content and viewport edits use the retained slot graph.
        let refresh_block = !self.declarations.is_empty()
            && self.frame.as_ref().is_some_and(|frame| frame.has_block);
        let rebuilt = self.frame.is_none() || self.graph_dirty;
        let repaired_intervals = if rebuilt {
            self.rebuild(source, population)?
        } else {
            local_repair.unwrap_or(0)
        };
        let frame = self.frame.as_mut().ok_or(BatchLayoutError::InvalidGraph)?;
        if local_repair.is_some() {
            frame.stack_fit.invalidate();
        }
        if rebuilt || local_repair.is_some() {
            frame.stack_shares.invalidate();
        }
        frame.grid_memo.output_index = None;
        let may_park_visibility = !rebuilt && !sizing_inputs_changed && !self.output_dirty;
        if !may_park_visibility {
            frame.parked_visibility = None;
        }
        if refresh_block {
            frame.block_plan.invalidate();
        }
        let mut stats = BatchLayoutStats {
            slots: frame.execution.len(),
            edges: frame.graph.edge_count(),
            repaired_intervals,
            rebuilt_graph: rebuilt,
            ..BatchLayoutStats::default()
        };
        let scale_changed = !frame.data.pixel_scale.same_input(&scale);
        let memo_input = if window_changed
            && !rebuilt
            && !self.values_dirty
            && local_repair.is_none()
            && frame.tail.is_none()
            && !self.visibility_dirty
            && self.content.is_empty()
            && self.reordered.is_empty()
        {
            self.viewport_memo.input(frame, window, scale)
        } else {
            None
        };
        if let Some(input) = memo_input
            && self.viewport_memo.restore(frame, source, input)
        {
            self.clear_edits();
            return Ok(stats);
        }
        let full_placement = rebuilt
            || window_changed
            || scale_changed
            || self.values_dirty
            || refresh_block
            || self.output_dirty;
        let previous_window = frame.data.window_size;
        frame.data.window_size = window;
        frame.data.pixel_scale = scale;
        let all_dirty = rebuilt || self.values_dirty || refresh_block;
        if rebuilt || sizing_changed {
            let refresh_visibility = self.visibility_dirty && !rebuilt;
            frame.dirty.fill(0);
            if local_repair.is_some() {
                frame.mark_new_tail();
            }
            if self.values_dirty && std::mem::take(&mut frame.cached_text_widths) {
                frame.text_widths.fill(None);
            }
            if refresh_visibility {
                frame.refresh_visibility(
                    source,
                    &self.visibility_roots,
                    !full_placement,
                    may_park_visibility,
                );
            }
            if !rebuilt {
                for key in &self.reordered {
                    if let Some(&node) = frame.indices.get(key) {
                        frame.mark_node(node);
                    }
                }
                let viewport_edits = Xy::new(
                    !previous_window.x.same_input(&window.x),
                    !previous_window.y.same_input(&window.y),
                );
                frame.seed_edits(
                    source,
                    viewport_edits,
                    &self.content,
                    &self.declarations,
                    !full_placement,
                );
            }
            stats.computed = if !all_dirty && !previous_window.x.same_input(&window.x) {
                frame.measure_block_resize(source).unwrap_or_else(|| {
                    frame.evaluate(
                        source,
                        rebuilt || refresh_visibility,
                        all_dirty,
                        !full_placement,
                    )
                })
            } else {
                frame.evaluate(
                    source,
                    rebuilt || refresh_visibility,
                    all_dirty,
                    !full_placement,
                )
            };
        }
        if full_placement {
            frame.place(source, all_dirty && frame.ready_wrap_placement);
        } else if sizing_changed || !self.placement_edits.is_empty() {
            frame.place_dirty(source, &self.placement_edits);
        }
        if let Some(input) = memo_input {
            self.viewport_memo.save(frame, source, input);
        }
        self.clear_edits();
        Ok(stats)
    }

    fn clear_edits(&mut self) {
        self.content.clear();
        self.declarations.clear();
        self.reordered.clear();
        self.placement_edits.clear();
        self.graph_dirty = false;
        self.visibility_dirty = false;
        self.visibility_roots.clear();
        self.values_dirty = false;
        self.output_dirty = false;
    }

    fn rebuild<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        population: usize,
    ) -> Result<usize, BatchLayoutError> {
        // A rejected rebuild leaves the old identity map and order intact.
        // The next solve must replace the partly captured frame before using it.
        self.graph_dirty = true;
        let frame = self.frame.get_or_insert_with(Frame::default);
        frame.graph.tail.forget();
        frame.tail = None;
        let previous_nodes = self.order.len() / N_SLOTS;
        frame.collect(source, population, previous_nodes, &mut self.capture)?;
        frame.prepare_block_margins()?;
        let mut all_visible = frame.begin_all_visible_capture(population);
        let stats = loop {
            frame.capture(source, &mut self.capture)?;
            frame.graph.pack(
                &self.capture.edges,
                self.order.positions(),
                &mut self.capture.backward,
            )?;
            frame.prepare_execution(self.capture.tasks.len(), self.capture.pending.len())?;
            let result = self.order.repair_with_appended(
                &frame.graph,
                &self.capture.backward,
                &mut self.repair,
            );
            if all_visible && result == Err(RepairError::Cycle) {
                // Hidden branches may add a cycle. The published layout
                // only requires the visible requests.
                frame.collect(source, population, previous_nodes, &mut self.capture)?;
                frame.prepare_block_margins()?;
                all_visible = false;
            } else {
                break result?;
            }
        };
        frame.install_execution(self.order.suffix(0), &self.capture.tasks);
        std::mem::swap(&mut frame.indices, &mut self.capture.indices);
        frame.prepare_grid_memo();
        frame.prepare_wrap_placement();
        if all_visible {
            frame.refresh_visibility(source, &[], false, false);
        }
        Ok(stats.regions)
    }
}

#[derive(Debug, Default)]
struct CaptureScratch {
    indices: HashMap<NodeKey, usize>,
    keys: Vec<WalkNode>,
    occupied: Vec<bool>,
    block_children: Vec<Option<bool>>,
    tasks: Vec<Option<CaptureTask>>,
    pending: Vec<usize>,
    edges: Vec<(usize, usize)>,
    backward: Vec<(usize, usize)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CaptureTask {
    kind: Kind,
    vertical: bool,
}

impl CaptureTask {
    fn request(self, vertex: usize) -> Request<usize> {
        sizing_requests::target(vertex / N_SLOTS, self.vertical, self.kind)
    }
}

const NO_ROW: usize = usize::MAX;

#[derive(Debug)]
struct WalkNode {
    key: NodeKey,
    parent: usize,
    first: usize,
    next: usize,
    dense: usize,
}

// Sparse rows are for graphs with a handful of captured edges and many
// isolated slots. Promote immediately when capture exceeds that budget.
const SPARSE_EDGE_LIMIT: usize = 32;
const SPARSE_VERTEX_MIN: usize = 256;

#[derive(Debug)]
struct SparseRow {
    vertex: usize,
    start: usize,
    end: usize,
}

#[derive(Debug, Default)]
struct BaseRows {
    vertices: usize,
    offsets: Vec<usize>,
    readers: Vec<usize>,
    sparse: Vec<SparseRow>,
}

#[derive(Debug, Default)]
struct Dependencies {
    base: BaseRows,
    tail: structural_delta::TailEdges,
}

impl Adjacency for Dependencies {
    fn vertex_count(&self) -> usize {
        self.base_vertex_count() + self.tail.vertex_count()
    }

    fn successors(&self, vertex: usize) -> &[usize] {
        self.tail
            .successors(vertex, self.base_vertex_count())
            .unwrap_or_else(|| self.base.successors(vertex))
    }
}

impl Dependencies {
    fn base_vertex_count(&self) -> usize {
        self.base.vertices
    }

    fn edge_count(&self) -> usize {
        self.base.readers.len() + self.tail.edge_count()
    }

    fn pack(
        &mut self,
        edges: &[(usize, usize)],
        positions: &[usize],
        backward: &mut Vec<(usize, usize)>,
    ) -> Result<(), BatchLayoutError> {
        self.base.pack(edges, positions, backward)
    }
}

impl BaseRows {
    #[inline]
    fn count_edge(
        &mut self,
        producer: usize,
        captured: &[(usize, usize)],
    ) -> Result<(), BatchLayoutError> {
        if let Some(count) = self.offsets.get_mut(producer) {
            *count += 1;
        } else if captured.len() > SPARSE_EDGE_LIMIT {
            self.promote(captured)?;
        }
        Ok(())
    }

    #[cold]
    fn promote(&mut self, captured: &[(usize, usize)]) -> Result<(), BatchLayoutError> {
        // The prefix has no degree counts yet. Count it exactly once
        // before subsequent captures take the ordinary CSR path.
        let count = self
            .vertices
            .checked_add(1)
            .ok_or(BatchLayoutError::Capacity)?;
        refill(&mut self.offsets, count, 0usize)?;
        for &(producer, _) in captured {
            self.offsets[producer] += 1;
        }
        Ok(())
    }

    fn begin(&mut self, vertices: usize) -> Result<(), BatchLayoutError> {
        self.vertices = vertices;
        self.offsets.clear();
        self.sparse.clear();
        if vertices < SPARSE_VERTEX_MIN {
            let count = vertices.checked_add(1).ok_or(BatchLayoutError::Capacity)?;
            refill(&mut self.offsets, count, 0usize)?;
        }
        Ok(())
    }

    #[inline]
    fn successors(&self, vertex: usize) -> &[usize] {
        if !self.offsets.is_empty() {
            return &self.readers[self.offsets[vertex]..self.offsets[vertex + 1]];
        }
        let Ok(index) = self.sparse.binary_search_by_key(&vertex, |row| row.vertex) else {
            return &[];
        };
        let row = &self.sparse[index];
        &self.readers[row.start..row.end]
    }

    fn pack(
        &mut self,
        edges: &[(usize, usize)],
        positions: &[usize],
        backward: &mut Vec<(usize, usize)>,
    ) -> Result<(), BatchLayoutError> {
        if self.offsets.is_empty() {
            return self.pack_sparse(edges, positions, backward);
        }
        let vertices = self.vertices;
        let offsets = &mut self.offsets;
        for vertex in 1..offsets.len() {
            offsets[vertex] += offsets[vertex - 1];
        }
        let readers = &mut self.readers;
        refill(readers, edges.len(), 0)?;
        // Capture records each producer's degree at its own index. The
        // prefix sum is its end; stable reverse scatter leaves its start.
        for &(producer, reader) in edges.iter().rev() {
            offsets[producer] -= 1;
            readers[offsets[producer]] = reader;
        }
        let rank = |vertex: usize| positions.get(vertex).copied().unwrap_or(vertex);
        backward.clear();
        let mut write = 0;
        for producer in 0..vertices {
            let start = offsets[producer];
            let end = offsets[producer + 1];
            offsets[producer] = write;
            if start == end {
                continue;
            }
            let from = rank(producer);
            let mut previous = None;
            for read in start..end {
                let reader = readers[read];
                if previous != Some(reader) {
                    if read != write {
                        readers[write] = reader;
                    }
                    if from >= rank(reader) {
                        push(backward, (producer, reader))?;
                    }
                    write += 1;
                    previous = Some(reader);
                }
            }
        }
        offsets[vertices] = write;
        readers.truncate(write);
        Ok(())
    }

    fn pack_sparse(
        &mut self,
        edges: &[(usize, usize)],
        positions: &[usize],
        backward: &mut Vec<(usize, usize)>,
    ) -> Result<(), BatchLayoutError> {
        let mut indexes = [0; SPARSE_EDGE_LIMIT];
        let indexes = indexes
            .get_mut(..edges.len())
            .ok_or(BatchLayoutError::InvalidGraph)?;
        for (index, slot) in indexes.iter_mut().enumerate() {
            *slot = index;
        }
        // CSR's reverse scatter is stable inside each producer row. The
        // original edge ordinal preserves that order before deduplication.
        indexes.sort_unstable_by_key(|&index| (edges[index].0, index));
        self.readers.clear();
        self.readers.try_reserve_exact(edges.len())?;
        self.sparse.clear();
        self.sparse.try_reserve_exact(edges.len())?;
        backward.clear();
        let rank = |vertex: usize| positions.get(vertex).copied().unwrap_or(vertex);
        for group in indexes.chunk_by(|a, b| edges[*a].0 == edges[*b].0) {
            let vertex = edges[group[0]].0;
            let start = self.readers.len();
            let from = rank(vertex);
            let mut previous = None;
            for &index in group {
                let reader = edges[index].1;
                if previous == Some(reader) {
                    continue;
                }
                self.readers.push(reader);
                previous = Some(reader);
                if from >= rank(reader) {
                    push(backward, (vertex, reader))?;
                }
            }
            self.sparse.push(SparseRow {
                vertex,
                start,
                end: self.readers.len(),
            });
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
struct Node {
    key: NodeKey,
    parent: Option<NonZeroU32>,
    first: Option<NonZeroU32>,
    next: Option<NonZeroU32>,
}

impl Node {
    fn new(
        key: NodeKey,
        parent: Option<usize>,
        first: Option<usize>,
        next: Option<usize>,
    ) -> Result<Self, BatchLayoutError> {
        let pack = |link: Option<usize>| {
            link.map(|id| {
                u32::try_from(id)
                    .ok()
                    .and_then(|id| id.checked_add(1))
                    .and_then(NonZeroU32::new)
                    .ok_or(BatchLayoutError::Capacity)
            })
            .transpose()
        };
        Ok(Self {
            key,
            parent: pack(parent)?,
            first: pack(first)?,
            next: pack(next)?,
        })
    }

    #[inline(always)]
    fn parent(self) -> Option<usize> {
        self.parent.map(|link| (link.get() - 1) as usize)
    }

    #[inline(always)]
    fn first(self) -> Option<usize> {
        self.first.map(|link| (link.get() - 1) as usize)
    }

    #[inline(always)]
    fn next(self) -> Option<usize> {
        self.next.map(|link| (link.get() - 1) as usize)
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
enum DirectSize {
    Generic,
    Final,
    IntrinsicFinal,
    ViewportFill,
    ParentFill,
    ParentFillMargins,
    StackFill,
    WrapMainFill,
    WrapCrossFill,
    WrapLeaves,
    GridFill,
    BoundedFinal,
    StackShare,
    Pixels,
    Ratio,
    ViewportFrac,
    ParentFrac,
    StackFrac,
}

#[derive(Debug, Clone, Copy)]
struct ScheduledSlot {
    vertex: usize,
    kind: Kind,
    vertical: bool,
    prepared: bool,
    direct: DirectSize,
    parent: u32,
}

#[derive(Debug, Default)]
struct Frame {
    root: usize,
    indices: HashMap<NodeKey, usize>,
    nodes: Vec<Option<Node>>,
    visible: Vec<usize>,
    count_grids: Vec<usize>,
    active_nodes: usize,
    visibility_marks: Vec<u8>,
    parked_visibility: Option<usize>,
    params: Vec<LayoutParams>,
    records: Vec<NodeLayoutData>,
    text_widths: Vec<Option<u32>>,
    cached_text_widths: bool,
    execution: Vec<ScheduledSlot>,
    warm_execution: Option<Vec<warm::WarmSlot>>,
    warm_needs_compile: bool,
    wrap_leaves: Option<wrap_leaves::Program>,
    warm_runs: warm::Runs,
    execution_ranks: Vec<usize>,
    ready: Vec<bool>,
    dirty: Vec<u64>,
    graph: Dependencies,
    tail: Option<structural_delta::Tail>,
    base_execution: usize,
    initial_tail_from: Option<usize>,
    data: LayoutData<usize>,
    has_block: bool,
    has_width_grid: bool,
    stack_placement: stack_placement::StackPlacement,
    stack_fit: stack_fit::StackFit,
    ready_wrap_placement: bool,
    stack_shares: stack_shares::StackShares,
    block_plan: block::BlockPlan,
    grid_memo: grid_memo::GridMemo,
    covers_visibility: bool,
}

impl Frame {
    fn collect<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &A,
        population: usize,
        before: usize,
        scratch: &mut CaptureScratch,
    ) -> Result<(), BatchLayoutError> {
        self.stack_placement.invalidate();
        self.stack_fit.invalidate();
        self.warm_runs.invalidate();
        let indices = &mut scratch.indices;
        let keys = &mut scratch.keys;
        breadth_first(source, population, keys)?;
        indices.clear();
        indices.try_reserve(keys.len())?;
        let first_capture = before == 0;
        let count = if first_capture {
            for (node, row) in keys.iter_mut().enumerate() {
                row.dense = node;
                if indices.insert(row.key, node).is_some() {
                    return Err(BatchLayoutError::InvalidGraph);
                }
            }
            keys.len()
        } else {
            // Retain positions through visibility changes and recycle positions
            // only after their generational key has left the tree.
            let occupied = &mut scratch.occupied;
            refill(occupied, before, false)?;
            for row in keys.iter_mut() {
                if let Some(&index) = self.indices.get(&row.key) {
                    row.dense = index;
                    occupied[index] = true;
                }
            }
            let mut holes = occupied
                .iter()
                .enumerate()
                .filter_map(|(index, used)| (!used).then_some(index));
            let mut count = before;
            for row in keys.iter_mut() {
                if row.dense == NO_ROW {
                    row.dense = if let Some(index) = holes.next() {
                        index
                    } else {
                        let index = count;
                        count = count.checked_add(1).ok_or(BatchLayoutError::Capacity)?;
                        index
                    };
                }
                if indices.insert(row.key, row.dense).is_some() {
                    return Err(BatchLayoutError::InvalidGraph);
                }
            }
            count
        };
        let vertices = count
            .checked_mul(N_SLOTS)
            .ok_or(BatchLayoutError::Capacity)?;
        let link = |row: usize| (row != NO_ROW).then(|| keys[row].dense);
        let nodes = &mut self.nodes;
        reserve_rows(nodes, count, None, first_capture)?;
        refill(&mut self.visibility_marks, count, 0)?;
        let records = &mut self.records;
        reserve_rows(records, count, NodeLayoutData::new(), first_capture)?;
        refill(&mut self.text_widths, count, None)?;
        self.cached_text_widths = false;
        reserve_rows(&mut self.params, count, ABSENT, first_capture)?;
        let block_children = &mut scratch.block_children;
        refill(block_children, count, None)?;
        let visible = &mut self.visible;
        visible.clear();
        visible.try_reserve_exact(keys.len())?;
        self.count_grids.clear();
        let mut has_block = false;
        let mut has_flow = false;
        let mut has_width_grid = false;
        let root = keys[0].dense;
        for row in keys.iter() {
            let key = row.key;
            let node = row.dense;
            let parent = link(row.parent);
            let first = link(row.first);
            let next = link(row.next);
            let links = Some(Node::new(key, parent, first, next)?);
            let params = source.node_layout_params(key);
            if first_capture {
                // Rows arrive in index order and their parents are already filled.
                nodes.push(links);
                records.push(NodeLayoutData::new());
                self.params.push(*params);
            } else {
                nodes[node] = links;
                self.params[node] = *params;
            }
            if params.disabled {
                continue;
            }
            visible.push(node);
            if matches!(
                params.children_layout,
                ChildrenLayout::Grid {
                    columns: MainAxisCellSize::Count(_),
                    ..
                }
            ) {
                push(&mut self.count_grids, node)?;
            }
            if let Some(parent) = parent {
                let data = &mut records[parent];
                crate::prepare_frame::summarize_child(
                    params,
                    &mut data.n_placed_children,
                    &mut data.flags.0,
                );
                if data.flags.is_block_container() {
                    data.n_placed_children = u32::from(data.n_placed_children != 0);
                }
            }
            let block_parent = block_schedule::in_flow_parent(
                parent.and_then(|i| block_children[i]),
                params.free_placement,
            );
            let block = matches!(params.children_layout, ChildrenLayout::Block);
            has_block |= block;
            has_flow |= block || matches!(params.children_layout, ChildrenLayout::Wrap { .. });
            block_children[node] = block.then(|| {
                block_schedule::auto_content_height(
                    matches!(params.size.y, Size::Auto | Size::FitContent),
                    params.size.y.is_flex(),
                    block_parent == Some(true),
                )
            });
            let data = &mut records[node];
            if let Some(auto_height) = block_parent {
                data.flags.0 |= NodeFlags::BLOCK_ITEM;
                if auto_height {
                    data.flags.0 |= NodeFlags::BLOCK_PARENT_AUTO_HEIGHT;
                }
            }
            if block {
                data.flags.0 |= NodeFlags::BLOCK_CONTAINER;
            }
            if matches!(params.children_layout, ChildrenLayout::Wrap { .. }) {
                data.flags.0 |= NodeFlags::WRAP_CONTAINER;
            }
            let width_grid = match params.children_layout {
                ChildrenLayout::Grid {
                    columns: MainAxisCellSize::Width(_),
                    main_axis,
                    ..
                } => Some(main_axis),
                _ => None,
            };
            has_width_grid |= width_grid.is_some();
            crate::prepare_nodes::seed_pixels::<RustFloat>(
                data,
                params,
                block_parent.is_some(),
                width_grid,
            );
        }
        self.root = root;
        self.data.has_flow = has_flow;
        self.data.block_margins.clear();
        self.data.sizing_warned = false;
        self.has_block = has_block;
        self.has_width_grid = has_width_grid;
        self.covers_visibility = !has_block && self.visible.len() == keys.len();
        self.active_nodes = self.visible.len();
        refill(&mut self.ready, vertices, false)?;
        Ok(())
    }

    fn begin_all_visible_capture(&mut self, population: usize) -> bool {
        if self.visible.len() == population
            || self.params.iter().any(|params| {
                !matches!(
                    params.children_layout,
                    ChildrenLayout::Free | ChildrenLayout::Stack { .. }
                )
            })
        {
            return false;
        }
        // Visibility removes requests in Stack and Free containers.
        // These modes have no extra grid assignment or flow state.
        for (row, node) in self.nodes.iter().enumerate() {
            let params = &mut self.params[row];
            if node.is_none() || !params.disabled {
                continue;
            }
            params.disabled = false;
            self.visible.push(row);
            crate::prepare_nodes::seed_pixels::<RustFloat>(
                &mut self.records[row],
                params,
                false,
                None,
            );
        }
        self.covers_visibility = true;
        self.active_nodes = population;
        true
    }

    fn refresh_visibility<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &A,
        roots: &[NodeKey],
        mark_placement: bool,
        may_park: bool,
    ) {
        self.stack_fit.invalidate();
        const VISITED: u8 = 1;
        const CHILDREN_CHANGED: u8 = 2;
        self.visibility_marks.fill(0);
        let last_parked = self.parked_visibility.take();
        let (mut park, restore) = if may_park {
            self.visibility_reuse(source, roots, last_parked)
        } else {
            (None, false)
        };
        // A freshly captured all-visible graph also restores the actual
        // inherited flags, starting at the root on that first refresh.
        let first = roots.is_empty().then(|| source.root());
        for key in first.into_iter().chain(roots.iter().copied()) {
            let Some(&root) = self.indices.get(&key) else {
                continue;
            };
            let mut row = root;
            loop {
                let Some(node) = self.nodes[row] else { break };
                if self.visibility_marks[row] & VISITED == 0 {
                    self.visibility_marks[row] |= VISITED;
                    let params = source.node_layout_params(node.key);
                    let was_disabled = self.params[row].disabled;
                    if was_disabled {
                        // Reenabling a branch makes all descendants visible.
                        // Reuse requires that same visibility before hiding.
                        park = None;
                    }
                    if was_disabled != params.disabled {
                        self.params[row].disabled = params.disabled;
                        if params.disabled {
                            self.active_nodes -= 1;
                        } else {
                            self.active_nodes += 1;
                        }
                        if !params.disabled && !restore {
                            self.mark_node(row);
                            let width_grid = match params.children_layout {
                                ChildrenLayout::Grid {
                                    columns: MainAxisCellSize::Width(_),
                                    main_axis,
                                    ..
                                } => Some(main_axis),
                                _ => None,
                            };
                            crate::prepare_nodes::seed_pixels::<RustFloat>(
                                &mut self.records[row],
                                params,
                                false,
                                width_grid,
                            );
                        }
                        if (!restore || row == root)
                            && !params.free_placement
                            && let Some(parent) = node.parent()
                        {
                            self.visibility_marks[parent] |= CHILDREN_CHANGED;
                        }
                        // A resumed root forces placement of its restored
                        // descendants as a unit.
                        if mark_placement && (!restore || row == root) {
                            self.mark_visibility_change(source, row, !params.disabled);
                        }
                    }
                    if let Some(child) = node.first() {
                        row = child;
                        continue;
                    }
                }
                // Backtrack only inside this edited subtree; other roots
                // in the batch can overlap it.
                while row != root && self.nodes[row].and_then(Node::next).is_none() {
                    row = self.nodes[row].and_then(Node::parent).unwrap_or(root);
                }
                if row == root {
                    break;
                }
                let Some(sibling) = self.nodes[row].and_then(Node::next) else {
                    break;
                };
                row = sibling;
            }
        }
        self.parked_visibility = park;
        let child_flags = NodeFlags::FLEX_CHILD_X | NodeFlags::FLEX_CHILD_Y | NodeFlags::GRID_SPANS;
        for row in 0..self.visibility_marks.len() {
            if self.visibility_marks[row] & CHILDREN_CHANGED == 0 || self.params[row].disabled {
                continue;
            }
            let params = &self.params[row];
            let stack_axis = match params.children_layout {
                ChildrenLayout::Stack { axis, .. } => Some(axis),
                _ => None,
            };
            if !matches!(params.children_layout, ChildrenLayout::Free)
                || placement::has_intrinsic_declaration(params)
            {
                self.mark_node(row);
            }
            let first = self.nodes[row].and_then(Node::first);
            let data = &mut self.records[row];
            let old_count = data.n_placed_children;
            data.n_placed_children = 0;
            data.flags.0 &= !child_flags;
            let mut child = first;
            while let Some(node) = child {
                crate::prepare_frame::summarize_child(
                    &self.params[node],
                    &mut data.n_placed_children,
                    &mut data.flags.0,
                );
                child = self.nodes[node].and_then(Node::next);
            }
            if data.n_placed_children != old_count
                && let Some(axis) = stack_axis
            {
                // Stack fractions also read the gap count directly, even
                // when both parent Final sizes remain the same.
                let mut child = first;
                while let Some(node) = child {
                    let params = &self.params[node];
                    if !params.disabled
                        && !params.free_placement
                        && [
                            Some(params.size[axis]),
                            params.min_size[axis],
                            params.max_size[axis],
                        ]
                        .into_iter()
                        .any(|size| matches!(size, Some(Size::Frac(_))))
                    {
                        self.mark_node(node);
                    }
                    child = self.nodes[node].and_then(Node::next);
                }
            }
        }
    }

    fn capture<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        scratch: &mut CaptureScratch,
    ) -> Result<(), BatchLayoutError> {
        let host = Host::new(
            source,
            &self.nodes,
            &self.params,
            &mut self.records,
            &mut self.data,
            self.root,
        );
        let tasks = &mut scratch.tasks;
        let pending = &mut scratch.pending;
        let edges = &mut scratch.edges;
        let vertices = self.ready.len();
        refill(tasks, vertices, None)?;
        self.graph.base.begin(vertices)?;
        let base = &mut self.graph.base;
        pending.clear();
        edges.clear();
        for &node in &self.visible {
            enqueue(
                tasks,
                pending,
                sizing_requests::target(node, false, Kind::Final),
            )?;
            enqueue(
                tasks,
                pending,
                sizing_requests::target(node, true, Kind::Final),
            )?;
            match host.node_layout_params(node).children_layout {
                ChildrenLayout::Block => {
                    enqueue(
                        tasks,
                        pending,
                        sizing_requests::target(node, true, Kind::Flow),
                    )?;
                }
                ChildrenLayout::Wrap { axis, .. } => {
                    enqueue(
                        tasks,
                        pending,
                        sizing_requests::target(node, axis == Axis::Y, Kind::EvenShare),
                    )?;
                }
                _ => {}
            }
        }
        let mut cursor = 0;
        while let Some(&reader) = pending.get(cursor) {
            cursor += 1;
            let slot = tasks[reader].ok_or(BatchLayoutError::InvalidGraph)?;
            let task = slot.request(reader);
            if host
                .node_layout_data(task.node)
                .flags
                .check_state(task.axis(), task.kind)
                == SOLVED
            {
                self.ready[reader] = true;
                continue;
            }
            let captured = sizing_requests::request_inputs(
                CaptureRequests {
                    host: &host,
                    tasks,
                    pending,
                    base,
                    edges,
                    reader,
                    result: Ok(()),
                },
                task,
            );
            captured.result?;
        }
        Ok(())
    }

    fn prepare_execution(&mut self, vertices: usize, slots: usize) -> Result<(), BatchLayoutError> {
        self.execution.clear();
        self.execution.try_reserve_exact(slots)?;
        self.execution_ranks.clear();
        self.execution_ranks.try_reserve_exact(vertices)?;
        self.execution_ranks.resize(vertices, usize::MAX);
        let words = slots.div_ceil(DIRTY_WORD_BITS);
        self.dirty.clear();
        self.dirty.try_reserve_exact(words)?;
        self.dirty.resize(words, 0);
        Ok(())
    }

    fn install_execution(
        &mut self,
        order: impl Iterator<Item = usize>,
        tasks: &[Option<CaptureTask>],
    ) {
        // Capture reserves an execution row for each live task before repair.
        // Retired slots retain their positions and have no execution rank.
        for vertex in order {
            if let Some(CaptureTask { kind, vertical }) = tasks[vertex] {
                self.execution_ranks[vertex] = self.execution.len();
                let slot = self.scheduled_slot(vertex, vertical, kind);
                self.execution.push(slot);
            }
        }
        // A rebuild evaluates the installed ordinary order. Compile a
        // warm-only sweep when the retained graph first needs one.
        self.warm_needs_compile = !self.has_block;
        if self.has_block {
            self.warm_execution = None;
        }
        self.wrap_leaves = None;
        self.prepare_block_plan();
    }

    fn scheduled_slot(&self, vertex: usize, vertical: bool, kind: Kind) -> ScheduledSlot {
        let prepared = self.ready[vertex];
        let (direct, parent) = if prepared {
            (DirectSize::Generic, 0)
        } else {
            let node = vertex / N_SLOTS;
            let axis = if vertical { Axis::Y } else { Axis::X };
            direct_size(&self.nodes, &self.params, &self.records, node, axis, kind)
        };
        ScheduledSlot {
            vertex,
            kind,
            vertical,
            prepared,
            direct,
            parent,
        }
    }

    fn mark_node(&mut self, node: usize) {
        let first = node * N_SLOTS;
        for &rank in &self.execution_ranks[first..first + N_SLOTS] {
            mark_dirty(&mut self.dirty, rank);
        }
    }

    fn seed_edits<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        viewport: Xy<bool>,
        content: &[NodeKey],
        edits: &[(NodeKey, NodeChange)],
        mark_placement: bool,
    ) {
        let mut host = Host::new(
            source,
            &self.nodes,
            &self.params,
            &mut self.records,
            &mut self.data,
            self.root,
        );
        let mut inbox = DirtySlots {
            host: &host,
            dirty: &mut self.dirty,
            ranks: &self.execution_ranks,
        };
        for axis in [Axis::X, Axis::Y] {
            if viewport[axis] {
                readers::declarations(&mut inbox, self.root, axis, readers::Filter::Flexible);
            }
        }
        for key in content {
            if let Some(&node) = self.indices.get(key)
                && !self.params[node].disabled
            {
                readers::content_edited(&mut inbox, node);
            }
        }
        for &(key, change) in edits {
            let Some(&node) = self.indices.get(&key) else {
                continue;
            };
            let params = *host.node_layout_params(node);
            if params.disabled {
                continue;
            }
            if mark_placement {
                host.mark_sized_output(node, true);
            }
            if change.declared != 0 {
                let width_grid = host.width_grid_main_axis(node);
                let data = host.node_layout_data_mut(node);
                let block_item = data.flags.is_block_item();
                crate::prepare_nodes::seed_pixels::<RustFloat>(
                    data, &params, block_item, width_grid,
                );
                // A prepared Final has no incoming edge from its Regular.
                // Seed both constants so each can reach its own readers.
                let start = node * N_SLOTS;
                for vertex in start..start + N_SLOTS {
                    if self.ready[vertex] {
                        mark_dirty(&mut self.dirty, self.execution_ranks[vertex]);
                    }
                }
            }
            tape_plan::dispatch_declaration(
                &mut DirtySlots {
                    host: &host,
                    dirty: &mut self.dirty,
                    ranks: &self.execution_ranks,
                },
                node,
                change,
                true,
            );
        }
    }

    fn evaluate<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        rebuilt: bool,
        all_dirty: bool,
        mark_placement: bool,
    ) -> usize {
        let skip_hidden = self.covers_visibility && self.active_nodes != self.indices.len();
        let warm_sweep = all_dirty
            && !rebuilt
            && !mark_placement
            && !skip_hidden
            && self.tail.is_none()
            && !self.has_block;
        if warm_sweep {
            if self.warm_needs_compile {
                self.warm_needs_compile = false;
                self.compile_warm_execution();
                self.wrap_leaves = wrap_leaves::Program::compile(self);
                if let Some(program) = &self.wrap_leaves {
                    program.reserve_packed(&mut self.data);
                }
            }
            if self.warm_execution.is_some() {
                self.prepare_stack_fit();
            }
        }
        let mut host = Host::new(
            source,
            &self.nodes,
            &self.params,
            &mut self.records,
            &mut self.data,
            self.root,
        );
        host.text_widths = Some((&mut self.text_widths, &mut self.cached_text_widths));
        host.prepare_wrap_output = all_dirty && self.ready_wrap_placement;
        if host.prepare_wrap_output && !host.data.packed_stack_leaves.groups.is_empty() {
            host.data
                .packed_stack_leaves
                .clear::<crate::vec_memory::RustVec>();
        }
        if rebuilt {
            for &node in &self.count_grids {
                if host.node_layout_params(node).disabled {
                    continue;
                }
                if let ChildrenLayout::Grid {
                    columns: MainAxisCellSize::Count(columns),
                    main_axis,
                    backfill,
                    ..
                } = host.node_layout_params(node).children_layout
                {
                    let count = columns.max(1);
                    host.assign_grid_cells(node, count as usize, count as f32, main_axis, backfill);
                }
            }
        }
        let ordinary_placement = self.initial_tail_from.take().unwrap_or(usize::MAX);
        // A grid's Final and assigned tracks precede its dependent Fill
        // producers. Share the track division for siblings in this sweep.
        let mut grid_tracks = Xy::new(None, None);
        if warm_sweep && let Some(warm) = &self.warm_execution {
            self.stack_shares
                .compile(&self.execution, &self.nodes, &self.params, host.records);
            let wraps = self
                .wrap_leaves
                .as_ref()
                .filter(|_| host.prepare_wrap_output);
            let execution = wraps.map_or(warm.as_slice(), |program| program.slots.as_slice());
            self.warm_runs.compile(execution, &self.params);
            warm::execute(
                &mut host,
                execution,
                &self.stack_shares,
                &mut grid_tracks,
                &self.stack_fit,
                &self.warm_runs,
                wraps,
            );
            return warm.len();
        }
        let mut finish = |host: &mut Host<'_, A>, slot: ScheduledSlot| {
            let node = slot.vertex / N_SLOTS;
            if skip_hidden && host.node_layout_params(node).disabled {
                return (0, false);
            }
            if slot.prepared {
                return (0, true);
            }
            let kind = slot.kind;
            let axis = if slot.vertical { Axis::Y } else { Axis::X };
            let previous = (!all_dirty).then(|| host.get_solved_value(node, axis, kind).to_bits());
            let direct = slot.direct;
            let parent = slot.parent as usize;
            let fill = host.direct_fill(direct, node, parent, axis, &mut grid_tracks[axis]);
            if let Some(value) = fill {
                host.records[node].publish_slot(slot.vertex % N_SLOTS, value);
                return (1, previous.is_none_or(|bits| bits != value.to_bits()));
            }
            let block_flow =
                kind == Kind::Flow && host.node_layout_data(node).flags.is_block_container();
            let wrap_share = kind == Kind::EvenShare
                && matches!(
                    host.node_layout_params(node).children_layout,
                    ChildrenLayout::Wrap { .. }
                );
            if matches!(direct, DirectSize::Final | DirectSize::IntrinsicFinal)
                && host.records[node].try_finish_unbounded_final::<RustFloat>(
                    axis,
                    matches!(direct, DirectSize::IntrinsicFinal),
                )
            {
                let value = host.records[node].values[slot.vertex % N_SLOTS];
                let changed = previous.is_none_or(|bits| bits != value.to_bits());
                let refresh_count_grid = rebuilt
                    && !all_dirty
                    && matches!(
                        host.node_layout_params(node).children_layout,
                        ChildrenLayout::Grid {
                            columns: MainAxisCellSize::Count(_),
                            ..
                        },
                    );
                if mark_placement {
                    if changed {
                        host.mark_final_output(node, axis);
                    } else if refresh_count_grid {
                        host.mark_sized_output(node, false);
                    }
                }
                return (1, changed || refresh_count_grid);
            }
            let mut margins_changed = false;
            if block_flow {
                margins_changed = host.finish_block_flow(node, rebuilt, !all_dirty);
            } else {
                host.node_layout_data_mut(node)
                    .flags
                    .set_state(axis, kind, UNSOLVED);
                if wrap_share {
                    host.reset_wrap_output(node);
                }
                if rebuilt {
                    host.finish_slot(Slot { node, axis, kind });
                } else {
                    host.finish_numeric_slot(sizing_requests::target(node, slot.vertical, kind));
                }
                host.finish_wrap_output(node, axis, kind);
            }
            // Grid assignments and flow summaries are separate outputs of
            // their producers. Always notify readers of those slots.
            let changed_word = previous
                .is_none_or(|bits| bits != host.get_solved_value(node, axis, kind).to_bits());
            let final_changed = kind == Kind::Final && changed_word;
            let wrote_placement = wrap_share
                || margins_changed
                || (kind == Kind::Flow && !block_flow)
                || (kind == Kind::Final
                    && (host.width_grid_main_axis(node) == Some(axis)
                        || (rebuilt
                            && !all_dirty
                            && matches!(
                                host.node_layout_params(node).children_layout,
                                ChildrenLayout::Grid {
                                    columns: MainAxisCellSize::Count(_),
                                    ..
                                }
                            ))));
            if mark_placement && node < ordinary_placement {
                if final_changed {
                    host.mark_final_output(node, axis);
                } else if wrote_placement {
                    host.mark_sized_output(node, margins_changed);
                }
            }
            (1, changed_word || wrote_placement)
        };
        if all_dirty {
            return self
                .execution
                .iter()
                .copied()
                .map(|slot| finish(&mut host, slot).0)
                .sum();
        }

        // Readers are always later in the schedule, even in the same word.
        // Taking the lowest bit visits only scheduled producers reached by edits.
        let mut computed = 0;
        for word in 0..self.dirty.len() {
            while self.dirty[word] != 0 {
                let bits = self.dirty[word];
                let bit = bits.trailing_zeros() as usize;
                self.dirty[word] = bits & (bits - 1);
                let slot = self.execution[word * DIRTY_WORD_BITS + bit];
                let (ran, changed) = finish(&mut host, slot);
                let restored = ran != 0
                    && self.grid_memo.boundary == Some(slot.vertex)
                    && !host.data.sizing_warned
                    && self
                        .grid_memo
                        .restore(&mut host, &mut self.dirty, mark_placement);
                if changed && !restored {
                    for &reader in self.graph.successors(slot.vertex) {
                        mark_dirty(&mut self.dirty, self.execution_ranks[reader]);
                    }
                }
                computed += ran;
            }
        }
        self.grid_memo.save(&host);
        computed
    }

    fn place<A: TreeAdapter<NodeId = NodeKey>>(&mut self, source: &mut A, prepared_wrap: bool) {
        if self.place_full_plan(source) || self.place_start_stacks(source, false) {
            return;
        }
        self.place_general::<_, false>(source, prepared_wrap);
    }

    fn place_general<A: TreeAdapter<NodeId = NodeKey>, const PARTIAL: bool>(
        &mut self,
        source: &mut A,
        prepared_wrap: bool,
    ) {
        let output = self
            .grid_memo
            .prepare_output(self.data.window_size, self.data.pixel_scale);
        let mut host = Host::new(
            source,
            &self.nodes,
            &self.params,
            &mut self.records,
            &mut self.data,
            self.root,
        );
        if output.is_none() {
            host.without_grid_output()
                .place_nodes_with::<PARTIAL>(prepared_wrap);
            return;
        }
        host.grid_output = output;
        host.place_nodes_with::<PARTIAL>(prepared_wrap);
        if let Some(output) = host.grid_output.take() {
            output.finish();
        }
    }
}

fn direct_size(
    nodes: &[Option<Node>],
    params: &[LayoutParams],
    records: &[NodeLayoutData],
    node: usize,
    axis: Axis,
    kind: Kind,
) -> (DirectSize, u32) {
    let style = &params[node];
    if kind == Kind::Final {
        return (
            match sizing_finish::unbounded_final_input(style, axis) {
                Some(false) => DirectSize::Final,
                Some(true) => DirectSize::IntrinsicFinal,
                None => DirectSize::Generic,
            },
            0,
        );
    }
    if kind != Kind::Regular
        || !matches!(style.size[axis], Size::Fill)
        || records[node].flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0
    {
        return (DirectSize::Generic, 0);
    }
    let Some(parent) = nodes[node].and_then(Node::parent) else {
        return (DirectSize::ViewportFill, 0);
    };
    let direct = match params[parent].children_layout {
        ChildrenLayout::Stack { axis: main, .. } if main == axis && !style.free_placement => {
            DirectSize::StackFill
        }
        ChildrenLayout::Wrap { axis: main, .. } if !style.free_placement => {
            if main == axis {
                DirectSize::WrapMainFill
            } else {
                DirectSize::WrapCrossFill
            }
        }
        ChildrenLayout::Free => DirectSize::ParentFill,
        ChildrenLayout::Grid { .. } if style.free_placement => DirectSize::ParentFill,
        ChildrenLayout::Grid { .. } => DirectSize::GridFill,
        ChildrenLayout::Stack { .. } => {
            if style.free_placement {
                DirectSize::ParentFill
            } else {
                DirectSize::ParentFillMargins
            }
        }
        _ => DirectSize::Generic,
    };
    match u32::try_from(parent) {
        Ok(parent) => (direct, parent),
        Err(_) => (DirectSize::Generic, 0),
    }
}

fn breadth_first<A: TreeAdapter<NodeId = NodeKey>>(
    source: &A,
    population: usize,
    keys: &mut Vec<WalkNode>,
) -> Result<(), BatchLayoutError> {
    keys.clear();
    keys.try_reserve_exact(population)?;
    let root = source.root();
    if population == 0 || source.parent(root).is_some() {
        return Err(BatchLayoutError::InvalidGraph);
    }
    keys.push(WalkNode {
        key: root,
        parent: NO_ROW,
        first: NO_ROW,
        next: NO_ROW,
        dense: NO_ROW,
    });
    let mut cursor = 0;
    while let Some(row) = keys.get(cursor) {
        let parent = row.key;
        let first = keys.len();
        let mut child = source.first_child(parent);
        while let Some(key) = child {
            if keys.len() >= population || source.parent(key) != Some(parent) {
                return Err(BatchLayoutError::InvalidGraph);
            }
            child = source.next_sibling(key);
            keys.push(WalkNode {
                key,
                parent: cursor,
                first: NO_ROW,
                next: child.map_or(NO_ROW, |_| keys.len() + 1),
                dense: NO_ROW,
            });
        }
        if keys.len() != first {
            keys[cursor].first = first;
        }
        cursor += 1;
    }
    if keys.len() != population {
        return Err(BatchLayoutError::InvalidGraph);
    }
    Ok(())
}

fn enqueue(
    tasks: &mut [Option<CaptureTask>],
    pending: &mut Vec<usize>,
    task: Request<usize>,
) -> Result<usize, BatchLayoutError> {
    let vertex = task
        .node
        .checked_mul(N_SLOTS)
        .and_then(|base| base.checked_add(slot_index(task.axis(), task.kind)))
        .ok_or(BatchLayoutError::InvalidGraph)?;
    let queued = CaptureTask {
        kind: task.kind,
        vertical: task.vertical,
    };
    let entry = tasks
        .get_mut(vertex)
        .ok_or(BatchLayoutError::InvalidGraph)?;
    match entry {
        Some(existing) if *existing != queued => {
            return Err(BatchLayoutError::InvalidGraph);
        }
        Some(_) => {}
        None => {
            push(pending, vertex)?;
            *entry = Some(queued);
        }
    }
    Ok(vertex)
}

fn refill<T: Clone>(result: &mut Vec<T>, len: usize, value: T) -> Result<(), BatchLayoutError> {
    result.clear();
    result.try_reserve_exact(len)?;
    result.resize(len, value);
    Ok(())
}

fn reserve_rows<T: Clone>(
    result: &mut Vec<T>,
    len: usize,
    empty: T,
    first_capture: bool,
) -> Result<(), BatchLayoutError> {
    if first_capture {
        result.clear();
        result.try_reserve_exact(len)?;
        Ok(())
    } else {
        refill(result, len, empty)
    }
}

fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), BatchLayoutError> {
    values.try_reserve(1)?;
    values.push(value);
    Ok(())
}

struct Requests<'a, A> {
    host: &'a A,
    inputs: &'a mut Vec<Request<usize>>,
    failed: bool,
}

struct CaptureRequests<'a, A> {
    host: &'a A,
    tasks: &'a mut [Option<CaptureTask>],
    pending: &'a mut Vec<usize>,
    base: &'a mut BaseRows,
    edges: &'a mut Vec<(usize, usize)>,
    reader: usize,
    result: Result<(), BatchLayoutError>,
}

impl<A: Solve<NodeId = usize>> RequestModel for CaptureRequests<'_, A> {
    type Id = usize;
    type Source = A;
}

impl<A: Solve<NodeId = usize>> RequestAccess for CaptureRequests<'_, A> {
    fn source(&self) -> &A {
        self.host
    }

    fn emit(&mut self, request: Request<usize>) {
        if self.result.is_err() {
            return;
        }
        self.result = (|| {
            if self.host.node_layout_params(request.node).disabled {
                return Err(BatchLayoutError::InvalidGraph);
            }
            let producer = enqueue(self.tasks, self.pending, request)?;
            push(self.edges, (producer, self.reader))?;
            self.base.count_edge(producer, self.edges)?;
            Ok(())
        })();
    }
}

struct DirtySlots<'a, A> {
    host: &'a A,
    dirty: &'a mut [u64],
    ranks: &'a [usize],
}

const DIRTY_WORD_BITS: usize = u64::BITS as usize;

#[inline]
fn mark_dirty(dirty: &mut [u64], rank: usize) {
    if rank != usize::MAX {
        dirty[rank / DIRTY_WORD_BITS] |= 1 << (rank % DIRTY_WORD_BITS);
    }
}

impl<A: Solve<NodeId = usize>> readers::Model for DirtySlots<'_, A> {
    type Id = usize;
}

impl<A: Solve<NodeId = usize>> readers::Access for DirtySlots<'_, A> {
    fn parameters(&self, node: usize) -> &LayoutParams {
        self.host.node_layout_params(node)
    }
    fn read_declaration(&self, node: usize, axis: Axis, kind: Kind) -> Option<Size> {
        self.host.read_size(node, axis, kind)
    }
    fn parent_id(&self, node: usize) -> Option<usize> {
        self.host.parent(node)
    }
    fn first_id(&self, node: usize) -> Option<usize> {
        self.host.first_child(node)
    }
    fn following_id(&self, node: usize) -> Option<usize> {
        self.host.next_sibling(node)
    }
    fn enqueue(&mut self, node: usize, axis: Axis, kind: Kind) {
        mark_dirty(
            self.dirty,
            self.ranks[node * N_SLOTS + slot_index(axis, kind)],
        );
    }
}

impl<A: sizing_requests::RequestSource<Id = usize>> RequestModel for Requests<'_, A> {
    type Id = usize;
    type Source = A;
}

impl<A: sizing_requests::RequestSource<Id = usize>> RequestAccess for Requests<'_, A> {
    fn source(&self) -> &A {
        self.host
    }

    fn emit(&mut self, request: Request<usize>) {
        if !self.failed {
            self.failed = push(self.inputs, request).is_err();
        }
    }
}

struct Host<'a, A, const GRID_OUTPUT: bool = true> {
    source: &'a mut A,
    nodes: &'a [Option<Node>],
    params: &'a [LayoutParams],
    records: &'a mut [NodeLayoutData],
    data: &'a mut LayoutData<usize>,
    root: usize,
    text_widths: Option<(&'a mut [Option<u32>], &'a mut bool)>,
    grid_output: Option<grid_memo::GridOutput<'a>>,
    prepare_wrap_output: bool,
}

struct GridFillTrack {
    parent: usize,
    track: sizing_finish::GridTrack,
    unit_extent: f32,
}

impl<'a, A> Host<'a, A> {
    fn new(
        source: &'a mut A,
        nodes: &'a [Option<Node>],
        params: &'a [LayoutParams],
        records: &'a mut [NodeLayoutData],
        data: &'a mut LayoutData<usize>,
        root: usize,
    ) -> Self {
        Self {
            source,
            nodes,
            params,
            records,
            data,
            root,
            text_widths: None,
            grid_output: None,
            prepare_wrap_output: false,
        }
    }

    fn without_grid_output(self) -> Host<'a, A, false> {
        Host {
            source: self.source,
            nodes: self.nodes,
            params: self.params,
            records: self.records,
            data: self.data,
            root: self.root,
            text_widths: self.text_widths,
            grid_output: None,
            prepare_wrap_output: self.prepare_wrap_output,
        }
    }
}

impl<A, const GRID_OUTPUT: bool> Host<'_, A, GRID_OUTPUT> {
    #[inline(always)]
    fn node(&self, id: usize) -> Option<Node> {
        self.nodes.get(id).copied().flatten()
    }

    #[inline(always)]
    fn direct_fill(
        &self,
        direct: DirectSize,
        node: usize,
        parent: usize,
        axis: Axis,
        grid_track: &mut Option<GridFillTrack>,
    ) -> Option<f32> {
        match direct {
            DirectSize::ViewportFill => Some(self.data.window_size[axis]),
            DirectSize::ParentFill => Some(self.parent_inner(parent, axis)),
            DirectSize::ParentFillMargins => Some(sizing_finish::inside_margins::<RustFloat>(
                self.parent_inner(parent, axis),
                crate::flow::margins(&self.params[node], axis),
            )),
            DirectSize::StackFill => Some(
                self.records[parent].values[slot_index(axis, Kind::EvenShare)]
                    * self.params[node].fill_weight,
            ),
            DirectSize::WrapMainFill => {
                let record = &self.records[parent];
                let share = if record.flags.0 & NodeFlags::WRAP_CONTAINER == 0 {
                    record.values[slot_index(axis, Kind::EvenShare)]
                } else {
                    self.wrap_value(
                        node,
                        parent,
                        axis,
                        Kind::EvenShare,
                        crate::flow::wrap_metrics::Metric::Share,
                    )
                };
                Some(share * self.params[node].fill_weight)
            }
            DirectSize::WrapCrossFill => {
                let extent = self.wrap_value(
                    node,
                    parent,
                    axis,
                    Kind::Flow,
                    crate::flow::wrap_metrics::Metric::Cross,
                );
                Some(sizing_finish::inside_margins::<RustFloat>(
                    extent,
                    crate::flow::margins(&self.params[node], axis),
                ))
            }
            DirectSize::GridFill => self.grid_fill(node, parent, axis, grid_track),
            _ => None,
        }
    }

    #[inline(always)]
    fn wrap_value(
        &self,
        child: usize,
        parent: usize,
        axis: Axis,
        producer: Kind,
        metric: crate::flow::wrap_metrics::Metric,
    ) -> f32 {
        if self.records[parent].flags.check_state(axis, producer) == SOLVED {
            f32::from_bits(crate::flow::wrap_metrics::read_metric(
                &self.records[child].parent_flow,
                metric,
            ))
        } else {
            0.0
        }
    }

    #[inline(always)]
    fn parent_inner(&self, parent: usize, axis: Axis) -> f32 {
        let size = self.records[parent].values[slot_index(axis, Kind::Final)];
        let padding = sizing_finish::padding(&self.params[parent], axis);
        sizing_finish::inner::<RustFloat>(size, padding)
    }

    #[inline]
    fn grid_fill(
        &self,
        node: usize,
        parent: usize,
        axis: Axis,
        cached: &mut Option<GridFillTrack>,
    ) -> Option<f32> {
        if cached.as_ref().is_none_or(|entry| entry.parent != parent) {
            let params = &self.params[parent];
            let ChildrenLayout::Grid {
                spacing_x,
                spacing_y,
                ..
            } = params.children_layout
            else {
                return None;
            };
            let record = &self.records[parent];
            let size = record.values[slot_index(axis, Kind::Final)];
            let inner =
                sizing_finish::inner::<RustFloat>(size, sizing_finish::padding(params, axis));
            let spacing = if axis == Axis::X {
                spacing_x
            } else {
                spacing_y
            };
            let track = sizing_finish::GridTrack::new::<RustFloat>(
                inner,
                record.grid_lines()[axis],
                spacing,
            );
            let unit_extent = track.extent::<RustFloat>(1);
            *cached = Some(GridFillTrack {
                parent,
                track,
                unit_extent,
            });
        }
        let entry = cached.as_ref()?;
        let style = &self.params[node];
        let span = style.grid_span[axis];
        let extent = if span <= 1 {
            entry.unit_extent
        } else {
            entry.track.extent::<RustFloat>(span)
        };
        Some(sizing_finish::inside_margins::<RustFloat>(
            extent,
            crate::flow::margins(style, axis),
        ))
    }
}

const ABSENT: LayoutParams = LayoutParams {
    disabled: true,
    ..LayoutParams::DEFAULT
};

impl<A: TreeAdapter<NodeId = NodeKey>, const GRID_OUTPUT: bool> TreeAdapter
    for Host<'_, A, GRID_OUTPUT>
{
    type NodeId = usize;

    #[inline(always)]
    fn root(&self) -> usize {
        self.root
    }
    #[inline(always)]
    fn parent(&self, id: usize) -> Option<usize> {
        self.node(id)?.parent()
    }
    #[inline(always)]
    fn first_child(&self, id: usize) -> Option<usize> {
        if GRID_OUTPUT
            && self
                .grid_output
                .as_ref()
                .is_some_and(|output| output.parent == id && output.replayed)
        {
            return None;
        }
        self.node(id)?.first()
    }
    #[inline(always)]
    fn next_sibling(&self, id: usize) -> Option<usize> {
        self.node(id)?.next()
    }
    #[inline(always)]
    fn node_layout_params(&self, id: usize) -> &LayoutParams {
        self.params.get(id).unwrap_or(&ABSENT)
    }
    #[inline(always)]
    fn node_layout_data(&self, id: usize) -> &NodeLayoutData {
        &self.records[id]
    }
    #[inline(always)]
    fn node_layout_data_mut(&mut self, id: usize) -> &mut NodeLayoutData {
        &mut self.records[id]
    }
    #[inline(always)]
    fn layout_data(&mut self) -> &mut LayoutData<usize> {
        self.data
    }
    fn measure_text_width(&mut self, id: usize) -> f32 {
        let Some(node) = self.node(id) else {
            return 0.0;
        };
        if let Some((widths, cached)) = &mut self.text_widths {
            let bits = widths[id]
                .get_or_insert_with(|| self.source.measure_text_width(node.key).to_bits());
            **cached = true;
            return f32::from_bits(*bits);
        }
        self.source.measure_text_width(node.key)
    }
    fn measure_text_height(&mut self, id: usize, width: Option<f32>) -> f32 {
        self.node(id)
            .map_or(0.0, |node| self.source.measure_text_height(node.key, width))
    }
    fn measure_content(&mut self, id: usize, input: ContentMeasureInput) -> Xy<f32> {
        self.node(id).map_or(Xy::new_symm(0.0), |node| {
            self.source.measure_content(node.key, input)
        })
    }
    #[inline(always)]
    fn write_output_rect(&mut self, id: usize, absolute: XyRect, local: XyRect) {
        if let Some(node) = self.node(id) {
            self.source.write_output_rect(node.key, absolute, local);
            if GRID_OUTPUT && let Some(output) = &mut self.grid_output {
                output.write(self.source, id, node.key, absolute, local);
            }
        }
    }
    fn layout_warning(&mut self, warning: LayoutWarning<usize>) {
        let root = self.source.root();
        let warning = warning.map_node(|id| self.node(id).map_or(root, |node| node.key));
        self.source.layout_warning(warning);
    }
}
