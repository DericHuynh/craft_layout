use super::{Adjacency, Frame, Host, Node, NodeKey, mark_dirty};
use crate::solve::{Kind, N_SLOTS, slot_index};
use crate::{ChildrenLayout, MainAxisCellSize, NodeLayoutData, SameInput, TreeAdapter, Xy, XyRect};

const MAX_FRAMES: usize = 8;
const MAX_BYTES: usize = 768 * 1024;

type SizeKey = [u32; 3];

#[derive(Debug, Default)]
struct Snapshot {
    input: Option<SizeKey>,
    active: Vec<bool>,
    records: Vec<NodeLayoutData>,
    geometry: Geometry,
    visible: usize,
}

#[derive(Debug, Default)]
pub(super) struct GridMemo {
    pub(super) boundary: Option<usize>,
    members: Vec<bool>,
    rows: Vec<usize>,
    mask: Vec<u64>,
    readers: Vec<usize>,
    active: Vec<bool>,
    pending: Option<SizeKey>,
    frames: Vec<Snapshot>,
    next: usize,
    pub(super) output_index: Option<usize>,
}

impl Frame {
    pub(super) fn invalidate_grid_memo(&mut self, key: NodeKey) {
        if let Some(boundary) = self.grid_memo.boundary
            && let Some(&node) = self.indices.get(&key)
            && (boundary / N_SLOTS == node || self.grid_memo.members[node])
        {
            self.grid_memo.invalidate();
        }
    }

    pub(super) fn prepare_grid_memo(&mut self) {
        let mut memo = std::mem::take(&mut self.grid_memo);
        memo.clear();
        if self.has_width_grid && self.covers_visibility && !self.has_block {
            for &row in &self.visible {
                if let ChildrenLayout::Grid {
                    columns: MainAxisCellSize::Width(_),
                    main_axis,
                    ..
                } = self.params[row].children_layout
                    && memo.compile(
                        self,
                        row,
                        row * N_SLOTS + slot_index(main_axis, Kind::Final),
                    )
                {
                    break;
                }
            }
        }
        self.grid_memo = memo;
    }
}

impl GridMemo {
    pub(super) fn invalidate(&mut self) {
        for snapshot in &mut self.frames {
            snapshot.input = None;
        }
        self.next = 0;
        self.pending = None;
        self.output_index = None;
    }

    pub(super) fn clear(&mut self) {
        self.boundary = None;
        self.invalidate();
    }

    fn compile(&mut self, frame: &Frame, parent: usize, boundary: usize) -> bool {
        self.members.clear();
        self.rows.clear();
        self.mask.clear();
        self.readers.clear();
        self.active.clear();
        if self.members.try_reserve_exact(frame.records.len()).is_err()
            || self.rows.try_reserve_exact(frame.records.len()).is_err()
            || self.mask.try_reserve_exact(frame.dirty.len()).is_err()
            || self.active.try_reserve_exact(frame.records.len()).is_err()
        {
            return false;
        }
        self.members.resize(frame.records.len(), false);
        self.mask.resize(frame.dirty.len(), 0);
        // Capture visits parents before their children.
        for &row in &frame.visible {
            if let Some(ancestor) = frame.nodes[row].and_then(Node::parent)
                && (ancestor == parent || self.members[ancestor])
            {
                if matches!(
                    frame.params[row].children_layout,
                    ChildrenLayout::Block | ChildrenLayout::Wrap { .. }
                ) {
                    return false;
                }
                self.members[row] = true;
                self.rows.push(row);
            }
        }
        let bytes_per_row =
            size_of::<NodeLayoutData>() + size_of::<bool>() + size_of::<Rectangle>();
        if self.rows.is_empty() || self.rows.len() > MAX_BYTES / MAX_FRAMES / bytes_per_row {
            return false;
        }
        let boundary_rank = frame.execution_ranks[boundary];
        if boundary_rank == usize::MAX {
            return false;
        }
        for (rank, slot) in frame.execution.iter().enumerate() {
            let inside = self.members[slot.vertex / N_SLOTS];
            if inside {
                mark_dirty(&mut self.mask, rank);
            }
            for &reader in frame.graph.successors(slot.vertex) {
                let reader_inside = self.members[reader / N_SLOTS];
                if reader_inside && !inside && slot.vertex != boundary {
                    return false;
                }
                if inside && !reader_inside {
                    let target = frame.execution_ranks[reader];
                    if target <= boundary_rank || self.readers.try_reserve(1).is_err() {
                        return false;
                    }
                    self.readers.push(target);
                }
            }
        }
        self.readers.sort_unstable();
        self.readers.dedup();
        self.boundary = Some(boundary);
        true
    }

    pub(super) fn restore<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        host: &mut Host<'_, A>,
        dirty: &mut [u64],
        place: bool,
    ) -> bool {
        let Some(boundary) = self.boundary else {
            return false;
        };
        let parent = boundary / N_SLOTS;
        let record = &host.records[parent];
        let tracks = record.grid_lines();
        let key = [
            record.values[boundary % N_SLOTS].to_bits(),
            tracks.x.to_bits(),
            tracks.y.to_bits(),
        ];
        self.active.clear();
        self.active
            .extend(self.rows.iter().map(|&row| !host.params[row].disabled));
        let Some((index, snapshot)) =
            self.frames.iter().enumerate().find(|(_, snapshot)| {
                snapshot.input == Some(key) && snapshot.active == self.active
            })
        else {
            self.pending = Some(key);
            return false;
        };
        // Every external edge into this group is supplied by this producer.
        // Readers outside the group follow the boundary in the same order.
        for (&row, &record) in self.rows.iter().zip(&snapshot.records) {
            host.records[row] = record;
        }
        for (dirty, &mask) in dirty.iter_mut().zip(&self.mask) {
            *dirty &= !mask;
        }
        for &reader in &self.readers {
            mark_dirty(dirty, reader);
        }
        if place {
            host.mark_sized_output(parent, false);
        }
        self.pending = None;
        self.output_index = Some(index);
        true
    }

    pub(super) fn save<A: TreeAdapter<NodeId = NodeKey>>(&mut self, host: &Host<'_, A>) {
        let Some(key) = self.pending.take() else {
            return;
        };
        if host.data.sizing_warned {
            return;
        }
        let index = if let Some(index) = self
            .frames
            .iter()
            .position(|snapshot| snapshot.input.is_none())
        {
            index
        } else if self.frames.len() < MAX_FRAMES {
            if self.frames.try_reserve(1).is_err() {
                return;
            }
            self.frames.push(Snapshot::default());
            self.frames.len() - 1
        } else {
            let index = self.next;
            self.next = (self.next + 1) % MAX_FRAMES;
            index
        };
        let snapshot = &mut self.frames[index];
        snapshot.input = None;
        snapshot.geometry.context = None;
        snapshot.active.clear();
        snapshot.records.clear();
        if snapshot
            .active
            .try_reserve_exact(self.active.len())
            .is_err()
            || snapshot.records.try_reserve_exact(self.rows.len()).is_err()
        {
            return;
        }
        snapshot.active.extend_from_slice(&self.active);
        snapshot.records.extend(self.rows.iter().map(|&row| {
            let mut record = host.records[row];
            record.placement = crate::placement_work::PlacementWork::Clean;
            record
        }));
        snapshot.visible = self.active.iter().filter(|&&visible| visible).count();
        snapshot.input = Some(key);
        self.output_index = Some(index);
    }

    pub(super) fn prepare_output(
        &mut self,
        window: Xy<f32>,
        scale: Option<f32>,
    ) -> Option<GridOutput<'_>> {
        let index = self.output_index.take()?;
        if scale.is_some() || !window.x.is_finite() || !window.y.is_finite() {
            return None;
        }
        let parent = self.boundary? / N_SLOTS;
        let snapshot = self.frames.get_mut(index)?;
        snapshot.input?;
        let geometry = &mut snapshot.geometry;
        if geometry.rectangles.capacity() < snapshot.visible
            && geometry
                .rectangles
                .try_reserve_exact(snapshot.visible.saturating_sub(geometry.rectangles.len()))
                .is_err()
        {
            return None;
        }
        Some(GridOutput {
            parent,
            window,
            members: &self.members,
            geometry,
            expected: snapshot.visible,
            replayed: false,
            captured: false,
        })
    }
}

#[derive(Debug, Default)]
struct Geometry {
    context: Option<GeometryInput>,
    rectangles: Vec<Rectangle>,
}

#[derive(Debug)]
struct Rectangle {
    key: NodeKey,
    absolute: XyRect,
    local: XyRect,
}

#[derive(Clone, Copy, Debug)]
struct GeometryInput {
    window: Xy<f32>,
    absolute: XyRect,
    local: XyRect,
}

impl GeometryInput {
    fn same(self, other: Self) -> bool {
        self.window.same_input(&other.window)
            && self.absolute.same_input(&other.absolute)
            && self.local.same_input(&other.local)
    }
}

pub(super) struct GridOutput<'a> {
    pub(super) parent: usize,
    pub(super) replayed: bool,
    captured: bool,
    window: Xy<f32>,
    members: &'a [bool],
    geometry: &'a mut Geometry,
    expected: usize,
}

impl GridOutput<'_> {
    pub(super) fn write<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        row: usize,
        key: NodeKey,
        absolute: XyRect,
        local: XyRect,
    ) {
        if row == self.parent {
            if !finite(absolute) || !finite(local) {
                return;
            }
            let input = GeometryInput {
                window: self.window,
                absolute,
                local,
            };
            if self.geometry.context.is_some_and(|saved| saved.same(input))
                && self.geometry.rectangles.len() == self.expected
            {
                for rectangle in &self.geometry.rectangles {
                    source.write_output_rect(rectangle.key, rectangle.absolute, rectangle.local);
                }
                self.replayed = true;
            } else {
                self.geometry.context = Some(input);
                self.geometry.rectangles.clear();
                self.captured = true;
            }
        } else if self.captured && self.members.get(row) == Some(&true) {
            if self.geometry.rectangles.len() >= self.expected
                || !finite(absolute)
                || !finite(local)
            {
                self.captured = false;
                self.geometry.context = None;
                return;
            }
            self.geometry.rectangles.push(Rectangle {
                key,
                absolute,
                local,
            });
        }
    }

    pub(super) fn finish(self) {
        if self.captured && self.geometry.rectangles.len() != self.expected {
            self.geometry.context = None;
        }
    }
}

fn finite(rectangle: XyRect) -> bool {
    [rectangle.x, rectangle.y]
        .into_iter()
        .flatten()
        .all(f32::is_finite)
}
