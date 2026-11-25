use super::{Frame, NodeKey};
use crate::{LayoutParams, NodeLayoutData, SameInput, TreeAdapter, Xy, XyRect};

const MAX_FRAMES: usize = 8;
const MAX_RECORD_BYTES: usize = 512 * 1024;

pub(in crate::layout_tree) trait MemoSource:
    TreeAdapter<NodeId = NodeKey>
{
    fn batch_rectangle(&self, key: NodeKey) -> Option<XyRect>;
    fn restore_batch_rectangle(&mut self, key: NodeKey, rectangle: XyRect);
}

#[derive(Clone, Copy, Debug)]
pub(super) struct Input {
    window: Xy<f32>,
    scale: Option<f32>,
    style: Option<LayoutParams>,
}

impl Input {
    fn matches(self, other: Self) -> bool {
        self.window.same_input(&other.window)
            && self.scale.same_input(&other.scale)
            && self.style.same_input(&other.style)
    }
}

#[derive(Debug, Default)]
struct Snapshot {
    input: Option<Input>,
    records: Vec<NodeLayoutData>,
    rectangles: Vec<(NodeKey, XyRect)>,
}

#[derive(Debug, Default)]
pub(super) struct ViewportMemo {
    owner: Option<NodeKey>,
    frames: Vec<Snapshot>,
    next: usize,
}

impl ViewportMemo {
    pub(super) fn invalidate(&mut self) {
        for frame in &mut self.frames {
            frame.input = None;
        }
        self.owner = None;
        self.next = 0;
    }

    pub(super) fn edit_style(&mut self, key: NodeKey) {
        if self.owner != Some(key) {
            self.invalidate();
            self.owner = Some(key);
        }
    }

    pub(super) fn input(
        &self,
        frame: &Frame,
        window: Xy<f32>,
        scale: Option<f32>,
    ) -> Option<Input> {
        // The records for Stack, Free and Grid include all published sizing
        // words. Flow graphs also have live margin and line state.
        let bytes_per_node = size_of::<NodeLayoutData>() + size_of::<(NodeKey, XyRect)>();
        if frame.data.has_flow
            || frame.data.sizing_warned
            || frame.active_nodes != frame.indices.len()
            || frame.records.len() > MAX_RECORD_BYTES / MAX_FRAMES / bytes_per_node
        {
            return None;
        }
        // A second varying node invalidates earlier snapshots. The only
        // declaration that can differ inside this history is compared exactly.
        let style = match self.owner {
            Some(owner) => Some(frame.params[*frame.indices.get(&owner)?]),
            None => None,
        };
        Some(Input {
            window,
            scale,
            style,
        })
    }

    pub(super) fn restore<A: MemoSource>(
        &self,
        frame: &mut Frame,
        source: &mut A,
        input: Input,
    ) -> bool {
        let Some(snapshot) = self
            .frames
            .iter()
            .find(|snapshot| snapshot.input.is_some_and(|key| key.matches(input)))
        else {
            return false;
        };
        frame.records.copy_from_slice(&snapshot.records);
        for &(key, rect) in &snapshot.rectangles {
            source.restore_batch_rectangle(key, rect);
        }
        frame.data.window_size = input.window;
        frame.data.pixel_scale = input.scale;
        true
    }

    pub(super) fn save<A: MemoSource>(&mut self, frame: &Frame, source: &A, input: Input) {
        if frame.data.sizing_warned {
            return;
        }
        let index = if let Some(slot) = self
            .frames
            .iter()
            .position(|snapshot| snapshot.input.is_none())
        {
            slot
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
        snapshot.records.clear();
        snapshot.rectangles.clear();
        if snapshot
            .records
            .try_reserve_exact(frame.records.len())
            .is_err()
            || snapshot
                .rectangles
                .try_reserve_exact(frame.visible.len())
                .is_err()
        {
            return;
        }
        for &row in &frame.visible {
            let Some(node) = frame.nodes[row] else { return };
            let Some(rectangle) = source.batch_rectangle(node.key) else {
                return;
            };
            snapshot.rectangles.push((node.key, rectangle));
        }
        snapshot.records.extend_from_slice(&frame.records);
        snapshot.input = Some(input);
    }
}
