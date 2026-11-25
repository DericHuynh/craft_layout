use super::{BatchLayoutError, DIRTY_WORD_BITS, Frame, Host, Node, NodeKey};
use crate::incremental::{accepts_block_declarations, resolve_block_width};
use crate::placement_geometry::RustFloat;
use crate::solve::sizing_finish::{bounded_axis, intrinsic_extent, padding_for};
use crate::solve::sizing_requests;
use crate::solve::{Kind, N_SLOTS, NodeFlags, Slot, Solve, slot_index};
use crate::{
    Axis, BlockMargins, ChildrenLayout, ContentMeasure, LayoutWarning, Size, TextContent,
    TreeAdapter,
};

impl Frame {
    pub(super) fn prepare_block_margins(&mut self) -> Result<(), BatchLayoutError> {
        if self.has_block {
            // The canonical Flow producer appends at most one summary. Move
            // that summary into its owner's permanent entry after the call.
            let count = self.records.len();
            let capacity = count.checked_add(1).ok_or(BatchLayoutError::Capacity)?;
            let margins = &mut self.data.block_margins;
            margins.clear();
            margins.try_reserve_exact(capacity)?;
            margins.resize(count, BlockMargins::default());
        }
        Ok(())
    }
}

impl<A: TreeAdapter<NodeId = NodeKey>> Host<'_, A> {
    pub(super) fn finish_block_flow(&mut self, node: usize, rebuilt: bool, compare: bool) -> bool {
        let index = self.records[node].block_margin_index::<RustFloat>();
        let before = if compare {
            index.map(|index| self.data.block_margins[index])
        } else {
            None
        };
        if index.is_some() {
            self.records[node].set_block_margin_index::<RustFloat>(None);
        }
        if rebuilt {
            self.finish_slot(Slot {
                node,
                axis: Axis::Y,
                kind: Kind::Flow,
            });
        } else {
            self.finish_numeric_slot(sizing_requests::target(node, true, Kind::Flow));
        }
        let margins = &mut self.data.block_margins;
        let after = if margins.len() > self.records.len() {
            let summary = margins.pop();
            if let Some(summary) = summary {
                margins[node] = summary;
                self.records[node].set_block_margin_index::<RustFloat>(Some(node));
            }
            summary
        } else {
            None
        };
        compare && before.map(margin_bits) != after.map(margin_bits)
    }
}

fn margin_bits(summary: BlockMargins) -> ([u32; 4], bool) {
    (
        [
            summary.before.positive,
            summary.before.negative,
            summary.after.positive,
            summary.after.negative,
        ]
        .map(f32::to_bits),
        summary.all_through,
    )
}

#[derive(Debug, Default)]
pub(super) struct BlockPlan {
    widths: Vec<usize>,
    heights: Vec<usize>,
    inner_widths: Vec<f32>,
    resized: Vec<bool>,
}

impl BlockPlan {
    pub(super) fn invalidate(&mut self) {
        self.widths.clear();
        self.heights.clear();
    }
}

impl Frame {
    /// Compile ordinary Block flows into parent-first widths and child-first
    /// intrinsic heights from the repaired Final slots.
    pub(super) fn prepare_block_plan(&mut self) {
        let plan = &mut self.block_plan;
        plan.invalidate();
        if !self.has_block
            || !self.records[self.root].flags.is_block_container()
            || self.visible.len() != self.nodes.iter().flatten().count()
        {
            return;
        }
        for &row in &self.visible {
            let style = &self.params[row];
            let root = row == self.root;
            let flags = self.records[row].flags;
            if flags.is_block_item() == root
                || style.free_placement
                || style.image.is_some()
                || style.content_measure != ContentMeasure::None
                || !accepts_block_declarations(style, root)
                || !padding_for::<RustFloat>(style, Axis::X).is_finite()
                || !padding_for::<RustFloat>(style, Axis::Y).is_finite()
            {
                return;
            }
            match style.children_layout {
                ChildrenLayout::Block
                    if style.text == TextContent::None
                        && if root {
                            matches!(style.size.y, Size::Fill | Size::Pixels(_))
                        } else {
                            matches!(style.size.y, Size::Auto | Size::FitContent)
                        } => {}
                ChildrenLayout::Free
                    if !root && self.nodes[row].and_then(Node::first).is_none() => {}
                _ => return,
            }
        }
        let count = self.visible.len();
        plan.inner_widths.clear();
        plan.resized.clear();
        if plan.widths.try_reserve_exact(count).is_err()
            || plan.heights.try_reserve_exact(count).is_err()
            || plan
                .inner_widths
                .try_reserve_exact(self.nodes.len())
                .is_err()
            || plan.resized.try_reserve_exact(self.nodes.len()).is_err()
        {
            return;
        }
        plan.inner_widths.resize(self.nodes.len(), 0.0);
        plan.resized.resize(self.nodes.len(), false);
        for slot in &self.execution {
            if slot.kind == Kind::Final {
                let row = slot.vertex / N_SLOTS;
                if slot.vertical {
                    plan.heights.push(row);
                } else {
                    plan.widths.push(row);
                }
            }
        }
    }

    pub(super) fn measure_block_resize<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
    ) -> Option<usize> {
        let plan = &mut self.block_plan;
        if plan.widths.is_empty() {
            return None;
        }
        let window = self.data.window_size;
        let mut host = Host::new(
            source,
            &self.nodes,
            &self.params,
            &mut self.records,
            &mut self.data,
            self.root,
        );
        let mut computed = 0;
        for &row in &plan.widths {
            let parent = self.nodes[row].and_then(Node::parent);
            let parent_width = parent.map_or(window.x, |parent| plan.inner_widths[parent]);
            let width =
                resolve_block_width::<RustFloat>(&self.params[row], parent_width, parent.is_none());
            plan.inner_widths[row] = width.available;
            let data = &mut host.records[row];
            let previous = data.values[slot_index(Axis::X, Kind::Final)];
            plan.resized[row] = previous.to_bits() != width.resolved.to_bits();
            data.publish_axis(Axis::X, width.regular, width.resolved, 0);
            if let Some(maximum) = width.maximum {
                data.publish_slot(slot_index(Axis::X, Kind::Max), maximum);
            }
            if !width.resolved.is_finite() {
                host.warn(LayoutWarning::NotFinite {
                    node: row,
                    axis: Axis::X,
                });
            }
            computed += 1;
        }

        for &row in &plan.heights {
            let style = &self.params[row];
            let is_block = host.records[row].flags.0 & NodeFlags::BLOCK_CONTAINER != 0;
            let padding = padding_for::<RustFloat>(style, Axis::Y);
            let regular = match style.size.y {
                Size::Pixels(_) => continue,
                Size::Fill => window.y,
                _ if is_block => {
                    host.finish_block_flow(row, false, false);
                    let flow = host.get_solved_value(row, Axis::Y, Kind::Flow);
                    intrinsic_extent::<RustFloat>(flow, 0.0, 0.0, padding)
                }
                _ => {
                    let vertex = row * N_SLOTS + slot_index(Axis::Y, Kind::Regular);
                    let rank = self.execution_ranks[vertex];
                    let edited = rank != usize::MAX
                        && self.dirty[rank / DIRTY_WORD_BITS] & (1 << (rank % DIRTY_WORD_BITS))
                            != 0;
                    let resized = style.text == TextContent::Wrapping && plan.resized[row];
                    if !edited && !resized {
                        continue;
                    }
                    let own = match style.text {
                        TextContent::None => 0.0,
                        TextContent::Fixed => host.measure_text_height(row, None),
                        TextContent::Wrapping => {
                            host.measure_text_height(row, Some(plan.inner_widths[row]))
                        }
                    };
                    intrinsic_extent::<RustFloat>(0.0, own, 0.0, padding)
                }
            };
            let floor = (row != self.root).then_some(padding);
            let resolved = bounded_axis::<RustFloat>(regular, None, None, floor);
            host.records[row].publish_axis(Axis::Y, regular, resolved, 0);
            if !resolved.is_finite() {
                host.warn(LayoutWarning::NotFinite {
                    node: row,
                    axis: Axis::Y,
                });
            }
            computed += 2;
        }
        host.finish_block_flow(self.root, false, false);
        Some(computed + 1)
    }
}
