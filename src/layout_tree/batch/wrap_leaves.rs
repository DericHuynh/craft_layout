//! A forced warm sweep can compute an independent Wrap leaf roster together.

use super::{
    Axis, ChildrenLayout, DirectSize, Frame, Host, Kind, LayoutData, N_SLOTS, Node, NodeFlags,
    NodeKey, NodeLayoutData, Size, TreeAdapter, slot_index, warm::WarmSlot,
};
use crate::flow::wrap_lines;
use crate::packed_stack_leaf::{PackedStackLeaves, PreparedStackLeaf, StackLeafGroup};
use crate::placement_geometry::RustFloat;
use crate::vec_memory::RustVec;

#[derive(Debug)]
pub(super) struct Program {
    pub(super) slots: Vec<WarmSlot>,
    runs: Vec<Run>,
    leaves: Vec<Leaf>,
}

#[derive(Debug)]
struct Run {
    parent: usize,
    axis: Axis,
    spacing: f32,
    line_spacing: f32,
    start: usize,
    end: usize,
}

#[derive(Debug)]
struct Leaf {
    row: u32,
    main: f32,
    // The other inputs are nonnegative finite pixel declarations.
    cross: f32,
}

#[derive(Clone, Copy)]
enum Edit {
    Fuse(u32),
    Covered,
}

impl Program {
    pub(super) fn compile(frame: &Frame) -> Option<Self> {
        if !frame.ready_wrap_placement {
            return None;
        }
        let ordinary = frame.warm_execution.as_ref()?;
        let mut program = Self {
            slots: Vec::new(),
            runs: Vec::new(),
            leaves: Vec::new(),
        };
        let mut edits = Vec::new();
        for &parent in &frame.visible {
            let start = program.leaves.len();
            let edit_start = edits.len();
            if program.add(frame, parent, &mut edits).is_none() {
                program.leaves.truncate(start);
                edits.truncate(edit_start);
            }
        }
        if program.runs.is_empty() {
            return None;
        }
        edits.sort_unstable_by_key(|(rank, _)| *rank);
        if edits.windows(2).any(|pair| pair[0].0 == pair[1].0) {
            return None;
        }
        let suppressed = edits.len().checked_sub(program.runs.len())?;
        program
            .slots
            .try_reserve_exact(ordinary.len().checked_sub(suppressed)?)
            .ok()?;
        let mut changed = edits.into_iter().peekable();
        for &slot in ordinary {
            let vertex = slot.row as usize * N_SLOTS + slot.index as usize;
            let rank = frame.execution_ranks[vertex];
            let next = match changed
                .next_if(|(edit_rank, _)| *edit_rank == rank)
                .map(|(_, edit)| edit)
            {
                Some(Edit::Covered) => continue,
                Some(Edit::Fuse(run)) => WarmSlot {
                    parent: run,
                    op: DirectSize::WrapLeaves,
                    ..slot
                },
                None => slot,
            };
            if program.slots.len() == program.slots.capacity() {
                return None;
            }
            program.slots.push(next);
        }
        changed.next().is_none().then_some(program)
    }

    fn add(&mut self, frame: &Frame, parent: usize, edits: &mut Vec<(usize, Edit)>) -> Option<()> {
        if frame.records[parent].prepared_placement & NodeLayoutData::PREPARED_WRAP_START == 0 {
            return None;
        }
        let ChildrenLayout::Wrap {
            axis,
            spacing,
            line_spacing,
            ..
        } = frame.params[parent].children_layout
        else {
            return None;
        };
        let cross = axis.other();
        let share = operation(frame, parent, axis, Kind::EvenShare)?;
        let flow = operation(frame, parent, cross, Kind::Flow)?;
        let main_final = rank(frame, parent, axis, Kind::Final)?;
        if main_final >= share || share >= flow || frame.records[parent].n_placed_children < 16 {
            return None;
        }
        let population = frame.records[parent].n_placed_children as usize;
        self.leaves.try_reserve(population).ok()?;
        let start = self.leaves.len();
        let mut next = frame.nodes[parent].and_then(Node::first);
        while let Some(row) = next {
            let node = frame.nodes[row]?;
            let params = &frame.params[row];
            if node.first().is_some()
                || !matches!(
                    params.children_layout,
                    ChildrenLayout::Free | ChildrenLayout::Stack { .. }
                )
                || self.leaves.len() - start == population
            {
                return None;
            }
            let Size::Pixels(main) = params.size[axis] else {
                return None;
            };
            if !constant(frame, row, axis, Kind::Final, main) {
                return None;
            }
            let rise = match params.size[cross] {
                Size::Pixels(rise)
                    if constant(frame, row, cross, Kind::Regular, rise)
                        && constant(frame, row, cross, Kind::Final, rise) =>
                {
                    rise
                }
                Size::Fill => {
                    let regular = operation(frame, row, cross, Kind::Regular)?;
                    let final_rank = operation(frame, row, cross, Kind::Final)?;
                    if !(flow < regular && regular < final_rank) {
                        return None;
                    }
                    edits.try_reserve(2).ok()?;
                    edits.push((regular, Edit::Covered));
                    edits.push((final_rank, Edit::Covered));
                    -1.0
                }
                _ => return None,
            };
            self.leaves.push(Leaf {
                row: u32::try_from(row).ok()?,
                main,
                cross: rise,
            });
            next = node.next();
        }
        if self.leaves.len() - start != population {
            return None;
        }
        let run = u32::try_from(self.runs.len()).ok()?;
        self.runs.try_reserve(1).ok()?;
        edits.try_reserve(2).ok()?;
        edits.push((share, Edit::Fuse(run)));
        edits.push((flow, Edit::Covered));
        self.runs.push(Run {
            parent,
            axis,
            spacing,
            line_spacing,
            start,
            end: self.leaves.len(),
        });
        Some(())
    }

    pub(super) fn reserve_packed(&self, data: &mut LayoutData<usize>) {
        let workspace = &mut data.packed_stack_leaves;
        workspace.clear::<RustVec>();
        let _ = workspace.rows.try_reserve_exact(self.leaves.len());
        let _ = workspace.groups.try_reserve_exact(self.runs.len());
    }

    pub(super) fn run<A: TreeAdapter<NodeId = NodeKey>>(&self, host: &mut Host<'_, A>, run: usize) {
        let run = &self.runs[run];
        let leaves = &self.leaves[run.start..run.end];
        let main_slot = slot_index(run.axis, Kind::EvenShare);
        let flow_slot = slot_index(run.axis.other(), Kind::Flow);
        let limit = host.parent_inner(run.parent, run.axis);
        let workspace = &mut host.data.packed_stack_leaves;
        let first_row = workspace.rows.len();
        let pack = host.data.pixel_scale.is_none()
            && workspace.rows.capacity() - first_row >= leaves.len()
            && workspace.groups.len() < workspace.groups.capacity()
            && first_row
                .checked_add(leaves.len())
                .is_some_and(|end| end <= u32::MAX as usize);
        let mut start = 0;
        let mut width = 0.0;
        let mut cross = 0.0_f32;
        let mut total = 0.0;
        for (index, leaf) in leaves.iter().enumerate() {
            let extended = if index == start {
                leaf.main
            } else {
                wrap_lines::extend_main(width, run.spacing, leaf.main)
            };
            if index != start && wrap_lines::beyond_limit(extended, limit) {
                run.publish_line(
                    host.records,
                    workspace,
                    &leaves[start..index],
                    cross,
                    start != 0,
                    pack,
                );
                total += cross;
                total += run.line_spacing;
                start = index;
                width = leaf.main;
                cross = 0.0;
            } else {
                width = extended;
            }
            cross = cross.max(leaf.cross);
        }
        run.publish_line(
            host.records,
            workspace,
            &leaves[start..],
            cross,
            start != 0,
            pack,
        );
        total += cross;
        if pack {
            workspace.groups.push(StackLeafGroup {
                parent: run.parent,
                span: [first_row as u32, workspace.rows.len() as u32],
            });
        }
        let parent = &mut host.records[run.parent];
        parent.publish_slot(main_slot, 0.0);
        parent.publish_slot(flow_slot, total);
        parent.prepared_placement |= NodeLayoutData::PREPARED_WRAP;
    }
}

impl Run {
    fn publish_line(
        &self,
        records: &mut [NodeLayoutData],
        workspace: &mut PackedStackLeaves<usize>,
        leaves: &[Leaf],
        cross: f32,
        later_line: bool,
        pack: bool,
    ) {
        let cross_axis = self.axis.other();
        let regular = slot_index(cross_axis, Kind::Regular);
        let final_slot = slot_index(cross_axis, Kind::Final);
        for (index, leaf) in leaves.iter().enumerate() {
            let id = leaf.row as usize;
            let record = &mut records[id];
            record.flags.0 &= !NodeFlags::WRAP_LINE_START;
            if later_line && index == 0 {
                record.mark_wrap_start();
            }
            record.parent_flow = [0, cross.to_bits()];
            let rise = if leaf.cross < 0.0 {
                record.publish_slot(regular, cross);
                record.publish_slot(final_slot, cross);
                cross
            } else {
                leaf.cross
            };
            if pack {
                let horizontal = self.axis == Axis::X;
                let size = if horizontal {
                    [leaf.main, rise]
                } else {
                    [rise, leaf.main]
                };
                workspace.rows.push(PreparedStackLeaf::wrapped::<RustFloat>(
                    id,
                    size,
                    horizontal,
                    self.spacing,
                    index == 0,
                    cross,
                ));
            }
        }
    }
}

fn operation(frame: &Frame, row: usize, axis: Axis, kind: Kind) -> Option<usize> {
    let rank = rank(frame, row, axis, kind)?;
    (!frame.execution[rank].prepared).then_some(rank)
}

fn rank(frame: &Frame, row: usize, axis: Axis, kind: Kind) -> Option<usize> {
    let vertex = row * N_SLOTS + slot_index(axis, kind);
    let rank = *frame.execution_ranks.get(vertex)?;
    let slot = frame.execution.get(rank)?;
    (slot.vertex == vertex).then_some(rank)
}

fn constant(frame: &Frame, row: usize, axis: Axis, kind: Kind, value: f32) -> bool {
    let index = slot_index(axis, kind);
    frame.ready[row * N_SLOTS + index]
        && frame.records[row].values[index].to_bits() == value.to_bits()
}
