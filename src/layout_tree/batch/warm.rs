//! Preclassified execution used to recompute every nonconstant producer.

mod fill_axis;
mod flex;
mod ratio;
mod runs;
pub(super) use runs::Runs;

use super::stack_fit::StackFit;
use super::stack_shares::StackShares;
use super::wrap_leaves;
use super::{
    Axis, ChildrenLayout, DirectSize, Frame, GridFillTrack, Host, Kind, LayoutParams,
    MainAxisCellSize, N_SLOTS, Node, NodeFlags, NodeKey, ScheduledSlot, Size, TreeAdapter,
    UNSOLVED, Xy, sizing_finish, sizing_requests, slot_index,
};
use crate::placement_geometry::{FloatBounds, RustFloat};
use crate::solve::Solve;

const HAS_MIN: u32 = 1;
const HAS_MAX: u32 = 2;
const CHECK_INTRINSIC: u32 = 4;

#[derive(Debug, Clone, Copy)]
pub(super) struct WarmSlot {
    pub(super) row: u32,
    // Parent row for dependent sizing, or bound flags for BoundedFinal.
    pub(super) parent: u32,
    pub(super) index: u8,
    pub(super) kind: Kind,
    pub(super) axis: Axis,
    pub(super) op: DirectSize,
}

impl Frame {
    // Reserve a sweep for a retained graph. An allocation failure leaves
    // the ordinary ordered execution available.
    pub(super) fn compile_warm_execution(&mut self) {
        let mut warm = self.warm_execution.take().unwrap_or_default();
        warm.clear();
        if self.has_block {
            return;
        }
        let count = self.execution.iter().filter(|slot| !slot.prepared).count();
        if warm.try_reserve_exact(count).is_err() {
            return;
        }
        for slot in self.execution.iter().filter(|slot| !slot.prepared) {
            let row = match u32::try_from(slot.vertex / N_SLOTS) {
                Ok(row) => row,
                Err(_) => return,
            };
            let axis = if slot.vertical { Axis::Y } else { Axis::X };
            let (op, parent) = self.warm_op(row as usize, axis, slot.kind, slot);
            warm.push(WarmSlot {
                row,
                parent,
                index: slot_index(axis, slot.kind) as u8,
                axis,
                kind: slot.kind,
                op,
            });
        }
        self.warm_execution = Some(warm);
    }

    fn warm_op(
        &self,
        node: usize,
        axis: Axis,
        kind: Kind,
        slot: &ScheduledSlot,
    ) -> (DirectSize, u32) {
        let style = &self.params[node];
        if !matches!(slot.direct, DirectSize::Generic) {
            return (slot.direct, slot.parent);
        }
        if kind == Kind::Final
            && !matches!(style.children_layout, ChildrenLayout::Grid {
                main_axis, columns: MainAxisCellSize::Width(_), ..
            } if main_axis == axis)
        {
            // Bound presence and declaration kind are stable for the
            // lifetime of the captured graph. Their values still vary.
            let bounds = u32::from(style.min_size[axis].is_some()) * HAS_MIN
                | u32::from(style.max_size[axis].is_some()) * HAS_MAX
                | u32::from(matches!(style.size[axis], Size::FitContent)) * CHECK_INTRINSIC;
            return (DirectSize::BoundedFinal, bounds);
        }
        if kind == Kind::EvenShare && matches!(style.children_layout, ChildrenLayout::Stack { .. })
        {
            return (DirectSize::StackShare, 0);
        }
        let declaration = scalar_declaration(style, axis, kind);
        match declaration {
            Some(Size::Pixels(_)) => (DirectSize::Pixels, 0),
            Some(Size::AspectRatio(_)) => (DirectSize::Ratio, 0),
            Some(Size::Fill | Size::Frac(_)) => {
                let fill = matches!(declaration, Some(Size::Fill));
                let Some(parent) = self.nodes[node].and_then(Node::parent) else {
                    return (
                        if fill {
                            DirectSize::ViewportFill
                        } else {
                            DirectSize::ViewportFrac
                        },
                        0,
                    );
                };
                let Ok(packed_parent) = u32::try_from(parent) else {
                    return (DirectSize::Generic, 0);
                };
                let (fill_op, frac_op) = if style.free_placement {
                    (DirectSize::ParentFill, DirectSize::ParentFrac)
                } else {
                    match self.params[parent].children_layout {
                        ChildrenLayout::Free => (DirectSize::ParentFill, DirectSize::ParentFrac),
                        ChildrenLayout::Stack { axis: main, .. } if main == axis => {
                            (DirectSize::StackFill, DirectSize::StackFrac)
                        }
                        ChildrenLayout::Stack { .. } => {
                            (DirectSize::ParentFillMargins, DirectSize::ParentFrac)
                        }
                        ChildrenLayout::Grid { .. } => (DirectSize::GridFill, DirectSize::Generic),
                        _ => (DirectSize::Generic, DirectSize::Generic),
                    }
                };
                (if fill { fill_op } else { frac_op }, packed_parent)
            }
            _ => (DirectSize::Generic, 0),
        }
    }
}

fn scalar_declaration(style: &LayoutParams, axis: Axis, kind: Kind) -> Option<Size> {
    match kind {
        Kind::Regular => Some(style.size[axis]),
        Kind::Min => style.min_size[axis],
        Kind::Max => style.max_size[axis],
        _ => None,
    }
}

pub(super) fn execute<A: TreeAdapter<NodeId = NodeKey>>(
    host: &mut Host<'_, A>,
    warm: &[WarmSlot],
    shares: &StackShares,
    grid_tracks: &mut Xy<Option<GridFillTrack>>,
    stack_fit: &StackFit,
    runs: &Runs,
    wrap_leaves: Option<&wrap_leaves::Program>,
) {
    let mut start = 0;
    for group in &runs.groups {
        execute_slots(
            host,
            &warm[start..group.start],
            shares,
            grid_tracks,
            stack_fit,
            wrap_leaves,
        );
        if !group.execute(host) {
            execute_slots(
                host,
                &warm[group.start..group.end],
                shares,
                grid_tracks,
                stack_fit,
                wrap_leaves,
            );
        }
        start = group.end;
    }
    execute_slots(
        host,
        &warm[start..],
        shares,
        grid_tracks,
        stack_fit,
        wrap_leaves,
    );
}

fn execute_slots<A: TreeAdapter<NodeId = NodeKey>>(
    host: &mut Host<'_, A>,
    warm: &[WarmSlot],
    shares: &StackShares,
    grid_tracks: &mut Xy<Option<GridFillTrack>>,
    stack_fit: &StackFit,
    wrap_leaves: Option<&wrap_leaves::Program>,
) {
    for &slot in warm {
        let node = slot.row as usize;
        let parent = slot.parent as usize;
        let axis = slot.axis;
        let value = match slot.op {
            DirectSize::WrapLeaves => {
                if let Some(program) = wrap_leaves {
                    program.run(host, parent);
                    continue;
                }
                None
            }
            DirectSize::Generic if slot.kind == Kind::Regular => {
                stack_fit.measure(host.records, node, axis)
            }
            DirectSize::Final | DirectSize::IntrinsicFinal => {
                if host.records[node].try_finish_unbounded_final::<RustFloat>(
                    axis,
                    matches!(slot.op, DirectSize::IntrinsicFinal),
                ) {
                    continue;
                }
                None
            }
            DirectSize::BoundedFinal => {
                let record = &host.records[node];
                let bounds = slot.parent;
                let min =
                    (bounds & HAS_MIN != 0).then(|| record.values[slot_index(axis, Kind::Min)]);
                let max =
                    (bounds & HAS_MAX != 0).then(|| record.values[slot_index(axis, Kind::Max)]);
                let size = sizing_finish::clamp::<RustFloat>(
                    record.values[slot_index(axis, Kind::Regular)],
                    min,
                    max,
                );
                // Keep the usual warning order and conditions for uncommon
                // conflicting, collapsed, and nonfinite Final values.
                if matches!((min, max), (Some(min), Some(max)) if min > max)
                    || !size.is_finite()
                    || (bounds & CHECK_INTRINSIC != 0
                        && record.flags.0 & NodeFlags::flex_child(axis) != 0)
                {
                    None
                } else {
                    Some(size)
                }
            }
            DirectSize::StackShare => shares.resolve(node, axis, &host.records[node]),
            DirectSize::Pixels => match scalar_declaration(&host.params[node], axis, slot.kind) {
                Some(Size::Pixels(value)) => Some(value),
                _ => None,
            },
            DirectSize::Ratio => match scalar_declaration(&host.params[node], axis, slot.kind) {
                Some(Size::AspectRatio(ratio)) => {
                    Some(crate::prepare_leaf::aspect_size::<RustFloat>(
                        axis,
                        host.records[node].values[slot_index(axis.other(), Kind::Final)],
                        ratio,
                    ))
                }
                _ => None,
            },
            DirectSize::ViewportFrac | DirectSize::ParentFrac | DirectSize::StackFrac => {
                match scalar_declaration(&host.params[node], axis, slot.kind) {
                    Some(Size::Frac(fraction)) => {
                        let extent = match slot.op {
                            DirectSize::ViewportFrac => host.data.window_size[axis],
                            DirectSize::ParentFrac => host.parent_inner(parent, axis),
                            _ => {
                                let spacing = match host.params[parent].children_layout {
                                    ChildrenLayout::Stack { spacing, .. } => spacing,
                                    _ => 0.0,
                                };
                                let count = host.records[parent].n_placed_children;
                                let gaps =
                                    sizing_finish::stack_gap_total::<RustFloat>(spacing, count);
                                RustFloat::max(host.parent_inner(parent, axis) - gaps, 0.0)
                            }
                        };
                        Some(extent * fraction)
                    }
                    _ => None,
                }
            }
            mode => host.direct_fill(mode, node, parent, axis, &mut grid_tracks[axis]),
        };
        if let Some(value) = value {
            host.records[node].publish_slot(slot.index as usize, value);
        } else {
            host.records[node]
                .flags
                .set_state(axis, slot.kind, UNSOLVED);
            if slot.kind == Kind::EvenShare
                && matches!(
                    host.params[node].children_layout,
                    ChildrenLayout::Wrap { .. }
                )
            {
                host.reset_wrap_output(node);
            }
            host.finish_numeric_slot(sizing_requests::target(node, axis == Axis::Y, slot.kind));
            host.finish_wrap_output(node, axis, slot.kind);
        }
    }
}
