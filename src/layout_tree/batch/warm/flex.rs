//! Recompute a run of consecutive two-axis Fill sizing boxes.

use super::{DirectSize, Host, Kind, NodeKey, UNSOLVED, WarmSlot, sizing_finish, sizing_requests};
use crate::placement_geometry::RustFloat;
use crate::solve::{Solve, slot_index};
use crate::{Axis, ChildrenLayout, LayoutParams, NodeLayoutData, TreeAdapter};

#[derive(Debug)]
pub(super) struct FlexRun {
    start: u32,
    end: u32,
    parent: u32,
    main: Axis,
    uniform: bool,
}

impl FlexRun {
    pub(super) fn compile(slots: &[WarmSlot], params: &[LayoutParams]) -> Option<(usize, Self)> {
        let (start, parent, main) = fill_box(slots)?;
        if !matches!(
            params.get(parent as usize)?.children_layout,
            ChildrenLayout::Stack { axis, .. } if axis == main
        ) {
            return None;
        }
        let mut end = start.checked_add(1)?;
        let mut consumed = 4;
        while fill_box(&slots[consumed..]) == Some((end, parent, main)) {
            end = end.checked_add(1)?;
            consumed += 4;
        }
        let styles = params.get(start as usize..end as usize)?;
        let cross = main.other();
        let uniform = styles.len() > 1
            && styles[1..].iter().all(|style| {
                style.fill_weight.to_bits() == styles[0].fill_weight.to_bits()
                    && style.margin[cross] == styles[0].margin[cross]
            });
        Some((
            consumed,
            Self {
                start,
                end,
                parent,
                main,
                uniform,
            },
        ))
    }

    pub(super) fn execute<A: TreeAdapter<NodeId = NodeKey>>(&self, host: &mut Host<'_, A>) -> bool {
        let start = self.start as usize;
        let end = self.end as usize;
        let parent = self.parent as usize;
        if end > host.records.len()
            || end > host.params.len()
            || parent >= host.records.len()
            || parent >= host.params.len()
        {
            return false;
        }
        if self.main == Axis::X {
            finish::<_, false>(host, parent, start, end, self.uniform);
        } else {
            finish::<_, true>(host, parent, start, end, self.uniform);
        }
        true
    }
}

// The original Regular writes are both pure, and the two Final writes can
// warn in X-then-Y order. No other producer lies inside this sequence.
fn fill_box(slots: &[WarmSlot]) -> Option<(u32, u32, Axis)> {
    let [rx, ry, fx, fy, ..] = slots else {
        return None;
    };
    if rx.row != ry.row
        || rx.row != fx.row
        || rx.row != fy.row
        || rx.parent != ry.parent
        || rx.kind != Kind::Regular
        || ry.kind != Kind::Regular
        || !matches!(fx.op, DirectSize::Final)
        || !matches!(fy.op, DirectSize::Final)
        || rx.axis != Axis::X
        || ry.axis != Axis::Y
        || fx.axis != Axis::X
        || fy.axis != Axis::Y
    {
        return None;
    }
    let main = match (rx.op, ry.op) {
        (DirectSize::StackFill, DirectSize::ParentFillMargins) => Axis::X,
        (DirectSize::ParentFillMargins, DirectSize::StackFill) => Axis::Y,
        _ => return None,
    };
    Some((rx.row, rx.parent, main))
}

fn finish<A: TreeAdapter<NodeId = NodeKey>, const VERTICAL: bool>(
    host: &mut Host<'_, A>,
    parent: usize,
    start: usize,
    end: usize,
    uniform: bool,
) {
    let (main, cross) = if VERTICAL {
        (Axis::Y, Axis::X)
    } else {
        (Axis::X, Axis::Y)
    };
    let share = host.records[parent].values[slot_index(main, Kind::EvenShare)];
    let available = host.parent_inner(parent, cross);
    if uniform {
        let (x, y) = dimensions::<VERTICAL>(&host.params[start], share, available, cross);
        if x.is_finite() && y.is_finite() {
            for record in &mut host.records[start..end] {
                publish_box(record, x, y);
            }
            return;
        }
    }
    for row in start..end {
        let (x, y) = dimensions::<VERTICAL>(&host.params[row], share, available, cross);
        let record = &mut host.records[row];
        if x.is_finite() && y.is_finite() {
            publish_box(record, x, y);
        } else {
            record.publish_slot(slot_index(Axis::X, Kind::Regular), x);
            record.publish_slot(slot_index(Axis::Y, Kind::Regular), y);
            for axis in [Axis::X, Axis::Y] {
                host.records[row]
                    .flags
                    .set_state(axis, Kind::Final, UNSOLVED);
                host.finish_numeric_slot(sizing_requests::target(
                    row,
                    axis == Axis::Y,
                    Kind::Final,
                ));
            }
        }
    }
}

#[inline(always)]
fn dimensions<const VERTICAL: bool>(
    style: &LayoutParams,
    share: f32,
    available: f32,
    cross: Axis,
) -> (f32, f32) {
    let along = share * style.fill_weight;
    let across =
        sizing_finish::inside_margins::<RustFloat>(available, crate::flow::margins(style, cross));
    if VERTICAL {
        (across, along)
    } else {
        (along, across)
    }
}

#[inline(always)]
fn publish_box(record: &mut NodeLayoutData, x: f32, y: f32) {
    record.publish_slot(slot_index(Axis::X, Kind::Regular), x);
    record.publish_slot(slot_index(Axis::Y, Kind::Regular), y);
    record.publish_slot(slot_index(Axis::X, Kind::Final), x);
    record.publish_slot(slot_index(Axis::Y, Kind::Final), y);
}
