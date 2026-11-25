//! The exact size words for one percentage and aspect-ratio run.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, X};
use crate::node_data::NodeLayoutData;
use crate::prepare_frame::FrameFloat;
use crate::prepare_leaf::aspect_size;
#[cfg(verus_keep_ghost)]
use crate::{
    cycle_rules,
    prepare_leaf::{aspect, other_axis},
};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures ({
        let cross = F::product(available, fraction);
        let main = aspect::<F>(other_axis(axis), cross, ratio);
        out == if F::finite_word(cross) && F::finite_word(main) {
            Some(if axis is X { [cross, main] } else { [main, cross] })
        } else { None }
    }),
    no_unwind
))]
pub(crate) fn finite_sizes<F: FrameFloat>(
    axis: Axis,
    available: f32,
    fraction: f32,
    ratio: f32,
) -> Option<[f32; 2]> {
    let cross = F::multiply(available, fraction);
    let main = aspect_size::<F>(axis.other(), cross, ratio);
    if !F::finite(cross) || !F::finite(main) {
        return None;
    }
    Some(if matches!(axis, X) {
        [cross, main]
    } else {
        [main, cross]
    })
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) open spec fn written(record: NodeLayoutData, size: [f32; 2], after: NodeLayoutData) -> bool {
        let phase = cycle_rules::SOLVED;
        let f0 = cycle_rules::phase_word(record.flags.0, 0, phase);
        let f1 = cycle_rules::phase_word(f0, 1, phase);
        let f2 = cycle_rules::phase_word(f1, 2, phase);
        let f3 = cycle_rules::phase_word(f2, 3, phase);
        &&& after.flags.0 == f3
        &&& after.values@ == record.values@.update(0, size[0]).update(1, size[1]).update(2, size[0]).update(3, size[1])
        &&& after == (NodeLayoutData { flags: after.flags, values: after.values, ..record })
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures written(*old(record), size, *final(record)),
    no_unwind
))]
fn publish(record: &mut NodeLayoutData, size: [f32; 2]) {
    record.publish_slot(0, size[0]);
    record.publish_slot(1, size[1]);
    record.publish_slot(2, size[0]);
    record.publish_slot(3, size[1]);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(records)@.len() == old(records)@.len(),
        forall |index: int| 0 <= index < final(records)@.len() ==> written(old(records)@[index], size, #[trigger] final(records)@[index]),
    no_unwind
))]
pub(crate) fn publish_run(records: &mut [NodeLayoutData], size: [f32; 2]) {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant records@.len() == old(records)@.len(), index <= records@.len(),
            forall |at: int| 0 <= at < index ==> written(old(records)@[at], size, #[trigger] records@[at]),
            forall |at: int| index <= at < records@.len() ==> #[trigger] records@[at] == old(records)@[at],
        ensures index == records.len(),
        decreases records.len() - index,
    ))]
    while index < records.len() {
        publish(&mut records[index], size);
        index += 1;
    }
}

#[cfg(not(verus_keep_ghost))]
use super::{
    DirectSize, Host, Kind, LayoutParams, NodeKey, RustFloat, Size, TreeAdapter, WarmSlot,
};
#[cfg(not(verus_keep_ghost))]
use std::ops::Range;

#[cfg(not(verus_keep_ghost))]
#[derive(Debug)]
pub(super) struct RatioRun {
    rows: Range<usize>,
    parent: usize,
    axis: Axis,
    fraction: f32,
    ratio: f32,
}

#[cfg(not(verus_keep_ghost))]
impl RatioRun {
    /// Keep exactly the original sequence of independent leaf operations.
    /// Every row reads the same already-available parent Final and then its
    /// own percentage-axis size. Matching bits preserve signed zeros.
    pub(super) fn compile(slots: &[WarmSlot], params: &[LayoutParams]) -> Option<(usize, Self)> {
        let (first, fraction, ratio) = recipe(slots, params)?;
        let mut used = 4;
        let row = first.row as usize;
        while let Some((next, f, r)) = slots.get(used..).and_then(|tail| recipe(tail, params)) {
            if next.parent != first.parent
                || next.axis != first.axis
                || next.row as usize != row + used / 4
                || f.to_bits() != fraction.to_bits()
                || r.to_bits() != ratio.to_bits()
            {
                break;
            }
            used += 4;
        }
        let count = used / 4;
        (count >= 4).then_some((
            used,
            Self {
                rows: row..row + count,
                parent: first.parent as usize,
                axis: first.axis,
                fraction,
                ratio,
            },
        ))
    }

    /// A warm run has no Block items. The caller discards cached recipes
    /// on declaration changes. Nonfinite outputs replay the old scalar slice.
    pub(super) fn execute<A: TreeAdapter<NodeId = NodeKey>>(&self, host: &mut Host<'_, A>) -> bool {
        let Some(size) = finite_sizes::<RustFloat>(
            self.axis,
            host.parent_inner(self.parent, self.axis),
            self.fraction,
            self.ratio,
        ) else {
            return false;
        };
        let Some(records) = host.records.get_mut(self.rows.clone()) else {
            return false;
        };
        publish_run(records, size);
        true
    }
}

#[cfg(not(verus_keep_ghost))]
fn recipe(slots: &[WarmSlot], params: &[LayoutParams]) -> Option<(WarmSlot, f32, f32)> {
    let [f, cross, r, main, ..] = slots else {
        return None;
    };
    if !matches!(f.op, DirectSize::ParentFrac)
        || f.kind != Kind::Regular
        || !matches!(cross.op, DirectSize::Final)
        || cross.kind != Kind::Final
        || !matches!(r.op, DirectSize::Ratio)
        || r.kind != Kind::Regular
        || !matches!(main.op, DirectSize::Final)
        || main.kind != Kind::Final
        || f.row != cross.row
        || f.row != r.row
        || f.row != main.row
        || f.axis != cross.axis
        || r.axis != main.axis
        || f.axis == r.axis
    {
        return None;
    }
    let style = params.get(f.row as usize)?;
    if style.min_size.x.is_some()
        || style.min_size.y.is_some()
        || style.max_size.x.is_some()
        || style.max_size.y.is_some()
    {
        return None;
    }
    let (Size::Frac(fraction), Size::AspectRatio(ratio)) = (style.size[f.axis], style.size[r.axis])
    else {
        return None;
    };
    Some((*f, fraction, ratio))
}
