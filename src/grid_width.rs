//! Preview the main track of a Width grid directly under a known root declaration.
#![allow(unexpected_cfgs)]

use crate::declarations::{ChildrenLayout, LayoutParams, MainAxisCellSize, Size, X, Xy};
#[cfg(verus_keep_ghost)]
use crate::declarations::Axis;
use crate::prepare_frame::{FrameFloat, KnownAxis, KnownStack};
#[cfg(not(verus_keep_ghost))]
use super::{dependency_rules, grid_state, sizing_finish};
#[cfg(verus_keep_ghost)]
use crate::{dependencies::{rules as dependency_rules, sizing_finish}, grid::frame::state as grid_state};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn regular(params: LayoutParams, axis: Axis) -> Size {
    if axis is X { params.size.x } else { params.size.y }
}

pub(crate) open spec fn no_bounds(params: LayoutParams, axis: Axis) -> bool {
    if axis is X {
        params.min_size.x.is_none() && params.max_size.x.is_none()
    } else {
        params.min_size.y.is_none() && params.max_size.y.is_none()
    }
}

pub(crate) open spec fn root_grid_boundary(grid: LayoutParams, root: LayoutParams, axis: Axis) -> bool {
    &&& !grid.disabled && !root.disabled && !grid.free_placement
    &&& regular(grid, axis) is Fill && no_bounds(grid, axis) && no_bounds(root, axis)
    &&& (regular(root, axis) is Pixels || regular(root, axis) is Fill)
    &&& match grid.children_layout {
        ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } => main_axis == axis,
        _ => false,
    }
    &&& match root.children_layout {
        ChildrenLayout::Free => true,
        ChildrenLayout::Stack { axis: main, .. } => main != axis,
        _ => false,
    }
}
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(preview =>
    ensures if let Some(track) = preview {
        root_grid_boundary(*grid, *root, track.own.axis)
            && track.own.rank == 2
            && track.child_space.is_some()
    } else { true },
    no_unwind
))]
pub(crate) fn preview<F: FrameFloat, M: grid_state::WidthRounding>(
    grid: &LayoutParams, root: &LayoutParams, window: Xy<f32>,
) -> Option<KnownStack> {
    let ChildrenLayout::Grid {
        columns: MainAxisCellSize::Width(width), spacing_x, spacing_y, main_axis: axis, ..
    } = grid.children_layout else { return None; };
    if grid.disabled || grid.free_placement || root.disabled
        || !matches!(*grid.size.component(axis), Size::Fill)
        || grid.min_size.component(axis).is_some() || grid.max_size.component(axis).is_some()
        || root.min_size.component(axis).is_some() || root.max_size.component(axis).is_some()
    {
        return None;
    }
    let root_main = match *root.size.component(axis) {
        Size::Fill => *window.component(axis),
        Size::Pixels(size) => size,
        _ => return None,
    };
    let root_inner = sizing_finish::inner::<F>(root_main, sizing_finish::padding(root, axis));
    let extent = match root.children_layout {
        ChildrenLayout::Free => root_inner,
        ChildrenLayout::Stack { axis: main, .. } if main.index() != axis.index() => {
            let [before, after] = *grid.margin.component(axis);
            sizing_finish::inside_margins::<F>(root_inner, [F::margin(before), F::margin(after)])
        }
        _ => return None,
    };
    if !F::finite(extent) || !F::finite(root_main) { return None; }
    let spacing = if matches!(axis, X) { spacing_x } else { spacing_y };
    if !F::finite(spacing) { return None; }
    let inner = sizing_finish::inner::<F>(extent, sizing_finish::padding(grid, axis));
    let key = grid_state::width_key::<M>(inner, width, spacing);
    let track = sizing_finish::GridTrack::new::<F>(inner, key.tracks, spacing).extent::<F>(1);
    if !F::finite(track) { return None; }
    let root_regular = 0;
    let root_final = dependency_rules::next_level(root_regular);
    let rank = dependency_rules::next_level(root_final);
    Some(KnownStack { own: KnownAxis { axis, size: extent, rank }, child_space: Some(track) })
}
