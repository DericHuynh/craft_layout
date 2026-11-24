use crate::*;

#[path = "block_flow.rs"]
mod block_flow;
pub(crate) use block_flow::{BlockFlow, BlockItem, BlockMargins, Scalar as BlockScalar, edge_adjoins, implicit_edges, item_adjoins};

#[inline]
pub(crate) fn margins(params: &LayoutParams, axis: Axis) -> [f32; 2] {
    params.margin[axis].map(Margin::pixels)
}

pub(crate) use crate::place::stack_line::with_margin;

pub(crate) fn block_can_collapse(params: &LayoutParams) -> bool {
    params.text == TextContent::None && params.image.is_none() && params.content_measure == ContentMeasure::None
}

pub(crate) fn zero_minimum(params: &LayoutParams) -> bool {
    matches!(params.min_size.y, None | Some(Size::Pixels(0.0) | Size::Frac(0.0)))
}

#[path = "wrap_lines.rs"]
pub(crate) mod wrap_lines;
use wrap_lines::{LineModel, LineSource};
#[path = "wrap_metrics.rs"]
pub(crate) mod wrap_metrics;

pub(crate) struct SolverLine<'a, T: ?Sized, const MARKS_READY: bool> {
    tree: &'a T,
    axis: Axis,
    spacing: f32,
}

impl<'a, T: ?Sized, const MARKS_READY: bool> SolverLine<'a, T, MARKS_READY> {
    #[inline(always)]
    pub(crate) fn new(tree: &'a T, axis: Axis, spacing: f32) -> Self {
        Self { tree, axis, spacing }
    }
}

impl<T: Solve + ?Sized, const MARKS_READY: bool> LineModel for SolverLine<'_, T, MARKS_READY> {
    type Id = T::NodeId;
    type Metric = f32;
}

impl<T: Solve + ?Sized, const MARKS_READY: bool> LineSource for SolverLine<'_, T, MARKS_READY> {
    #[inline]
    fn in_flow(&self, child: Self::Id) -> bool {
        let params = self.tree.node_layout_params(child);
        !params.disabled && !params.free_placement
    }

    #[inline]
    fn marked(&self, child: Self::Id) -> bool {
        MARKS_READY && self.tree.node_layout_data(child).flags.starts_wrap_line()
    }

    #[inline]
    fn fills(&self, child: Self::Id) -> bool {
        self.tree.any_size_is_fill(child, self.axis)
    }

    #[inline]
    fn sibling(&self, child: Self::Id) -> Option<Self::Id> {
        self.tree.next_sibling(child)
    }

    #[inline]
    fn extent(&self, child: Self::Id, base: bool) -> f32 {
        let size = if base {
            self.tree.wrap_fill_base(child, self.axis)
        } else {
            self.tree.get_solved_value(child, self.axis, Kind::Final)
        };
        let [start, end] = margins(self.tree.node_layout_params(child), self.axis);
        with_margin(size, start + end)
    }

    #[inline]
    fn cross_extent(&self, child: Self::Id) -> f32 {
        let axis = self.axis.other();
        let [start, end] = margins(self.tree.node_layout_params(child), axis);
        with_margin(self.tree.pre_grow_size(child, axis), start + end)
    }

    #[inline]
    fn empty_extent(&self) -> f32 { 0.0 }

    #[inline]
    fn append_extent(&self, main: f32, extent: f32) -> f32 { wrap_lines::extend_main(main, self.spacing, extent) }

    #[inline]
    fn max_cross(&self, cross: f32, extent: f32) -> f32 { cross.max(extent) }

    #[inline]
    fn exceeds_limit(&self, main: f32, limit: f32) -> bool { wrap_lines::beyond_limit(main, limit) }
}

pub(crate) struct WrapRecords<'a, T: ?Sized> {
    pub(crate) tree: &'a mut T,
}

impl<T: TreeAdapter + ?Sized> wrap_metrics::CacheModel for WrapRecords<'_, T> {
    type Id = T::NodeId;
}

impl<T: TreeAdapter + ?Sized> wrap_metrics::LineCache for WrapRecords<'_, T> {
    #[inline]
    fn same_cursor(&self, next: Option<Self::Id>, stop: Option<Self::Id>) -> bool {
        next == stop
    }

    #[inline]
    fn row(&self, child: Self::Id) -> (Option<Self::Id>, bool) {
        let params = self.tree.node_layout_params(child);
        (self.tree.next_sibling(child), !params.disabled && !params.free_placement)
    }

    #[inline]
    fn set_line_bits(&mut self, child: Self::Id, metric: wrap_metrics::Metric, bits: u32) {
        self.tree.node_layout_data_mut(child).set_wrap_metric(metric, bits);
    }
}

impl<T: TreeAdapter + ?Sized> wrap_metrics::LineRecordAccess for WrapRecords<'_, T> {
    #[inline(always)]
    fn finish(self) {}
}
