use crate::*;

#[path = "block_flow.rs"]
mod block_flow;
pub(crate) use block_flow::{BlockFlow, BlockMargins};
use block_flow::BlockItem;

#[inline]
pub(crate) fn margins(params: &LayoutParams, axis: Axis) -> [f32; 2] {
    params.margin[axis].map(Margin::pixels)
}

pub(crate) use crate::place::stack_line::with_margin;

impl BlockItem {
    pub(crate) fn new(params: &LayoutParams, layout: &NodeLayoutData, nested: Option<BlockMargins>) -> Self {
        let [top, bottom] = margins(params, Y);
        let size = layout.size().y;
        let adjoins = size == 0.0 && block_can_collapse(params)
            && params.padding.y == [0.0; 2]
            && params.min_size.y.is_none_or(|size| size == Size::Pixels(0.0) || size == Size::Frac(0.0));
        Self::from_edges(top, bottom, size, adjoins, layout.n_placed_children == 0, nested)
    }
}

fn block_can_collapse(params: &LayoutParams) -> bool {
    params.text == TextContent::None && params.image.is_none() && params.content_measure == ContentMeasure::None
}

#[path = "wrap_lines.rs"]
mod wrap_lines;
use wrap_lines::{LineModel, LineSource, WrapLine, scan_line};
#[path = "wrap_metrics.rs"]
pub(crate) mod wrap_metrics;

struct SolverLine<'a, T: ?Sized, const MARKS_READY: bool> {
    tree: &'a T,
    axis: Axis,
    spacing: f32,
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
    fn append_extent(&self, main: f32, extent: f32) -> f32 { main + self.spacing + extent }

    #[inline]
    fn max_cross(&self, cross: f32, extent: f32) -> f32 { cross.max(extent) }

    #[inline]
    fn exceeds_limit(&self, main: f32, limit: f32) -> bool { main > limit }
}

impl<T: TreeAdapter + ?Sized> wrap_metrics::CacheModel for T {
    type Id = T::NodeId;
}

impl<T: TreeAdapter + ?Sized> wrap_metrics::LineCache for T {
    #[inline]
    fn same_cursor(&self, next: Option<Self::Id>, stop: Option<Self::Id>) -> bool {
        next == stop
    }

    #[inline]
    fn row(&self, child: Self::Id) -> (Option<Self::Id>, bool) {
        let params = self.node_layout_params(child);
        (self.next_sibling(child), !params.disabled && !params.free_placement)
    }

    #[inline]
    fn set_line_bits(&mut self, child: Self::Id, metric: wrap_metrics::Metric, bits: u32) {
        self.node_layout_data_mut(child).set_wrap_metric(metric, bits);
    }
}

pub(crate) trait Flow: Solve {
    /// With an available size, find a break using each child's size before Fill. Otherwise
    /// reuse the saved break and read the resolved dimensions for measurement or placement.
    fn wrap_line<const MARKS_READY: bool>(&self, next: Option<Self::NodeId>, axis: Axis, available: Option<f32>, spacing: f32) -> WrapLine<Self::NodeId> {
        scan_line(&SolverLine::<_, MARKS_READY> { tree: self, axis, spacing }, next, available)
    }

    fn block_flow(&self, i: Self::NodeId) -> BlockFlow {
        let params = self.node_layout_params(i);
        let margins_adjoin = self.node_layout_data(i).flags.is_block_item() && block_can_collapse(params);
        BlockFlow::from_edges(
            margins_adjoin && params.padding.y[0] == 0.0,
            margins_adjoin && params.padding.y[1] == 0.0
                && self.read_size(i, Y, Kind::Regular) == Some(Size::FitContent)
                && params.min_size.y.is_none_or(|size| size == Size::Pixels(0.0) || size == Size::Frac(0.0)),
        )
    }

    fn block_item(&mut self, i: Self::NodeId) -> BlockItem {
        let index = self.node_layout_data(i).block_margin_index();
        let nested = index.map(|index| margin_storage::read_margin(&self.layout_data().block_margins, index));
        BlockItem::new(self.node_layout_params(i), self.node_layout_data(i), nested)
    }
}

impl<T: TreeAdapter + ?Sized> Flow for T {}
