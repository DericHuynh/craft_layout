use std::borrow::Borrow;

use crate::*;
#[cfg(any(test, not(target_arch = "x86_64")))]
use crate::placement_geometry as geometry;
use crate::placement_geometry::RustFloat;
use crate::vec_memory::RustVec;
#[cfg(feature = "incremental")]
use crate::vec_memory::VecMemory;
use crate::packed_stack_leaf::PreparedStackLeaf;

#[path = "free_placement.rs"]
mod free_placement;
pub use free_placement::FreePlacementError;

#[path = "placement_node.rs"]
mod placement_node;
#[path = "placement_modes.rs"]
pub(crate) mod placement_modes;

#[path = "placement_entry.rs"]
pub(crate) mod placement_entry;

#[path = "placement_walk.rs"]
mod placement_walk;

#[path = "stack_line.rs"]
pub(crate) mod stack_line;

#[path = "placement_batch.rs"]
mod placement_batch;

struct NodeOutput<'tree, T: ?Sized, S, const UNSNAPPED: bool = false> {
    fresh_placement: bool,
    tree: &'tree mut T,
    snapper: Option<S>,
}

impl<T: ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn snapper(&self) -> Option<&Snapper> { if UNSNAPPED { None } else { self.snapper.as_ref().map(Borrow::borrow) } }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_node::NodeModel<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    type PublicationFloat = RustFloat;
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_node::NodeTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn read_work(&self, _node: T::NodeId) -> Option<crate::placement_work::PlacementWork> {
        #[cfg(feature = "incremental")]
        { Some(crate::placement_adapter::read_work(self.tree, _node)) }
        #[cfg(not(feature = "incremental"))]
        { None }
    }

    #[inline(always)]
    fn clear_work(&mut self, _node: T::NodeId) {
        #[cfg(feature = "incremental")]
        { crate::placement_adapter::clear_work(self.tree, _node); }
    }

    #[inline(always)]
    fn snap(&self, [[left, right], [top, bottom]]: placement_node::Edges) -> placement_node::Edges {
        match self.snapper() {
            Some(snapper) => {
                let [left, right, top, bottom] = snapper.snap([left, right, top, bottom]);
                [[left, right], [top, bottom]]
            }
            None => [[left, right], [top, bottom]],
        }
    }

    #[inline(always)]
    fn subtract_edges(left: f32, right: f32) -> f32 { left - right }

    #[inline(always)]
    fn write(&mut self, node: T::NodeId, absolute: placement_node::Edges, local: placement_node::Edges) {
        crate::placement_adapter::publish(self.tree, node, absolute, local);
    }

    #[inline(always)]
    fn first_child(&self, node: T::NodeId) -> Option<T::NodeId> {
        self.tree.first_child(node)
    }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool>
    placement_modes::FreePlacementInputs<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_modes::SiblingTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn next_sibling(&self, id: T::NodeId) -> Option<T::NodeId> { self.tree.next_sibling(id) }

    #[inline(always)]
    fn disabled(&self, id: T::NodeId) -> bool { self.tree.node_layout_params(id).disabled }

    #[inline(always)]
    fn size(&self, id: T::NodeId) -> [f32; 2] {
        crate::placement_adapter::size(self.tree, id)
    }

    #[inline(always)]
    fn free_style(&self, id: T::NodeId) -> placement_modes::FreeStyle {
        crate::placement_adapter::free_style(self.tree.node_layout_params(id))
    }

    #[inline(always)]
    fn align_style(&self, id: T::NodeId) -> placement_modes::StackStyle {
        crate::placement_adapter::stack_style::<RustFloat>(self.tree.node_layout_params(id))
    }

    #[inline(always)]
    fn margins(&self, id: T::NodeId, x: bool) -> [f32; 2] {
        margins(self.tree.node_layout_params(id), if x { X } else { Y })
    }

    #[inline(always)]
    fn declaration(&self, id: T::NodeId, x: bool, kind: Kind) -> Option<Size> {
        self.tree.read_size(id, if x { X } else { Y }, kind)
    }

    #[inline(always)]
    fn window_size(&mut self, x: bool) -> f32 {
        crate::placement_adapter::window_axis(&self.tree.layout_data().window_size, x)
    }
}

impl placement_modes::StackDataModel for NodeLayoutData {}

impl placement_modes::StackData for NodeLayoutData {
    #[inline(always)]
    fn stack_size(&self) -> [f32; 2] {
        let size = self.size();
        [size.x, size.y]
    }

    #[inline(always)]
    fn cached_start(&self) -> bool {
        #[cfg(feature = "incremental")]
        { self.cached_stack_start() }
        #[cfg(not(feature = "incremental"))]
        { false }
    }

    #[inline(always)]
    fn dirty(&self) -> bool {
        #[cfg(feature = "incremental")]
        { self.placement != PlacementWork::Clean }
        #[cfg(not(feature = "incremental"))]
        { false }
    }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_batch::OutputModel<T::NodeId, [f32; 4]> for NodeOutput<'_, T, S, UNSNAPPED> {}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_batch::BatchTarget<T::NodeId, [f32; 4]> for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline]
    fn snap(&mut self, edges: &mut [[f32; 4]]) {
        if let Some(snapper) = self.snapper() { snapper.snap_many(edges); }
    }

    #[inline]
    fn write(&mut self, node: T::NodeId, [left, right, top, bottom]: [f32; 4], dirty: bool, origin: [f32; 2]) {
        placement_node::write_snapped(self, node, [[left, right], [top, bottom]], origin, dirty);
    }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_modes::StackTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    type Data = NodeLayoutData;

    #[inline(always)]
    fn stack_data(&self, id: T::NodeId) -> &Self::Data { self.tree.node_layout_data(id) }

    #[inline(always)]
    fn stack_params(&self, id: T::NodeId) -> &LayoutParams { self.tree.node_layout_params(id) }

    #[inline(always)]
    fn stack_align(params: &LayoutParams) -> placement_modes::StackStyle {
        crate::placement_adapter::stack_style::<RustFloat>(params)
    }

    #[inline(always)]
    fn prepared_styles(&self) -> bool {
        #[cfg(feature = "incremental")]
        { self.tree.retains_output_rects() }
        #[cfg(not(feature = "incremental"))]
        { false }
    }

    #[inline(always)]
    fn snapping(&self) -> bool { !UNSNAPPED && self.snapper.is_some() }

    #[inline(always)]
    fn full_unsnapped(&self) -> bool { UNSNAPPED }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_modes::WrapTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn ready_wrap_lines(&self, id: T::NodeId) -> bool {
        #[cfg(feature = "incremental")]
        {
            self.fresh_placement && self.snapper().is_none()
                && self.tree.node_layout_data(id).prepared_placement & NodeLayoutData::PREPARED_WRAP != 0
        }
        #[cfg(not(feature = "incremental"))]
        { let _ = (self.fresh_placement, id); false }
    }

    #[inline(always)]
    fn ready_wrap_start(&self, id: T::NodeId) -> bool {
        #[cfg(feature = "incremental")]
        { self.tree.node_layout_data(id).prepared_placement & NodeLayoutData::PREPARED_WRAP_START != 0 }
        #[cfg(not(feature = "incremental"))]
        { let _ = id; false }
    }

    #[inline(always)]
    fn wrap_line_height(&self, id: T::NodeId) -> f32 {
        f32::from_bits(self.tree.node_layout_data(id).parent_flow[1])
    }

    #[inline(always)]
    fn same_cursor(&self, next: Option<T::NodeId>, id: T::NodeId) -> bool { next == Some(id) }

    #[inline(always)]
    fn wrap_in_flow(&self, id: T::NodeId) -> bool {
        let params = self.tree.node_layout_params(id);
        !params.disabled && !params.free_placement
    }

    #[inline(always)]
    fn wrap_marked(&self, id: T::NodeId) -> bool { self.tree.node_layout_data(id).flags.starts_wrap_line() }

    #[inline(always)]
    fn wrap_slot(&self, id: T::NodeId, x: bool, kind: Kind) -> f32 {
        self.tree.get_solved_value(id, if x { X } else { Y }, kind)
    }

}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_modes::BlockTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    type Flow = BlockFlow;
    type Item = BlockItem;
    type Nested = BlockMargins;

    #[inline(always)]
    fn block_style(&self, id: T::NodeId) -> placement_modes::BlockStyle {
        let params = self.tree.node_layout_params(id);
        let [left, right] = params.margin.x;
        placement_modes::BlockStyle {
            free: params.free_placement,
            inline_margin: [left.pixels(), right.pixels()], auto: [left == Margin::AUTO, right == Margin::AUTO],
        }
    }

    #[inline(always)]
    fn margin_index(&self, id: T::NodeId) -> Option<usize> { self.tree.node_layout_data(id).block_margin_index::<RustFloat>() }

    #[inline(always)]
    fn nested_margin(&mut self, index: usize) -> Option<Self::Nested> {
        margin_storage::read_margin(&self.tree.layout_data().block_margins, index)
    }

    #[inline(always)]
    fn block_item_inputs(&self, id: T::NodeId) -> placement_modes::BlockItemInputs {
        let params = self.tree.node_layout_params(id);
        let layout = self.tree.node_layout_data(id);
        placement_modes::BlockItemInputs {
            bounds: placement_modes::BlockEdges {
                padding: params.padding.y, collapse: block_can_collapse(params), zero_minimum: zero_minimum(params),
            },
            height: layout.size().y, margins: margins(params, Y), children_empty: !layout.has_in_flow_children(),
        }
    }

    #[inline(always)]
    fn block_from_edges([top, bottom]: [f32; 2], height: f32, adjoins: bool, children_empty: bool, nested: Option<Self::Nested>) -> Self::Item {
        BlockItem::from_edges(top, bottom, height, adjoins, children_empty, nested)
    }

    #[inline(always)]
    fn append_block(flow: &mut Self::Flow, item: Self::Item) -> f32 { flow.push(item) }

    #[inline(always)]
    fn block_parent_edges(&self, id: T::NodeId) -> placement_modes::BlockEdges {
        let params = self.tree.node_layout_params(id);
        placement_modes::BlockEdges {
            padding: params.padding.y,
            collapse: self.tree.node_layout_data(id).flags.is_block_item() && block_can_collapse(params),
            zero_minimum: zero_minimum(params),
        }
    }

    #[inline(always)]
    fn block_from_parent(before: bool, after: bool) -> Self::Flow { BlockFlow::from_edges(before, after) }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_modes::GridTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn grid_lines(&self, id: T::NodeId) -> [f32; 2] {
        crate::placement_adapter::grid_lines(self.tree, id)
    }

    #[inline(always)]
    fn grid_cell(&self, id: T::NodeId) -> [f32; 2] {
        crate::placement_adapter::grid_cell(self.tree, id)
    }

    #[inline(always)]
    fn grid_style(&self, id: T::NodeId) -> placement_modes::GridStyle {
        crate::placement_adapter::grid_style::<RustFloat>(self.tree.node_layout_params(id))
    }

    #[inline(always)]
    fn grid_start([x, y]: [f32; 2], [dx, dy]: [f32; 2], [cx, cy]: [f32; 2], [w, h]: [f32; 2]) -> placement_node::Edges {
        let rect = grid_start_rect(Xy::new(x, y), Xy::new(dx, dy), Xy::new(cx, cy), Xy::new(w, h));
        [rect.x, rect.y]
    }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_modes::ParentTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn ready_pair(&self, id: T::NodeId) -> bool {
        #[cfg(feature = "incremental")]
        {
            self.fresh_placement && self.snapper().is_none()
                && self.tree.node_layout_data(id).prepared_placement & NodeLayoutData::PREPARED_PAIR != 0
        }
        #[cfg(not(feature = "incremental"))]
        { let _ = id; false }
    }

    #[inline(always)]
    fn packed_leaf_span(&mut self, id: T::NodeId) -> Option<[usize; 2]> {
        #[cfg(feature = "incremental")]
        {
            if !self.fresh_placement || self.snapper().is_some() { return None; }
            let record = self.tree.node_layout_data(id);
            let ready = NodeLayoutData::PREPARED_FIT_LEAVES | NodeLayoutData::PREPARED_WRAP_START;
            if record.prepared_placement & ready == 0 { return None; }
            let prepared = &mut self.tree.layout_data().packed_stack_leaves;
            if prepared.next_parent() != Some(id) { return None; }
            prepared.take_span()
        }
        #[cfg(not(feature = "incremental"))]
        { let _ = id; None }
    }

    #[inline(always)]
    fn take_uniform_leaves(&mut self, id: T::NodeId) -> Option<([f32; 2], Vec<T::NodeId>)> {
        #[cfg(feature = "incremental")]
        if self.fresh_placement && UNSNAPPED
            && self.tree.node_layout_data(id).prepared_placement & NodeLayoutData::PREPARED_UNIFORM_LEAVES != 0
        {
            let workspace = &mut self.tree.layout_data().packed_stack_leaves;
            if let Some((parent, size)) = workspace.uniform_run {
                if parent == id {
                    workspace.uniform_run = None;
                    return Some((size, RustVec::take(&mut workspace.uniform_ids)));
                }
            }
        }
        let _ = id;
        None
    }

    #[inline(always)]
    fn recycle_uniform_leaves(&mut self, ids: Vec<T::NodeId>) {
        #[cfg(feature = "incremental")]
        { self.tree.layout_data().packed_stack_leaves.uniform_ids = ids; }
        #[cfg(not(feature = "incremental"))]
        { let _ = ids; }
    }

    #[inline(always)]
    fn same_packed_id(&self, left: T::NodeId, right: T::NodeId) -> bool { left == right }

    #[inline]
    fn take_packed_leaves(&mut self) -> Vec<PreparedStackLeaf<T::NodeId>> {
        #[cfg(feature = "incremental")]
        { RustVec::take(&mut self.tree.layout_data().packed_stack_leaves.rows) }
        #[cfg(not(feature = "incremental"))]
        { Vec::new() }
    }

    #[inline]
    fn put_packed_leaves(&mut self, rows: Vec<PreparedStackLeaf<T::NodeId>>) {
        #[cfg(feature = "incremental")]
        { self.tree.layout_data().packed_stack_leaves.rows = rows; }
        #[cfg(not(feature = "incremental"))]
        { let _ = rows; }
    }

    #[inline(always)]
    fn parent_style(&self, id: T::NodeId) -> placement_modes::ParentStyle {
        crate::placement_adapter::parent_style(self.tree.node_layout_params(id))
    }

    #[inline(always)]
    fn free_placement(&self, id: T::NodeId) -> bool { self.tree.node_layout_params(id).free_placement }

    #[inline(always)]
    fn prefers_batch(&self) -> bool { self.snapper().is_some_and(Snapper::prefers_batch) }

    #[inline(always)]
    fn placed_children(&self, id: T::NodeId) -> u32 { self.tree.node_layout_data(id).n_placed_children }

}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_modes::RootTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn clear_scale_changed(&mut self) {
        #[cfg(feature = "incremental")]
        { self.tree.layout_data().placement_scale_changed = false; }
    }

    #[inline(always)]
    fn root_id(&self) -> T::NodeId { self.tree.root() }

    #[inline(always)]
    fn pixel_scale(&mut self) -> Option<f32> { if UNSNAPPED { None } else { self.tree.layout_data().pixel_scale } }
}

impl<T: TreeAdapter + ?Sized, const UNSNAPPED: bool> placement_entry::RootPlacementTarget<T::NodeId> for NodeOutput<'_, T, Snapper, UNSNAPPED> {
    #[inline(always)]
    fn prepare_rounding(&mut self, scale: Option<f32>) { if !UNSNAPPED { self.snapper = scale.map(Snapper::new); } }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> placement_entry::FreeTarget<T::NodeId> for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn mark_repositioned(&mut self, _node: T::NodeId) {
        #[cfg(feature = "incremental")]
        self.tree.node_layout_data_mut(_node).mark_placement_changed();
    }
}

impl placement_modes::StackMath for RustFloat {
    #[inline(always)]
    fn negate(value: f32) -> f32 { -value }

    #[inline(always)]
    fn with_margin(x: f32, margin: f32) -> f32 { stack_line::with_margin(x, margin) }

    #[inline(always)]
    fn place(cursor: &mut f32, flipped: bool, range: [f32; 2], size: f32, margin: [f32; 2], gap: f32) -> [f32; 2] {
        stack_line::place(cursor, flipped, range, size, margin, gap)
    }

    #[inline(always)]
    fn place_start(cursor: &mut f32, cross_start: f32, x: bool, size: [f32; 2], gap: f32) -> placement_node::Edges {
        stack_line::place_start(cursor, cross_start, x, size, gap)
    }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn after_item(start: f32, size: f32, trailing: f32, gap: f32) -> f32 {
        stack_line::after_item(start, size, trailing, gap)
    }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> crate::tree_walk::LinkModel for NodeOutput<'_, T, S, UNSNAPPED> {
    type Id = T::NodeId;
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> crate::tree_walk::AncestorLinks for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn following(&self, node: Self::Id) -> Option<Self::Id> { self.tree.next_sibling(node) }

    #[inline(always)]
    fn enclosing(&self, node: Self::Id) -> Option<Self::Id> { self.tree.parent(node) }

    #[inline(always)]
    fn same(&self, node: Self::Id, root: Self::Id) -> bool { node == root }
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> free_placement::PreflightModel for NodeOutput<'_, T, S, UNSNAPPED> {
    type Axis = Axis;
}

impl<T: TreeAdapter + ?Sized, S: Borrow<Snapper>, const UNSNAPPED: bool> free_placement::PreflightHost for NodeOutput<'_, T, S, UNSNAPPED> {
    #[inline(always)]
    fn style(&self, node: Self::Id) -> free_placement::PreflightStyle<Self::Axis> {
        let params = self.tree.node_layout_params(node);
        free_placement::PreflightStyle {
            disabled: params.disabled,
            free: params.free_placement,
            free_children: matches!(params.children_layout, ChildrenLayout::Free),
            wrap_cross_axis: match params.children_layout {
                ChildrenLayout::Wrap { axis, .. } => Some(axis.other()),
                _ => None,
            },
        }
    }

    #[inline(always)]
    fn first_child(&self, node: Self::Id) -> Option<Self::Id> { self.tree.first_child(node) }

    #[inline(always)]
    fn finals(&self, node: Self::Id) -> [u32; 2] {
        let flags = self.tree.node_layout_data(node).flags;
        [flags.check_state(X, Kind::Final), flags.check_state(Y, Kind::Final)]
    }

    #[inline(always)]
    fn flex_declarations(&self, node: Self::Id, axis: Self::Axis) -> [Option<bool>; 3] {
        DECLARED_SIZES.map(|kind| self.tree.read_size(node, axis, kind).map(|size| size.is_flex()))
    }

    #[inline(always)]
    fn declared_states(&self, node: Self::Id, axis: Self::Axis) -> [u32; 3] {
        let flags = self.tree.node_layout_data(node).flags;
        DECLARED_SIZES.map(|kind| flags.check_state(axis, kind))
    }
}

impl<T: Place + ?Sized> full_layout::Access for T {
    #[cfg(feature = "incremental")]
    type Change = (T::NodeId, NodeChange);

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn changes(&mut self) -> (&mut bool, &mut bool, &mut Vec<Self::Change>, &mut Vec<Self::Id>) {
        let data = self.layout_data();
        data.replay_pending = false;
        data.numeric_tape.invalidate::<RustVec>();
        data.numeric_wrap = None;
        data.sizing_warned = false;
        (&mut data.children_changed, &mut data.unknown_structure, &mut data.node_changes, &mut data.content_changes)
    }

    #[inline(always)]
    fn place_full(&mut self) -> placement_entry::RootPlacement<T::NodeId> { self.place_nodes_with::<false>(true) }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn keeps_rectangles(&self) -> bool { self.retains_output_rects() }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn tracking_topology(&mut self) -> &mut bool { &mut self.layout_data().track_topology }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn save_topology(&mut self) { self.remember_topology(); }
}

/// The placement part of the layout. Every `TreeAdapter` gets it from the blanket impl.
pub(crate) trait Place: Solve {
    fn solve_full<const REGISTERED_PIXELS: bool>(&mut self, window_size: Xy<f32>) {
        full_layout::run::<_, RustVec, REGISTERED_PIXELS>(self, window_size);
    }

    #[cfg(any(feature = "incremental", test))]
    fn place_nodes<const PARTIAL: bool>(&mut self) -> placement_entry::RootPlacement<Self::NodeId> {
        self.place_nodes_with::<PARTIAL>(false)
    }

    fn place_nodes_with<const PARTIAL: bool>(&mut self, fresh_placement: bool) -> placement_entry::RootPlacement<Self::NodeId> {
        // Select the unrounded implementation once so each write can publish its edges directly.
        if self.layout_data().pixel_scale.is_none() {
            let mut target = NodeOutput::<_, _, true> { tree: self, snapper: None::<Snapper>, fresh_placement };
            return placement_entry::root::<_, _, RustFloat, RustVec, 4, PARTIAL>(&mut target);
        }
        let mut target = NodeOutput::<_, _, false> { tree: self, snapper: None::<Snapper>, fresh_placement };
        placement_entry::root::<_, _, RustFloat, RustVec, 4, PARTIAL>(&mut target)
    }

    #[cfg(feature = "incremental")]
    fn place_children<const PARTIAL: bool>(&mut self, parent: Self::NodeId, first: Self::NodeId, rect: XyRect, origin: Xy<f32>, snapper: Option<&Snapper>) {
        let mut target = NodeOutput::<_, _, false> { tree: self, snapper, fresh_placement: false };
        placement_entry::children::<_, _, RustFloat, RustVec, 4, PARTIAL>(
            &mut target, parent, first, [rect.x, rect.y], [origin.x, origin.y],
        );
    }

    fn place_free_node(&mut self, node: Self::NodeId, parent_rect: XyRect) -> Result<(), FreePlacementError> {
        let mut target = NodeOutput::<_, _, false> { tree: self, snapper: None::<Snapper>, fresh_placement: false };
        placement_entry::free::<_, _, RustFloat, RustVec, 4>(&mut target, node, [parent_rect.x, parent_rect.y])
    }

    /// Place an appended leaf when the preceding stack items retain their sizes and
    /// positions. Both cached rectangles must be unrounded. The previous item, if
    /// present, is the last enabled, in-flow sibling.
    #[cfg(feature = "incremental")]
    fn place_appended_stack_leaf(&mut self, parent: Self::NodeId, child: Self::NodeId, parent_rect: XyRect,
        previous: Option<(Self::NodeId, XyRect)>) -> bool
    {
        let previous = previous.map(|(id, rect)| (id, [rect.x, rect.y]));
        let mut target = NodeOutput::<_, _, false> { tree: self, snapper: None::<&Snapper>, fresh_placement: false };
        placement_entry::append::<_, _, RustFloat>(&mut target, parent, child, [parent_rect.x, parent_rect.y], previous)
    }
}

impl<T: TreeAdapter + ?Sized> Place for T {}

#[inline]
fn grid_start_rect(origin: Xy<f32>, step: Xy<f32>, cell: Xy<f32>, size: Xy<f32>) -> XyRect {
    // Entering the cell's inner range adds its zero padding before sizing.
    #[cfg(target_arch = "x86_64")]
    {
        use std::arch::x86_64::*;
        // SAFETY: SSE2 is part of x86-64 and the array has four lanes.
        unsafe {
            let pack = |value: Xy<f32>| _mm_setr_ps(value.x, value.y, 0.0, 0.0);
            let offset = _mm_mul_ps(pack(cell), pack(step));
            let start = _mm_add_ps(_mm_add_ps(pack(origin), offset), _mm_setzero_ps());
            let end = _mm_add_ps(start, pack(size));
            let mut edges = [0.0; 4];
            _mm_storeu_ps(edges.as_mut_ptr(), _mm_unpacklo_ps(start, end));
            let [left, right, top, bottom] = edges;
            Xy::new([left, right], [top, bottom])
        }
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        Xy::new(
            geometry::grid_start_edges(origin.x, step.x, cell.x, size.x),
            geometry::grid_start_edges(origin.y, step.y, cell.y, size.y),
        )
    }
}

#[cfg(test)]
#[inline]
fn snap_rect(rect: XyRect, snapper: &Snapper) -> XyRect {
    let [left, right, top, bottom] = snapper.snap([rect.x[0], rect.x[1], rect.y[0], rect.y[1]]);
    Xy::new([left, right], [top, bottom])
}

#[path = "pixel_grid.rs"]
mod pixel_grid;
pub(crate) use pixel_grid::Snapper;


#[cfg(test)]
#[path = "placement_depth_tests.rs"]
mod placement_depth_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grid_start_rect_preserves_scalar_coordinates() {
        #[inline(never)]
        fn reference(origin: f32, step: f32, cell: f32, size: f32) -> [f32; 2] {
            geometry::grid_start_edges(origin, step, cell, size)
        }

        let coordinates = [
            0.0, -0.0, f32::from_bits(1), -f32::from_bits(1), 0.25, -8.75,
            16_777_216.0, f32::MAX, f32::MIN, f32::INFINITY, f32::NEG_INFINITY, f32::NAN,
        ];
        for origin in coordinates {
            for step in coordinates {
                for size in coordinates {
                    let actual = grid_start_rect(Xy::new(origin, step), Xy::new(step, origin),
                        Xy::new(-0.0, 3.0), Xy::new(size, -size));
                    let expected = Xy::new(reference(origin, step, -0.0, size),
                        reference(step, origin, 3.0, -size));
                    for (actual, expected) in actual.x.into_iter().chain(actual.y)
                        .zip(expected.x.into_iter().chain(expected.y))
                    {
                        if expected.is_nan() { assert!(actual.is_nan()); }
                        else { assert_eq!(actual.to_bits(), expected.to_bits()); }
                    }
                }
            }
        }
    }
    use rand::{Rng, SeedableRng};

    #[test]
    fn evenly_spaced_lines_use_the_full_gap_count() {
        // The integer denominator is exact before conversion to f32, including
        // counts that would round down if converted before adding the extra gap.
        for count in [16_777_217, u32::MAX - 1, u32::MAX] {
            let expected = 4_294_967_296.0 / (u64::from(count) + 1) as f32;
            let (start, gap) = geometry::line_start_and_gap::<RustFloat>(
                Arrange::SpaceEvenly, [0.0, 4_294_967_296.0], 0.0, count, 0.0,
            );
            assert_eq!((start, gap), (expected, expected));
        }
    }

    #[test]
    fn resuming_a_stack_preserves_cursor_rounding() {
        // The first rectangle's end rounds down to its start. Its size and trailing
        // gap still advance the cursor together by one representable coordinate.
        let start = (1_u32 << 24) as f32;
        let range = [start, start + 8.0];
        let mut cursor = start;
        let first = stack_line::place(&mut cursor, false, range, 1.0, [0.0; 2], 1.0);
        assert_eq!(first, [start; 2]);
        assert_eq!(cursor, start + 2.0);
        assert_eq!(stack_line::after_item(first[0], 1.0, 0.0, 1.0), cursor);
    }

    #[test]
    fn packed_snapping_matches_scalar_rounding() {
        let check = |edges: [f32; 4], scale: f32| {
            let snapped = snap_rect(Xy::new([edges[0], edges[1]], [edges[2], edges[3]]), &Snapper::new(scale));
            let actual = [snapped.x[0], snapped.x[1], snapped.y[0], snapped.y[1]];
            for (edge, actual) in edges.into_iter().zip(actual) {
                let expected = ((f64::from(edge) * f64::from(scale)).round() / f64::from(scale)) as f32;
                if expected.is_nan() {
                    assert!(actual.is_nan());
                } else {
                    assert_eq!(actual.to_bits(), expected.to_bits(), "edge={edge}, scale={scale}");
                }
            }
        };

        for scale in [0.125, 0.75, 1.0, 1.5, 2.0, f32::MIN_POSITIVE, f32::MAX] {
            for half_pixel in [0.5, 1.5, 2.5, 127.5, 4095.5, 8_388_607.5] {
                let edge = (half_pixel / f64::from(scale)) as f32;
                check([edge.next_down(), edge, edge.next_up(), -edge], scale);
            }
            check([-0.0, f32::from_bits(1), f32::INFINITY, f32::NEG_INFINITY], scale);
            check([f32::MAX, -f32::MAX, (1_u64 << 47) as f32, f32::NAN], scale);
        }

        let mut rng = rand::rngs::StdRng::seed_from_u64(0x52_47);
        for _ in 0..10_000 {
            let scale = f32::from_bits(rng.random_range(1..=f32::MAX.to_bits()));
            check(std::array::from_fn(|_| f32::from_bits(rng.random())), scale);
        }
    }
}
