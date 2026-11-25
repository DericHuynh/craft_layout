//! Placement of sibling runs using the host's measured slots and declarations.
#![allow(unexpected_cfgs)]

#[cfg(not(verus_keep_ghost))]
use crate::placement_geometry as geometry;
#[cfg(not(verus_keep_ghost))]
use super::placement_node as node;
#[cfg(not(verus_keep_ghost))]
use super::placement_batch as batch;
#[cfg(verus_keep_ghost)]
use super::{geometry, node, PlacementWork};
#[cfg(verus_keep_ghost)]
use crate::placement_batch::{clean_tail, kernel as batch};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use geometry::{Anchor, Arrange, FloatBounds, Pos, WindowOverflow};
use node::{Edges, NodeTarget};
use crate::declarations::{Axis, ChildrenLayout, LayoutParams};
#[cfg(not(verus_keep_ghost))]
use crate::solve::Kind;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::Kind;
use crate::vec_memory::VecMemory;
use crate::packed_stack_leaf::PreparedStackLeaf;
use crate::work_stack::WorkStack;
#[cfg(not(verus_keep_ghost))]
use super::stack_line::between_gaps;
#[cfg(verus_keep_ghost)]
use crate::stack_line::between_gaps;
#[cfg(not(verus_keep_ghost))]
use super::placement_walk;
#[cfg(verus_keep_ghost)]
use crate::placement_walk;

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Frame {
    pub edges: Edges,
    pub origin: [f32; 2],
    pub padding: Edges,
    pub flipped: [bool; 2],
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
#[derive(Clone, Copy)]
pub(crate) struct Branch<I> {
    pub parent: I,
    pub first: I,
    pub rect: Edges,
    pub origin: [f32; 2],
    pub partial: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct FreeStyle {
    pub pos: [Pos; 2],
    pub anchor: [Anchor; 2],
    pub overflow: [WindowOverflow; 2],
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait FreePlacementInputs<I> {
    spec fn free_declarations(&self) -> spec_fn(I) -> LayoutParams;
    spec fn placement_window(&self) -> [f32; 2];
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait FreePlacementInputs<I> {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait SiblingTarget<I>: NodeTarget<I> + FreePlacementInputs<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(sibling => ensures sibling == self.links().next(id), no_unwind))]
    fn next_sibling(&self, id: I) -> Option<I>;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns (self.hidden())(id), no_unwind))]
    fn disabled(&self, id: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.solved_size(id), no_unwind))]
    fn size(&self, id: I) -> [f32; 2];

    #[cfg_attr(verus_keep_ghost, verus_spec(style =>
        ensures style == crate::placement_adapter::free_style_from((self.free_declarations())(id)), no_unwind
    ))]
    fn free_style(&self, id: I) -> FreeStyle;

    #[cfg_attr(verus_keep_ghost, verus_spec(style =>
        ensures style.disabled == (self.hidden())(id), no_unwind
    ))]
    fn align_style(&self, id: I) -> StackStyle;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn margins(&self, id: I, x: bool) -> [f32; 2];

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn declaration(&self, id: I, x: bool, kind: Kind) -> Option<crate::declarations::Size>;

    #[cfg_attr(verus_keep_ghost, verus_spec(size =>
        ensures size == (old(self).placement_window())@[if x { 0 } else { 1 }],
            final(self).placement_window() == old(self).placement_window(),
            final(self).free_declarations() == old(self).free_declarations(),
            final(self).links() == old(self).links(), final(self).written() == old(self).written(),
            final(self).hidden() == old(self).hidden(),
                final(self).plain() == old(self).plain(),
            final(self).rectangles() == old(self).rectangles(), final(self).rounding() == old(self).rounding(),
            forall|id: I| #[trigger] final(self).mark(id) == old(self).mark(id),
        no_unwind
    ))]
    fn window_size(&mut self, x: bool) -> f32;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct StackStyle {
    pub disabled: bool,
    pub free: bool,
    pub pos: [Pos; 2],
    pub anchor: [Anchor; 2],
    pub margin: Edges,
    pub zero_margins: bool,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait StackDataModel {
    spec fn placement_mark(&self) -> Option<PlacementWork>;
    spec fn enabled(&self) -> bool;
    spec fn pixel_size(&self) -> [f32; 2];
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait StackDataModel {}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn aligned_start_style(params: LayoutParams, cross: Axis) -> bool {
    &&& !params.disabled && !params.free_placement
    &&& params.margin.x[0].is_zero() && params.margin.x[1].is_zero()
    &&& params.margin.y[0].is_zero() && params.margin.y[1].is_zero()
    &&& (if cross is X { params.position.x } else { params.position.y }) is Start
}

pub(crate) open spec fn plain_start_child<I, T: StackTarget<I>>(tree: &T, id: I, horizontal: bool) -> bool {
    (tree.start_aligned())(id, horizontal) && tree.links().first(id).is_none()
}
}

/// The packed values read before advancing the sibling link on the Stack path.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait StackData: StackDataModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.pixel_size(), no_unwind))]
    fn stack_size(&self) -> [f32; 2];

    #[cfg_attr(verus_keep_ghost, verus_spec(cached => ensures cached ==> self.enabled(), no_unwind))]
    fn cached_start(&self) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(dirty => ensures dirty == dirty_work(self.placement_mark()), no_unwind))]
    fn dirty(&self) -> bool;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait StackTarget<I>: SiblingTarget<I> + batch::BatchTarget<I, [f32; 4]> {
    type Data: StackData;

    #[cfg_attr(verus_keep_ghost, verus_spec(data =>
        ensures data.placement_mark() == self.mark(id), data.enabled() == !(self.hidden())(id),
            data.pixel_size() == self.solved_size(id), no_unwind
    ))]
    fn stack_data(&self, id: I) -> &Self::Data;

    #[cfg_attr(verus_keep_ghost, verus_spec(params =>
        ensures params.disabled == (self.hidden())(id),
            (self.start_aligned())(id, true) == aligned_start_style(*params, Axis::Y),
            (self.start_aligned())(id, false) == aligned_start_style(*params, Axis::X),
        no_unwind
    ))]
    fn stack_params(&self, id: I) -> &LayoutParams;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn stack_align(params: &LayoutParams) -> StackStyle;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn prepared_styles(&self) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn snapping(&self) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn full_unsnapped(&self) -> bool;
}

/// Operations provided by the checked stack-line kernel instantiated for `f32`.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait StackMath: crate::prepare_frame::FrameFloat {
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn negate(value: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns adjusted::<Self>(x, margin), no_unwind))]
    fn with_margin(x: f32, margin: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(edges =>
        ensures (edges, *final(cursor)) == axis_step::<Self>(*old(cursor), flipped, range, size, margin, gap),
        no_unwind
    ))]
    fn place(cursor: &mut f32, flipped: bool, range: [f32; 2], size: f32, margin: [f32; 2], gap: f32) -> [f32; 2];

    #[cfg_attr(verus_keep_ghost, verus_spec(edges =>
        ensures (edges, *final(cursor)) == start_step::<Self>(*old(cursor), cross_start, x, size, gap),
        no_unwind
    ))]
    fn place_start(cursor: &mut f32, cross_start: f32, x: bool, size: [f32; 2], gap: f32) -> Edges;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns stack_advance::<Self>(start, size, trailing, gap), no_unwind))]
    fn after_item(start: f32, size: f32, trailing: f32, gap: f32) -> f32;
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct WrapCursor<I> {
    pub x: bool,
    pub arrange: Arrange,
    pub spacing: f32,
    pub line_spacing: f32,
    pub next_line: Option<I>,
    pub ready_cross: bool,
    pub ready_start: bool,
    pub cross_position: f32,
    pub cross_edges: [f32; 2],
    pub main_position: f32,
    pub auto_share: f32,
    pub gap: f32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct PlacedLine<I> {
    pub next: Option<I>,
    pub main: f32,
    pub cross: f32,
    pub count: u32,
    pub auto_edges: u32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait WrapTarget<I>: SiblingTarget<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(ready => ensures self.plain() ==> !ready, no_unwind))]
    fn ready_wrap_lines(&self, id: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(ready =>
        ensures ready ==> enabled_siblings(self.links(), self.hidden(), self.links().first(id)), no_unwind
    ))]
    fn ready_wrap_start(&self, id: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn wrap_line_height(&self, id: I) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (next == Some(id)), no_unwind))]
    fn same_cursor(&self, next: Option<I>, id: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn wrap_in_flow(&self, id: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn wrap_marked(&self, id: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn wrap_slot(&self, id: I, x: bool, kind: Kind) -> f32;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct BlockStyle {
    pub free: bool,
    pub inline_margin: [f32; 2],
    pub auto: [bool; 2],
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct BlockEdges {
    pub padding: [f32; 2],
    pub collapse: bool,
    pub zero_minimum: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct BlockItemInputs {
    pub bounds: BlockEdges,
    pub height: f32,
    pub margins: [f32; 2],
    pub children_empty: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait BlockTarget<I>: SiblingTarget<I> {
    type Flow: Copy;
    type Item;
    type Nested: Copy;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn block_style(&self, id: I) -> BlockStyle;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn margin_index(&self, id: I) -> Option<usize>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).links() == old(self).links(), final(self).hidden() == old(self).hidden(),
            final(self).plain() == old(self).plain(),
            final(self).written() == old(self).written(), final(self).rectangles() == old(self).rectangles(),
            forall|id: I| #[trigger] final(self).mark(id) == old(self).mark(id),
        no_unwind
    ))]
    fn nested_margin(&mut self, index: usize) -> Option<Self::Nested>;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn block_item_inputs(&self, id: I) -> BlockItemInputs;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn block_from_edges(
        margins: [f32; 2], height: f32, adjoins: bool, children_empty: bool, nested: Option<Self::Nested>,
    ) -> Self::Item;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn append_block(flow: &mut Self::Flow, item: Self::Item) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn block_parent_edges(&self, id: I) -> BlockEdges;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn block_from_parent(before: bool, after: bool) -> Self::Flow;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct GridStyle {
    pub align: StackStyle,
    pub span: [u16; 2],
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait GridTarget<I>: SiblingTarget<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn grid_lines(&self, parent: I) -> [f32; 2];

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn grid_cell(&self, id: I) -> [f32; 2];

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn grid_style(&self, id: I) -> GridStyle;

    /// Fixed-width hardware entry for the forward Start-aligned fast path.
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn grid_start(origin: [f32; 2], step: [f32; 2], cell: [f32; 2], size: [f32; 2]) -> Edges;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct ParentStyle {
    pub layout: ChildrenLayout,
    pub padding: Edges,
    pub flipped: [bool; 2],
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait ParentModel<I> {
    spec fn parent_layout(&self, id: I) -> ParentStyle;
    spec fn packed_rows(&self) -> Seq<PreparedStackLeaf<I>>;
    spec fn packed_span(&self, parent: I) -> Option<[usize; 2]>;
    spec fn uniform_rows(&self, parent: I) -> Option<([f32; 2], Seq<I>)>;
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait ParentModel<I> {}
#[cfg(not(verus_keep_ghost))]
impl<I, T: ?Sized> ParentModel<I> for T {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait ParentTarget<I>: StackTarget<I> + WrapTarget<I> + BlockTarget<I> + GridTarget<I> + ParentModel<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(ready =>
        ensures self.plain() ==> !ready,
            ready ==> {
                let pair = self.links().leaf_pair(id);
                &&& pair.is_some()
                &&& !(self.hidden())(pair.unwrap().0) && !(self.hidden())(pair.unwrap().1)
            },
        no_unwind
    ))]
    fn ready_pair(&self, id: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures final(self).links() == old(self).links(), final(self).written() == old(self).written(),
            final(self).parent_layout(id) == old(self).parent_layout(id),
            final(self).packed_rows() == old(self).packed_rows(),
            final(self).rectangles() == old(self).rectangles(),
            final(self).plain() == old(self).plain(), final(self).hidden() == old(self).hidden(),
            old(self).plain() ==> result.is_none(),
            result.is_some() ==> {
                let [start, end] = result.unwrap();
                &&& result == old(self).packed_span(id)
                &&& start < end <= old(self).packed_rows().len()
                &&& leaf_path(old(self).links(), old(self).hidden(), old(self).links().first(id),
                    packed_ids(old(self).packed_rows(), start as int, end as int), None)
            },
            forall|other: I| #[trigger] final(self).mark(other) == old(self).mark(other),
        no_unwind
    ))]
    fn packed_leaf_span(&mut self, id: I) -> Option<[usize; 2]>;

    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (left == right), no_unwind))]
    fn same_packed_id(&self, left: I, right: I) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures final(self).links() == old(self).links(), final(self).written() == old(self).written(),
            final(self).parent_layout(id) == old(self).parent_layout(id),
            final(self).rectangles() == old(self).rectangles(),
            final(self).plain() == old(self).plain(), final(self).hidden() == old(self).hidden(),
            old(self).plain() ==> result.is_none(),
            result.is_some() ==> {
                let rows = result.unwrap().1@;
                &&& old(self).uniform_rows(id) == Some((result.unwrap().0, rows))
                &&& leaf_path(old(self).links(), old(self).hidden(), old(self).links().first(id), rows, None)
            },
            forall|other: I| #[trigger] final(self).mark(other) == old(self).mark(other),
        no_unwind
    ))]
    fn take_uniform_leaves(&mut self, id: I) -> Option<([f32; 2], Vec<I>)>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).links() == old(self).links(), final(self).written() == old(self).written(),
            final(self).rectangles() == old(self).rectangles(),
            final(self).hidden() == old(self).hidden(), final(self).plain() == old(self).plain(),
            forall|other: I| #[trigger] final(self).mark(other) == old(self).mark(other),
        no_unwind
    ))]
    fn recycle_uniform_leaves(&mut self, ids: Vec<I>);

    #[cfg_attr(verus_keep_ghost, verus_spec(rows =>
        ensures final(self).links() == old(self).links(), final(self).written() == old(self).written(),
            final(self).rectangles() == old(self).rectangles(), rows@ == old(self).packed_rows(),
            final(self).hidden() == old(self).hidden(), final(self).plain() == old(self).plain(),
            forall|other: I| #[trigger] final(self).mark(other) == old(self).mark(other),
        no_unwind
    ))]
    fn take_packed_leaves(&mut self) -> Vec<PreparedStackLeaf<I>>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).links() == old(self).links(), final(self).written() == old(self).written(),
            final(self).rectangles() == old(self).rectangles(), final(self).packed_rows() == rows@,
            final(self).hidden() == old(self).hidden(), final(self).plain() == old(self).plain(),
            forall|other: I| #[trigger] final(self).mark(other) == old(self).mark(other),
        no_unwind
    ))]
    fn put_packed_leaves(&mut self, rows: Vec<PreparedStackLeaf<I>>);

    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.parent_layout(id), no_unwind))]
    fn parent_style(&self, id: I) -> ParentStyle;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn prefers_batch(&self) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn placed_children(&self, id: I) -> u32;

}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait RootTarget<I>: SiblingTarget<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).links() == old(self).links(), final(self).hidden() == old(self).hidden(),
            final(self).plain() == old(self).plain(), final(self).written() == old(self).written(),
            final(self).rectangles() == old(self).rectangles(),
            final(self).root_key() == old(self).root_key(),
            final(self).solved_size(old(self).root_key()) == old(self).solved_size(old(self).root_key()),
            final(self).configured_scale() == old(self).configured_scale(),
            forall|id: I| #[trigger] final(self).mark(id) == old(self).mark(id),
        no_unwind
    ))]
    fn clear_scale_changed(&mut self);

    #[cfg_attr(verus_keep_ghost, verus_spec(root =>
        ensures self.links().cost(Some(root)) > 0, root == self.root_key(), no_unwind
    ))]
    fn root_id(&self) -> I;

    #[cfg_attr(verus_keep_ghost, verus_spec(scale =>
        ensures final(self).links() == old(self).links(), final(self).hidden() == old(self).hidden(),
            final(self).plain() == old(self).plain(), final(self).written() == old(self).written(),
            final(self).rectangles() == old(self).rectangles(),
            final(self).root_key() == old(self).root_key(),
            scale == old(self).configured_scale(),
            forall|id: I| #[trigger] final(self).mark(id) == old(self).mark(id),
        no_unwind
    ))]
    fn pixel_scale(&mut self) -> Option<f32>;
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
enum Mode<I, F> {
    Free,
    Stack { head: I, x: bool, position: f32, gap: f32, auto_share: Option<f32>, batch: bool, paired_leaves: bool },
    Wrap(WrapCursor<I>),
    Block(F),
    Grid { parent: I, spacing: [f32; 2] },
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct Siblings<I, F> {
    next: Option<I>,
    frame: Frame,
    partial: bool,
    mode: Mode<I, F>,
}

#[cfg(verus_keep_ghost)]
verus! {
/// The math model keeps each binary32 operation in `stack_line` in source order.
pub(crate) open spec fn adjusted<M: crate::prepare_frame::FrameFloat + ?Sized>(start: f32, margin: f32) -> f32 {
    if M::word(margin) & 0x7fff_ffffu32 == 0 { start } else { M::sum(start, margin) }
}

pub(crate) open spec fn stack_advance<M: crate::prepare_frame::FrameFloat + ?Sized>(start: f32, size: f32, after: f32, gap: f32) -> f32 {
    M::sum(start, M::sum(adjusted::<M>(size, after), gap))
}

pub(crate) open spec fn axis_step<M: crate::prepare_frame::FrameFloat + ?Sized>(
    cursor: f32, flipped: bool, range: [f32; 2], size: f32, margin: [f32; 2], gap: f32,
) -> ([f32; 2], f32) {
    let start = adjusted::<M>(cursor, if flipped { margin[1] } else { margin[0] });
    let end = M::difference(M::sum(range[0], range[1]), start);
    let edges = if flipped { [M::difference(end, size), end] } else { [start, M::sum(start, size)] };
    (edges, stack_advance::<M>(start, size, if flipped { margin[0] } else { margin[1] }, gap))
}

pub(crate) open spec fn start_step<M: crate::prepare_frame::FrameFloat + ?Sized>(
    cursor: f32, cross_start: f32, x: bool, size: [f32; 2], gap: f32,
) -> (Edges, f32) {
    let (left, top) = if x { (cursor, cross_start) } else { (cross_start, cursor) };
    let edges = [[left, M::sum(left, size[0])], [top, M::sum(top, size[1])]];
    (edges, M::sum(cursor, M::sum(if x { size[0] } else { size[1] }, gap)))
}

pub(crate) open spec fn put_rect<I, T: node::NodeModel<I>>(
    rects: Map<I, (Edges, Edges)>, id: I, raw: Edges, origin: [f32; 2],
) -> Map<I, (Edges, Edges)> {
    rects.insert(id, (node::published_edges::<I, T>(raw),
        node::published_edges::<I, T>(node::relative_edges::<I, T>(raw, origin))))
}

/// Each cached row executes the same ordered binary32 arithmetic before the
/// common absolute and parent-local publication path.
#[verifier::opaque]
spec fn draw_rows<I, T: node::NodeModel<I>, R, State>(
    initial: Map<I, (Edges, Edges)>, rows: Seq<R>, state: State, origin: [f32; 2],
    step: spec_fn(R, State) -> (I, Edges, State),
) -> (Map<I, (Edges, Edges)>, State)
    decreases rows.len(),
{
    if rows.len() == 0 {
        (initial, state)
    } else {
        let (prior, cursor) = draw_rows::<I, T, R, State>(initial, rows.drop_last(), state, origin, step);
        let (id, rect, next) = step(rows.last(), cursor);
        (put_rect::<I, T>(prior, id, rect, origin), next)
    }
}

spec fn solved_start_step<I, T: node::NodeModel<I>, M: StackMath>(
    source: &T, cross_start: f32, x: bool, gap: f32,
) -> spec_fn(I, f32) -> (I, Edges, f32) {
    |id: I, cursor: f32| {
        let (edges, next) = start_step::<M>(cursor, cross_start, x, source.solved_size(id), gap);
        (id, (source.rounding())(edges), next)
    }
}

pub(crate) closed spec fn paired_start_rects<I, T: node::NodeModel<I>, M: StackMath>(
    source: &T, ids: Seq<I>, cursor: f32, frame: &Frame, x: bool, gap: f32,
) -> (Map<I, (Edges, Edges)>, f32) {
    let cross = if x { 1int } else { 0int };
    let start = geometry::padded_start::<M>(frame.edges[cross], frame.padding[cross][0]);
    draw_rows::<I, T, _, _>(source.rectangles(), ids, cursor, frame.origin,
        solved_start_step::<I, T, M>(source, start, x, gap))
}

fn save_rect_cursor<I, T: node::NodeModel<I>>(source: &T, cursor: f32)
    -> (saved: Ghost<(Map<I, (Edges, Edges)>, f32)>)
    ensures saved@ == (source.rectangles(), cursor),
    no_unwind
{ Ghost((source.rectangles(), cursor)) }

proof fn paired_rect_push<I, T: node::NodeModel<I>, M: StackMath>(
    source: &T, ids: Seq<I>, id: I, cursor: f32, frame: &Frame, x: bool, gap: f32,
)
    ensures ({
        let (prior, position) = paired_start_rects::<I, T, M>(source, ids, cursor, frame, x, gap);
        let cross = if x { 1int } else { 0int };
        let start = geometry::padded_start::<M>(frame.edges[cross], frame.padding[cross][0]);
        let (raw, next) = start_step::<M>(position, start, x, source.solved_size(id), gap);
        paired_start_rects::<I, T, M>(source, ids.push(id), cursor, frame, x, gap)
            == (put_rect::<I, T>(prior, id, (source.rounding())(raw), frame.origin), next)
    }),
{
    reveal(draw_rows);
    assert(ids.push(id).drop_last() =~= ids);
}

spec fn uniform_step<I, M: StackMath>(
    cross_start: f32, x: bool, size: [f32; 2], gap: f32,
) -> spec_fn(I, f32) -> (I, Edges, f32) {
    |id: I, cursor: f32| {
        let (edges, next) = start_step::<M>(cursor, cross_start, x, size, gap);
        (id, edges, next)
    }
}

pub(crate) open spec fn packed_stack_step<I, M: StackMath>(cross_start: f32, x: bool)
    -> spec_fn(PreparedStackLeaf<I>, f32) -> (I, Edges, f32)
{
    |row: PreparedStackLeaf<I>, position: f32| {
        let from = adjusted::<M>(position, row.main_leading);
        let across = adjusted::<M>(cross_start, row.cross_leading);
        let (left, top) = if x { (from, across) } else { (across, from) };
        let edges = [[left, M::sum(left, row.size[0])], [top, M::sum(top, row.size[1])]];
        (row.id, edges, M::sum(from, row.advance))
    }
}

pub(crate) open spec fn forward_step<M: StackMath>(
    cursor: f32, cross_start: f32, margin: Edges, x: bool, size: [f32; 2], gap: f32,
) -> (Edges, f32) {
    let (main, cross): (int, int) = if x { (0, 1) } else { (1, 0) };
    let across = adjusted::<M>(cross_start, margin[cross][0]);
    let other = [across, M::sum(across, size[cross])];
    let (along, next) = axis_step::<M>(cursor, false, [0.0, 0.0], size[main], margin[main], gap);
    (if x { [along, other] } else { [other, along] }, next)
}

pub(crate) proof fn packed_stack_matches_forward<I, M: StackMath>(
    row: PreparedStackLeaf<I>, cursor: f32, cross_start: f32, margin: Edges, x: bool, gap: f32,
)
    requires ({
        let (main, cross): (int, int) = if x { (0, 1) } else { (1, 0) };
        &&& row.main_leading == margin[main][0]
        &&& row.cross_leading == margin[cross][0]
        &&& row.advance == M::sum(adjusted::<M>(row.size[main], margin[main][1]), gap)
    }),
    ensures ({
        let (edges, next) = forward_step::<M>(cursor, cross_start, margin, x, row.size, gap);
        packed_stack_step::<I, M>(cross_start, x)(row, cursor) == (row.id, edges, next)
    }),
{
    if x {} else {}
}

fn save_cursor(value: f32) -> (out: Ghost<f32>)
    ensures out@ == value,
    no_unwind
{ Ghost(value) }

pub(crate) open spec fn packed_wrap_step<I, M: StackMath>(main_start: f32, line_spacing: f32, x: bool)
    -> spec_fn(PreparedStackLeaf<I>, (f32, f32, f32)) -> (I, Edges, (f32, f32, f32))
{
    |row: PreparedStackLeaf<I>, state: (f32, f32, f32)| {
        let (position, cross_position, cross_start) = state;
        let (main, cross_next, cross) = if M::word(row.main_leading) & 0x7fff_ffffu32 == 0 {
            state
        } else {
            (main_start, M::sum(cross_position, M::sum(row.cross_leading, line_spacing)), M::sum(cross_position, 0.0))
        };
        let (left, top) = if x { (main, cross) } else { (cross, main) };
        let edges = [[left, M::sum(left, row.size[0])], [top, M::sum(top, row.size[1])]];
        (row.id, edges, (M::sum(main, row.advance), cross_next, cross))
    }
}

pub(crate) proof fn packed_wrap_matches_forward<I, M: StackMath>(
    row: PreparedStackLeaf<I>, state: (f32, f32, f32), main_start: f32,
    line_start: bool, line_height: f32, spacing: f32, line_spacing: f32, x: bool,
)
    requires M::word(0.0) & 0x7fff_ffffu32 == 0,
        line_start == (M::word(row.main_leading) & 0x7fff_ffffu32 != 0),
        line_start ==> row.cross_leading == line_height,
        row.advance == M::sum(if x { row.size[0] } else { row.size[1] }, spacing),
    ensures ({
        let (cursor, cross_position, prior_cross) = state;
        let (cross_edges, after_cross) = axis_step::<M>(cross_position, false, [0.0, 0.0], line_height,
            [0.0, 0.0], line_spacing);
        let main = if line_start { main_start } else { cursor };
        let cross = if line_start { M::sum(cross_edges[0], 0.0) } else { prior_cross };
        let (rect, after_main) = start_step::<M>(main, cross, x, row.size, spacing);
        packed_wrap_step::<I, M>(main_start, line_spacing, x)(row, state)
            == (row.id, rect, (after_main, if line_start { after_cross } else { cross_position }, cross))
    }),
{
    if line_start {} else {}
}

spec fn packed_rects<I, T: ParentTarget<I>, M: StackMath>(
    tree: &T, branch: &Branch<I>, start: usize, end: usize,
) -> Map<I, (Edges, Edges)> {
    let style = tree.parent_layout(branch.parent);
    let rows = tree.packed_rows().subrange(start as int, end as int);
    match style.layout {
        ChildrenLayout::Stack { axis, arrange: Arrange::Start, .. } => {
            let x = axis is X;
            let (main, cross): (int, int) = if x { (0, 1) } else { (1, 0) };
            let position = geometry::padded_start::<M>(branch.rect[main], style.padding[main][0]);
            let cross_start = geometry::padded_start::<M>(branch.rect[cross], style.padding[cross][0]);
            draw_rows::<I, T, _, _>(tree.rectangles(), rows, position, branch.origin, packed_stack_step::<I, M>(cross_start, x)).0
        },
        ChildrenLayout::Wrap { axis, arrange: Arrange::Start, line_spacing, .. } => {
            let x = axis is X;
            let (main, cross): (int, int) = if x { (0, 1) } else { (1, 0) };
            let position = geometry::padded_start::<M>(branch.rect[main], style.padding[main][0]);
            let cross_start = geometry::padded_start::<M>(branch.rect[cross], style.padding[cross][0]);
            draw_rows::<I, T, _, _>(tree.rectangles(), rows, (position, cross_start, 0.0), branch.origin,
                packed_wrap_step::<I, M>(position, line_spacing, x)).0
        },
        _ => tree.rectangles(),
    }
}

pub(crate) closed spec fn uniform_rects<I, T: ParentTarget<I>, M: StackMath>(
    tree: &T, branch: &Branch<I>, size: [f32; 2], ids: Seq<I>,
) -> Map<I, (Edges, Edges)> {
    let style = tree.parent_layout(branch.parent);
    if let ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing } = style.layout {
        let x = axis is X;
        let (main, cross): (int, int) = if x { (0, 1) } else { (1, 0) };
        let position = geometry::padded_start::<M>(branch.rect[main], style.padding[main][0]);
        let cross_start = geometry::padded_start::<M>(branch.rect[cross], style.padding[cross][0]);
        draw_rows::<I, T, _, _>(tree.rectangles(), ids, position, branch.origin, uniform_step::<I, M>(cross_start, x, size, spacing)).0
    } else { tree.rectangles() }
}

proof fn uniform_fold_uses_solved_sizes<I, T: node::NodeModel<I>, M: StackMath>(
    source: &T, frame: &Frame, ids: Seq<I>, cursor: f32, x: bool, size: [f32; 2], gap: f32,
)
    requires forall|i: int| 0 <= i < ids.len() ==> {
            let resolved = source.solved_size(#[trigger] ids[i]);
            &&& M::word(resolved[0]) == M::word(size[0])
            &&& M::word(resolved[1]) == M::word(size[1])
        },
        forall|edges: Edges| #[trigger] (source.rounding())(edges) == edges,
    ensures ({
        let cross = if x { 1int } else { 0int };
        let start = geometry::padded_start::<M>(frame.edges[cross], frame.padding[cross][0]);
        paired_start_rects::<I, T, M>(source, ids, cursor, frame, x, gap)
            == draw_rows::<I, T, _, _>(source.rectangles(), ids, cursor, frame.origin,
                uniform_step::<I, M>(start, x, size, gap))
    }),
    decreases ids.len(),
{
    reveal(draw_rows);
    if ids.len() > 0 {
        let prefix = ids.drop_last();
        assert forall|i: int| 0 <= i < prefix.len() implies {
            let resolved = source.solved_size(#[trigger] prefix[i]);
            &&& M::word(resolved[0]) == M::word(size[0])
            &&& M::word(resolved[1]) == M::word(size[1])
        } by {
            assert(prefix[i] == ids[i]);
        };
        uniform_fold_uses_solved_sizes::<I, T, M>(source, frame, prefix, cursor, x, size, gap);
        assert(ids.last() == ids[ids.len() - 1]);
        let resolved = source.solved_size(ids.last());
        crate::prepare_frame::same_float_word::<M>(resolved[0], size[0]);
        crate::prepare_frame::same_float_word::<M>(resolved[1], size[1]);
        assert(resolved =~= size);
    }
}

pub(crate) proof fn uniform_matches_paired_recipe<I, T: ParentTarget<I>, M: StackMath>(
    source: &T, branch: &Branch<I>, ids: Seq<I>, size: [f32; 2], x: bool, spacing: f32,
)
    requires source.parent_layout(branch.parent).layout == (ChildrenLayout::Stack {
            axis: if x { Axis::X } else { Axis::Y }, arrange: Arrange::Start, spacing,
        }),
        forall|i: int| 0 <= i < ids.len() ==> {
            let resolved = source.solved_size(#[trigger] ids[i]);
            &&& M::word(resolved[0]) == M::word(size[0])
            &&& M::word(resolved[1]) == M::word(size[1])
        },
        forall|edges: Edges| #[trigger] (source.rounding())(edges) == edges,
    ensures ({
        let style = source.parent_layout(branch.parent);
        let frame = Frame { edges: branch.rect, origin: branch.origin, padding: style.padding, flipped: style.flipped };
        let main = if x { 0int } else { 1int };
        let cursor = geometry::padded_start::<M>(frame.edges[main], frame.padding[main][0]);
        uniform_rects::<I, T, M>(source, branch, size, ids)
            == paired_start_rects::<I, T, M>(source, ids, cursor, &frame, x, spacing).0
    }),
{
    let style = source.parent_layout(branch.parent);
    let frame = Frame { edges: branch.rect, origin: branch.origin, padding: style.padding, flipped: style.flipped };
    let main = if x { 0int } else { 1int };
    let cursor = geometry::padded_start::<M>(frame.edges[main], frame.padding[main][0]);
    uniform_fold_uses_solved_sizes::<I, T, M>(source, &frame, ids, cursor, x, size, spacing);
}

pub(crate) open spec fn dirty_work(work: Option<PlacementWork>) -> bool {
    work.is_some() && work != Some(PlacementWork::Clean)
}

spec fn leaf_prefix<I>(links: node::PlacementLinks<I>, start: Option<I>, count: nat) -> (Seq<I>, Option<I>)
    decreases count,
{
    if count == 0 {
        (Seq::empty(), start)
    } else {
        let (prior, next) = leaf_prefix(links, start, (count - 1) as nat);
        match next {
            Some(node) => (prior.push(node), links.next(node)),
            None => (prior, None),
        }
    }
}

/// The consumed list is an actual physical sibling prefix of enabled leaves.
#[verifier::opaque]
pub(crate) open spec fn leaf_path<I>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool,
    first: Option<I>, rows: Seq<I>, next: Option<I>,
) -> bool
    decreases rows.len(),
{
    if rows.len() == 0 {
        first == next
    } else {
        let id = rows.first();
        &&& first == Some(id)
        &&& !hidden(id) && links.first(id).is_none()
        &&& leaf_path(links, hidden, links.next(id), rows.drop_first(), next)
    }
}

pub(crate) proof fn leaf_path_push<I>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool,
    first: Option<I>, rows: Seq<I>, next: I,
)
    requires leaf_path(links, hidden, first, rows, Some(next)), !hidden(next), links.first(next).is_none(),
    ensures leaf_path(links, hidden, first, rows.push(next), links.next(next)),
    decreases rows.len(),
{
    reveal_with_fuel(leaf_path, 2);
    let published = rows.push(next);
    assert(published.len() == rows.len() + 1);
    if rows.len() > 0 {
        leaf_path_push(links, hidden, links.next(rows.first()), rows.drop_first(), next);
        assert(published.first() == rows.first());
        assert(published.drop_first() =~= rows.drop_first().push(next));
        assert(leaf_path(links, hidden, links.next(rows.first()), published.drop_first(), links.next(next)));
    } else {
        assert(first == Some(next));
        assert(published.first() == next);
        assert(published.drop_first() =~= Seq::<I>::empty());
        assert(leaf_path(links, hidden, links.next(next), published.drop_first(), links.next(next)));
    }
    assert(leaf_path(links, hidden, first, published, links.next(next)));
}

/// A consumed prefix identifies the next child of the same physical roster.
proof fn roster_prefix<I>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool,
    first: Option<I>, all: Seq<I>, prefix: Seq<I>, next: Option<I>)
    requires leaf_path(links, hidden, first, all, None), leaf_path(links, hidden, first, prefix, next),
    ensures prefix.len() <= all.len(), prefix == all.take(prefix.len() as int),
        next == if prefix.len() < all.len() { Some(all[prefix.len() as int]) } else { None },
    decreases prefix.len(),
{
    reveal(leaf_path);
    if prefix.len() == 0 {
        assert(prefix =~= all.take(0));
    } else {
        assert(all.len() > 0);
        let head = prefix.first();
        assert(head == all.first());
        let tail = prefix.drop_first();
        let remaining = all.drop_first();
        roster_prefix(links, hidden, links.next(head), remaining, tail, next);
        assert(tail.len() + 1 == prefix.len());
        assert(remaining.len() + 1 == all.len());
        assert(prefix.len() <= all.len());
        let consumed = all.take(prefix.len() as int);
        assert(consumed.len() == prefix.len());
        assert forall |i: int| 0 <= i < prefix.len() implies #[trigger] prefix[i] == consumed[i] by {
            if i == 0 {
                assert(prefix[i] == head && all[i] == head);
            } else {
                assert(prefix[i] == tail[i - 1]);
                assert(tail[i - 1] == remaining[i - 1]);
                assert(remaining[i - 1] == all[i]);
            }
        };
        assert(prefix =~= consumed);
        if prefix.len() < all.len() {
            assert(tail.len() < remaining.len());
            assert(remaining[tail.len() as int] == all[prefix.len() as int]);
        }
    }
}

pub(crate) proof fn paired_consumes_admitted_roster<I, T: StackTarget<I>>(
    source: &T, first: Option<I>, all: Seq<I>, prefix: Seq<I>, stop: Option<I>, x: bool,
)
    requires leaf_path(source.links(), source.hidden(), first, all, None),
        leaf_path(source.links(), source.hidden(), first, prefix, stop),
        forall|i: int| 0 <= i < all.len() ==> plain_start_child(source, #[trigger] all[i], x),
        stop.is_some() ==> !plain_start_child(source, stop.unwrap(), x),
    ensures stop.is_none(), prefix == all,
{
    roster_prefix(source.links(), source.hidden(), first, all, prefix, stop);
    if let Some(remaining) = stop {
        assert(remaining == all[prefix.len() as int]);
        assert(plain_start_child(source, remaining, x));
    }
    assert(prefix =~= all);
}

fn start_leaf_prefix() -> (count: Ghost<nat>)
    ensures count@ == 0,
    no_unwind
{ Ghost(0nat) }

fn step_leaf_prefix(count: Ghost<nat>) -> (following: Ghost<nat>)
    ensures following@ == count@ + 1,
    no_unwind
{ Ghost(count@ + 1) }

pub(crate) open spec fn consistent_cursor<I>(links: node::PlacementLinks<I>, next: Option<I>) -> bool {
    next.is_some() ==> links.cost(next) > 0
}

#[verifier::opaque]
pub(crate) closed spec fn enabled_siblings<I>(
    links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool, next: Option<I>,
) -> bool
    decreases links.cost(next),
{
    match next {
        Some(id) if links.covers(id) => !hidden(id) && enabled_siblings(links, hidden, links.next(id)),
        None => true,
        _ => false,
    }
}

proof fn advance_enabled_sibling<I>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool, id: I)
    requires links.covers(id), enabled_siblings(links, hidden, Some(id)),
    ensures !hidden(id), enabled_siblings(links, hidden, links.next(id)),
{
    reveal(enabled_siblings);
}

pub(crate) proof fn complete_leaf_path_is_enabled<I>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool,
    first: Option<I>, rows: Seq<I>)
    requires links.finite(), consistent_cursor(links, first), leaf_path(links, hidden, first, rows, None),
    ensures enabled_siblings(links, hidden, first),
    decreases rows.len(),
{
    reveal(leaf_path);
    reveal(enabled_siblings);
    if rows.len() > 0 {
        let id = rows.first();
        complete_leaf_path_is_enabled(links, hidden, links.next(id), rows.drop_first());
    }
}

pub(crate) closed spec fn wrap_admitted<I, F>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool, cursor: Siblings<I, F>) -> bool {
    match cursor.mode {
        Mode::Wrap(wrap) => wrap.ready_start && enabled_siblings(links, hidden, cursor.next),
        _ => false,
    }
}

pub(crate) closed spec fn cursor_admitted<I, F>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool, cursor: Siblings<I, F>) -> bool {
    &&& ordinary_siblings(cursor, cursor.partial) || wrap_admitted(links, hidden, cursor)
    &&& match cursor.mode { Mode::Stack { head, .. } => links.cost(Some(head)) > 0, _ => true }
}

pub(crate) closed spec fn ordinary_siblings<I, F>(cursor: Siblings<I, F>, partial: bool) -> bool {
    match cursor.mode {
        Mode::Stack { batch, .. } => partial ==> !batch,
        Mode::Wrap(wrap) => !wrap.ready_start,
        _ => true,
    }
}

pub(crate) open spec fn sibling_progress<I>(
    links: node::PlacementLinks<I>, before: Option<I>, next: Option<I>, branch: Option<Branch<I>>,
) -> bool {
    &&& consistent_cursor(links, next)
    &&& match branch {
        Some(branch) => links.cost(Some(branch.first)) > 0
            && links.cost(Some(branch.first)) + links.cost(next) < links.cost(before),
        None => next.is_none(),
    }
}

pub(crate) struct SiblingWrites<I> {
    pub writes: Seq<I>,
    pub resume: Option<I>,
    pub branch: Option<(I, I, bool)>,
}

#[verifier::reject_recursive_types(I)]
pub(crate) struct SiblingInputs<I> {
    pub links: node::PlacementLinks<I>,
    pub hidden: spec_fn(I) -> bool,
    pub work: spec_fn(I) -> Option<PlacementWork>,
}

pub(crate) open spec fn sibling_inputs<I, T: NodeTarget<I>>(tree: &T) -> SiblingInputs<I> {
    SiblingInputs { links: tree.links(), hidden: tree.hidden(), work: |id: I| tree.mark(id) }
}

/// All placement marks at and after a preorder rank are still original.
#[verifier::opaque]
pub(crate) closed spec fn marks_from<I>(before: SiblingInputs<I>, after: SiblingInputs<I>, first: nat) -> bool {
    forall|id: I| before.links.rank(id) >= first ==> #[trigger] (after.work)(id) == (before.work)(id)
}

pub(crate) open spec fn cursor_rank<I>(links: node::PlacementLinks<I>, initial: Option<I>, next: Option<I>) -> nat {
    match next {
        Some(id) => links.rank(id),
        None => match initial { Some(id) => links.limit(id), None => 0 },
    }
}

pub(crate) open spec fn marks_after_siblings<I, T: NodeTarget<I>>(
    before: &T, after: &T, first: Option<I>, branch: Option<Branch<I>>,
) -> bool {
    let rank = match branch {
        Some(branch) => before.links().rank(branch.parent) + 1,
        None => cursor_rank(before.links(), first, None),
    };
    marks_from(sibling_inputs(before), sibling_inputs(after), rank)
}

#[verifier::opaque]
spec fn writes_before<I>(links: node::PlacementLinks<I>, writes: Seq<I>, rank: nat) -> bool {
    forall|i: int| 0 <= i < writes.len() ==> links.rank(#[trigger] writes[i]) < rank
}

pub(crate) proof fn preserved_marks<I>(before: SiblingInputs<I>, after: SiblingInputs<I>, first: nat)
    requires forall|id: I| #[trigger] (after.work)(id) == (before.work)(id),
    ensures marks_from(before, after, first),
{
    reveal(marks_from);
}

proof fn later_marks<I>(before: SiblingInputs<I>, after: SiblingInputs<I>, first: nat, later: nat)
    requires first <= later, marks_from(before, after, first),
    ensures marks_from(before, after, later),
{
    reveal(marks_from);
}

proof fn mark_at<I>(before: SiblingInputs<I>, after: SiblingInputs<I>, first: nat, id: I)
    requires first <= before.links.rank(id), marks_from(before, after, first),
    ensures (after.work)(id) == (before.work)(id),
{
    reveal(marks_from);
}

proof fn empty_writes_before<I>(links: node::PlacementLinks<I>, rank: nat)
    ensures writes_before(links, Seq::<I>::empty(), rank),
{
    reveal(writes_before);
}

proof fn later_writes<I>(links: node::PlacementLinks<I>, writes: Seq<I>, first: nat, later: nat)
    requires writes_before(links, writes, first), first <= later,
    ensures writes_before(links, writes, later),
{
    reveal(writes_before);
}

proof fn extend_staged<I>(links: node::PlacementLinks<I>, prior: Seq<I>, current: I, next: Seq<I>, until: nat)
    requires writes_before(links, prior, links.rank(current)), links.rank(current) < until,
        next.len() == 0 || next == prior || next == prior.push(current),
    ensures writes_before(links, prior, until), writes_before(links, next, until),
{
    reveal(writes_before);
    assert forall|i: int| 0 <= i < next.len() implies links.rank(#[trigger] next[i]) < until by {
        if i < prior.len() { assert(next[i] == prior[i]); }
        else { assert(next[i] == current); }
    };
}

proof fn staged_marks<I>(
    before: SiblingInputs<I>, after: SiblingInputs<I>, staged: Seq<I>, current: Option<I>, first: nat,
)
    requires writes_before(before.links, staged, first),
        current.is_some() ==> before.links.rank(current.unwrap()) < first,
        forall|id: I| current != Some(id) && !staged.contains(id)
            ==> #[trigger] (after.work)(id) == (before.work)(id),
    ensures marks_from(before, after, first),
{
    reveal(marks_from);
    reveal(writes_before);
    assert forall|id: I| before.links.rank(id) >= first implies #[trigger] (after.work)(id) == (before.work)(id) by {
        assert(current != Some(id));
        if staged.contains(id) {
            let index = choose|i: int| 0 <= i < staged.len() && staged[i] == id;
            assert(before.links.rank(staged[index]) < first);
        }
    };
}

pub(crate) open spec fn branch_keys<I>(branch: Option<Branch<I>>) -> Option<(I, I, bool)> {
    match branch { Some(b) => Some((b.parent, b.first, b.partial)), None => None }
}

pub(crate) open spec fn executed_sibling_plan<I, T: NodeTarget<I>>(
    before: &T, after: &T, first: Option<I>, resume: Option<I>, branch: Option<Branch<I>>, partial: bool,
) -> bool {
    let expected = sibling_writes(sibling_inputs(before), first, partial);
    &&& after.written() == before.written() + expected.writes
    &&& resume == expected.resume
    &&& branch_keys(branch) == expected.branch
    &&& marks_after_siblings(before, after, first, branch)
}

pub(crate) open spec fn sibling_write<I>(inputs: SiblingInputs<I>, id: I, partial: bool) -> Seq<I> {
    if !(inputs.hidden)(id) && node::writes((inputs.work)(id), partial) { seq![id] } else { Seq::empty() }
}

pub(crate) open spec fn sibling_child<I>(inputs: SiblingInputs<I>, id: I, partial: bool) -> Option<(I, I, bool)> {
    if !(inputs.hidden)(id) && node::visits((inputs.work)(id), partial) {
        match inputs.links.first(id) {
            Some(child) => Some((id, child, partial && !node::writes((inputs.work)(id), partial))),
            None => None,
        }
    } else {
        None
    }
}

#[verifier::opaque]
pub(crate) closed spec fn sibling_writes<I>(
    inputs: SiblingInputs<I>, cursor: Option<I>, partial: bool,
) -> SiblingWrites<I>
    decreases inputs.links.cost(cursor),
{
    match cursor {
        Some(id) if inputs.links.covers(id) => {
            let writes = sibling_write(inputs, id, partial);
            let branch = sibling_child(inputs, id, partial);
            let following = inputs.links.next(id);
            if branch.is_some() {
                SiblingWrites { writes, resume: following, branch }
            } else {
                let tail = sibling_writes(inputs, following, partial);
                SiblingWrites { writes: writes + tail.writes, ..tail }
            }
        },
        _ => SiblingWrites { writes: Seq::empty(), resume: None, branch: None },
    }
}

/// Ordered geometry writes from a sibling suffix and its selected subtrees.
#[verifier::opaque]
pub(crate) closed spec fn forest_writes<I>(
    inputs: SiblingInputs<I>, cursor: Option<I>, partial: bool,
) -> Seq<I>
    decreases inputs.links.cost(cursor),
{
    match cursor {
        Some(id) if inputs.links.covers(id) => {
            let prefix = sibling_write(inputs, id, partial);
            let children = match sibling_child(inputs, id, partial) {
                Some((_, child, child_partial)) => forest_writes(inputs, Some(child), child_partial),
                None => Seq::empty(),
            };
            prefix + children + forest_writes(inputs, inputs.links.next(id), partial)
        },
        _ => Seq::empty(),
    }
}

pub(crate) open spec fn subtree_writes<I>(inputs: SiblingInputs<I>, root: I, partial: bool) -> Seq<I> {
    let children = match sibling_child(inputs, root, partial) {
        Some((_, child, child_partial)) => forest_writes(inputs, Some(child), child_partial),
        None => Seq::empty(),
    };
    sibling_write(inputs, root, partial) + children
}

pub(crate) proof fn forest_starts_with_subtree<I>(inputs: SiblingInputs<I>, head: I, partial: bool)
    requires inputs.links.covers(head),
    ensures forest_writes(inputs, Some(head), partial) == subtree_writes(inputs, head, partial)
        + forest_writes(inputs, inputs.links.next(head), partial),
        forest_writes(inputs, None, partial).len() == 0,
{
    reveal(forest_writes);
}

proof fn sibling_step<I>(inputs: SiblingInputs<I>, head: I, partial: bool)
    requires inputs.links.covers(head),
    ensures ({
        let next = inputs.links.next(head);
        let own = sibling_write(inputs, head, partial);
        let branch = sibling_child(inputs, head, partial);
        let tail = sibling_writes(inputs, next, partial);
        sibling_writes(inputs, Some(head), partial) == if branch.is_some() {
            SiblingWrites { writes: own, resume: next, branch }
        } else {
            SiblingWrites { writes: own + tail.writes, ..tail }
        }
    }),
{
    reveal(sibling_writes);
}

/// Splitting a walk at a real mode's next descent preserves callback order.
pub(crate) proof fn sibling_plan_splits_forest<I>(
    inputs: SiblingInputs<I>, cursor: Option<I>, partial: bool,
)
    requires inputs.links.finite(), consistent_cursor(inputs.links, cursor),
    ensures ({
        let step = sibling_writes(inputs, cursor, partial);
        let children = match step.branch {
            Some((_, child, child_partial)) => forest_writes(inputs, Some(child), child_partial),
            None => Seq::empty(),
        };
        forest_writes(inputs, cursor, partial) == step.writes + children + forest_writes(inputs, step.resume, partial)
    }),
    decreases inputs.links.cost(cursor),
{
    if let Some(id) = cursor {
        assert(inputs.links.covers(id));
        sibling_step(inputs, id, partial);
        forest_starts_with_subtree(inputs, id, partial);
        let next = inputs.links.next(id);
        if sibling_child(inputs, id, partial).is_none() {
            sibling_plan_splits_forest(inputs, next, partial);
            let step = sibling_writes(inputs, next, partial);
            let children = match step.branch {
                Some((_, child, child_partial)) => forest_writes(inputs, Some(child), child_partial),
                None => Seq::empty(),
            };
            let prefix = sibling_write(inputs, id, partial);
            let resume = forest_writes(inputs, step.resume, partial);
            assert(forest_writes(inputs, next, partial) == step.writes + children + resume);
            assert(prefix + (step.writes + children + resume) =~= prefix + step.writes + children + resume);
        }
    } else {
        reveal(sibling_writes);
        reveal(forest_writes);
    }
}

proof fn leaves_split_siblings<I>(inputs: SiblingInputs<I>, first: Option<I>, rows: Seq<I>, next: Option<I>)
    requires inputs.links.finite(), consistent_cursor(inputs.links, first),
        leaf_path(inputs.links, inputs.hidden, first, rows, next),
    ensures ({
        let original = sibling_writes(inputs, first, false);
        let following = sibling_writes(inputs, next, false);
        &&& original.writes == rows + following.writes
        &&& original.resume == following.resume && original.branch == following.branch
    }),
    decreases rows.len(),
{
    reveal(leaf_path);
    reveal(sibling_writes);
    if rows.len() == 0 {
        assert(rows =~= Seq::<I>::empty());
    } else {
        let id = rows.first();
        assert(inputs.links.covers(id));
        leaves_split_siblings(inputs, inputs.links.next(id), rows.drop_first(), next);
        let tail = sibling_writes(inputs, next, false).writes;
        assert(sibling_writes(inputs, first, false).writes =~= rows + tail);
    }
}

proof fn complete_leaf_forest<I>(inputs: SiblingInputs<I>, first: Option<I>, rows: Seq<I>)
    requires inputs.links.finite(), consistent_cursor(inputs.links, first),
        leaf_path(inputs.links, inputs.hidden, first, rows, None),
    ensures forest_writes(inputs, first, false) == rows,
{
    leaves_split_siblings(inputs, first, rows, None);
    sibling_plan_splits_forest(inputs, first, false);
    reveal(sibling_writes);
    reveal(forest_writes);
}

proof fn packets_keep_unvisited_marks<I>(first: SiblingInputs<I>, second: SiblingInputs<I>, cursor: Option<I>, partial: bool)
    requires first.links.finite(), first.links == second.links, first.hidden == second.hidden,
        consistent_cursor(first.links, cursor),
        partial && cursor.is_some() ==> marks_from(first, second, first.links.rank(cursor.unwrap())),
    ensures sibling_writes(first, cursor, partial) == sibling_writes(second, cursor, partial),
    decreases first.links.cost(cursor),
{
    reveal(sibling_writes);
    if let Some(id) = cursor {
        assert(first.links.covers(id));
        if partial { mark_at(first, second, first.links.rank(id), id); }
        if sibling_child(first, id, partial).is_none() {
            let next = first.links.next(id);
            if partial && next.is_some() {
                later_marks(first, second, first.links.rank(id), first.links.rank(next.unwrap()));
            }
            packets_keep_unvisited_marks(first, second, next, partial);
        }
    }
}

proof fn packet_stays_in_scope<I>(inputs: SiblingInputs<I>, first: I, partial: bool)
    requires inputs.links.finite(), inputs.links.cost(Some(first)) > 0,
    ensures ({
        let links = inputs.links;
        let step = sibling_writes(inputs, Some(first), partial);
        match step.branch {
            Some((parent, child, child_partial)) => {
                &&& child_partial ==> partial
                &&& links.first(parent) == Some(child)
                &&& links.cost(Some(parent)) > 0
                &&& links.rank(first) <= links.rank(parent) < links.rank(child)
                &&& links.limit(child) <= links.limit(first)
                &&& step.resume.is_some() ==> links.limit(child) <= links.rank(step.resume.unwrap())
                    < links.limit(first) && links.limit(step.resume.unwrap()) == links.limit(first)
            },
            None => step.resume.is_none(),
        }
    }),
    decreases inputs.links.cost(Some(first)),
{
    reveal(sibling_writes);
    let links = inputs.links;
    assert(links.covers(first));
    if let Some((parent, child, _)) = sibling_child(inputs, first, partial) {
        assert(parent == first && links.first(first) == Some(child));
        assert(links.rank(first) < links.rank(child));
        assert(links.limit(child) == links.end(first));
    } else if let Some(next) = links.next(first) {
        packet_stays_in_scope(inputs, next, partial);
        assert(links.rank(first) < links.rank(next));
        assert(links.limit(first) == links.limit(next));
        assert(sibling_writes(inputs, Some(first), partial).branch == sibling_writes(inputs, Some(next), partial).branch);
        assert(sibling_writes(inputs, Some(first), partial).resume == sibling_writes(inputs, Some(next), partial).resume);
    } else {
        assert(sibling_writes(inputs, None, partial).branch.is_none());
        assert(sibling_writes(inputs, None, partial).resume.is_none());
    }
}

proof fn forests_keep_unvisited_marks<I>(first: SiblingInputs<I>, second: SiblingInputs<I>, cursor: Option<I>, partial: bool)
    requires first.links.finite(), first.links == second.links, first.hidden == second.hidden,
        consistent_cursor(first.links, cursor),
        partial && cursor.is_some() ==> marks_from(first, second, first.links.rank(cursor.unwrap())),
    ensures forest_writes(first, cursor, partial) == forest_writes(second, cursor, partial),
    decreases first.links.cost(cursor),
{
    reveal(forest_writes);
    if let Some(id) = cursor {
        assert(first.links.covers(id));
        if partial { mark_at(first, second, first.links.rank(id), id); }
        if let Some((_, child, child_partial)) = sibling_child(first, id, partial) {
            if child_partial { later_marks(first, second, first.links.rank(id), first.links.rank(child)); }
            forests_keep_unvisited_marks(first, second, Some(child), child_partial);
        }
        let next = first.links.next(id);
        if partial && next.is_some() {
            later_marks(first, second, first.links.rank(id), first.links.rank(next.unwrap()));
        }
        forests_keep_unvisited_marks(first, second, next, partial);
    }
}

pub(crate) proof fn subtrees_keep_unvisited_marks<I>(first: SiblingInputs<I>, second: SiblingInputs<I>, root: I, partial: bool)
    requires first.links.finite(), first.links == second.links, first.hidden == second.hidden,
        first.links.cost(Some(root)) > 0,
        partial ==> marks_from(first, second, first.links.rank(root)),
    ensures subtree_writes(first, root, partial) == subtree_writes(second, root, partial),
{
    assert(first.links.covers(root));
    if partial { mark_at(first, second, first.links.rank(root), root); }
    if let Some((_, child, child_partial)) = sibling_child(first, root, partial) {
        if child_partial { later_marks(first, second, first.links.rank(root), first.links.rank(child)); }
        forests_keep_unvisited_marks(first, second, Some(child), child_partial);
    }
}

spec fn frontier_writes<I, F>(inputs: SiblingInputs<I>, cursors: Seq<Siblings<I, F>>) -> Seq<I>
    decreases cursors.len(),
{
    if cursors.len() == 0 {
        Seq::empty()
    } else {
        forest_writes(inputs, cursors.first().next, cursors.first().partial) + frontier_writes(inputs, cursors.drop_first())
    }
}

#[verifier::opaque]
spec fn pending_scopes<I, F>(links: node::PlacementLinks<I>, pending: Seq<Siblings<I, F>>) -> bool {
    &&& forall|i: int| 0 <= i < pending.len() ==> (#[trigger] pending[i]).next.is_some()
    &&& forall|i: int, j: int| 0 <= i < j < pending.len() ==> {
        let earlier = #[trigger] pending[j];
        let later = #[trigger] pending[i];
        links.limit(earlier.next.unwrap()) <= links.rank(later.next.unwrap())
    }
}

#[verifier::opaque]
spec fn scope_before_pending<I, F>(
    links: node::PlacementLinks<I>, cursor: Siblings<I, F>, pending: Seq<Siblings<I, F>>,
) -> bool {
    cursor.next.is_some() && forall|i: int| 0 <= i < pending.len()
        ==> links.limit(cursor.next.unwrap()) <= links.rank((#[trigger] pending[i]).next.unwrap())
}

proof fn marks_from_both<I>(first: SiblingInputs<I>, middle: SiblingInputs<I>, last: SiblingInputs<I>, a: nat, b: nat, later: nat)
    requires first.links == middle.links, marks_from(first, middle, a), marks_from(middle, last, b), a <= later, b <= later,
    ensures marks_from(first, last, later),
{
    reveal(marks_from);
    assert forall|id: I| first.links.rank(id) >= later implies #[trigger] (last.work)(id) == (first.work)(id) by {
        assert((last.work)(id) == (middle.work)(id));
        assert((middle.work)(id) == (first.work)(id));
    };
}

proof fn replacing_cursor<I, F>(
    inputs: SiblingInputs<I>, previous: Siblings<I, F>, resume: Siblings<I, F>,
    child: Option<Siblings<I, F>>, pending: Seq<Siblings<I, F>>,
)
    requires inputs.links.finite(), consistent_cursor(inputs.links, previous.next),
        ({
            let selected = sibling_writes(inputs, previous.next, previous.partial);
            &&& selected.resume == resume.next
            &&& match selected.branch {
                Some((_, first, partial)) => child.is_some() && child.unwrap().next == Some(first)
                    && child.unwrap().partial == partial,
                None => child.is_none(),
            }
        }), resume.partial == previous.partial,
    ensures ({
        let selected = sibling_writes(inputs, previous.next, previous.partial);
        let prior = placement_walk::frontier(Some(previous), pending);
        let next = placement_walk::next_frontier(child, resume, resume.next.is_some(), pending);
        frontier_writes(inputs, prior) == selected.writes + frontier_writes(inputs, next)
    }),
{
    let partial = previous.partial;
    let selected = sibling_writes(inputs, previous.next, partial);
    let incoming = placement_walk::pending_in_visit_order(pending);
    let prior = placement_walk::frontier(Some(previous), pending);
    let next = placement_walk::next_frontier(child, resume, resume.next.is_some(), pending);
    assert(prior.first() == previous);
    assert(prior.drop_first() =~= incoming);
    reveal(frontier_writes);
    assert(frontier_writes(inputs, prior) == forest_writes(inputs, previous.next, partial) + frontier_writes(inputs, incoming));
    sibling_plan_splits_forest(inputs, previous.next, partial);
    if let Some(inside) = child {
        let later = placement_walk::frontier(if resume.next.is_some() { Some(resume) } else { None }, pending);
        assert(next.first() == inside);
        assert(next.drop_first() =~= later);
        assert(frontier_writes(inputs, next) == forest_writes(inputs, inside.next, inside.partial) + frontier_writes(inputs, later));
        if resume.next.is_some() {
            assert(later.first() == resume);
            assert(later.drop_first() =~= incoming);
            assert(frontier_writes(inputs, later) == forest_writes(inputs, resume.next, partial) + frontier_writes(inputs, incoming));
        } else {
            reveal(forest_writes);
        }
        assert(selected.branch.is_some());
        no_descent_no_resume(inputs, previous.next, partial);
        assert(selected.branch.unwrap().2 == inside.partial);
        assert(selected.branch.unwrap().1 == inside.next.unwrap());
        assert(forest_writes(inputs, previous.next, partial) == selected.writes
            + forest_writes(inputs, inside.next, inside.partial) + forest_writes(inputs, resume.next, partial));
        assert(selected.writes + frontier_writes(inputs, next) =~= frontier_writes(inputs, prior));
    } else {
        reveal(sibling_writes);
        reveal(forest_writes);
        assert(selected.branch.is_none() ==> selected.resume.is_none()) by {
            no_descent_no_resume(inputs, previous.next, partial);
        };
        reveal_with_fuel(frontier_writes, 2);
        assert(selected.writes + frontier_writes(inputs, next) =~= frontier_writes(inputs, prior));
    }
}

proof fn replacing_forced_cursor<I, F>(
    inputs: SiblingInputs<I>, previous: Siblings<I, F>, resume: Siblings<I, F>,
    child: Option<Siblings<I, F>>, pending: Seq<Siblings<I, F>>,
    before: Seq<I>, after: Seq<I>,
)
    requires !previous.partial, !resume.partial,
        child.is_some() ==> !child.unwrap().partial,
        child.is_none() ==> resume.next.is_none(),
        ({
            let children = if let Some(inside) = child { forest_writes(inputs, inside.next, false) } else { Seq::empty() };
            after + children + forest_writes(inputs, resume.next, false)
                == before + forest_writes(inputs, previous.next, false)
        }),
    ensures ({
        let prior = placement_walk::frontier(Some(previous), pending);
        let next = placement_walk::next_frontier(child, resume, resume.next.is_some(), pending);
        after + frontier_writes(inputs, next) == before + frontier_writes(inputs, prior)
    }),
{
    let incoming = placement_walk::pending_in_visit_order(pending);
    let prior = placement_walk::frontier(Some(previous), pending);
    let next = placement_walk::next_frontier(child, resume, resume.next.is_some(), pending);
    assert(prior.first() == previous);
    assert(prior.drop_first() =~= incoming);
    reveal(frontier_writes);
    assert(frontier_writes(inputs, prior) == forest_writes(inputs, previous.next, false) + frontier_writes(inputs, incoming));
    let siblings = forest_writes(inputs, resume.next, false);
    let children = if let Some(inside) = child { forest_writes(inputs, inside.next, false) } else { Seq::empty() };
    if let Some(inside) = child {
        let later = placement_walk::frontier(if resume.next.is_some() { Some(resume) } else { None }, pending);
        assert(next.first() == inside);
        assert(next.drop_first() =~= later);
        if resume.next.is_some() {
            assert(later.first() == resume);
            assert(later.drop_first() =~= incoming);
        } else {
            reveal(forest_writes);
            assert(later == incoming);
        }
        assert(frontier_writes(inputs, later) =~= siblings + frontier_writes(inputs, incoming));
        assert(frontier_writes(inputs, next) == children + frontier_writes(inputs, later));
    } else {
        reveal(forest_writes);
    }
    assert(frontier_writes(inputs, next) =~= children + siblings + frontier_writes(inputs, incoming));
    assert(after + frontier_writes(inputs, next) =~= (after + children + siblings) + frontier_writes(inputs, incoming));
}

proof fn no_descent_no_resume<I>(inputs: SiblingInputs<I>, cursor: Option<I>, partial: bool)
    requires inputs.links.finite(), consistent_cursor(inputs.links, cursor),
    ensures sibling_writes(inputs, cursor, partial).branch.is_none()
        ==> sibling_writes(inputs, cursor, partial).resume.is_none(),
        sibling_writes(inputs, cursor, partial).branch.is_some()
            && sibling_writes(inputs, cursor, partial).branch.unwrap().2
            ==> partial,
    decreases inputs.links.cost(cursor),
{
    reveal(sibling_writes);
    if let Some(id) = cursor {
        assert(inputs.links.covers(id));
        if sibling_child(inputs, id, partial).is_none() {
            no_descent_no_resume(inputs, inputs.links.next(id), partial);
        }
    }
}

proof fn empty_sibling_plan<I>(inputs: SiblingInputs<I>, partial: bool)
    ensures sibling_writes(inputs, None, partial) == (SiblingWrites {
        writes: Seq::<I>::empty(), resume: None, branch: None,
    }),
{
    reveal(sibling_writes);
}

/// Close one sibling step after the mode has supplied its actual write. The
/// mode's numerical expressions need no unfolding to establish the roster.
proof fn consume_sibling<I>(
    initial: SiblingInputs<I>, before: SiblingInputs<I>, after: SiblingInputs<I>,
    id: I, next: Option<I>, prefix: Seq<I>, emitted: Seq<I>, cutoff: nat, partial: bool,
)
    requires before.links.finite(), before.links.covers(id), next == before.links.next(id),
        initial.links == before.links, after.links == before.links, after.hidden == before.hidden,
        marks_from(initial, before, before.links.rank(id)),
        marks_from(before, after, before.links.rank(id) + 1),
        before.links.rank(id) < cutoff,
        next.is_some() ==> cutoff == before.links.rank(next.unwrap()),
        emitted == prefix + sibling_write(before, id, partial),
    ensures ({
        let plan = sibling_writes(before, Some(id), partial);
        let child = sibling_child(before, id, partial);
        if child.is_some() {
            &&& plan.branch == child && plan.resume == next
            &&& emitted == prefix + plan.writes
            &&& marks_from(initial, after, before.links.rank(id) + 1)
        } else {
            let tail = sibling_writes(after, next, partial);
            &&& plan.branch == tail.branch && plan.resume == tail.resume
            &&& emitted + tail.writes == prefix + plan.writes
            &&& marks_from(initial, after, cutoff)
        }
    }),
{
    reveal(sibling_writes);
    let rank = before.links.rank(id) + 1;
    if sibling_child(before, id, partial).is_some() {
        marks_from_both(initial, before, after, before.links.rank(id), rank, rank);
    } else {
        marks_from_both(initial, before, after, before.links.rank(id), rank, cutoff);
        later_marks(before, after, rank, cutoff);
        packets_keep_unvisited_marks(before, after, next, partial);
        let plan = sibling_writes(before, Some(id), partial);
        let tail = sibling_writes(after, next, partial);
        assert(emitted + tail.writes =~= prefix + plan.writes);
    }
}

fn saved_sibling<I, T: NodeTarget<I>>(tree: &T) -> (out: Ghost<(SiblingInputs<I>, Seq<I>)>)
    ensures out@ == (sibling_inputs(tree), tree.written()),
    no_unwind
{ Ghost((sibling_inputs(tree), tree.written())) }

fn saved_next<I: Copy>(next: &Option<I>) -> (out: Ghost<Option<I>>)
    ensures out@ == *next,
    no_unwind
{ Ghost(*next) }

fn projected_leaf_prefix<I: Copy, T: StackTarget<I>>(
    tree: &T, previous: Ghost<(SiblingInputs<I>, Seq<I>)>, first: Ghost<Option<I>>, next: &Option<I>,
) -> (rows: Ghost<Seq<I>>)
    requires exists|count: nat| {
        let prefix = #[trigger] leaf_prefix(previous@.0.links, first@, count);
        &&& prefix.1 == *next
        &&& tree.written() == previous@.1 + prefix.0
        &&& leaf_path(previous@.0.links, previous@.0.hidden, first@, prefix.0, *next)
    },
    ensures tree.written() == previous@.1 + rows@,
        leaf_path(previous@.0.links, previous@.0.hidden, first@, rows@, *next),
    no_unwind
{
    let ghost count = choose|count: nat| {
        let prefix = #[trigger] leaf_prefix(previous@.0.links, first@, count);
        &&& prefix.1 == *next
        &&& tree.written() == previous@.1 + prefix.0
        &&& leaf_path(previous@.0.links, previous@.0.hidden, first@, prefix.0, *next)
    };
    Ghost(leaf_prefix(previous@.0.links, first@, count).0)
}

fn empty_staged_writes<I>() -> (out: Ghost<Seq<I>>)
    ensures out@ == Seq::<I>::empty(),
    no_unwind
{ Ghost(Seq::empty()) }

spec fn staged_writes<I: Copy>(batch: Option<batch::Buffer<I, [f32; 4]>>) -> Seq<I> {
    match batch {
        Some(buffer) => buffer.ids@.take(buffer.pending.len as int),
        None => Seq::empty(),
    }
}

fn saved_staged_writes<I: Copy>(batch: &Option<batch::Buffer<I, [f32; 4]>>) -> (out: Ghost<Seq<I>>)
    ensures out@ == staged_writes(*batch),
    no_unwind
{ Ghost(staged_writes(*batch)) }

fn saved_branch_keys<I>(branch: &Option<Branch<I>>) -> (out: Ghost<Option<(I, I, bool)>>)
    ensures out@ == branch_keys(*branch),
    no_unwind
{ Ghost(branch_keys(*branch)) }

pub(crate) open spec fn packed_ids<I>(rows: Seq<PreparedStackLeaf<I>>, start: int, end: int) -> Seq<I> {
    Seq::new((end - start) as nat, |i: int| rows[start + i].id)
}

pub(crate) proof fn packed_ids_push<I>(rows: Seq<PreparedStackLeaf<I>>, start: int, index: int)
    requires 0 <= start <= index < rows.len(),
    ensures packed_ids(rows, start, index + 1) == packed_ids(rows, start, index).push(rows[index].id),
{
    assert(packed_ids(rows, start, index + 1) =~= packed_ids(rows, start, index).push(rows[index].id));
}

spec fn wrote_group<I>(before: Seq<I>, after: Seq<I>, first: I) -> bool {
    &&& after.len() > before.len()
    &&& after.take(before.len() as int) == before
    &&& after[before.len() as int] == first
}

#[verifier::opaque]
spec fn pending_cost<I, F>(links: node::PlacementLinks<I>, stack: Seq<Siblings<I, F>>) -> nat
    decreases stack.len(),
{
    if stack.len() == 0 { 0 }
    else { pending_cost(links, stack.drop_last()) + links.cost(stack.last().next) }
}

proof fn empty_pending_scope<I, F>(links: node::PlacementLinks<I>, cursor: Siblings<I, F>, pending: Seq<Siblings<I, F>>)
    requires pending.len() == 0, cursor.next.is_some(),
    ensures pending_scopes(links, pending), scope_before_pending(links, cursor, pending),
{
    reveal(pending_scopes);
    reveal(scope_before_pending);
}

proof fn pending_scope_step<I, F>(
    links: node::PlacementLinks<I>, previous: Siblings<I, F>, resume: Siblings<I, F>,
    child: Option<Siblings<I, F>>, upcoming: Siblings<I, F>,
    prior: Seq<Siblings<I, F>>, pending: Seq<Siblings<I, F>>,
)
    requires pending_scopes(links, prior), scope_before_pending(links, previous, prior),
        if let Some(inside) = child {
            &&& inside == upcoming && inside.next.is_some()
            &&& links.limit(inside.next.unwrap()) <= links.limit(previous.next.unwrap())
            &&& if let Some(next) = resume.next {
                &&& pending == prior.push(resume)
                &&& links.limit(inside.next.unwrap()) <= links.rank(next)
                &&& links.limit(next) == links.limit(previous.next.unwrap())
            } else { pending == prior }
        } else {
            &&& prior.len() > 0 && upcoming == prior.last()
            &&& pending == prior.drop_last()
        },
    ensures pending_scopes(links, pending), scope_before_pending(links, upcoming, pending),
        child.is_none() ==> links.limit(previous.next.unwrap()) <= links.rank(upcoming.next.unwrap()),
{
    reveal(pending_scopes);
    reveal(scope_before_pending);
    if child.is_none() {
        assert(upcoming == prior[prior.len() - 1]);
    }
    assert forall |i: int| 0 <= i < pending.len() implies {
        let item = #[trigger] pending[i];
        &&& item.next.is_some()
        &&& links.limit(upcoming.next.unwrap()) <= links.rank(item.next.unwrap())
    } by {
        if i < prior.len() {
            assert(pending[i] == prior[i]);
            if child.is_none() {
                assert(i < prior.len() - 1);
            }
        } else {
            assert(pending[i] == resume);
        }
    };
    assert forall |i: int, j: int| 0 <= i < j < pending.len() implies {
        let earlier = #[trigger] pending[j];
        let later = #[trigger] pending[i];
        links.limit(earlier.next.unwrap()) <= links.rank(later.next.unwrap())
    } by {
        assert(pending[i] == prior[i]);
        if j < prior.len() {
            assert(pending[j] == prior[j]);
        } else {
            assert(pending[j] == resume);
        }
    };
}

proof fn pending_cost_step<I, F>(
    links: node::PlacementLinks<I>, previous: Siblings<I, F>, resume: Siblings<I, F>,
    child: Option<Siblings<I, F>>, upcoming: Siblings<I, F>,
    prior: Seq<Siblings<I, F>>, pending: Seq<Siblings<I, F>>,
)
    requires links.cost(previous.next) > 0,
        forall |i: int| 0 <= i < prior.len() ==> links.cost((#[trigger] prior[i]).next) > 0,
        if let Some(inside) = child {
            &&& upcoming == inside && links.cost(inside.next) > 0
            &&& links.cost(inside.next) + links.cost(resume.next) < links.cost(previous.next)
            &&& if resume.next.is_some() {
                &&& links.cost(resume.next) > 0
                &&& pending == prior.push(resume)
            } else { pending == prior }
        } else {
            &&& prior.len() > 0 && upcoming == prior.last()
            &&& pending == prior.drop_last()
        },
    ensures links.cost(upcoming.next) > 0,
        forall |i: int| 0 <= i < pending.len() ==> links.cost((#[trigger] pending[i]).next) > 0,
        links.cost(upcoming.next) + pending_cost(links, pending)
            < links.cost(previous.next) + pending_cost(links, prior),
{
    reveal(pending_cost);
    if child.is_some() {
        if resume.next.is_some() {
            assert(pending.drop_last() =~= prior);
            assert(pending.last() == resume);
            assert forall |i: int| 0 <= i < pending.len()
                implies links.cost((#[trigger] pending[i]).next) > 0 by {
                if i < prior.len() { assert(pending[i] == prior[i]); }
                else { assert(pending[i] == resume); }
            }
        }
    } else {
        assert(prior.last() == prior[prior.len() - 1]);
        assert forall |i: int| 0 <= i < pending.len()
            implies links.cost((#[trigger] pending[i]).next) > 0 by {
            assert(pending[i] == prior[i]);
        }
    }
}

spec fn admitted_for_walk<I, F>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool,
    cursor: Siblings<I, F>, forced: bool, plain: bool) -> bool
{
    &&& cursor_admitted(links, hidden, cursor)
    &&& forced ==> !cursor.partial
    &&& plain ==> ordinary_siblings(cursor, cursor.partial)
}

#[verifier::opaque]
spec fn pending_admitted<I, F>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool,
    pending: Seq<Siblings<I, F>>, forced: bool, plain: bool) -> bool
{
    forall |i: int| 0 <= i < pending.len() ==>
        admitted_for_walk(links, hidden, #[trigger] pending[i], forced, plain)
}

proof fn empty_pending_admitted<I, F>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool,
    pending: Seq<Siblings<I, F>>, forced: bool, plain: bool)
    requires pending.len() == 0,
    ensures pending_admitted(links, hidden, pending, forced, plain),
{
    reveal(pending_admitted);
}

proof fn pending_admission_step<I, F>(links: node::PlacementLinks<I>, hidden: spec_fn(I) -> bool,
    resume: Siblings<I, F>, child: Option<Siblings<I, F>>, upcoming: Siblings<I, F>,
    prior: Seq<Siblings<I, F>>, pending: Seq<Siblings<I, F>>, forced: bool, plain: bool)
    requires pending_admitted(links, hidden, prior, forced, plain),
        admitted_for_walk(links, hidden, resume, forced, plain),
        if let Some(inside) = child {
            &&& upcoming == inside
            &&& admitted_for_walk(links, hidden, inside, forced, plain)
            &&& pending == (if resume.next.is_some() { prior.push(resume) } else { prior })
        } else {
            &&& prior.len() > 0
            &&& upcoming == prior.last()
            &&& pending == prior.drop_last()
        },
    ensures admitted_for_walk(links, hidden, upcoming, forced, plain),
        pending_admitted(links, hidden, pending, forced, plain),
{
    reveal(pending_admitted);
    if child.is_some() {
        if resume.next.is_some() {
            assert forall |i: int| 0 <= i < pending.len()
                implies admitted_for_walk(links, hidden, #[trigger] pending[i], forced, plain) by {
                if i < prior.len() { assert(pending[i] == prior[i]); }
                else { assert(pending[i] == resume); }
            }
        }
    } else {
        assert(upcoming == prior[prior.len() - 1]);
        assert forall |i: int| 0 <= i < pending.len()
            implies admitted_for_walk(links, hidden, #[trigger] pending[i], forced, plain) by {
            assert(pending[i] == prior[i]);
        }
    }
}

fn saved<I: Copy, F: Copy, T: ParentTarget<I>, const N: usize>(
    tree: &T, stack: &WorkStack<Siblings<I, F>, N>, cursor: &Siblings<I, F>,
) -> (out: Ghost<(Seq<Siblings<I, F>>, nat, Siblings<I, F>)>)
    ensures out@ == (stack.items(), tree.links().cost(cursor.next), *cursor),
    no_unwind
{ Ghost((stack.items(), tree.links().cost(cursor.next), *cursor)) }
}

// Consume one link before its rectangle callback and stop at the next descent.
macro_rules! positioned_siblings {
    ($tree:ident, $next:ident, $id:ident, $partial:ident; $item:block) => {
        positioned_siblings!($tree, $next, $id, $partial; [true] {} $item {})
    };
    ($tree:ident, $next:ident, $id:ident, $partial:ident;
        [$covered:expr $(, $bounds:expr)*] { $($before:tt)* } $item:block $finish:block
    ) => {
        positioned_siblings!($tree, $next, $id, $partial;
            [$covered $(, $bounds)*] [Seq::<I>::empty(), empty_staged_writes::<I>()] { $($before)* } $item $finish)
    };
    ($tree:ident, $next:ident, $id:ident, $partial:ident;
        [$covered:expr $(, $bounds:expr)*] [$staged:expr, $saved:expr] { $($before:tt)* } $item:block $finish:block
    ) => {{
        #[cfg(verus_keep_ghost)]
        proof! {
            let inputs = sibling_inputs($tree);
            let rank = cursor_rank(inputs.links, *old($next), *$next);
            preserved_marks(sibling_inputs(old($tree)), inputs, rank);
            assert($staged =~= Seq::<I>::empty());
            empty_writes_before(inputs.links, rank);
        }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant $tree.links() == old($tree).links(), $tree.links().finite(),
                $tree.hidden() == old($tree).hidden(), $tree.plain() == old($tree).plain(),
                consistent_cursor($tree.links(), *$next), $tree.links().cost(*$next) <= $tree.links().cost(*old($next)),
                match *$next {
                    Some(id) => old($next).is_some() && $tree.links().limit(id)
                        == $tree.links().limit(old($next).unwrap()),
                    None => true,
                },
                $($bounds,)*
                (!($covered) || {
                    let expected = sibling_writes(sibling_inputs(old($tree)), *old($next), $partial);
                    let suffix = sibling_writes(sibling_inputs($tree), *$next, $partial);
                    let rank = cursor_rank($tree.links(), *old($next), *$next);
                    $tree.written() + ($staged) + suffix.writes == old($tree).written() + expected.writes
                        && suffix.resume == expected.resume && suffix.branch == expected.branch
                        && marks_from(sibling_inputs(old($tree)), sibling_inputs($tree), rank)
                        && writes_before($tree.links(), $staged, rank)
                }),
            decreases $tree.links().cost(*$next),
        ))]
        loop {
            let Some($id) = *$next else {
                #[cfg(verus_keep_ghost)]
                let before = saved_sibling($tree);
                #[cfg(verus_keep_ghost)]
                let staged_before = $saved;
                let _ = $finish;
                #[cfg(verus_keep_ghost)]
                proof! {
                    if $covered {
                        let rank = cursor_rank($tree.links(), *old($next), None);
                        empty_sibling_plan(before@.0, $partial);
                        staged_marks(before@.0, sibling_inputs($tree), staged_before@, None, rank);
                        marks_from_both(sibling_inputs(old($tree)), before@.0, sibling_inputs($tree), rank, rank, rank);
                        assert(marks_after_siblings(old($tree), $tree, *old($next), None));
                    }
                }
                return None;
            };
            #[cfg(verus_keep_ghost)]
            let before = saved_sibling($tree);
            #[cfg(verus_keep_ghost)]
            let staged_before = $saved;
            #[cfg(verus_keep_ghost)]
            proof! { assert($tree.links().covers($id)); }
            $($before)*
            *$next = $tree.next_sibling($id);
            let branch = $item;
            #[cfg(verus_keep_ghost)]
            proof! {
                if $covered {
                    let (inputs, written) = before@;
                    let slice = sibling_write(inputs, $id, $partial);
                    let child = sibling_child(inputs, $id, $partial);
                    assert(branch_keys(branch) == child);
                    assert($tree.written() + ($staged) =~= written + staged_before@ + slice);
                    let rank = inputs.links.rank($id) + 1;
                    let following = cursor_rank(inputs.links, *old($next), *$next);
                    assert(rank <= following);
                    let after = sibling_inputs($tree);
                    let staged = $staged;
                    extend_staged(inputs.links, staged_before@, $id, staged, rank);
                    staged_marks(inputs, after, staged_before@, Some($id), rank);
                    later_writes(inputs.links, staged, rank, following);
                    consume_sibling(sibling_inputs(old($tree)), inputs, after, $id, *$next,
                        written + staged_before@, $tree.written() + staged, following, $partial);
                    if child.is_some() {
                        assert(($staged).len() == 0);
                        assert(marks_after_siblings(old($tree), $tree, *old($next), branch));
                    }
                }
            }
            if let Some(branch) = branch { return Some(branch); }
        }
    }};
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    ensures final(tree).links() == old(tree).links(),
        final(tree).hidden() == old(tree).hidden(),
            final(tree).plain() == old(tree).plain(),
        forall|other: I| other != id ==> #[trigger] final(tree).mark(other) == old(tree).mark(other),
        final(tree).rounding() == old(tree).rounding(),
        final(tree).rectangles() == node::resulting_rectangles(old(tree), id, rect, origin, PARTIAL),
        final(tree).written() == (if node::writes(old(tree).mark(id), PARTIAL) {
            old(tree).written().push(id)
        } else { old(tree).written() }),
        match branch {
            Some(b) => node::visits(old(tree).mark(id), PARTIAL) && b.parent == id
                && Some(b.first) == old(tree).links().first(id) && b.rect == rect
                && b.origin == node::snapped_origin((old(tree).rounding())(rect))
                && b.partial == (PARTIAL && !node::writes(old(tree).mark(id), PARTIAL)),
            None => !node::visits(old(tree).mark(id), PARTIAL) || old(tree).links().first(id).is_none(),
        },
    no_unwind
))]
pub(crate) fn emit<I: Copy, T: SiblingTarget<I>, const PARTIAL: bool>(tree: &mut T, id: I, rect: Edges, origin: [f32; 2]) -> Option<Branch<I>> {
    let Some((first, origin, partial)) = node::publish::<_, _, PARTIAL>(tree, id, rect, origin) else { return None };
    Some(Branch { parent: id, first, rect, origin, partial })
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn free_axis<F: crate::prepare_frame::FrameFloat>(
    edges: [f32; 2], padding: [f32; 2], placement: (Pos, Anchor, WindowOverflow),
    flipped: bool, size: f32, window: f32,
) -> [f32; 2] {
    let (position, anchor, overflow) = placement;
    let inner = geometry::padded_range::<F>(edges, padding);
    let rect = geometry::positioned::<F>(inner, position, anchor, flipped, size);
    if overflow is Ignore { rect } else { geometry::fit_window::<F>(window, overflow, flipped, anchor, rect) }
}

/// The raw edges use the two physical sizes and the exact padded parent frame.
pub(crate) open spec fn free_rect_value<F: crate::prepare_frame::FrameFloat>(
    style: FreeStyle, frame: Frame, size: [f32; 2], window: [f32; 2],
) -> Edges {
    let [edges_x, edges_y] = frame.edges;
    let [pad_x, pad_y] = frame.padding;
    let [flip_x, flip_y] = frame.flipped;
    let [pos_x, pos_y] = style.pos;
    let [anchor_x, anchor_y] = style.anchor;
    let [overflow_x, overflow_y] = style.overflow;
    let [width, height] = size;
    let [window_x, window_y] = window;
    [free_axis::<F>(edges_x, pad_x, (pos_x, anchor_x, overflow_x), flip_x, width, window_x),
        free_axis::<F>(edges_y, pad_y, (pos_y, anchor_y, overflow_y), flip_y, height, window_y)]
}

pub(crate) open spec fn free_node_rect<I, T: SiblingTarget<I>>(tree: &T, id: I, frame: Frame) -> Edges {
    free_rect_value::<T::PublicationFloat>(
        crate::placement_adapter::free_style_from((tree.free_declarations())(id)),
        frame, tree.solved_size(id), tree.placement_window(),
    )
}

/// Recomputing a selected Free node uses the same rectangle words as the
/// full pass when its stored size, frame, and current inputs agree.
pub(crate) proof fn same_written_free_node<I, T: SiblingTarget<I>>(
    retained: &T, fresh: &T, id: I, frame: Frame,
)
    requires retained.solved_size(id) == fresh.solved_size(id),
        crate::placement_adapter::free_style_from((retained.free_declarations())(id))
            == crate::placement_adapter::free_style_from((fresh.free_declarations())(id)),
        retained.placement_window() == fresh.placement_window(), retained.rounding() == fresh.rounding(),
        node::writes(retained.mark(id), true),
    ensures node::resulting_rectangles(retained, id, free_node_rect(retained, id, frame), frame.origin, true)[id]
        == node::resulting_rectangles(fresh, id, free_node_rect(fresh, id, frame), frame.origin, false)[id],
{
    assert(node::writes(fresh.mark(id), false));
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == free_rect_value::<T::PublicationFloat>(
        crate::placement_adapter::free_style_from((old(tree).free_declarations())(id)),
        *frame, size, old(tree).placement_window()),
        final(tree).placement_window() == old(tree).placement_window(),
        final(tree).free_declarations() == old(tree).free_declarations(),
        final(tree).links() == old(tree).links(), final(tree).written() == old(tree).written(),
        final(tree).hidden() == old(tree).hidden(),
            final(tree).plain() == old(tree).plain(),
        final(tree).rectangles() == old(tree).rectangles(), final(tree).rounding() == old(tree).rounding(),
        forall|id: I| #[trigger] final(tree).mark(id) == old(tree).mark(id),
    no_unwind
))]
pub(crate) fn free_rect<I: Copy, T: SiblingTarget<I>>(tree: &mut T, id: I, frame: &Frame, size: [f32; 2]) -> Edges {
    let [width, height] = size;
    let FreeStyle { pos: [x, y], anchor: [ax, ay], overflow: [ox, oy] } = tree.free_style(id);
    let [edges_x, edges_y] = frame.edges;
    let [padding_x, padding_y] = frame.padding;
    let [[left, right], [top, bottom]] = [
        geometry::inner_range::<T::PublicationFloat>(edges_x, padding_x),
        geometry::inner_range::<T::PublicationFloat>(edges_y, padding_y),
    ];
    if matches!((x, y, ox, oy), (Pos::Center, Pos::Center, WindowOverflow::Ignore, WindowOverflow::Ignore)) {
        return [geometry::centered_range::<T::PublicationFloat>(left, right, width), geometry::centered_range::<T::PublicationFloat>(top, bottom, height)];
    }
    let [flip_x, flip_y] = frame.flipped;
    let mut horizontal = geometry::resolve_position::<T::PublicationFloat>([left, right], x, ax, flip_x, width);
    let mut vertical = geometry::resolve_position::<T::PublicationFloat>([top, bottom], y, ay, flip_y, height);
    if !matches!(ox, WindowOverflow::Ignore) {
        horizontal = geometry::window_overflow::<T::PublicationFloat>(tree.window_size(true), ox, flip_x, ax, horizontal);
    }
    if !matches!(oy, WindowOverflow::Ignore) {
        vertical = geometry::window_overflow::<T::PublicationFloat>(tree.window_size(false), oy, flip_y, ay, vertical);
    }
    [horizontal, vertical]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    ensures final(tree).links() == old(tree).links(),
        final(tree).hidden() == old(tree).hidden(), final(tree).plain() == old(tree).plain(),
        final(tree).rounding() == old(tree).rounding(),
        forall|other: I| other != id ==> #[trigger] final(tree).mark(other) == old(tree).mark(other),
        final(tree).rectangles() == node::resulting_rectangles(old(tree), id, free_node_rect(old(tree), id, *frame), frame.origin, PARTIAL),
        final(tree).written() == (if node::writes(old(tree).mark(id), PARTIAL) {
            old(tree).written().push(id)
        } else { old(tree).written() }),
        match branch {
            Some(b) => node::visits(old(tree).mark(id), PARTIAL) && b.parent == id
                && Some(b.first) == old(tree).links().first(id) && b.rect == free_node_rect(old(tree), id, *frame)
                && b.origin == node::snapped_origin((old(tree).rounding())(b.rect))
                && b.partial == (PARTIAL && !node::writes(old(tree).mark(id), PARTIAL)),
            None => !node::visits(old(tree).mark(id), PARTIAL) || old(tree).links().first(id).is_none(),
        },
    no_unwind
))]
fn emit_free_node<I: Copy, T: SiblingTarget<I>, const PARTIAL: bool>(tree: &mut T, id: I, frame: &Frame) -> Option<Branch<I>> {
    let size = tree.size(id);
    let rect = free_rect(tree, id, frame, size);
    emit::<_, _, PARTIAL>(tree, id, rect, frame.origin)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    requires old(tree).links().finite(), consistent_cursor(old(tree).links(), *old(next)),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        sibling_progress(old(tree).links(), *old(next), *final(next), branch),
        executed_sibling_plan(old(tree), final(tree), *old(next), *final(next), branch, PARTIAL),
    no_unwind
))]
pub(crate) fn free<I: Copy, T: SiblingTarget<I>, const PARTIAL: bool>(
    tree: &mut T, next: &mut Option<I>, frame: &Frame,
) -> Option<Branch<I>> {
    positioned_siblings!(tree, next, id, PARTIAL; {
        if tree.disabled(id) || node::skip_clean::<_, _, PARTIAL>(tree, id) {
            None
        } else {
            emit_free_node::<_, _, PARTIAL>(tree, id, frame)
        }
    })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(axes =>
    ensures axes.0 < 2, axes.1 < 2, axes.0 != axes.1, axes == if x { (0, 1) } else { (1, 0) },
    no_unwind
))]
fn axes(x: bool) -> (usize, usize) {
    if x { (0, 1) } else { (1, 0) }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires axis < 2, no_unwind
))]
fn aligned_axis<M: StackMath>(frame: &Frame, axis: usize, size: f32, pos: Pos, anchor: Anchor, [start, end]: [f32; 2]) -> [f32; 2] {
    let [left, right] = geometry::inner_range::<M>(frame.edges[axis], frame.padding[axis]);
    let range = [M::with_margin(left, start), M::with_margin(right, M::negate(end))];
    geometry::resolve_position::<M>(range, pos, anchor, frame.flipped[axis], size)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn stack_item<M: StackMath>(frame: &Frame, style: StackStyle, size: [f32; 2], x: bool, position: &mut f32, gap: f32) -> Edges {
    let (main, cross) = axes(x);
    let other = aligned_axis::<M>(frame, cross, size[cross], style.pos[cross], style.anchor[cross], style.margin[cross]);
    let range = geometry::inner_range::<M>(frame.edges[main], frame.padding[main]);
    let along = M::place(position, frame.flipped[main], range, size[main], style.margin[main], gap);
    if x { [along, other] } else { [other, along] }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(edges =>
    ensures (edges, *final(position)) == forward_step::<M>(*old(position), cross_start, margin, x, size, gap),
    no_unwind
))]
fn stack_start_with_margin<M: StackMath>(
    cross_start: f32, margin: Edges, size: [f32; 2], x: bool, position: &mut f32, gap: f32,
) -> Edges {
    let (main, cross) = axes(x);
    // Forward Start alignment uses only the padded leading edge and margin.
    let cross_start = M::with_margin(cross_start, margin[cross][0]);
    let other = [cross_start, M::add(cross_start, size[cross])];
    let along = M::place(position, false, [0.0, 0.0], size[main], margin[main], gap);
    if x { [along, other] } else { [other, along] }
}

#[cfg(test)]
#[test]
fn forward_start_with_margin_matches_stack_edges_and_cursor() {
    use crate::placement_geometry::RustFloat;

    let frame = Frame {
        edges: [[-0.0, 114.0], [-0.0, 212.0]], origin: [0.0, 0.0],
        padding: [[-0.0, 0.25], [-0.0, 0.5]], flipped: [false, false],
    };
    let margin = [[0.125, 0.125], [-0.0, -0.25]];
    for x in [false, true] {
        let (_, cross) = axes(x);
        let [cross_start, _] = geometry::inner_range::<RustFloat>(frame.edges[cross], frame.padding[cross]);
        let style = StackStyle {
            disabled: false, free: false, pos: [Pos::Start, Pos::Start], anchor: [Anchor::End; 2],
            margin, zero_margins: false,
        };
        let size = [-0.0, 1.0 / 3.0];
        let gap = 1.0 / 7.0;
        let mut normal_cursor = -0.0;
        let mut fast_cursor = normal_cursor;
        let normal = stack_item::<RustFloat>(&frame, style, size, x, &mut normal_cursor, gap);
        let fast = stack_start_with_margin::<RustFloat>(cross_start, margin, size, x, &mut fast_cursor, gap);
        assert_eq!(fast.map(|axis| axis.map(f32::to_bits)), normal.map(|axis| axis.map(f32::to_bits)));
        assert_eq!(fast_cursor.to_bits(), normal_cursor.to_bits());
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(buffer).pending.len < batch::CAPACITY, clean_tail(old(buffer).pending),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        final(buffer).pending.len == 0, clean_tail(final(buffer).pending),
        final(tree).written() == old(tree).written() + old(buffer).ids@.take(old(buffer).pending.len as int),
        forall|other: I| !old(buffer).ids@.take(old(buffer).pending.len as int).contains(other)
            ==> #[trigger] final(tree).mark(other) == old(tree).mark(other),
    no_unwind
))]
fn flush<I: Copy, T: StackTarget<I>>(tree: &mut T, buffer: &mut batch::Buffer<I, [f32; 4]>, origin: [f32; 2]) {
    let run = buffer.drain();
    if !run.is_empty() { run.publish(&buffer.ids, &mut buffer.edges, tree, origin); }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(buffer).pending.len < batch::CAPACITY, clean_tail(old(buffer).pending),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        final(buffer).pending.len < batch::CAPACITY, clean_tail(final(buffer).pending),
        final(tree).written() + final(buffer).ids@.take(final(buffer).pending.len as int)
            == (old(tree).written() + old(buffer).ids@.take(old(buffer).pending.len as int)).push(id),
        final(buffer).pending.len == 0 || final(buffer).ids@.take(final(buffer).pending.len as int)
            == old(buffer).ids@.take(old(buffer).pending.len as int).push(id),
        forall|other: I| other != id && !old(buffer).ids@.take(old(buffer).pending.len as int).contains(other)
            ==> #[trigger] final(tree).mark(other) == old(tree).mark(other),
    no_unwind
))]
fn batch_leaf<I: Copy, T: StackTarget<I>>(
    tree: &mut T, buffer: &mut batch::Buffer<I, [f32; 4]>, id: I,
    [[left, right], [top, bottom]]: Edges, dirty: bool, origin: [f32; 2],
) {
    if let Some(run) = buffer.push(id, [left, right, top, bottom], dirty) {
        run.publish(&buffer.ids, &mut buffer.edges, tree, origin);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let prior = old(buffer).ids@.take(old(buffer).pending.len as int);
        assert(old(tree).written() + prior.push(id) =~= (old(tree).written() + prior).push(id));
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    requires old(tree).links().finite(), consistent_cursor(old(tree).links(), *old(next)),
        old(tree).links().cost(Some(head)) > 0, !BATCH || !PARTIAL,
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        sibling_progress(old(tree).links(), *old(next), *final(next), branch),
        executed_sibling_plan(old(tree), final(tree), *old(next), *final(next), branch, PARTIAL),
    no_unwind
))]
pub(crate) fn stack<I: Copy, T: StackTarget<I>, M: StackMath, const PARTIAL: bool, const BATCH: bool>(
    tree: &mut T, head: I, next: &mut Option<I>, frame: &Frame, x: bool,
    position: &mut f32, gap: f32, auto_share: &mut Option<f32>,
) -> Option<Branch<I>> {
    let (main, cross) = axes(x);
    let axis = if x { Axis::X } else { Axis::Y };
    let [cross_start, _] = geometry::inner_range::<M>(frame.edges[cross], frame.padding[cross]);
    let [flip_x, flip_y] = frame.flipped;
    let forward = !flip_x && !flip_y;
    let Some(first) = *next else {
        #[cfg(verus_keep_ghost)]
        proof! {
            reveal(sibling_writes);
            preserved_marks(sibling_inputs(old(tree)), sibling_inputs(tree), 0);
        }
        return None;
    };
    let mut batch = if BATCH && tree.snapping() { Some(batch::empty_buffer(first, [0.0, 0.0, 0.0, 0.0])) } else { None };
    let use_prepared_styles = !PARTIAL && forward && tree.prepared_styles();
    positioned_siblings!(tree, next, id, PARTIAL;
        [true, main < 2, cross < 2, tree.links().cost(Some(head)) > 0,
            batch.is_none() || (BATCH && !PARTIAL),
            batch.is_none() || batch.unwrap().pending.len < batch::CAPACITY && clean_tail(batch.unwrap().pending)]
        [staged_writes(batch), saved_staged_writes(&batch)] {
        let child = tree.stack_data(id);
        let cached = use_prepared_styles && child.cached_start();
        // Borrow the declarations and expand the alignment only when needed.
        let style = if cached { None } else { Some(tree.stack_params(id)) };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((tree.hidden())(id) == match style { Some(params) => params.disabled, None => false });
            assert(batch.is_some() ==> !PARTIAL);
        }
    } {
        if matches!(style, Some(params) if params.disabled) {
            None
        } else {
            let size = child.stack_size();
            #[cfg(verus_keep_ghost)]
            let original = saved_sibling(tree);
            #[cfg(verus_keep_ghost)]
            let staged = saved_staged_writes(&batch);
            let rect = match style {
                Some(style) if style.free_placement => {
                    if let Some(buffer) = &mut batch { flush(tree, buffer, frame.origin); }
                    Some(free_rect(tree, id, frame, size))
                }
                _ => {
                    let rect = match style {
                        Some(params) if !forward || !matches!(if x { params.position.y } else { params.position.x }, Pos::Start)
                            || !zero_margins(params) => {
                            let mut style = T::stack_align(params);
                            let auto = params.auto_margins(axis);
                            if auto[0] || auto[1] {
                                let share = match *auto_share {
                                    Some(share) => share,
                                    None => {
                                        // Start-aligned stacks need a sibling scan only if an
                                        // in-flow item actually asks for an automatic margin.
                                        let [start, end] = geometry::inner_range::<M>(frame.edges[main], frame.padding[main]);
                                        let (used, _, edges) = stack_line_totals::<_, _, M>(tree, head, x, gap);
                                        let share = geometry::auto_margin_share((end - start) - used, edges as usize);
                                        *auto_share = Some(share);
                                        share
                                    }
                                };
                                style.margin[main] = resolved_margins(style.margin[main], auto, share);
                            }
                            if forward && matches!(style.pos[cross], Pos::Start) {
                                stack_start_with_margin::<M>(cross_start, style.margin, size, x, position, gap)
                            } else {
                                stack_item::<M>(frame, style, size, x, position, gap)
                            }
                        }
                        _ => M::place_start(position, cross_start, x, size, gap),
                    };
                    if let Some(buffer) = &mut batch {
                        if tree.first_child(id).is_none() {
                            let dirty = child.dirty();
                            batch_leaf(tree, buffer, id, rect, dirty, frame.origin);
                            None
                        } else {
                            flush(tree, buffer, frame.origin);
                            Some(rect)
                        }
                    } else {
                        Some(rect)
                    }
                }
            };
            #[cfg(verus_keep_ghost)]
            proof! {
                let (inputs, written) = original@;
                assert(!(inputs.hidden)(id));
                if rect.is_some() {
                    assert(staged_writes(batch).len() == 0);
                    assert(tree.written() == written + staged@);
                    assert(PARTIAL ==> tree.mark(id) == (inputs.work)(id));
                } else {
                    assert(!PARTIAL);
                    assert(tree.links().first(id).is_none());
                    assert(tree.written() + staged_writes(batch) =~= (written + staged@).push(id));
                    assert(staged_writes(batch).len() == 0 || staged_writes(batch) == staged@.push(id));
                }
                assert forall |other: I| other != id && !staged@.contains(other)
                    implies #[trigger] tree.mark(other) == (inputs.work)(other) by {
                    if let Some(buffer) = batch {
                        assert(buffer.pending.len == 0 || rect.is_none());
                    }
                };
            }
            match rect {
                Some(rect) => emit::<_, _, PARTIAL>(tree, id, rect, frame.origin),
                None => None,
            }
        }
    } {
        if let Some(buffer) = &mut batch { flush(tree, buffer, frame.origin); }
    })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(zero =>
    ensures zero == (params.margin.x[0].is_zero() && params.margin.x[1].is_zero()
        && params.margin.y[0].is_zero() && params.margin.y[1].is_zero()),
    no_unwind
))]
pub(crate) fn zero_margins(params: &LayoutParams) -> bool {
    let [left, right] = params.margin.x;
    let [top, bottom] = params.margin.y;
    left.is_zero() && right.is_zero() && top.is_zero() && bottom.is_zero()
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn wrap_bound<I: Copy, T: WrapTarget<I>>(tree: &T, id: I, x: bool, kind: Kind) -> Option<f32> {
    let Some(declared) = tree.declaration(id, x, kind) else { return None };
    if !declared.is_flex() { Some(tree.wrap_slot(id, x, kind)) } else { None }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn wrap_cross<I: Copy, T: WrapTarget<I>, M: StackMath + FloatBounds>(tree: &T, id: I, x: bool) -> f32 {
    let [start, end] = tree.margins(id, x);
    let initial = match tree.declaration(id, x, Kind::Regular) {
        Some(crate::declarations::Size::Fill | crate::declarations::Size::Frac(_)) => 0.0,
        _ => tree.wrap_slot(id, x, Kind::Regular),
    };
    let min = wrap_bound(tree, id, x, Kind::Min);
    let max = wrap_bound(tree, id, x, Kind::Max);
    let size = if let Some(max) = max { M::min(initial, max) } else { initial };
    let size = if let Some(min) = min { M::max(size, min) } else { size };
    M::with_margin(size, start + end)
}

/// Placement replays the saved line starts against the resolved sizes. The
/// first in-flow item is consumed even if it is marked as a line start.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires tree.links().finite(), consistent_cursor(tree.links(), start),
    no_unwind
))]
fn scan_placed_line<I: Copy, T: WrapTarget<I> + StackTarget<I>, M: StackMath + FloatBounds>(
    tree: &T, start: Option<I>, x: bool, spacing: f32,
) -> PlacedLine<I> {
    let mut next = start;
    let mut count = 0u32;
    let mut main = 0.0;
    let mut cross = 0.0;
    let mut auto_edges = 0u32;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.links().finite(), consistent_cursor(tree.links(), next),
        decreases tree.links().cost(next),
    ))]
    while let Some(id) = next {
        #[cfg(verus_keep_ghost)]
        proof! { assert(tree.links().covers(id)); }
        if tree.wrap_in_flow(id) {
            if count != 0 && tree.wrap_marked(id) { break; }
            let size = tree.wrap_slot(id, x, Kind::Final);
            let [start, end] = tree.margins(id, x);
            let [auto_start, auto_end] = tree.stack_params(id).auto_margins(if x { Axis::X } else { Axis::Y });
            auto_edges = auto_edges.saturating_add(auto_start as u32 + auto_end as u32);
            let extent = M::with_margin(size, start + end);
            main = if count == 0 { extent } else { main + spacing + extent };
            cross = M::max(cross, wrap_cross::<_, _, M>(tree, id, !x));
            count = count.saturating_add(1);
        }
        next = tree.next_sibling(id);
    }
    PlacedLine { next, main, cross, count, auto_edges }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    requires old(tree).links().finite(), consistent_cursor(old(tree).links(), *old(next)),
        old(cursor).ready_start ==> enabled_siblings(old(tree).links(), old(tree).hidden(), *old(next)),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        sibling_progress(old(tree).links(), *old(next), *final(next), branch),
        final(cursor).ready_start == old(cursor).ready_start,
        final(cursor).ready_start ==> enabled_siblings(final(tree).links(), final(tree).hidden(), *final(next)),
        executed_sibling_plan(old(tree), final(tree), *old(next), *final(next), branch, PARTIAL),
    no_unwind
))]
pub(crate) fn wrap<I: Copy, T: WrapTarget<I> + StackTarget<I>, M: StackMath + FloatBounds, const PARTIAL: bool>(
    tree: &mut T, next: &mut Option<I>, frame: &Frame, cursor: &mut WrapCursor<I>,
) -> Option<Branch<I>> {
    let (main, cross) = axes(cursor.x);
    let main_range = geometry::inner_range::<M>(frame.edges[main], frame.padding[main]);
    let cross_range = geometry::inner_range::<M>(frame.edges[cross], frame.padding[cross]);
    positioned_siblings!(tree, next, id, PARTIAL;
        [true, cursor.ready_start == old(cursor).ready_start, main < 2, cross < 2,
            !cursor.ready_start || enabled_siblings(tree.links(), tree.hidden(), *next)] {
        #[cfg(verus_keep_ghost)]
        proof! {
            if cursor.ready_start { advance_enabled_sibling(tree.links(), tree.hidden(), id); }
        }
        if cursor.ready_cross && (tree.same_cursor(cursor.next_line, id) || tree.wrap_marked(id)) {
            cursor.main_position = main_range[0];
            cursor.gap = cursor.spacing;
            cursor.cross_edges = M::place(
                &mut cursor.cross_position, frame.flipped[cross], cross_range, tree.wrap_line_height(id), [0.0, 0.0], cursor.line_spacing,
            );
            cursor.next_line = None;
        } else if !cursor.ready_cross && tree.same_cursor(cursor.next_line, id) {
            let line = scan_placed_line::<_, _, M>(tree, *next, cursor.x, cursor.spacing);
            let (position, gap, share) = arranged_line::<M>(cursor.arrange, main_range, line.main, line.count, cursor.spacing, line.auto_edges);
            cursor.auto_share = share;
            cursor.main_position = position;
            cursor.gap = gap;
            cursor.cross_edges = M::place(
                &mut cursor.cross_position, frame.flipped[cross], cross_range, line.cross, [0.0, 0.0], cursor.line_spacing,
            );
            cursor.next_line = line.next;
        }
    } {
        let rect = if cursor.ready_start {
            // The regular line frame adds its zero cross padding, including
            // when the line edge is negative zero.
            let cross_start = M::add(cursor.cross_edges[0], 0.0);
            Some(M::place_start(&mut cursor.main_position, cross_start, cursor.x, tree.size(id), cursor.gap))
        } else {
            let style = tree.align_style(id);
            if style.disabled {
                None
            } else {
                let size = tree.size(id);
                Some(if style.free {
                    free_rect(tree, id, frame, size)
                } else {
                    let mut line_frame = *frame;
                    line_frame.edges[cross] = cursor.cross_edges;
                    line_frame.padding[cross] = [0.0, 0.0];
                    let mut margins = style.margin[main];
                    if cursor.auto_share > 0.0 && !style.zero_margins {
                        let axis = if cursor.x { Axis::X } else { Axis::Y };
                        margins = resolved_margins(margins, tree.stack_params(id).auto_margins(axis), cursor.auto_share);
                    }
                    let along = M::place(
                        &mut cursor.main_position, frame.flipped[main], main_range, size[main], margins, cursor.gap,
                    );
                    let other = aligned_axis::<M>(&line_frame, cross, size[cross], style.pos[cross], style.anchor[cross], style.margin[cross]);
                    if cursor.x { [along, other] } else { [other, along] }
                })
            }
        };
        match rect {
            Some(rect) => emit::<_, _, PARTIAL>(tree, id, rect, frame.origin),
            None => None,
        }
    } {})
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    requires old(tree).links().finite(), consistent_cursor(old(tree).links(), *old(next)),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        sibling_progress(old(tree).links(), *old(next), *final(next), branch),
        executed_sibling_plan(old(tree), final(tree), *old(next), *final(next), branch, PARTIAL),
    no_unwind
))]
pub(crate) fn block<I: Copy, T: BlockTarget<I>, M: FloatBounds, const PARTIAL: bool>(
    tree: &mut T, next: &mut Option<I>, frame: &Frame, flow: &mut T::Flow,
) -> Option<Branch<I>> {
    let range = geometry::inner_range::<T::PublicationFloat>(frame.edges[0], frame.padding[0]);
    let [top, _] = geometry::inner_range::<T::PublicationFloat>(frame.edges[1], frame.padding[1]);
    positioned_siblings!(tree, next, id, PARTIAL; {
        if tree.disabled(id) {
            None
        } else {
            let style = tree.block_style(id);
            let [width, height] = tree.size(id);
            let rect = if style.free {
                free_rect(tree, id, frame, [width, height])
            } else {
                let inline = geometry::block_inline_edges::<M>(range, width, style.inline_margin, style.auto, frame.flipped[0]);
                let item = block_item(tree, id);
                let y = top + T::append_block(flow, item);
                [inline, [y, y + height]]
            };
            emit::<_, _, PARTIAL>(tree, id, rect, frame.origin)
        }
    })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        final(tree).written() == old(tree).written(), final(tree).rectangles() == old(tree).rectangles(),
        forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other),
    no_unwind
))]
fn block_item<I: Copy, T: BlockTarget<I>>(tree: &mut T, id: I) -> T::Item {
    let nested = if let Some(index) = tree.margin_index(id) { tree.nested_margin(index) } else { None };
    let BlockItemInputs { bounds, height, margins, children_empty } = tree.block_item_inputs(id);
    let [top, bottom] = bounds.padding;
    let adjoins = height == 0.0 && bounds.collapse && top == 0.0 && bottom == 0.0 && bounds.zero_minimum;
    T::block_from_edges(margins, height, adjoins, children_empty, nested)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn block_start<I: Copy, T: ParentTarget<I>>(tree: &T, id: I) -> T::Flow {
    let BlockEdges { padding: [top, bottom], collapse, zero_minimum } = tree.block_parent_edges(id);
    let before = collapse && top == 0.0;
    let after = collapse && bottom == 0.0
        && matches!(tree.declaration(id, false, Kind::Regular), Some(crate::declarations::Size::FitContent))
        && zero_minimum;
    T::block_from_parent(before, after)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    requires old(tree).links().finite(), consistent_cursor(old(tree).links(), *old(next)),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        sibling_progress(old(tree).links(), *old(next), *final(next), branch),
        executed_sibling_plan(old(tree), final(tree), *old(next), *final(next), branch, PARTIAL),
    no_unwind
))]
pub(crate) fn grid<I: Copy, T: GridTarget<I>, M: StackMath + FloatBounds, const PARTIAL: bool>(
    tree: &mut T, parent: I, next: &mut Option<I>, frame: &Frame, spacing: [f32; 2],
) -> Option<Branch<I>> {
    let lines = tree.grid_lines(parent);
    let size = tree.size(parent);
    let cell = [
        geometry::grid_track_size::<M>(size[0], frame.padding[0], spacing[0], lines[0]),
        geometry::grid_track_size::<M>(size[1], frame.padding[1], spacing[1], lines[1]),
    ];
    let [left, _] = geometry::inner_range::<M>(frame.edges[0], frame.padding[0]);
    let [top, _] = geometry::inner_range::<M>(frame.edges[1], frame.padding[1]);
    let step = [cell[0] + spacing[0], cell[1] + spacing[1]];
    let forward = !frame.flipped[0] && !frame.flipped[1];
    positioned_siblings!(tree, next, id, PARTIAL; {
        // The solved cell of the next sibling is independent of this rectangle.
        if tree.disabled(id) || node::skip_clean::<_, _, PARTIAL>(tree, id) {
            None
        } else {
            let size = tree.size(id);
            let GridStyle { align: style, span } = tree.grid_style(id);
            let rect = if style.free {
                free_rect(tree, id, frame, size)
            } else {
                let child_cell = tree.grid_cell(id);
                if forward && matches!(style.pos, [Pos::Start, Pos::Start]) && style.zero_margins {
                    T::grid_start([left, top], step, child_cell, size)
                } else {
                    let bounds = Frame {
                        edges: [
                            geometry::grid_cell_edges::<M>(frame.edges[0], frame.padding[0], frame.flipped[0], child_cell[0], cell[0], spacing[0], span[0], lines[0]),
                            geometry::grid_cell_edges::<M>(frame.edges[1], frame.padding[1], frame.flipped[1], child_cell[1], cell[1], spacing[1], span[1], lines[1]),
                        ],
                        padding: [[0.0, 0.0], [0.0, 0.0]], ..*frame
                    };
                    [
                        aligned_axis::<M>(&bounds, 0, size[0], style.pos[0], style.anchor[0], style.margin[0]),
                        aligned_axis::<M>(&bounds, 1, size[1], style.pos[1], style.anchor[1], style.margin[1]),
                    ]
                }
            };
            emit::<_, _, PARTIAL>(tree, id, rect, frame.origin)
        }
    })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn resolved_margins(margins: [f32; 2], auto: [bool; 2], share: f32) -> [f32; 2] {
    [if auto[0] { share } else { margins[0] }, if auto[1] { share } else { margins[1] }]
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires tree.links().finite(), tree.links().cost(Some(first)) > 0,
    no_unwind
))]
fn stack_line_totals<I: Copy, T: StackTarget<I>, M: StackMath>(
    tree: &T, first: I, x: bool, spacing: f32,
) -> (f32, u32, u32) {
    let (main, _) = axes(x);
    let mut count = 0u32;
    let mut auto_edges = 0u32;
    let mut widths = 0.0;
    let mut next = Some(first);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.links().finite(), consistent_cursor(tree.links(), next), main < 2,
        decreases tree.links().cost(next),
    ))]
    while let Some(id) = next {
        #[cfg(verus_keep_ghost)]
        proof! { assert(tree.links().covers(id)); }
        next = tree.next_sibling(id);
        let params = tree.stack_params(id);
        if !params.disabled && !params.free_placement {
            let [start, end] = tree.margins(id, x);
            widths += M::with_margin(tree.size(id)[main], start + end);
            let [auto_start, auto_end] = params.auto_margins(if x { Axis::X } else { Axis::Y });
            auto_edges = auto_edges.saturating_add(auto_start as u32 + auto_end as u32);
            count = count.saturating_add(1);
        }
    }
    let total = if count > 0 { widths + spacing * between_gaps(count) as f32 } else { widths };
    (total, count, auto_edges)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn arranged_line<M: FloatBounds>(
    arrange: Arrange, range: [f32; 2], total: f32, count: u32, spacing: f32, edges: u32,
) -> (f32, f32, f32) {
    let share = geometry::auto_margin_share((range[1] - range[0]) - total, edges as usize);
    let (position, gap) = if share > 0.0 { (range[0], spacing) }
        else { geometry::line_start_and_gap::<M>(arrange, range, total, count, spacing) };
    (position, gap, share)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires tree.links().finite(), tree.links().cost(Some(branch.first)) > 0,
        tree.links().first(branch.parent) == Some(branch.first),
    ensures out.next == Some(branch.first), out.partial == branch.partial,
        cursor_admitted(tree.links(), tree.hidden(), out),
        tree.plain() ==> ordinary_siblings(out, branch.partial),
    no_unwind
))]
fn cursor_for<I: Copy, T: ParentTarget<I>, M: StackMath + FloatBounds>(tree: &T, branch: Branch<I>) -> Siblings<I, T::Flow> {
    let Branch { parent, first, rect, origin, partial } = branch;
    let ParentStyle { layout, padding, flipped } = tree.parent_style(parent);
    let frame = Frame { edges: rect, origin, padding, flipped };
    let mode = match layout {
        ChildrenLayout::Free => Mode::Free,
        ChildrenLayout::Stack { axis, arrange, spacing } => {
            let x = matches!(axis, Axis::X);
            let (main, _) = axes(x);
            let range = geometry::inner_range::<M>(frame.edges[main], frame.padding[main]);
            let (position, gap, auto_share) = if matches!(arrange, Arrange::Start) {
                (range[0], spacing, None)
            } else {
                let (total, count, edges) = stack_line_totals::<_, _, M>(tree, first, x, spacing);
                let (position, gap, share) = arranged_line::<M>(arrange, range, total, count, spacing, edges);
                (position, gap, Some(share))
            };
            let batch = !partial && tree.prefers_batch() && tree.placed_children(parent) >= batch::CAPACITY as u32;
            let paired_leaves = !partial && tree.full_unsnapped() && !flipped[0] && !flipped[1]
                && matches!(arrange, Arrange::Start) && tree.placed_children(parent) >= 8;
            Mode::Stack { head: first, x, position, gap, auto_share, batch, paired_leaves }
        }
        ChildrenLayout::Wrap { axis, arrange, spacing, line_spacing } => {
            let x = matches!(axis, Axis::X);
            let (_, cross) = axes(x);
            let [cross_position, _] = geometry::inner_range::<M>(frame.edges[cross], frame.padding[cross]);
            let ready_cross = !partial && matches!(arrange, Arrange::Start) && tree.ready_wrap_lines(parent);
            Mode::Wrap(WrapCursor {
                x, arrange, spacing, line_spacing, next_line: Some(first), cross_position,
                ready_cross,
                ready_start: ready_cross && !flipped[0] && !flipped[1] && tree.ready_wrap_start(parent),
                cross_edges: [0.0, 0.0], main_position: 0.0, gap: 0.0, auto_share: 0.0,
            })
        }
        ChildrenLayout::Block => Mode::Block(block_start(tree, parent)),
        ChildrenLayout::Grid { spacing_x, spacing_y, .. } => Mode::Grid { parent, spacing: [spacing_x, spacing_y] },
    };
    let out = Siblings { next: Some(first), frame, partial, mode };
    #[cfg(verus_keep_ghost)]
    proof! { reveal(ordinary_siblings); reveal(wrap_admitted); reveal(cursor_admitted); }
    out
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct PlainLeaf<I> {
    id: I,
    size: [f32; 2],
    dirty: bool,
    next: Option<I>,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(leaf =>
    ensures leaf.is_some() == plain_start_child(tree, id, x),
        leaf.is_some() ==> {
        let leaf = leaf.unwrap();
        &&& leaf.id == id
        &&& leaf.size == tree.solved_size(id)
        &&& !(tree.hidden())(id)
        &&& tree.links().first(id).is_none()
        &&& leaf.next == tree.links().next(id)
        &&& leaf.dirty == dirty_work(tree.mark(id))
    },
    no_unwind
))]
fn load_plain_leaf<I: Copy, T: StackTarget<I>>(tree: &T, id: I, x: bool) -> Option<PlainLeaf<I>> {
    let params = tree.stack_params(id);
    if params.disabled || params.free_placement || !matches!(if x { params.position.y } else { params.position.x }, Pos::Start)
        || !zero_margins(params) || tree.first_child(id).is_some()
    {
        return None;
    }
    let child = tree.stack_data(id);
    Some(PlainLeaf { id, size: child.stack_size(), dirty: child.dirty(), next: tree.next_sibling(id) })
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires leaf.dirty == dirty_work(old(tree).mark(leaf.id)),
    ensures final(tree).links() == old(tree).links(),
        final(tree).hidden() == old(tree).hidden(), final(tree).plain() == old(tree).plain(),
        final(tree).written() == old(tree).written().push(leaf.id),
        final(tree).rounding() == old(tree).rounding(),
        final(tree).start_aligned() == old(tree).start_aligned(),
        forall|id: I| #[trigger] final(tree).solved_size(id) == old(tree).solved_size(id),
        ({
            let (raw, cursor) = start_step::<M>(*old(position), cross, x, leaf.size, gap);
            &&& *final(position) == cursor
            &&& final(tree).rectangles() == put_rect::<I, T>(old(tree).rectangles(), leaf.id,
                (old(tree).rounding())(raw), origin)
        }),
        !dirty_work(final(tree).mark(leaf.id)),
        forall|other: I| other != leaf.id ==> #[trigger] final(tree).mark(other) == old(tree).mark(other),
    no_unwind
))]
fn emit_plain_leaf<I: Copy, T: StackTarget<I>, M: StackMath>(
    tree: &mut T, leaf: &PlainLeaf<I>, position: &mut f32, cross: f32, x: bool, gap: f32, origin: [f32; 2],
) {
    let rect = M::place_start(position, cross, x, leaf.size, gap);
    if leaf.dirty { tree.clear_work(leaf.id); }
    let output = NodeTarget::snap(tree, rect);
    node::write_snapped(tree, leaf.id, output, origin, false);
}

/// Look ahead by one leaf so the next node's loads can run alongside the
/// current write. Each accepted leaf is read once and published in order.
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tree).links().finite(), consistent_cursor(old(tree).links(), *old(next)),
    ensures final(tree).links() == old(tree).links(), consistent_cursor(old(tree).links(), *final(next)),
        final(tree).hidden() == old(tree).hidden(), final(tree).plain() == old(tree).plain(),
        final(tree).rounding() == old(tree).rounding(),
        final(tree).start_aligned() == old(tree).start_aligned(),
        final(next).is_some() ==> !plain_start_child(old(tree), final(next).unwrap(), X),
        forall|id: I| #[trigger] final(tree).solved_size(id) == old(tree).solved_size(id),
        old(tree).links().cost(*final(next)) <= old(tree).links().cost(*old(next)),
        final(next).is_some() ==> old(next).is_some()
            && old(tree).links().limit(final(next).unwrap()) == old(tree).links().limit(old(next).unwrap()),
        marks_from(sibling_inputs(old(tree)), sibling_inputs(final(tree)), cursor_rank(old(tree).links(), *old(next), *final(next))),
        exists|count: nat| {
            let prefix = #[trigger] leaf_prefix(old(tree).links(), *old(next), count);
            &&& prefix.1 == *final(next)
            &&& final(tree).written() == old(tree).written() + prefix.0
            &&& leaf_path(old(tree).links(), old(tree).hidden(), *old(next), prefix.0, *final(next))
            &&& (final(tree).rectangles(), *final(position)) ==
                paired_start_rects::<I, T, M>(old(tree), prefix.0, *old(position), frame, X, gap)
        },
    no_unwind
))]
fn paired_start_leaves<I: Copy, T: StackTarget<I>, M: StackMath, const X: bool>(
    tree: &mut T, next: &mut Option<I>, frame: &Frame, position: &mut f32, gap: f32,
) {
    let (_, axis) = axes(X);
    let [cross, _] = geometry::inner_range::<M>(frame.edges[axis], frame.padding[axis]);
    #[cfg(verus_keep_ghost)]
    let mut count = start_leaf_prefix();
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal(leaf_path);
        reveal(draw_rows);
        if X { assert(axis == 1); } else { assert(axis == 0); }
        preserved_marks(sibling_inputs(old(tree)), sibling_inputs(tree), cursor_rank(tree.links(), *old(next), *next));
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.links() == old(tree).links(), tree.links().finite(), consistent_cursor(tree.links(), *next),
            tree.hidden() == old(tree).hidden(), tree.plain() == old(tree).plain(),
            tree.rounding() == old(tree).rounding(),
            tree.start_aligned() == old(tree).start_aligned(),
            cross == (if X { geometry::padded_start::<M>(frame.edges[1], frame.padding[1][0]) }
                else { geometry::padded_start::<M>(frame.edges[0], frame.padding[0][0]) }),
            forall|id: I| #[trigger] tree.solved_size(id) == old(tree).solved_size(id),
            (tree.rectangles(), *position) == paired_start_rects::<I, T, M>(old(tree),
                leaf_prefix(tree.links(), *old(next), count@).0, *old(position), frame, X, gap),
            tree.links().cost(*next) <= tree.links().cost(*old(next)),
            next.is_some() ==> old(next).is_some() && tree.links().limit(next.unwrap()) == tree.links().limit(old(next).unwrap()),
            leaf_prefix(tree.links(), *old(next), count@).1 == *next,
            tree.written() == old(tree).written() + leaf_prefix(tree.links(), *old(next), count@).0,
            leaf_path(tree.links(), tree.hidden(), *old(next), leaf_prefix(tree.links(), *old(next), count@).0, *next),
            marks_from(sibling_inputs(old(tree)), sibling_inputs(tree), cursor_rank(tree.links(), *old(next), *next)),
        ensures next.is_none(),
        decreases tree.links().cost(*next),
    ))]
    while let Some(first) = *next {
        #[cfg(verus_keep_ghost)]
        proof! { assert(tree.links().covers(first)); }
        let Some(leaf) = load_plain_leaf(tree, first, X) else {
            #[cfg(verus_keep_ghost)]
            proof! { assert(!plain_start_child(old(tree), first, X)); }
            return;
        };
        let following = match leaf.next {
            Some(id) => load_plain_leaf(tree, id, X),
            None => None,
        };
        #[cfg(verus_keep_ghost)]
        let before = saved_sibling(tree);
        #[cfg(verus_keep_ghost)]
        proof! {
            if following.is_none() && leaf.next.is_some() {
                assert(!plain_start_child(old(tree), leaf.next.unwrap(), X));
            }
        }
        #[cfg(verus_keep_ghost)]
        let saved_rects = save_rect_cursor::<I, T>(tree, *position);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(leaf.size == old(tree).solved_size(first));
            if let Some(second) = &following { assert(second.size == old(tree).solved_size(second.id)); }
            let rows = leaf_prefix(tree.links(), *old(next), count@).0;
            assert(saved_rects@ == paired_start_rects::<I, T, M>(old(tree), rows, *old(position), frame, X, gap));
        }
        emit_plain_leaf::<_, _, M>(tree, &leaf, position, cross, X, gap, frame.origin);
        #[cfg(verus_keep_ghost)]
        proof! {
            let prior = leaf_prefix(tree.links(), *old(next), count@);
            let prefix = leaf_prefix(tree.links(), *old(next), count@ + 1);
            assert(prefix.0 == prior.0.push(first));
            paired_rect_push::<I, T, M>(old(tree), prior.0, first, *old(position), frame, X, gap);
            let (raw, resulting) = start_step::<M>(saved_rects@.1, cross, X, leaf.size, gap);
            assert((tree.rectangles(), *position) == (put_rect::<I, T>(saved_rects@.0, first,
                (old(tree).rounding())(raw), frame.origin), resulting));
            assert((tree.rectangles(), *position) ==
                paired_start_rects::<I, T, M>(old(tree), prefix.0, *old(position), frame, X, gap));
            assert((old(tree).written() + prefix.0) =~= before@.1.push(first));
            leaf_path_push(tree.links(), tree.hidden(), *old(next), prior.0, first);
            let rank = cursor_rank(tree.links(), *old(next), prefix.1);
            assert(tree.links().rank(first) < rank);
            empty_writes_before(tree.links(), rank);
            staged_marks(before@.0, sibling_inputs(tree), Seq::empty(), Some(first), rank);
            marks_from_both(sibling_inputs(old(tree)), before@.0, sibling_inputs(tree), tree.links().rank(first), rank, rank);
        }
        #[cfg(verus_keep_ghost)]
        { count = step_leaf_prefix(count); }
        if let Some(leaf) = following {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(tree.links().covers(leaf.id));
                assert(leaf.id != first);
            }
            #[cfg(verus_keep_ghost)]
            let before = saved_sibling(tree);
            #[cfg(verus_keep_ghost)]
            let saved_rects = save_rect_cursor::<I, T>(tree, *position);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(leaf.size == old(tree).solved_size(leaf.id));
                let rows = leaf_prefix(tree.links(), *old(next), count@).0;
                assert(saved_rects@ == paired_start_rects::<I, T, M>(old(tree), rows, *old(position), frame, X, gap));
            }
            emit_plain_leaf::<_, _, M>(tree, &leaf, position, cross, X, gap, frame.origin);
            #[cfg(verus_keep_ghost)]
            proof! {
                let prior = leaf_prefix(tree.links(), *old(next), count@);
                let prefix = leaf_prefix(tree.links(), *old(next), count@ + 1);
                assert(prefix.0 == prior.0.push(leaf.id));
                paired_rect_push::<I, T, M>(old(tree), prior.0, leaf.id, *old(position), frame, X, gap);
                let (raw, resulting) = start_step::<M>(saved_rects@.1, cross, X, leaf.size, gap);
                assert((tree.rectangles(), *position) == (put_rect::<I, T>(saved_rects@.0, leaf.id,
                    (old(tree).rounding())(raw), frame.origin), resulting));
                assert((tree.rectangles(), *position) ==
                    paired_start_rects::<I, T, M>(old(tree), prefix.0, *old(position), frame, X, gap));
                assert((old(tree).written() + prefix.0) =~= before@.1.push(leaf.id));
                leaf_path_push(tree.links(), tree.hidden(), *old(next), prior.0, leaf.id);
                let rank = cursor_rank(tree.links(), *old(next), prefix.1);
                assert(tree.links().rank(leaf.id) < rank);
                empty_writes_before(tree.links(), rank);
                staged_marks(before@.0, sibling_inputs(tree), Seq::empty(), Some(leaf.id), rank);
                marks_from_both(sibling_inputs(old(tree)), before@.0, sibling_inputs(tree), tree.links().rank(leaf.id), rank, rank);
            }
            #[cfg(verus_keep_ghost)]
            { count = step_leaf_prefix(count); }
            *next = leaf.next;
        } else {
            *next = leaf.next;
            return;
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    requires old(tree).links().finite(), consistent_cursor(old(tree).links(), old(siblings).next),
        old(siblings).partial == PARTIAL,
        cursor_admitted(old(tree).links(), old(tree).hidden(), *old(siblings)),
    ensures final(tree).links() == old(tree).links(),
        sibling_progress(old(tree).links(), old(siblings).next, final(siblings).next, branch),
        final(siblings).partial == old(siblings).partial,
        final(tree).plain() == old(tree).plain(), final(tree).hidden() == old(tree).hidden(),
        executed_sibling_plan(old(tree), final(tree), old(siblings).next, final(siblings).next, branch, PARTIAL),
        cursor_admitted(final(tree).links(), final(tree).hidden(), *final(siblings)),
        ordinary_siblings(*old(siblings), PARTIAL) ==> ordinary_siblings(*final(siblings), PARTIAL),
    no_unwind
))]
fn dispatch<I: Copy, T: ParentTarget<I>, M: StackMath + FloatBounds, const PARTIAL: bool>(
    tree: &mut T, siblings: &mut Siblings<I, T::Flow>,
) -> Option<Branch<I>> {
    #[cfg(verus_keep_ghost)]
    proof! { reveal(ordinary_siblings); reveal(wrap_admitted); reveal(cursor_admitted); }
    let Siblings { next, frame, mode, .. } = siblings;
    match mode {
        Mode::Free => free::<_, _, PARTIAL>(tree, next, frame),
        Mode::Block(flow) => block::<_, _, M, PARTIAL>(tree, next, frame, flow),
        Mode::Wrap(cursor) => wrap::<_, _, M, PARTIAL>(tree, next, frame, cursor),
        Mode::Grid { parent, spacing } => grid::<_, _, M, PARTIAL>(tree, *parent, next, frame, *spacing),
        Mode::Stack { head, x, position, gap, auto_share, batch, paired_leaves } => {
            #[cfg(verus_keep_ghost)]
            let mut prefix = empty_staged_writes::<I>();
            #[cfg(verus_keep_ghost)]
            let original = saved_sibling(tree);
            #[cfg(verus_keep_ghost)]
            let initial = saved_next(next);
            #[cfg(verus_keep_ghost)]
            proof! {
                let before = sibling_inputs(old(tree));
                reveal(leaf_path);
                preserved_marks(before, sibling_inputs(tree), cursor_rank(before.links, old(siblings).next, *next));
            }
            if !PARTIAL && *paired_leaves {
                if *x {
                    paired_start_leaves::<_, _, M, true>(tree, next, frame, position, *gap);
                } else {
                    paired_start_leaves::<_, _, M, false>(tree, next, frame, position, *gap);
                }
                *paired_leaves = false;
                #[cfg(verus_keep_ghost)]
                { prefix = projected_leaf_prefix(tree, original, initial, next); }
                if next.is_none() {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        let inputs = sibling_inputs(old(tree));
                        leaves_split_siblings(inputs, old(siblings).next, prefix@, None);
                        reveal(sibling_writes);
                    }
                    return None;
                }
            }
            #[cfg(verus_keep_ghost)]
            let after_prefix = saved_sibling(tree);
            #[cfg(verus_keep_ghost)]
            let remaining = saved_next(next);
            let result = if *batch { stack::<_, _, M, false, true>(tree, *head, next, frame, *x, position, *gap, auto_share) }
                else { stack::<_, _, M, PARTIAL, false>(tree, *head, next, frame, *x, position, *gap, auto_share) };
            #[cfg(verus_keep_ghost)]
            proof! {
                if !PARTIAL {
                    let before = sibling_inputs(old(tree));
                    let mid = after_prefix@.0;
                    let after = sibling_inputs(tree);
                    let first = old(siblings).next;
                    let tail = remaining@;
                    leaves_split_siblings(before, first, prefix@, tail);
                    packets_keep_unvisited_marks(before, mid, tail, false);
                    let original = sibling_writes(before, first, false);
                    let pending = sibling_writes(mid, tail, false);
                    assert(tree.written() == after_prefix@.1 + pending.writes);
                    assert(tree.written() =~= old(tree).written() + original.writes);
                    if let Some(branch) = result {
                        let rank = before.links.rank(branch.parent) + 1;
                        packet_stays_in_scope(mid, tail.unwrap(), false);
                        marks_from_both(before, mid, after, cursor_rank(before.links, first, tail), rank, rank);
                    } else {
                        let end = cursor_rank(before.links, first, None);
                        let tail_end = cursor_rank(before.links, tail, None);
                        assert(end == tail_end);
                        marks_from_both(before, mid, after, cursor_rank(before.links, first, tail), tail_end, end);
                    }
                }
            }
            result
        }
    }
}

/// The fresh preparation marker describes two in-flow Start leaves. Both
/// records have clean placement work and this path runs without a snapper.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placed =>
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        old(tree).plain() ==> !placed && final(tree).plain() && final(tree).hidden() == old(tree).hidden()
            && (forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other)),
        if placed {
            old(tree).links().next(branch.first).is_some()
                && final(tree).written() == old(tree).written().push(branch.first)
                    .push(old(tree).links().next(branch.first).unwrap())
        } else { final(tree).written() == old(tree).written() },
        placed && old(tree).links().finite() && old(tree).links().cost(Some(branch.parent)) > 0
            && old(tree).links().first(branch.parent) == Some(branch.first) ==>
                final(tree).written() == old(tree).written()
                    + forest_writes(sibling_inputs(old(tree)), Some(branch.first), false),
        if placed {
            let style = old(tree).parent_layout(branch.parent);
            match style.layout {
                ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing } => {
                    let (main, cross): (int, int) = if axis is X { (0, 1) } else { (1, 0) };
                    let position = geometry::padded_start::<M>(branch.rect[main], style.padding[main][0]);
                    let cross_start = geometry::padded_start::<M>(branch.rect[cross], style.padding[cross][0]);
                    let second = old(tree).links().next(branch.first).unwrap();
                    let (first_rect, next) = start_step::<M>(position, cross_start, axis is X, old(tree).solved_size(branch.first), spacing);
                    let (second_rect, _) = start_step::<M>(next, cross_start, axis is X, old(tree).solved_size(second), spacing);
                    let first = put_rect::<I, T>(old(tree).rectangles(), branch.first, first_rect, branch.origin);
                    final(tree).rectangles() == put_rect::<I, T>(first, second, second_rect, branch.origin)
                },
                _ => false,
            }
        } else { final(tree).rectangles() == old(tree).rectangles() },
        !placed ==> (forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other)),
    no_unwind
))]
fn place_pair<I: Copy, T: ParentTarget<I>, M: StackMath>(tree: &mut T, branch: &Branch<I>) -> bool {
    if branch.partial || !tree.ready_pair(branch.parent) { return false; }
    let ParentStyle { layout, padding, flipped } = tree.parent_style(branch.parent);
    let ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing } = layout else { return false; };
    if flipped[0] || flipped[1] { return false; }
    let Some(second) = tree.next_sibling(branch.first) else { return false; };
    let x = matches!(axis, Axis::X);
    let (main, cross) = axes(x);
    let mut position = geometry::inner_start::<M>(branch.rect[main], padding[main][0]);
    let cross_start = geometry::inner_start::<M>(branch.rect[cross], padding[cross][0]);
    let a = M::place_start(&mut position, cross_start, x, tree.size(branch.first), spacing);
    let b = M::place_start(&mut position, cross_start, x, tree.size(second), spacing);
    node::write_snapped(tree, branch.first, a, branch.origin, false);
    node::write_snapped(tree, second, b, branch.origin, false);
    #[cfg(verus_keep_ghost)]
    proof! {
        let links = old(tree).links();
        if links.finite() && links.cost(Some(branch.parent)) > 0 && links.first(branch.parent) == Some(branch.first) {
            assert(links.leaf_pair(branch.parent) == Some((branch.first, second)));
            assert(links.covers(branch.parent));
            assert(links.covers(branch.first));
            assert(links.covers(second));
            reveal_with_fuel(forest_writes, 3);
            assert(forest_writes(sibling_inputs(old(tree)), Some(branch.first), false) =~= seq![branch.first, second]);
            assert(old(tree).written().push(branch.first).push(second) =~= old(tree).written() + seq![branch.first, second]);
        }
    }
    true
}

/// Recompute absolute Start positions using compact inputs from fresh sizing.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placed =>
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        old(tree).plain() ==> !placed && final(tree).plain() && final(tree).hidden() == old(tree).hidden()
            && (forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other)),
        placed && old(tree).links().finite() && old(tree).links().cost(Some(branch.first)) > 0
            && old(tree).links().first(branch.parent) == Some(branch.first) ==>
                final(tree).written() == old(tree).written()
                    + forest_writes(sibling_inputs(old(tree)), Some(branch.first), false),
        if placed {
            let span = old(tree).packed_span(branch.parent);
            let [start, end] = span.unwrap();
            &&& span.is_some() && start < end <= old(tree).packed_rows().len()
            &&& final(tree).written() == old(tree).written() + packed_ids(old(tree).packed_rows(), start as int, end as int)
            &&& wrote_group(old(tree).written(), final(tree).written(), branch.first)
            &&& final(tree).rectangles() == packed_rects::<I, T, M>(old(tree), branch, start, end)
        } else { final(tree).written() == old(tree).written() && final(tree).rectangles() == old(tree).rectangles() },
        !placed ==> (forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other)),
    no_unwind
))]
fn place_packed_leaves<I: Copy, T: ParentTarget<I>, M: StackMath>(tree: &mut T, branch: &Branch<I>) -> bool {
    if branch.partial { return false; }
    let Some([start, end]) = tree.packed_leaf_span(branch.parent) else { return false; };
    let ParentStyle { layout, padding, flipped } = tree.parent_style(branch.parent);
    let (axis, wrap) = match layout {
        ChildrenLayout::Stack { axis, arrange: Arrange::Start, .. } => (axis, None),
        ChildrenLayout::Wrap { axis, arrange: Arrange::Start, line_spacing, .. } => (axis, Some(line_spacing)),
        _ => return false,
    };
    if flipped[0] || flipped[1] { return false; }
    let rows = tree.take_packed_leaves();
    if start >= end || end > rows.len() || !tree.same_packed_id(rows[start].id, branch.first) {
        tree.put_packed_leaves(rows);
        return false;
    }
    let x = matches!(axis, Axis::X);
    let (main, cross) = axes(x);
    let position = geometry::inner_start::<M>(branch.rect[main], padding[main][0]);
    let cross_start = geometry::inner_start::<M>(branch.rect[cross], padding[cross][0]);
    match (x, wrap) {
        (true, Some(line_spacing)) => {
            publish_packed_wrap::<_, _, M, true>(tree, branch, &rows, start, end, position, cross_start, line_spacing);
        }
        (false, Some(line_spacing)) => {
            publish_packed_wrap::<_, _, M, false>(tree, branch, &rows, start, end, position, cross_start, line_spacing);
        }
        (true, None) => publish_packed_stack::<_, _, M, true>(tree, branch, rows.as_slice(), start, end, position, cross_start),
        (false, None) => publish_packed_stack::<_, _, M, false>(tree, branch, rows.as_slice(), start, end, position, cross_start),
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let written = tree.written();
        assert(written == old(tree).written() + packed_ids(rows@, start as int, end as int));
        assert(written.take(old(tree).written().len() as int) =~= old(tree).written());
        assert(wrote_group(old(tree).written(), written, branch.first));
        let inputs = sibling_inputs(old(tree));
        if inputs.links.finite() && inputs.links.cost(Some(branch.first)) > 0
            && inputs.links.first(branch.parent) == Some(branch.first) {
            complete_leaf_forest(inputs, Some(branch.first), packed_ids(rows@, start as int, end as int));
        }
    }
    tree.put_packed_leaves(rows);
    true
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires start <= end <= rows.len(),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        final(tree).written() == old(tree).written() + packed_ids(rows@, start as int, end as int),
        final(tree).rectangles() == draw_rows::<I, T, _, _>(old(tree).rectangles(), rows@.subrange(start as int, end as int),
            position, branch.origin, packed_stack_step::<I, M>(cross_start, HORIZONTAL)).0,
    no_unwind
))]
fn publish_packed_stack<I: Copy, T: ParentTarget<I>, M: StackMath, const HORIZONTAL: bool>(
    tree: &mut T, branch: &Branch<I>, rows: &[PreparedStackLeaf<I>], start: usize, end: usize,
    position: f32, cross_start: f32,
) {
    let mut at = start;
    let mut cursor = position;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(packed_ids(rows@, start as int, start as int) =~= Seq::<I>::empty());
        reveal(draw_rows);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= at <= end <= rows.len(),
            tree.links() == old(tree).links(),
            tree.hidden() == old(tree).hidden(), tree.plain() == old(tree).plain(),
            tree.written() == old(tree).written() + packed_ids(rows@, start as int, at as int),
            (tree.rectangles(), cursor) == draw_rows::<I, T, _, _>(old(tree).rectangles(), rows@.subrange(start as int, at as int),
                position, branch.origin, packed_stack_step::<I, M>(cross_start, HORIZONTAL)),
        decreases end - at,
    ))]
    while at < end {
        let row = rows[at];
        #[cfg(verus_keep_ghost)]
        let before = save_cursor(cursor);
        let from = M::with_margin(cursor, row.main_leading);
        cursor = M::add(from, row.advance);
        let across = M::with_margin(cross_start, row.cross_leading);
        let (left, top) = if HORIZONTAL { (from, across) } else { (across, from) };
        let [width, height] = row.size;
        let rect = [[left, M::add(left, width)], [top, M::add(top, height)]];
        node::write_snapped(tree, row.id, rect, branch.origin, false);
        #[cfg(verus_keep_ghost)]
        proof! {
            packed_ids_push(rows@, start as int, at as int);
            let taken = rows@.subrange(start as int, at as int + 1);
            assert(taken.len() == at - start + 1);
            assert(taken.last() == row);
            assert(taken.drop_last() =~= rows@.subrange(start as int, at as int));
            let step = packed_stack_step::<I, M>(cross_start, HORIZONTAL);
            let prior = draw_rows::<I, T, _, _>(old(tree).rectangles(), taken.drop_last(), position, branch.origin, step);
            assert(prior.1 == before@);
            assert(from == adjusted::<M>(before@, row.main_leading));
            assert(across == adjusted::<M>(cross_start, row.cross_leading));
            assert(cursor == M::sum(from, row.advance));
            assert(step(row, before@) == (row.id, rect, cursor));
            reveal(draw_rows);
            assert(draw_rows::<I, T, _, _>(old(tree).rectangles(), taken, position, branch.origin, step)
                == (tree.rectangles(), cursor));
            assert((old(tree).written() + packed_ids(rows@, start as int, at as int)).push(row.id)
                =~= old(tree).written() + packed_ids(rows@, start as int, at as int + 1));
        }
        at += 1;
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires start <= end <= rows.len(),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        final(tree).written() == old(tree).written() + packed_ids(rows@, start as int, end as int),
        final(tree).rectangles() == draw_rows::<I, T, _, _>(old(tree).rectangles(), rows@.subrange(start as int, end as int),
            (main_start, cross_position, 0.0), branch.origin, packed_wrap_step::<I, M>(main_start, line_spacing, HORIZONTAL)).0,
    no_unwind
))]
fn publish_packed_wrap<I: Copy, T: ParentTarget<I>, M: StackMath, const HORIZONTAL: bool>(
    tree: &mut T, branch: &Branch<I>, rows: &Vec<PreparedStackLeaf<I>>, start: usize, end: usize,
    main_start: f32, cross_position: f32, line_spacing: f32,
) {
    let mut position = main_start;
    let mut cross_cursor = cross_position;
    let mut cross_start = 0.0;
    let mut at = start;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(packed_ids(rows@, start as int, start as int) =~= Seq::<I>::empty());
        reveal(draw_rows);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= at <= end <= rows.len(), tree.links() == old(tree).links(),
            tree.hidden() == old(tree).hidden(), tree.plain() == old(tree).plain(),
            tree.written() == old(tree).written() + packed_ids(rows@, start as int, at as int),
            (tree.rectangles(), (position, cross_cursor, cross_start)) == draw_rows::<I, T, _, _>(old(tree).rectangles(),
                rows@.subrange(start as int, at as int), (main_start, cross_position, 0.0), branch.origin,
                packed_wrap_step::<I, M>(main_start, line_spacing, HORIZONTAL)),
        decreases end - at,
    ))]
    while at < end {
        let row = rows[at];
        if let Some(height) = row.line_height::<M>() {
            position = main_start;
            cross_start = M::add(cross_cursor, 0.0);
            cross_cursor = M::add(cross_cursor, M::add(height, line_spacing));
        }
        let [width, height] = row.size;
        let (left, top) = if HORIZONTAL { (position, cross_start) } else { (cross_start, position) };
        let rect = [[left, M::add(left, width)], [top, M::add(top, height)]];
        position = M::add(position, row.advance);
        node::write_snapped(tree, row.id, rect, branch.origin, false);
        #[cfg(verus_keep_ghost)]
        proof! {
            packed_ids_push(rows@, start as int, at as int);
            let taken = rows@.subrange(start as int, at as int + 1);
            assert(taken.last() == row && taken.drop_last() =~= rows@.subrange(start as int, at as int));
            reveal(draw_rows);
            assert((old(tree).written() + packed_ids(rows@, start as int, at as int)).push(row.id)
                =~= old(tree).written() + packed_ids(rows@, start as int, at as int + 1));
        }
        at += 1;
    }
}

/// Publish one prepared run without visiting its per-leaf records.
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        final(tree).written() == old(tree).written() + ids@,
        final(tree).rectangles() == ({
            let (main, cross): (int, int) = if X { (0, 1) } else { (1, 0) };
            let position = geometry::padded_start::<M>(branch.rect[main], padding[main][0]);
            let cross_start = geometry::padded_start::<M>(branch.rect[cross], padding[cross][0]);
            draw_rows::<I, T, _, _>(old(tree).rectangles(), ids@, position, branch.origin, uniform_step::<I, M>(cross_start, X, size, gap)).0
        }),
    no_unwind
))]
fn emit_uniform_leaves<I: Copy, T: ParentTarget<I>, M: StackMath, const X: bool>(
    tree: &mut T, ids: &[I], size: [f32; 2], branch: &Branch<I>, padding: Edges, gap: f32,
) {
    let (main, cross) = axes(X);
    let position = geometry::inner_start::<M>(branch.rect[main], padding[main][0]);
    let cross_start = geometry::inner_start::<M>(branch.rect[cross], padding[cross][0]);
    let mut cursor = position;
    let mut at = 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(ids@.take(0) =~= Seq::<I>::empty());
        reveal(draw_rows);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant at <= ids.len(), tree.links() == old(tree).links(),
            tree.hidden() == old(tree).hidden(), tree.plain() == old(tree).plain(),
            tree.written() == old(tree).written() + ids@.take(at as int),
            (tree.rectangles(), cursor) == draw_rows::<I, T, _, _>(old(tree).rectangles(), ids@.take(at as int), position,
                branch.origin, uniform_step::<I, M>(cross_start, X, size, gap)),
        decreases ids.len() - at,
    ))]
    while at < ids.len() {
        let id = ids[at];
        let rect = M::place_start(&mut cursor, cross_start, X, size, gap);
        node::write_snapped(tree, id, rect, branch.origin, false);
        #[cfg(verus_keep_ghost)]
        proof! {
            let taken = ids@.take(at as int + 1);
            assert(taken.last() == id && taken.drop_last() =~= ids@.take(at as int));
            reveal(draw_rows);
            assert(ids@.take(at as int + 1) =~= ids@.take(at as int).push(id));
        }
        at += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(ids@.take(ids.len() as int) =~= ids@); }
}

#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placed =>
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        if placed {
            final(tree).written() == old(tree).written() + rows@
                && rows.len() > 0 && rows@[0] == branch.first
                && wrote_group(old(tree).written(), final(tree).written(), branch.first)
                && final(tree).rectangles() == uniform_rects::<I, T, M>(old(tree), branch, size, rows@)
        } else { final(tree).written() == old(tree).written() && final(tree).rectangles() == old(tree).rectangles() },
        !placed ==> (forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other)),
    no_unwind
))]
fn replay_uniform_leaves<I: Copy, T: ParentTarget<I>, M: StackMath>(
    tree: &mut T, branch: &Branch<I>, size: [f32; 2], rows: Vec<I>,
) -> bool {
    let ParentStyle { layout, padding, flipped } = tree.parent_style(branch.parent);
    let mut placed = false;
    if let ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing } = layout {
        if !flipped[0] && !flipped[1] && !rows.is_empty() && tree.same_packed_id(rows[0], branch.first) {
            if matches!(axis, Axis::X) {
                emit_uniform_leaves::<_, _, M, true>(tree, rows.as_slice(), size, branch, padding, spacing);
            } else {
                emit_uniform_leaves::<_, _, M, false>(tree, rows.as_slice(), size, branch, padding, spacing);
            }
            placed = true;
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        if placed {
            assert(tree.written().take(old(tree).written().len() as int) =~= old(tree).written());
            assert(wrote_group(old(tree).written(), tree.written(), branch.first));
        }
    }
    tree.recycle_uniform_leaves(rows);
    placed
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placed =>
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        old(tree).plain() ==> !placed && final(tree).plain() && final(tree).hidden() == old(tree).hidden()
            && (forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other)),
        placed && old(tree).links().finite() && old(tree).links().cost(Some(branch.first)) > 0
            && old(tree).links().first(branch.parent) == Some(branch.first) ==>
                final(tree).written() == old(tree).written()
                    + forest_writes(sibling_inputs(old(tree)), Some(branch.first), false),
        if placed {
            let payload = old(tree).uniform_rows(branch.parent);
            &&& payload.is_some()
            &&& final(tree).written() == old(tree).written() + payload.unwrap().1
            &&& wrote_group(old(tree).written(), final(tree).written(), branch.first)
            &&& final(tree).rectangles() == uniform_rects::<I, T, M>(old(tree), branch, payload.unwrap().0, payload.unwrap().1)
        } else { final(tree).written() == old(tree).written() && final(tree).rectangles() == old(tree).rectangles() },
        !placed ==> (forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other)),
    no_unwind
))]
fn place_uniform_leaves<I: Copy, T: ParentTarget<I>, M: StackMath>(tree: &mut T, branch: &Branch<I>) -> bool {
    if branch.partial { return false; }
    let Some((size, rows)) = tree.take_uniform_leaves(branch.parent) else { return false; };
    #[cfg(verus_keep_ghost)]
    proof! {
        let inputs = sibling_inputs(old(tree));
        if inputs.links.finite() && inputs.links.cost(Some(branch.first)) > 0
            && inputs.links.first(branch.parent) == Some(branch.first) {
            complete_leaf_forest(inputs, Some(branch.first), rows@);
        }
    }
    replay_uniform_leaves::<_, _, M>(tree, branch, size, rows)
}

// All three shortcuts either leave the child forest to the cursor or publish it in full.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placed =>
    requires old(tree).links().finite(), old(tree).links().cost(Some(branch.parent)) > 0,
        old(tree).links().cost(Some(branch.first)) > 0,
        old(tree).links().first(branch.parent) == Some(branch.first), !branch.partial,
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(), old(tree).plain() ==> !placed,
        if placed {
            final(tree).written() == old(tree).written()
                + forest_writes(sibling_inputs(old(tree)), Some(branch.first), false)
        } else {
            final(tree).written() == old(tree).written()
                && (forall|other: I| #[trigger] final(tree).mark(other) == old(tree).mark(other))
        },
    no_unwind
))]
fn place_prepared_branch<I: Copy, T: ParentTarget<I>, M: StackMath>(tree: &mut T, branch: &Branch<I>) -> bool {
    if place_pair::<_, _, M>(tree, branch) { return true; }
    #[cfg(verus_keep_ghost)]
    proof! {
        forests_keep_unvisited_marks(sibling_inputs(old(tree)), sibling_inputs(tree), Some(branch.first), false);
    }
    if place_packed_leaves::<_, _, M>(tree, branch) { return true; }
    #[cfg(verus_keep_ghost)]
    proof! {
        forests_keep_unvisited_marks(sibling_inputs(old(tree)), sibling_inputs(tree), Some(branch.first), false);
    }
    place_uniform_leaves::<_, _, M>(tree, branch)
}

#[cfg(verus_keep_ghost)]
verus! {
spec fn branch_writes<I>(inputs: SiblingInputs<I>, branch: Option<Branch<I>>) -> Seq<I> {
    match branch {
        Some(branch) => forest_writes(inputs, Some(branch.first), branch.partial),
        None => Seq::empty(),
    }
}
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(child =>
    requires old(tree).links().finite(), consistent_cursor(old(tree).links(), old(cursor).next),
        cursor_admitted(old(tree).links(), old(tree).hidden(), *old(cursor)),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        cursor_admitted(final(tree).links(), final(tree).hidden(), *final(cursor)),
        !old(cursor).partial ==> (
            final(tree).written() + branch_writes(sibling_inputs(old(tree)), child)
                + forest_writes(sibling_inputs(old(tree)), final(cursor).next, false)
            == old(tree).written() + forest_writes(sibling_inputs(old(tree)), old(cursor).next, false)
        ),
        final(cursor).partial == old(cursor).partial,
        old(tree).plain() && ordinary_siblings(*old(cursor), old(cursor).partial) ==> {
            &&& final(tree).plain() && final(tree).hidden() == old(tree).hidden()
            &&& ordinary_siblings(*final(cursor), old(cursor).partial)
            &&& executed_sibling_plan(old(tree), final(tree), old(cursor).next, final(cursor).next, child, old(cursor).partial)
        },
        consistent_cursor(old(tree).links(), final(cursor).next),
        match child {
            Some(child) => old(tree).links().first(child.parent) == Some(child.first)
                && (child.partial ==> old(cursor).partial)
                && old(tree).links().cost(Some(child.first)) > 0
                && old(tree).links().cost(Some(child.first)) + old(tree).links().cost(final(cursor).next)
                    < old(tree).links().cost(old(cursor).next),
            None => final(cursor).next.is_none(),
        },
    no_unwind
))]
fn advance<I: Copy, T: ParentTarget<I>, M: StackMath + FloatBounds>(
    tree: &mut T, cursor: &mut Siblings<I, T::Flow>,
) -> Option<Branch<I>> {
    let partial = cursor.partial;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.links() == old(tree).links(), tree.links().finite(),
            tree.hidden() == old(tree).hidden(), tree.plain() == old(tree).plain(),
            cursor_admitted(tree.links(), tree.hidden(), *cursor),
            !partial ==> tree.written() + forest_writes(sibling_inputs(old(tree)), cursor.next, false)
                == old(tree).written() + forest_writes(sibling_inputs(old(tree)), old(cursor).next, false),
            consistent_cursor(tree.links(), cursor.next),
            tree.links().cost(cursor.next) <= tree.links().cost(old(cursor).next),
            cursor.partial == partial, old(cursor).partial == partial,
            old(tree).plain() && ordinary_siblings(*old(cursor), partial) ==> {
                &&& tree.plain() && *cursor == *old(cursor)
                &&& sibling_inputs(tree) == sibling_inputs(old(tree))
                &&& tree.written() == old(tree).written()
            },
        decreases tree.links().cost(cursor.next),
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        let before = saved_sibling(tree);
        #[cfg(verus_keep_ghost)]
        let first = saved_next(&cursor.next);
        let branch = if partial { dispatch::<_, _, M, true>(tree, cursor) }
            else { dispatch::<_, _, M, false>(tree, cursor) };
        #[cfg(verus_keep_ghost)]
        proof! {
            let inputs = sibling_inputs(old(tree));
            if let Some(id) = first@ {
                packet_stays_in_scope(before@.0, id, partial);
            } else {
                empty_sibling_plan(before@.0, partial);
            }
            if !partial {
                packets_keep_unvisited_marks(inputs, before@.0, first@, false);
                sibling_plan_splits_forest(inputs, first@, false);
                let children = branch_writes(inputs, branch);
                let resume = forest_writes(inputs, cursor.next, false);
                assert(tree.written() + children + resume =~= before@.1 + forest_writes(inputs, first@, false));
            }
        }
        let Some(branch) = branch else { return None; };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(tree.links().cost(Some(branch.parent)) > 0);
            assert(tree.links().first(branch.parent) == Some(branch.first));
            assert(branch.partial ==> partial);
        }
        #[cfg(verus_keep_ghost)]
        let dispatched = saved_sibling(tree);
        #[cfg(verus_keep_ghost)]
        proof! {
            if old(tree).plain() && ordinary_siblings(*old(cursor), partial) {
                let cutoff = tree.links().rank(branch.parent) + 1;
                assert(marks_from(sibling_inputs(old(tree)), dispatched@.0, cutoff));
            }
        }
        if partial || !place_prepared_branch::<_, _, M>(tree, &branch) {
            #[cfg(verus_keep_ghost)]
            proof! {
                if old(tree).plain() && ordinary_siblings(*old(cursor), partial) {
                    let cutoff = tree.links().rank(branch.parent) + 1;
                    preserved_marks(dispatched@.0, sibling_inputs(tree), cutoff);
                    marks_from_both(sibling_inputs(old(tree)), dispatched@.0, sibling_inputs(tree), cutoff, cutoff, cutoff);
                }
            }
            return Some(branch);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let inputs = sibling_inputs(old(tree));
            let children = forest_writes(inputs, Some(branch.first), false);
            forests_keep_unvisited_marks(inputs, dispatched@.0, Some(branch.first), false);
            assert(tree.written() == dispatched@.1 + children);
        }
    }
}

/// Traverse the real mode cursors in preorder, including branches deep enough
/// to use spill storage. Each dispatch consumes at least the published node.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tree).links().finite(), old(tree).links().cost(Some(start.first)) > 0,
        old(tree).links().first(start.parent) == Some(start.first),
    ensures final(tree).links() == old(tree).links(), final(tree).hidden() == old(tree).hidden(),
        final(tree).plain() == old(tree).plain(),
        (old(tree).plain() || !start.partial) ==> final(tree).written() == old(tree).written()
            + forest_writes(sibling_inputs(old(tree)), Some(start.first), start.partial),
    no_unwind
))]
pub(crate) fn walk<I: Copy, T: ParentTarget<I>, M: StackMath + FloatBounds, V: VecMemory, const N: usize>(
    tree: &mut T, start: Branch<I>,
) {
    if place_uniform_leaves::<_, _, M>(tree, &start) { return; }
    let mut pending: WorkStack<Siblings<I, T::Flow>, N> = crate::work_stack::work_stack::<_, N, V>(V::empty());
    let mut cursor = cursor_for::<_, _, M>(tree, start);
    #[cfg(verus_keep_ghost)]
    proof! {
        empty_pending_admitted(tree.links(), tree.hidden(), pending.items(), !start.partial, old(tree).plain());
        if old(tree).plain() || !start.partial {
            let inputs = sibling_inputs(old(tree));
            assert(tree.plain() == old(tree).plain() && tree.hidden() == old(tree).hidden());
            assert(cursor.partial == start.partial);
            assert(old(tree).plain() ==> ordinary_siblings(cursor, cursor.partial));
            assert(tree.written() == old(tree).written());
            preserved_marks(inputs, sibling_inputs(tree), inputs.links.rank(start.first));
            assert(pending.items() =~= Seq::<Siblings<I, T::Flow>>::empty());
            empty_pending_scope(inputs.links, cursor, pending.items());
            let first = placement_walk::frontier(Some(cursor), pending.items());
            assert(first =~= seq![cursor]);
            assert(first.first() == cursor && first.drop_first().len() == 0);
            reveal_with_fuel(frontier_writes, 2);
            assert(frontier_writes(inputs, first) == forest_writes(inputs, Some(start.first), start.partial));
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant pending.valid(), tree.links().finite(), tree.links() == old(tree).links(),
            tree.plain() == old(tree).plain(), tree.hidden() == old(tree).hidden(),
            tree.links().cost(cursor.next) > 0,
            old(tree).plain() ==> ordinary_siblings(cursor, cursor.partial),
            cursor_admitted(tree.links(), tree.hidden(), cursor), !start.partial ==> !cursor.partial,
            forall |i: int| 0 <= i < pending.items().len() ==> tree.links().cost((#[trigger] pending.items()[i]).next) > 0,
            pending_admitted(tree.links(), tree.hidden(), pending.items(), !start.partial, old(tree).plain()),
            !start.partial ==> tree.written() + frontier_writes(sibling_inputs(old(tree)),
                placement_walk::frontier(Some(cursor), pending.items()))
                == old(tree).written() + forest_writes(sibling_inputs(old(tree)), Some(start.first), false),
            (old(tree).plain() && start.partial) ==> {
                &&& marks_from(sibling_inputs(old(tree)), sibling_inputs(tree), tree.links().rank(cursor.next.unwrap()))
                &&& scope_before_pending(tree.links(), cursor, pending.items())
                &&& pending_scopes(tree.links(), pending.items())
                &&& tree.written() + frontier_writes(sibling_inputs(old(tree)),
                    placement_walk::frontier(Some(cursor), pending.items()))
                    == old(tree).written() + forest_writes(sibling_inputs(old(tree)), Some(start.first), start.partial)
            },
        decreases tree.links().cost(cursor.next) + pending_cost(tree.links(), pending.items()),
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        let before = saved(tree, &pending, &cursor);
        #[cfg(verus_keep_ghost)]
        let before_write = saved_sibling(tree);
        let branch = advance::<_, _, M>(tree, &mut cursor);
        #[cfg(verus_keep_ghost)]
        let keys = saved_branch_keys(&branch);
        let child = match branch {
            Some(branch) => Some(cursor_for::<_, _, M>(tree, branch)),
            None => None,
        };
        let more = cursor.next.is_some();
        let upcoming = placement_walk::next::<_, N, V>(&mut pending, child, &cursor, more);
        #[cfg(verus_keep_ghost)]
        proof! {
            if !start.partial {
                let inputs = sibling_inputs(old(tree));
                let (previous_pending, _, previous) = before@;
                let (before_inputs, written) = before_write@;
                forests_keep_unvisited_marks(inputs, before_inputs, previous.next, false);
                forests_keep_unvisited_marks(inputs, before_inputs, cursor.next, false);
                if let Some(inside) = child {
                    forests_keep_unvisited_marks(inputs, before_inputs, inside.next, false);
                }
                replacing_forced_cursor(inputs, previous, cursor, child, previous_pending, written, tree.written());
                let next = placement_walk::frontier(upcoming, pending.items());
                assert(tree.written() + frontier_writes(inputs, next) =~=
                    old(tree).written() + forest_writes(inputs, Some(start.first), false));
                if upcoming.is_none() {
                    assert(next.len() == 0);
                    reveal(frontier_writes);
                }
            }
            if old(tree).plain() && start.partial {
                let inputs = sibling_inputs(old(tree));
                let (previous_pending, _, previous) = before@;
                let (before_inputs, written) = before_write@;
                let links = inputs.links;
                let id = previous.next.unwrap();
                assert(links.covers(id));
                let selected = sibling_writes(inputs, previous.next, previous.partial);
                packets_keep_unvisited_marks(inputs, before_inputs, previous.next, previous.partial);
                assert(selected.branch == keys@);
                packet_stays_in_scope(inputs, id, previous.partial);
                assert(tree.written() == written + selected.writes);
                replacing_cursor(inputs, previous, cursor, child, previous_pending);
                let cutoff = match selected.branch {
                    Some((parent, first, _)) => {
                        assert(links.covers(first));
                        assert(links.rank(parent) < links.rank(first) < links.limit(first));
                        links.rank(parent) + 1
                    },
                    None => links.limit(id),
                };
                assert(links.rank(id) <= cutoff <= links.limit(id));
                assert(marks_from(before_inputs, sibling_inputs(tree), cutoff));
                let next_frontier = placement_walk::frontier(upcoming, pending.items());
                assert(tree.written() + frontier_writes(inputs, next_frontier) =~=
                    old(tree).written() + forest_writes(inputs, Some(start.first), start.partial));
                assert(tree.plain() && tree.hidden() == old(tree).hidden());
                if let Some(resumed) = upcoming {
                    assert(ordinary_siblings(cursor, cursor.partial));
                    pending_scope_step(links, previous, cursor, child, resumed, previous_pending, pending.items());
                    if let Some(inside) = child {
                        assert(ordinary_siblings(inside, inside.partial));
                        assert(resumed == inside);
                        assert(cutoff <= links.rank(inside.next.unwrap()));
                        assert(links.limit(inside.next.unwrap()) <= links.limit(id));
                    } else {
                        assert(previous_pending.len() > 0 && resumed == previous_pending.last());
                        assert(previous_pending.last() == previous_pending[previous_pending.len() - 1]);
                        assert(links.limit(id) <= links.rank(resumed.next.unwrap()));
                    }
                    let rank = links.rank(resumed.next.unwrap());
                    marks_from_both(inputs, before_inputs, sibling_inputs(tree), links.rank(id), cutoff, rank);
                } else {
                    assert(next_frontier.len() == 0);
                    reveal(frontier_writes);
                    assert(tree.written() == old(tree).written() + forest_writes(inputs, Some(start.first), start.partial));
                }
            }
        }
        let Some(upcoming) = upcoming else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert((old(tree).plain() || !start.partial) ==> tree.written() == old(tree).written()
                    + forest_writes(sibling_inputs(old(tree)), Some(start.first), start.partial));
            }
            return;
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let prior = before@.0;
            pending_cost_step(tree.links(), before@.2, cursor, child, upcoming, prior, pending.items());
            pending_admission_step(tree.links(), tree.hidden(), cursor, child, upcoming, prior, pending.items(),
                !start.partial, old(tree).plain());
        }
        cursor = upcoming;
    }
}

/// Publish a subtree root before entering the checked sibling cursor loop.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tree).links().finite(), old(tree).links().cost(Some(root)) > 0,
    ensures final(tree).links() == old(tree).links(),
        (old(tree).plain() || !PARTIAL) && !(old(tree).hidden())(root) ==>
            final(tree).written() == old(tree).written() + subtree_writes(sibling_inputs(old(tree)), root, PARTIAL),
        (!node::visits(old(tree).mark(root), PARTIAL) || old(tree).links().first(root).is_none())
            ==> final(tree).rectangles() == node::resulting_rectangles(old(tree), root, rect, origin, PARTIAL),
    no_unwind
))]
pub(crate) fn place_subtree<
    I: Copy, T: ParentTarget<I>, M: StackMath + FloatBounds, V: VecMemory, const N: usize, const PARTIAL: bool,
>(tree: &mut T, root: I, rect: Edges, origin: [f32; 2]) {
    #[cfg(verus_keep_ghost)]
    proof! { assert(tree.links().covers(root)); }
    if let Some(branch) = emit::<_, _, PARTIAL>(tree, root, rect, origin) {
        #[cfg(verus_keep_ghost)]
        proof! {
            if (old(tree).plain() || !PARTIAL) && !(old(tree).hidden())(root) {
                assert(tree.links().rank(root) < tree.links().rank(branch.first));
                let rank = tree.links().rank(branch.first);
                empty_writes_before(tree.links(), rank);
                staged_marks(sibling_inputs(old(tree)), sibling_inputs(tree), Seq::empty(), Some(root), rank);
                forests_keep_unvisited_marks(sibling_inputs(old(tree)), sibling_inputs(tree), Some(branch.first), branch.partial);
            }
        }
        walk::<_, _, M, V, N>(tree, branch);
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(plan =>
    ensures final(tree).links() == old(tree).links(),
        final(tree).hidden() == old(tree).hidden(), final(tree).plain() == old(tree).plain(),
        final(tree).root_key() == old(tree).root_key(), final(tree).written() == old(tree).written(),
        forall|id: I| #[trigger] final(tree).mark(id) == old(tree).mark(id),
        plan.is_some() <==> !(old(tree).hidden())(old(tree).root_key()),
        old(tree).links().cost(Some(old(tree).root_key())) > 0,
        plan.is_some() ==> ({
            let root = old(tree).root_key();
            let [width, height] = old(tree).solved_size(root);
            plan.unwrap() == (root, [[0.0f32, width], [0.0f32, height]], old(tree).configured_scale())
        }),
    no_unwind
))]
pub(crate) fn root_plan<I: Copy, T: RootTarget<I>>(tree: &mut T) -> Option<(I, Edges, Option<f32>)> {
    tree.clear_scale_changed();
    let root = tree.root_id();
    if tree.disabled(root) { return None; }
    let [width, height] = tree.size(root);
    Some((root, [[0.0, width], [0.0, height]], tree.pixel_scale()))
}

/// Reuse the preceding unrounded edge when an enabled Stack leaf is appended.
/// The shape is checked before the single write can reach the adapter.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(appended =>
    ensures final(tree).links() == old(tree).links(),
        final(tree).written() == (if appended { old(tree).written().push(child) } else { old(tree).written() }),
        appended ==> old(tree).links().first(child).is_none(),
        !appended ==> final(tree).rectangles() == old(tree).rectangles(),
        appended ==> final(tree).rectangles() == old(tree).rectangles().insert(child, final(tree).rectangles()[child]),
    no_unwind
))]
pub(crate) fn append_stack_leaf<I: Copy, T: ParentTarget<I>, M: StackMath>(
    tree: &mut T, parent: I, child: I, rect: Edges, previous: Option<(I, Edges)>, rounded: bool,
) -> bool {
    if rounded || tree.first_child(child).is_some() { return false; }
    let origin = [rect[0][0], rect[1][0]];
    let ParentStyle { layout, padding, flipped } = tree.parent_style(parent);
    let ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing } = layout else { return false };
    let frame = Frame { edges: rect, origin, padding, flipped };
    let x = matches!(axis, Axis::X);
    let (main, _) = axes(x);
    let style = tree.align_style(child);
    if frame.flipped[main] || style.disabled || style.free { return false; }

    let [begin, _] = geometry::inner_range::<M>(frame.edges[main], frame.padding[main]);
    let mut cursor = if let Some((prior, edges)) = previous {
        let style = tree.align_style(prior);
        if style.disabled || style.free { return false; }
        // Recompute the advance using the same operation order as a full walk.
        M::after_item(edges[main][0], tree.size(prior)[main], style.margin[main][1], spacing)
    } else { begin };
    let size = tree.size(child);
    let rect = stack_item::<M>(&frame, style, size, x, &mut cursor, spacing);
    emit::<_, _, false>(tree, child, rect, origin);
    true
}
