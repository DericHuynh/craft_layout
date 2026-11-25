//! Project placement work and rectangle writes onto the host adapter.
#![allow(unexpected_cfgs)]

use crate::declarations::{LayoutParams, Xy};
use crate::prepare_frame::FrameFloat;
use crate::prepare_nodes::Records;
#[cfg(not(verus_keep_ghost))]
use crate::place::placement_modes::{FreeStyle, GridStyle, ParentStyle, StackStyle, zero_margins};
#[cfg(verus_keep_ghost)]
use crate::placement::modes::{FreeStyle, GridStyle, ParentStyle, StackStyle, zero_margins};
#[cfg(verus_keep_ghost)]
use crate::prepare_frame::FrameWords;
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::placement_work::{PlacementWork, update_scale_dirty};
#[cfg(verus_keep_ghost)]
use crate::{placement::{PlacementWork, kernel::update_scale_dirty}, prepare_nodes::live};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(crate) type Edges<W> = [[W; 2]; 2];

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait OutputModel<I, W> {
    spec fn emitted(&self) -> Seq<(I, Edges<W>, Edges<W>)>;
    spec fn retained(&self) -> bool;
    spec fn rectangles(&self) -> Map<I, (Edges<W>, Edges<W>)>;
}

pub(crate) open spec fn stable_rectangle<F: FrameFloat>(input: Edges<f32>, output: Edges<f32>) -> bool {
    forall|axis: int, edge: int| 0 <= axis < 2 && 0 <= edge < 2 ==>
        #[trigger] F::word(output@[axis]@[edge]) == crate::input_words::layout_word(F::word(input@[axis]@[edge]))
}

pub(crate) open spec fn stable_value<F: FrameFloat>(value: f32) -> f32 {
    F::decode(crate::input_words::layout_word(F::word(value)))
}

pub(crate) open spec fn stable_rectangle_value<F: FrameFloat>(edges: Edges<f32>) -> Edges<f32> {
    let [[left, right], [top, bottom]] = edges;
    [[stable_value::<F>(left), stable_value::<F>(right)], [stable_value::<F>(top), stable_value::<F>(bottom)]]
}

pub(crate) proof fn same_published_edges<F: FrameFloat>(
    left: Edges<f32>, right: Edges<f32>, left_output: Edges<f32>, right_output: Edges<f32>,
)
    requires stable_rectangle::<F>(left, left_output), stable_rectangle::<F>(right, right_output),
        forall|axis: int, edge: int| 0 <= axis < 2 && 0 <= edge < 2 ==> {
            let a = #[trigger] F::word(left@[axis]@[edge]);
            let b = F::word(right@[axis]@[edge]);
            a == b || crate::input_words::layout_nan(a) && crate::input_words::layout_nan(b)
        },
    ensures forall|axis: int, edge: int| 0 <= axis < 2 && 0 <= edge < 2 ==>
        #[trigger] F::word(left_output@[axis]@[edge]) == F::word(right_output@[axis]@[edge]),
{
    assert forall|axis: int, edge: int| 0 <= axis < 2 && 0 <= edge < 2 implies
        #[trigger] F::word(left_output@[axis]@[edge]) == F::word(right_output@[axis]@[edge]) by {
        let a = F::word(left@[axis]@[edge]);
        let b = F::word(right@[axis]@[edge]);
        crate::input_words::stable_layout_words(a, b);
    }
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait OutputModel<I, W> {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Output<I, W>: OutputModel<I, W> {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).emitted() == old(self).emitted().push((id,
                [absolute.x, absolute.y], [local.x, local.y])),
            final(self).retained() == old(self).retained(),
            old(self).retained() ==> final(self).rectangles() == old(self).rectangles().insert(id,
                ([absolute.x, absolute.y], [local.x, local.y])),
        no_unwind
    ))]
    fn write_output(&mut self, id: I, absolute: Xy<[W; 2]>, local: Xy<[W; 2]>);
}

#[cfg(not(verus_keep_ghost))]
impl<T: crate::TreeAdapter + ?Sized> OutputModel<T::NodeId, f32> for T {}

#[cfg(not(verus_keep_ghost))]
impl<T: crate::TreeAdapter + ?Sized> Output<T::NodeId, f32> for T {
    #[inline(always)]
    fn write_output(&mut self, id: T::NodeId, absolute: Xy<[f32; 2]>, local: Xy<[f32; 2]>) {
        self.write_output_rect(id, absolute, local);
    }
}

/// The ordinary and checked sinks put the same axis order on the host call.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(host).emitted() == old(host).emitted().push((id, absolute, local)),
        final(host).retained() == old(host).retained(),
        old(host).retained() ==> final(host).rectangles() == old(host).rectangles().insert(id, (absolute, local)),
    no_unwind
))]
pub(crate) fn publish<I, W: Copy, T: Output<I, W> + ?Sized>(
    host: &mut T, id: I, absolute: Edges<W>, local: Edges<W>,
) {
    let [x, y] = absolute;
    let [local_x, local_y] = local;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert([x, y] =~= absolute);
        assert([local_x, local_y] =~= local);
    }
    host.write_output(id, Xy::new(x, y), Xy::new(local_x, local_y));
}

/// Convert NaNs after geometric computation and before either output sink.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures stable_rectangle::<F>(edges, out), out == stable_rectangle_value::<F>(edges),
    no_unwind
))]
pub(crate) fn stable_edges<F: FrameFloat>(edges: Edges<f32>) -> Edges<f32> {
    let [[left, right], [top, bottom]] = edges;
    let out = [
        [stable_edge::<F>(left), stable_edge::<F>(right)],
        [stable_edge::<F>(top), stable_edge::<F>(bottom)],
    ];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(edges@[0]@[0] == left && edges@[0]@[1] == right);
        assert(edges@[1]@[0] == top && edges@[1]@[1] == bottom);
        assert(out =~= stable_rectangle_value::<F>(edges));
    }
    out
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures F::word(out) == crate::input_words::layout_word(F::word(value)), out == stable_value::<F>(value),
    no_unwind
))]
fn stable_edge<F: FrameFloat>(value: f32) -> f32 {
    F::from_word(crate::input_words::stable_word(F::bits(value)))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(size =>
    requires live(tree, id),
    ensures size@[0] == tree.layout_record(id).values@[crate::cycles::kernel::slot_index(
            0, crate::cycles::kernel::Kind::Final) as int],
        size@[1] == tree.layout_record(id).values@[crate::cycles::kernel::slot_index(
            1, crate::cycles::kernel::Kind::Final) as int],
    no_unwind
))]
pub(crate) fn size<T: Records + ?Sized>(tree: &T, id: T::Id) -> [f32; 2] {
    let size = tree.record(id).size();
    [size.x, size.y]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(lines =>
    requires live(tree, id),
    ensures lines@[0] == tree.layout_record(id).values@[crate::cycles::kernel::slot_index(
            0, crate::cycles::kernel::Kind::EvenShare) as int],
        lines@[1] == tree.layout_record(id).values@[crate::cycles::kernel::slot_index(
            1, crate::cycles::kernel::Kind::Flow) as int],
    no_unwind
))]
pub(crate) fn grid_lines<T: Records + ?Sized>(tree: &T, id: T::Id) -> [f32; 2] {
    let lines = tree.record(id).grid_lines();
    [lines.x, lines.y]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(cell =>
    requires live(tree, id),
    ensures T::Float::word(cell@[0]) == tree.layout_record(id).parent_flow@[0],
        T::Float::word(cell@[1]) == tree.layout_record(id).parent_flow@[1],
    no_unwind
))]
pub(crate) fn grid_cell<T: Records + ?Sized>(tree: &T, id: T::Id) -> [f32; 2] {
    let cell = tree.record(id).grid_cell::<T::Float>();
    [cell.x, cell.y]
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn free_style_from(params: LayoutParams) -> FreeStyle {
    FreeStyle {
        pos: [params.position.x, params.position.y],
        anchor: [params.anchor.x, params.anchor.y],
        overflow: [params.window_overflow.x, params.window_overflow.y],
    }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns free_style_from(*params), no_unwind))]
pub(crate) fn free_style(params: &LayoutParams) -> FreeStyle {
    FreeStyle {
        pos: [params.position.x, params.position.y], anchor: [params.anchor.x, params.anchor.y],
        overflow: [params.window_overflow.x, params.window_overflow.y],
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(edge =>
    ensures edge == if horizontal { window.x } else { window.y }, no_unwind
))]
pub(crate) fn window_axis(window: &Xy<f32>, horizontal: bool) -> f32 {
    if horizontal { window.x } else { window.y }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn stack_inputs<F: FrameFloat>(style: StackStyle, params: LayoutParams) -> bool {
    &&& style.disabled == params.disabled && style.free == params.free_placement
    &&& style.pos == [params.position.x, params.position.y] && style.anchor == [params.anchor.x, params.anchor.y]
    &&& style.margin == [[F::margin_value(params.margin.x[0]), F::margin_value(params.margin.x[1])],
        [F::margin_value(params.margin.y[0]), F::margin_value(params.margin.y[1])]]
    &&& style.zero_margins == (params.margin.x[0].is_zero() && params.margin.x[1].is_zero()
        && params.margin.y[0].is_zero() && params.margin.y[1].is_zero())
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(style => ensures stack_inputs::<F>(style, *params), no_unwind))]
pub(crate) fn stack_style<F: FrameFloat>(params: &LayoutParams) -> StackStyle {
    let [left, right] = params.margin.x;
    let [top, bottom] = params.margin.y;
    StackStyle {
        disabled: params.disabled, free: params.free_placement,
        pos: [params.position.x, params.position.y], anchor: [params.anchor.x, params.anchor.y],
        margin: [[F::margin(left), F::margin(right)], [F::margin(top), F::margin(bottom)]],
        zero_margins: zero_margins(params),
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(style =>
    ensures stack_inputs::<F>(style.align, *params), style.span == [params.grid_span.x, params.grid_span.y],
    no_unwind
))]
pub(crate) fn grid_style<F: FrameFloat>(params: &LayoutParams) -> GridStyle {
    GridStyle { align: stack_style::<F>(params), span: [params.grid_span.x, params.grid_span.y] }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(style =>
    ensures style.layout == params.children_layout, style.padding == [params.padding.x, params.padding.y],
        style.flipped == [params.children_origin_flipped.x, params.children_origin_flipped.y],
    no_unwind
))]
pub(crate) fn parent_style(params: &LayoutParams) -> ParentStyle {
    ParentStyle {
        layout: params.children_layout, padding: [params.padding.x, params.padding.y],
        flipped: [params.children_origin_flipped.x, params.children_origin_flipped.y],
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(mark =>
    requires live(tree, id),
    ensures mark == tree.layout_record(id).placement,
    no_unwind
))]
pub(crate) fn read_work<T: Records + ?Sized>(tree: &T, id: T::Id) -> PlacementWork {
    tree.record(id).placement
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(old(tree), id),
    ensures final(tree).order() == old(tree).order(),
        final(tree).layout_record(id) == (crate::node_data::NodeLayoutData {
            placement: PlacementWork::Clean, ..old(tree).layout_record(id)
        }),
        forall|other: T::Id| other != id ==> #[trigger] final(tree).layout_record(other) == old(tree).layout_record(other),
    no_unwind
))]
pub(crate) fn clear_work<T: Records + ?Sized>(tree: &mut T, id: T::Id) {
    tree.edit(id).placement = PlacementWork::Clean;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn scale_word<F: FrameFloat>(scale: Option<f32>) -> Option<u32> {
    match scale { Some(value) => Some(F::word(value)), None => None }
}
}

/// A sequence of scale edits keeps the placement flag set until placement.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(current) == next,
        *final(dirty) == update_scale_dirty(*old(dirty), scale_word::<F>(*old(current)) != scale_word::<F>(next)),
    no_unwind
))]
pub(crate) fn set_scale<F: FrameFloat>(current: &mut Option<f32>, dirty: &mut bool, next: Option<f32>) {
    let changed = match (*current, next) {
        (Some(current), Some(next)) => F::bits(current) != F::bits(next),
        (None, None) => false,
        _ => true,
    };
    *dirty = update_scale_dirty(*dirty, changed);
    *current = next;
}
