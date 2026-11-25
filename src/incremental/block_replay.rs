//! Direct sizing of an acyclic tree of ordinary Block boxes.
#![allow(unexpected_cfgs)]

use crate::declarations::{ChildrenLayout, ContentMeasure, LayoutParams, Size, TextContent, Xy, X, Y};
use crate::node_data::NodeLayoutData;
use crate::node_flags::slot_index;
use crate::prepare_frame::FrameFloat;
#[cfg(verus_keep_ghost)]
use crate::prepare_frame::FrameWords;
use crate::prepare_nodes::Records;
use crate::vec_memory::VecMemory;
#[cfg(not(verus_keep_ghost))]
use crate::margin_storage;
#[cfg(verus_keep_ghost)]
use crate::sizing_pass;
#[cfg(not(verus_keep_ghost))]
use crate::{StructuralChange, flow::{BlockFlow, BlockItem, BlockMargins, BlockScalar as Scalar, edge_adjoins, implicit_edges, item_adjoins},
    solve::{cycle_rules, sizing_finish::{bounded_axis, inner, inside_margins, intrinsic_extent, padding_for, IntrinsicOracle}}};
#[cfg(verus_keep_ghost)]
use crate::{block_flow::kernel::{BlockFlow, BlockItem, BlockMargins, Scalar, edge_adjoins, implicit_edges, item_adjoins}, cycles::kernel as cycle_rules,
    margin_storage::kernel::{self as margin_storage, block_has_children},
    prepare_frame::Order, prepare_nodes::live, dependencies::sizing_finish::{bounded_axis, inner, inside_margins, intrinsic_extent, padding_for, IntrinsicOracle},
    structural::kernel::StructuralChange};
#[cfg(verus_keep_ghost)]
use crate::dependencies::sizing_finish::{bounded_extent, inherent_extent, inner_extent, margin_pair, pad_extent, subtract_margins};
#[cfg(verus_keep_ghost)]
use crate::measurement_contract::Request as MeasureRequest;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use cycle_rules::{Kind, SOLVED};

#[cfg_attr(verus_keep_ghost, verus_verify)]
// Bound both recursive walks independently of the size of the document.
const DEPTH_LIMIT: u8 = 24;

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait Storage: Records + IntrinsicOracle<Self::Id> {
    type Block: Scalar;
    spec fn block_arena(&self) -> Seq<BlockMargins<Self::Block>>;
    spec fn lift(value: f32) -> Self::Block;
    spec fn lower(value: Self::Block) -> f32;
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait Storage: Records + IntrinsicOracle<Self::Id> { type Block: Scalar; }

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: Storage {
    type BlockMemory: VecMemory;

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == Self::lift(value), no_unwind))]
    fn scalar(value: f32) -> Self::Block;

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == Self::lower(value), no_unwind))]
    fn word(value: Self::Block) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(height =>
        requires live(old(self), node),
        ensures inputs_unchanged(old(self), final(self)),
            entire_records_unchanged(old(self), final(self)),
            final(self).block_arena() == old(self).block_arena(),
            height == (old(self).measurement())(node, MeasureRequest::TextHeight { wrap_width: logical_constraint::<Self::Float>(width) }),
        no_unwind
    ))]
    fn text_height(&mut self, node: Self::Id, width: Option<f32>) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node),
        ensures inputs_unchanged(old(self), final(self)), entire_records_unchanged(old(self), final(self)),
            final(self).block_arena() == old(self).block_arena(),
        no_unwind
    ))]
    fn warn_height(&mut self, node: Self::Id);

    #[cfg_attr(verus_keep_ghost, verus_spec(arena =>
        ensures inputs_unchanged(old(self), final(self)), entire_records_unchanged(old(self), final(self)),
            arena@ == old(self).block_arena(), final(arena)@ == final(self).block_arena(),
            arena.len() < isize::MAX as usize,
        no_unwind
    ))]
    fn block_margins(&mut self) -> &mut Vec<BlockMargins<Self::Block>>;

    #[cfg_attr(verus_keep_ghost, verus_spec(record =>
        requires live(old(self), node),
        ensures inputs_unchanged(old(self), final(self)), final(self).block_arena() == old(self).block_arena(),
            *record == old(self).layout_record(node), *final(record) == final(self).layout_record(node),
            forall |id: Self::Id| id != node ==>
                #[trigger] final(self).layout_record(id) == old(self).layout_record(id),
        no_unwind
    ))]
    fn update_block_record(&mut self, node: Self::Id) -> &mut NodeLayoutData;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum Attempt {
    Unsupported,
    Rejected,
    Measured(u32),
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Width {
    pub(crate) regular: f32,
    pub(crate) resolved: f32,
    pub(crate) available: f32,
    pub(crate) maximum: Option<f32>,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn inputs_unchanged<A: Storage + ?Sized>(before: &A, after: &A) -> bool {
    &&& after.order() == before.order()
    &&& after.measurement() == before.measurement()
    &&& forall |id: A::Id| #[trigger] after.layout_params(id) == before.layout_params(id)
}

pub(crate) open spec fn entire_records_unchanged<A: Storage + ?Sized>(before: &A, after: &A) -> bool {
    forall |id: A::Id| #[trigger] after.layout_record(id) == before.layout_record(id)
}

pub(crate) open spec fn keeps_exterior<A: Storage + ?Sized>(before: &A, after: &A, root: A::Id) -> bool {
    forall |id: A::Id| !before.order().inside(root, id) ==> #[trigger] after.layout_record(id) == before.layout_record(id)
}

pub(crate) open spec fn arena_prefix<B: Scalar>(before: Seq<BlockMargins<B>>, after: Seq<BlockMargins<B>>) -> bool {
    &&& before.len() <= after.len()
    &&& forall |index: int| 0 <= index < before.len() ==> #[trigger] before[index] == after[index]
}

pub(crate) open spec fn basic_item<A: Storage + ?Sized>(tree: &A, node: A::Id) -> bool {
    let params = tree.layout_params(node);
    &&& !params.disabled && !params.free_placement
    &&& params.image.is_none() && params.content_measure is None && params.min_size.y.is_none()
    &&& (params.children_layout is Block) == (tree.layout_record(node).flags.0 & crate::node_flags::NodeFlags::BLOCK_CONTAINER != 0)
}

pub(crate) open spec fn basic_items<A: Storage + ?Sized>(tree: &A) -> (spec_fn(A::Id) -> bool) {
    |node: A::Id| basic_item(tree, node)
}

pub(crate) open spec fn flags_unchanged<A: Storage + ?Sized>(before: &A, after: &A) -> bool {
    forall |id: A::Id| #[trigger] after.layout_record(id).flags == before.layout_record(id).flags
}

proof fn same_admission<A: Storage + ?Sized>(before: &A, after: &A)
    requires inputs_unchanged(before, after), flags_unchanged(before, after),
    ensures basic_items(before) == basic_items(after),
{
    assert(basic_items(before) =~= basic_items(after));
}

pub(crate) open spec fn published_item<A: Storage + ?Sized>(tree: &A, node: A::Id) -> BlockItem<A::Block> {
    crate::dependencies::sizing_finish::block::item_words::<A::Float, A::Block>(tree.layout_params(node),
        tree.layout_record(node), tree.block_arena(), |value: f32| A::lift(value))
}

pub(crate) open spec fn valid_packed_index<A: Storage + ?Sized>(tree: &A, node: A::Id) -> bool {
    match crate::dependencies::sizing_finish::block::saved_margin_index::<A::Float>(tree.layout_record(node)) {
        Some(index) => index < tree.block_arena().len(),
        None => true,
    }
}

pub(crate) open spec fn keeps_published_exterior<A: Storage + ?Sized>(before: &A, after: &A, cut: A::Id) -> bool {
    forall |id: A::Id| !before.order().inside(cut, id) && valid_packed_index(before, id) ==>
        (#[trigger] published_item(after, id)) == published_item(before, id) && valid_packed_index(after, id)
}

proof fn stable_item<A: Storage + ?Sized>(before: &A, after: &A, node: A::Id)
    requires inputs_unchanged(before, after), before.layout_record(node) == after.layout_record(node),
        arena_prefix(before.block_arena(), after.block_arena()), valid_packed_index(before, node),
    ensures published_item(after, node) == published_item(before, node), valid_packed_index(after, node),
{
    let index = crate::dependencies::sizing_finish::block::saved_margin_index::<A::Float>(before.layout_record(node));
    if let Some(i) = index { assert(before.block_arena()[i as int] == after.block_arena()[i as int]); }
}

proof fn exterior_items<A: Storage + ?Sized>(before: &A, after: &A, cut: A::Id)
    requires inputs_unchanged(before, after), keeps_exterior(before, after, cut),
        arena_prefix(before.block_arena(), after.block_arena()),
    ensures keeps_published_exterior(before, after, cut),
{
    assert forall |id: A::Id| !before.order().inside(cut, id) && valid_packed_index(before, id) implies
        (#[trigger] published_item(after, id)) == published_item(before, id) && valid_packed_index(after, id) by {
        stable_item(before, after, id);
    }
}

pub(crate) open spec fn ready_flow_items<A: Storage + ?Sized>(tree: &A, node: A::Id,
    rows: Seq<(A::Id, BlockItem<A::Block>)>, next: Option<A::Id>,
) -> bool {
    &&& follows(tree.order(), node, rows, next)
    &&& forall |i: int| 0 <= i < rows.len() ==> {
        let row = #[trigger] rows[i];
        &&& tree.order().child(node, row.0)
        &&& basic_item(tree, row.0) && valid_packed_index(tree, row.0) && published_item(tree, row.0) == row.1
        &&& next.is_some() ==> (tree.order().interval)(row.0).1 <= (tree.order().interval)(next.unwrap()).0
    }
}

/// The stored Flow word is the ordered reduction of the physical child
/// records. Each margin index still refers to its original append.
pub(crate) open spec fn measured_flow<A: Storage + ?Sized>(tree: &A, node: A::Id, root: bool,
    rows: Seq<(A::Id, BlockItem<A::Block>)>,
) -> bool {
    let p = tree.layout_params(node);
    let top = edge_adjoins(!root, A::Float::word(p.padding.y[0]) & 0x7fff_ffffu32 == 0);
    let bottom = edge_adjoins(!root, A::Float::word(p.padding.y[1]) & 0x7fff_ffffu32 == 0)
        && (p.size.y is Auto || p.size.y is FitContent);
    &&& ready_flow_items(tree, node, rows, None)
    &&& tree.layout_record(node).values@[cycle_rules::slot_index(1, Kind::Flow) as int]
        == A::lower(crate::block_flow::finish(crate::block_flow::replay(flow_items(rows), top, bottom)).0)
}

pub(crate) open spec fn logical_constraint<F: FrameFloat>(width: Option<f32>) -> Option<u32> {
    match width { Some(width) => Some(F::word(width)), None => None }
}

pub(crate) open spec fn saved_regular_y<F: FrameFloat>(record: NodeLayoutData, text: TextContent, new_width: f32) -> Option<f32> {
    let opposite = cycle_rules::slot_index(0, Kind::Final) as int;
    let index = cycle_rules::slot_index(1, Kind::Regular) as int;
    if record.structural_change is Clean && cycle_rules::read_state(record.flags.0, index as u32) == SOLVED
        && (!(text is Wrapping) || F::word(record.values@[opposite]) == F::word(new_width))
    {
        Some(record.values@[index])
    } else { None }
}

pub(crate) open spec fn ordinary_intrinsic_y<F: FrameFloat, I>(
    calls: spec_fn(I, MeasureRequest) -> f32, node: I, text: TextContent, width: f32, padding: f32,
) -> f32 {
    let own = match text {
        TextContent::None => 0.0f32,
        TextContent::Fixed => calls(node, MeasureRequest::TextHeight { wrap_width: None }),
        TextContent::Wrapping => calls(node, MeasureRequest::TextHeight { wrap_width: Some(F::word(width)) }),
    };
    inherent_extent::<F>(0.0, own, 0.0, padding)
}

/// Canonical X declarations, cap, padding floor, and child content extent
/// when preflight admits either a document root or an in-flow Block item.
pub(crate) open spec fn ordinary_block_width<F: FrameFloat>(params: LayoutParams, parent: f32, root: bool) -> Width {
    let regular = match params.size.x {
        Size::Pixels(pixels) => pixels,
        _ if root => parent,
        _ => subtract_margins::<F>(parent, margin_pair::<F>(params, X)),
    };
    let maximum = match params.max_size.x { Some(Size::Pixels(pixels)) => Some(pixels), _ => None };
    let padding = pad_extent::<F>(params, X);
    let resolved = bounded_extent::<F>(regular, None, maximum, if root { None } else { Some(padding) });
    Width { regular, resolved, available: inner_extent::<F>(resolved, padding), maximum }
}

pub(crate) open spec fn supported_declarations(p: LayoutParams, root: bool) -> bool {
    &&& p.size.x is Pixels || p.size.x is Fill || !root && p.size.x is Auto
    &&& p.size.y is Pixels || p.size.y is FitContent || p.size.y is Auto || root && p.size.y is Fill
    &&& p.min_size.x.is_none() && p.min_size.y.is_none() && p.max_size.y.is_none()
    &&& match p.max_size.x { Some(size) => size is Pixels, None => true }
}

/// Compare the two source producer equations using the actual parent Final
/// and padding, or the incoming viewport when this is the document root.
pub(crate) proof fn direct_x_matches_ordinary<A: crate::dependencies::sizing_finish::FinishModel + ?Sized>(
    reference: &A, node: A::Id, parent: f32, root: bool,
)
    requires
        supported_declarations(reference.finish_layout(node), root),
        reference.finish_flags(node).is_block_item() == !root,
        !reference.finish_layout(node).free_placement,
        (reference.topology().stack_parent)(crate::dependencies::sizing_requests::target(node, false, Kind::Regular)).is_none(),
        if root {
            (reference.topology().parent)(node).is_none()
                && parent == crate::dependencies::sizing_finish::viewport_extent(reference, X)
        } else {
            crate::dependencies::sizing_finish::block_parent_extent(reference,
                crate::dependencies::sizing_requests::target(node, false, Kind::Regular)) == Some(parent)
        },
    ensures ({
        let direct = ordinary_block_width::<A::Float>(reference.finish_layout(node), parent, root);
        &&& crate::dependencies::sizing_finish::declared_scalar(reference,
            crate::dependencies::sizing_requests::target(node, false, Kind::Regular)) == Some(direct.regular)
        &&& direct.maximum == crate::dependencies::sizing_finish::declared_scalar(reference,
            crate::dependencies::sizing_requests::target(node, false, Kind::Max))
        &&& direct.resolved == bounded_extent::<A::Float>(direct.regular, None, direct.maximum,
            if root { None } else { Some(pad_extent::<A::Float>(reference.finish_layout(node), X)) })
    }),
{
    let params = reference.finish_layout(node);
    let auto_parent = reference.finish_flags(node).0 & crate::node_flags::NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0;
    if root && auto_parent {
        // No admitted parentless width or bound depends on this stale flag.
        accepted_sizes_are_canonical(params, root, false);
    } else {
        accepted_sizes_are_canonical(params, root, auto_parent);
    }
}

/// A freshly measured direct leaf issues the ordinary Y intrinsic request
/// when its packed X Final word supplies the same inner constraint.
pub(crate) proof fn direct_y_measures_ordinary_leaf<A>(reference: &A, node: A::Id, inner_width: f32)
    where A: crate::dependencies::sizing_finish::FinishModel + IntrinsicOracle<A::Id> + ?Sized,
    requires supported_declarations(reference.finish_layout(node), false),
        reference.finish_layout(node).image.is_none(), reference.finish_layout(node).content_measure is None,
        inner_width == crate::dependencies::sizing_finish::opposite_content(reference,
            crate::dependencies::sizing_requests::target(node, true, Kind::Regular)),
    ensures ({
        let slot = crate::dependencies::sizing_requests::target(node, true, Kind::Regular);
        let params = reference.finish_layout(node);
        let pad = pad_extent::<A::Float>(params, Y);
        ordinary_intrinsic_y::<A::Float, A::Id>(reference.measurement(), node, params.text, inner_width, pad)
            == inherent_extent::<A::Float>(0.0, crate::dependencies::sizing_finish::own_extent(reference, slot), 0.0, pad)
    }),
{
}

/// The direct Block fold starts with the ordinary collapse flags under the
/// shape checks used by the direct preflight.
pub(crate) proof fn direct_edges_match_ordinary<F: FrameFloat>(params: LayoutParams, flags: crate::node_flags::NodeFlags, root: bool)
    requires supported_declarations(params, root), flags.is_block_item() == !root,
        params.text is None, params.image.is_none(), params.content_measure is None,
        root ==> flags.0 & crate::node_flags::NodeFlags::BLOCK_PARENT_AUTO_HEIGHT == 0,
    ensures crate::dependencies::sizing_finish::block::edge_words::<F>(params, flags) == (
        edge_adjoins(!root, F::word(params.padding.y[0]) & 0x7fff_ffffu32 == 0),
        edge_adjoins(!root, F::word(params.padding.y[1]) & 0x7fff_ffffu32 == 0)
            && (params.size.y is Auto || params.size.y is FitContent),
    ),
{
    accepted_sizes_are_canonical(params, root, flags.0 & crate::node_flags::NodeFlags::BLOCK_PARENT_AUTO_HEIGHT != 0);
}

/// The permitted raw declarations resolve to the same effective declarations
/// used by the ordinary request dispatcher. In particular an Auto width is a
/// parent read only inside Block, and no admitted child reads the parent's Y.
pub(crate) proof fn accepted_sizes_are_canonical(p: LayoutParams, root: bool, auto_parent: bool)
    requires supported_declarations(p, root), root ==> !auto_parent,
    ensures
        crate::dependencies::sizing_requests::resolved_size(p, false, Kind::Regular, !root, auto_parent)
            == Some(if p.size.x is Auto { Size::Fill } else { p.size.x }),
        crate::dependencies::sizing_requests::resolved_size(p, true, Kind::Regular, !root, auto_parent)
            == Some(if p.size.y is Auto { Size::FitContent } else { p.size.y }),
        crate::dependencies::sizing_requests::resolved_size(p, false, Kind::Min, !root, auto_parent).is_none(),
        crate::dependencies::sizing_requests::resolved_size(p, false, Kind::Max, !root, auto_parent) == p.max_size.x,
        crate::dependencies::sizing_requests::resolved_size(p, true, Kind::Min, !root, auto_parent).is_none(),
        crate::dependencies::sizing_requests::resolved_size(p, true, Kind::Max, !root, auto_parent).is_none(),
{
}

/// Every child reached during preflight is an ordinary Block item and has
/// budget for both physical walks.
spec fn fits_budget<I>(order: Order<I>, allowed: spec_fn(I) -> bool, node: I, depth: nat) -> bool
    decreases depth, 0nat, 0int,
{
    depth > 0 && allowed(node) && suffix_fits(order, allowed, node, (order.first)(node), (depth - 1) as nat)
}

spec fn suffix_fits<I>(order: Order<I>, allowed: spec_fn(I) -> bool, parent: I, next: Option<I>, depth: nat) -> bool
    decreases depth, 1nat, sizing_pass::remaining(order, parent, next),
{
    match next {
        None => true,
        Some(child) if order.ordered() && order.child(parent, child) => {
            let later = (order.sibling)(child);
            fits_budget(order, allowed, child, depth)
                && suffix_fits(order, allowed, parent, later, depth)
        },
        Some(_) => false,
    }
}

pub(crate) open spec fn packed_margin<F: FrameFloat, B: Scalar>(record: NodeLayoutData, arena: Seq<BlockMargins<B>>)
    -> Option<BlockMargins<B>>
{
    let word = F::word(record.values@[cycle_rules::slot_index(0, Kind::EvenShare) as int]);
    match margin_storage::margin_index(word, record.n_placed_children) {
        Some(index) if index < arena.len() => Some(arena[index as int]),
        _ => None,
    }
}

spec fn block_words(previous: Seq<f32>, width: &Width, regular: f32, resolved: f32,
    is_block: bool, height: f32, margin_word: f32) -> Seq<f32>
{
    let words = previous
        .update(cycle_rules::slot_index(0, Kind::Regular) as int, width.regular)
        .update(cycle_rules::slot_index(0, Kind::Final) as int, width.resolved);
    let words = match width.maximum {
        Some(maximum) => words.update(cycle_rules::slot_index(0, Kind::Max) as int, maximum),
        None => words,
    };
    let words = words.update(cycle_rules::slot_index(1, Kind::Regular) as int, regular)
        .update(cycle_rules::slot_index(1, Kind::Final) as int, resolved);
    if is_block {
        words.update(cycle_rules::slot_index(1, Kind::Flow) as int, height)
            .update(cycle_rules::slot_index(0, Kind::EvenShare) as int, margin_word)
    } else {
        words
    }
}

pub(crate) open spec fn flow_items<I, F: Copy>(rows: Seq<(I, BlockItem<F>)>) -> Seq<BlockItem<F>> {
    Seq::new(rows.len(), |i: int| rows[i].1)
}

/// Rows already folded, followed by exactly the next link in that same list.
pub(crate) open spec fn follows<I, F: Copy>(order: Order<I>, parent: I, rows: Seq<(I, BlockItem<F>)>, next: Option<I>) -> bool {
    if rows.len() == 0 {
        next == (order.first)(parent)
    } else {
        &&& (order.first)(parent) == Some(rows[0].0)
        &&& (order.sibling)(rows.last().0) == next
        &&& forall |i: int| 0 < i < rows.len()
            ==> (order.sibling)(rows[i - 1].0) == Some((#[trigger] rows[i]).0)
    }
}

fn empty_flow<I, F: Copy>() -> (rows: Ghost<Seq<(I, BlockItem<F>)>>)
    ensures rows@ == Seq::<(I, BlockItem<F>)>::empty(),
    no_unwind
{
    Ghost(Seq::<(I, BlockItem<F>)>::empty())
}

fn next_flow<I: Copy, F: Copy>(rows: Ghost<Seq<(I, BlockItem<F>)>>, id: I, item: &BlockItem<F>)
    -> (out: Ghost<Seq<(I, BlockItem<F>)>>)
    ensures out@ == rows@.push((id, *item)),
    no_unwind
{
    Ghost(rows@.push((id, *item)))
}

proof fn append_flow<I, F: Scalar>(order: Order<I>, parent: I, rows: Seq<(I, BlockItem<F>)>,
    id: I, item: BlockItem<F>, top: bool, bottom: bool,
)
    requires follows(order, parent, rows, Some(id)),
    ensures
        follows(order, parent, rows.push((id, item)), (order.sibling)(id)),
        crate::block_flow::replay(flow_items(rows.push((id, item))), top, bottom)
            == crate::block_flow::push(crate::block_flow::replay(flow_items(rows), top, bottom), item).0,
{
    let appended = rows.push((id, item));
    assert(appended.last() == (id, item));
    assert forall |i: int| 0 < i < appended.len() implies
        (order.sibling)(appended[i - 1].0) == Some((#[trigger] appended[i]).0) by {
        if i == rows.len() {
            assert(rows[i - 1] == rows.last());
        } else {
            assert(rows[i] == appended[i]);
        }
    }
    let inputs = flow_items(appended);
    assert(inputs.drop_last() =~= flow_items(rows));
    assert(inputs.last() == item);
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(accepted =>
    ensures accepted == supported_declarations(*p, root),
    no_unwind
))]
pub(crate) fn accepts_declarations(p: &LayoutParams, root: bool) -> bool {
    let inline = matches!(p.size.x, Size::Pixels(_) | Size::Fill) || !root && matches!(p.size.x, Size::Auto);
    let block = matches!(p.size.y, Size::Pixels(_) | Size::Auto | Size::FitContent) || root && matches!(p.size.y, Size::Fill);
    inline && block && p.min_size.x.is_none() && p.min_size.y.is_none() && p.max_size.y.is_none()
        && matches!(p.max_size.x, None | Some(Size::Pixels(_)))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(width => ensures width == ordinary_block_width::<F>(*p, parent, root), no_unwind))]
pub(crate) fn width<F: FrameFloat>(p: &LayoutParams, parent: f32, root: bool) -> Width {
    let [before, after] = p.margin.x;
    let regular = match p.size.x {
        Size::Pixels(pixels) => pixels,
        _ if root => parent,
        _ => inside_margins::<F>(parent, [F::margin(before), F::margin(after)]),
    };
    let maximum = match p.max_size.x { Some(Size::Pixels(pixels)) => Some(pixels), _ => None };
    let pad = padding_for::<F>(p, X);
    let resolved = bounded_axis::<F>(regular, None, maximum, if root { None } else { Some(pad) });
    Width { regular, resolved, available: inner::<F>(resolved, pad), maximum }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(supported =>
    requires live(tree, node), tree.order().ordered(),
    ensures supported ==> fits_budget(tree.order(), basic_items(tree), node, depth as nat),
    decreases depth,
    no_unwind
))]
fn supports<A: Access + ?Sized>(tree: &A, node: A::Id, parent: f32, root: bool, depth: u8) -> bool {
    if depth == 0 { return false; }
    let p = tree.params(node);
    let data = tree.record(node);
    if p.disabled || p.free_placement || p.image.is_some() || !matches!(p.content_measure, ContentMeasure::None)
        || !accepts_declarations(p, root)
        || !A::Float::finite(padding_for::<A::Float>(p, Y)) || data.flags.has_cycle()
        || data.flags.check_state(X, Kind::Final) != SOLVED || data.flags.check_state(Y, Kind::Final) != SOLVED
    {
        return false;
    }
    if let Size::Pixels(pixels) = p.size.y {
        if !A::Float::finite(pixels) { return false; }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        accepted_sizes_are_canonical(*p, root, false);
        if !root { accepted_sizes_are_canonical(*p, false, true); }
    }
    let first = tree.first(node);
    let has_children = first.is_some();
    if data.flags.is_block_item() == root
        || data.flags.is_block_container() != matches!(p.children_layout, ChildrenLayout::Block)
        || data.has_in_flow_children() != has_children
    {
        return false;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(basic_item(tree, node)); }
    let width = width::<A::Float>(p, parent, root);
    if !A::Float::finite(width.resolved) || !A::Float::finite(width.available) { return false; }
    match p.children_layout {
        ChildrenLayout::Block => {
            if !matches!(p.text, TextContent::None) { return false; }
            let mut next = first;
            #[cfg(verus_keep_ghost)]
            proof! { tree.order().node_facts(node); }
            #[cfg_attr(verus_keep_ghost, verus_spec(
                invariant live(tree, node), tree.order().ordered(), depth > 0, basic_item(tree, node),
                    next.is_some() ==> tree.order().child(node, next.unwrap()),
                    fits_budget(tree.order(), basic_items(tree), node, depth as nat)
                        == suffix_fits(tree.order(), basic_items(tree), node, next, (depth - 1) as nat),
                decreases sizing_pass::remaining(tree.order(), node, next),
            ))]
            loop {
                let Some(child) = next else {
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        assert(suffix_fits(tree.order(), basic_items(tree), node, None, (depth - 1) as nat));
                        assert(fits_budget(tree.order(), basic_items(tree), node, depth as nat));
                    }
                    return true;
                };
                #[cfg(verus_keep_ghost)]
                proof! { tree.order().node_facts(child); }
                if !supports(tree, child, width.available, false, depth - 1) { return false; }
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(fits_budget(tree.order(), basic_items(tree), child, (depth - 1) as nat));
                    assert(next == Some(child));
                    assert(suffix_fits(tree.order(), basic_items(tree), node, next, (depth - 1) as nat)
                        == suffix_fits(tree.order(), basic_items(tree), node, (tree.order().sibling)(child), (depth - 1) as nat));
                }
                next = tree.sibling(child);
            }
        }
        ChildrenLayout::Free => {
            #[cfg(verus_keep_ghost)]
            proof! {
                if !has_children {
                    assert((tree.order().first)(node).is_none());
                    assert(suffix_fits(tree.order(), basic_items(tree), node, None, (depth - 1) as nat));
                    assert(fits_budget(tree.order(), basic_items(tree), node, depth as nat));
                }
            }
            !root && !has_children
        },
        _ => false,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
fn implicit<A: Access + ?Sized>(margin: &BlockMargins<A::Block>, empty: bool) -> bool {
    implicit_edges([
        A::Float::is_zero(A::word(margin.before.positive)), A::Float::is_zero(A::word(margin.before.negative)),
        A::Float::is_zero(A::word(margin.after.positive)), A::Float::is_zero(A::word(margin.after.negative)),
    ], margin.all_through, empty)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(data).values@[cycle_rules::slot_index(1, Kind::Final) as int] == resolved,
        is_block ==> final(data).values@[cycle_rules::slot_index(1, Kind::Flow) as int] == height,
        final(data).values@ == block_words(old(data).values@, width, regular, resolved, is_block, height,
            final(data).values@[cycle_rules::slot_index(0, Kind::EvenShare) as int]),
        *final(data) == (NodeLayoutData {
            values: final(data).values, n_placed_children: final(data).n_placed_children,
            structural_change: StructuralChange::Clean, ..*old(data)
        }),
        !is_block ==> final(data).n_placed_children == old(data).n_placed_children,
        is_block ==> margin_storage::margin_index(
            F::word(final(data).values@[cycle_rules::slot_index(0, Kind::EvenShare) as int]), final(data).n_placed_children)
            == match margin { Some(i) if i < isize::MAX as usize => Some(i), _ => None },
        block_has_children(final(data).n_placed_children) == block_has_children(old(data).n_placed_children),
    no_unwind
))]
fn publish<F: FrameFloat>(data: &mut NodeLayoutData, width: &Width, regular: f32, resolved: f32,
    is_block: bool, height: f32, margin: Option<usize>,
) {
    // The dependency graph stays fixed, so publication preserves phased
    // flags and ranks along with topology and placement state.
    data.values[slot_index(X, Kind::Regular)] = width.regular;
    data.values[slot_index(X, Kind::Final)] = width.resolved;
    if let Some(maximum) = width.maximum { data.values[slot_index(X, Kind::Max)] = maximum; }
    data.values[slot_index(Y, Kind::Regular)] = regular;
    data.values[slot_index(Y, Kind::Final)] = resolved;
    if is_block {
        data.values[slot_index(Y, Kind::Flow)] = height;
        data.set_block_margin_index::<F>(margin);
    }
    data.structural_change = StructuralChange::Clean;
}

/// Store the logical margin summary through the same packed index read by
/// ordinary Block layout. Other records keep their words and indices.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(saved =>
    requires live(old(tree), node), nested.is_some() ==> is_block,
    ensures inputs_unchanged(old(tree), final(tree)), flags_unchanged(old(tree), final(tree)),
        final(tree).layout_record(node).values@[cycle_rules::slot_index(1, Kind::Final) as int] == resolved,
        final(tree).layout_record(node).flags == old(tree).layout_record(node).flags,
        is_block == (old(tree).layout_record(node).flags.0 & crate::node_flags::NodeFlags::BLOCK_CONTAINER != 0)
            ==> crate::dependencies::sizing_finish::block::child_word_has_flow(final(tree).layout_record(node))
                == crate::dependencies::sizing_finish::block::child_word_has_flow(old(tree).layout_record(node)),
        !is_block ==> saved.is_none(),
        is_block || old(tree).layout_record(node).flags.0 & crate::node_flags::NodeFlags::BLOCK_CONTAINER == 0
            ==> valid_packed_index(final(tree), node),
        is_block ==> final(tree).layout_record(node).values@[cycle_rules::slot_index(1, Kind::Flow) as int] == height,
        final(tree).block_arena() == if let Some(value) = saved { old(tree).block_arena().push(value) }
            else { old(tree).block_arena() },
        is_block ==> packed_margin::<A::Float, A::Block>(final(tree).layout_record(node), final(tree).block_arena()) == saved,
        (final(tree).layout_record(node)).values@ == block_words(old(tree).layout_record(node).values@,
            width, regular, resolved, is_block, height,
            (final(tree).layout_record(node)).values@[cycle_rules::slot_index(0, Kind::EvenShare) as int]),
        forall |id: A::Id| id != node ==>
            #[trigger] final(tree).layout_record(id) == old(tree).layout_record(id),
        forall |id: A::Id| id != node && valid_packed_index(old(tree), id) ==>
            (#[trigger] published_item(final(tree), id)) == published_item(old(tree), id) && valid_packed_index(final(tree), id),
    no_unwind
))]
fn publish_box<A: Access + ?Sized>(
    tree: &mut A, node: A::Id, width: &Width, regular: f32, resolved: f32, is_block: bool,
    height: f32, nested: Option<BlockMargins<A::Block>>, root: bool, children_empty: bool,
) -> Option<BlockMargins<A::Block>> {
    let saved = match nested {
        Some(margin) if !root && !implicit::<A>(&margin, children_empty) => {
            let index = margin_storage::append_margin::<_, A::BlockMemory>(tree.block_margins(), margin);
            Some((margin, index))
        }
        _ => None,
    };
    let index = match &saved { Some((_, index)) => Some(*index), None => None };
    publish::<A::Float>(tree.update_block_record(node), width, regular, resolved, is_block, height, index);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(arena_prefix(old(tree).block_arena(), tree.block_arena()));
        assert forall |id: A::Id| id != node && valid_packed_index(old(tree), id) implies
            (#[trigger] published_item(tree, id)) == published_item(old(tree), id) && valid_packed_index(tree, id) by {
            stable_item(old(tree), tree, id);
        }
    }
    match saved { Some((margin, _)) => Some(margin), None => None }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(height =>
    requires live(old(tree), node),
    ensures inputs_unchanged(old(tree), final(tree)), entire_records_unchanged(old(tree), final(tree)),
        final(tree).block_arena() == old(tree).block_arena(),
        height == match saved_regular_y::<A::Float>(old(tree).layout_record(node), text, width.resolved) {
            Some(saved) => saved,
            None => ordinary_intrinsic_y::<A::Float, A::Id>(old(tree).measurement(), node, text, width.available, padding),
        },
    no_unwind
))]
fn leaf_height<A: Access + ?Sized>(tree: &mut A, node: A::Id, text: TextContent, width: &Width, padding: f32) -> f32 {
    let old = tree.record(node);
    let old_width = cycle_rules::read_slot(&old.values, X.index(), Kind::Final);
    let cached = matches!(old.structural_change, StructuralChange::Clean)
        && old.flags.check_state(Y, Kind::Regular) == SOLVED
        && (!matches!(text, TextContent::Wrapping) || A::Float::bits(old_width) == A::Float::bits(width.resolved));
    if cached {
        cycle_rules::read_slot(&old.values, Y.index(), Kind::Regular)
    } else {
        let own = match text {
            TextContent::None => 0.0,
            TextContent::Wrapping => tree.text_height(node, Some(width.available)),
            TextContent::Fixed => tree.text_height(node, None),
        };
        intrinsic_extent::<A::Float>(0.0, own, 0.0, padding)
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), node), old(tree).order().ordered(), fits_budget(old(tree).order(), basic_items(old(tree)), node, depth as nat),
    ensures inputs_unchanged(old(tree), final(tree)), keeps_exterior(old(tree), final(tree), node),
        flags_unchanged(old(tree), final(tree)),
        arena_prefix(old(tree).block_arena(), final(tree).block_arena()),
        final(tree).layout_record(node).flags == old(tree).layout_record(node).flags,
        result.is_some(), *final(computed) >= old(computed).saturating_add(4),
        result.unwrap() == published_item(final(tree), node), valid_packed_index(final(tree), node),
        keeps_published_exterior(old(tree), final(tree), node),
        old(tree).layout_params(node).children_layout is Block ==>
            exists |rows: Seq<(A::Id, BlockItem<A::Block>)>| #[trigger] measured_flow(final(tree), node, viewport_height.is_some(), rows),
    decreases depth,
    no_unwind
))]
fn measure<A: Access + ?Sized>(
    tree: &mut A, node: A::Id, parent_width: f32, viewport_height: Option<f32>, depth: u8, computed: &mut u32,
) -> Option<BlockItem<A::Block>> {
    if depth == 0 { return None; }
    let root = viewport_height.is_some();
    let p = tree.params(node);
    let width = width::<A::Float>(p, parent_width, root);
    let is_block = matches!(p.children_layout, ChildrenLayout::Block);
    let text = p.text;
    let y_size = p.size.y;
    let [before_pad, after_pad] = p.padding.y;
    let pad = padding_for::<A::Float>(p, Y);
    let [before, after] = p.margin.y;
    let fit = matches!(y_size, Size::Auto | Size::FitContent);
    let children_empty = !tree.record(node).has_in_flow_children();
    #[cfg(verus_keep_ghost)]
    let mut rows = empty_flow::<A::Id, A::Block>();
    let (height, nested) = if is_block {
        let top = edge_adjoins(!root, A::Float::is_zero(before_pad));
        let bottom = edge_adjoins(!root, A::Float::is_zero(after_pad)) && fit;
        let mut flow = BlockFlow::from_edges(top, bottom);
        let mut next = tree.first(node);
        #[cfg(verus_keep_ghost)]
        proof! { tree.order().node_facts(node); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant inputs_unchanged(old(tree), tree), keeps_exterior(old(tree), tree, node),
                flags_unchanged(old(tree), tree), basic_items(tree) == basic_items(old(tree)),
                arena_prefix(old(tree).block_arena(), tree.block_arena()),
                tree.layout_record(node) == old(tree).layout_record(node),
                live(tree, node), tree.order().ordered(), depth > 0,
                next.is_some() ==> tree.order().child(node, next.unwrap()),
                ready_flow_items(tree, node, rows@, next),
                suffix_fits(tree.order(), basic_items(tree), node, next, (depth - 1) as nat),
                flow == crate::block_flow::replay(flow_items(rows@), top, bottom),
                *computed >= *old(computed),
            decreases sizing_pass::remaining(tree.order(), node, next),
        ))]
        while next.is_some() {
            let Some(child) = next else { return None; };
            #[cfg(verus_keep_ghost)]
            proof! {
                tree.order().node_facts(child);
                assert(fits_budget(tree.order(), basic_items(tree), child, (depth - 1) as nat));
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall |i: int| 0 <= i < rows@.len() implies !tree.order().inside(child, (#[trigger] rows@[i]).0) by {
                    let earlier = rows@[i].0;
                    assert((tree.order().interval)(earlier).1 <= (tree.order().interval)(child).0);
                }
            }
            next = tree.sibling(child);
            let item = measure(tree, child, width.available, None, depth - 1, computed)?;
            #[cfg(verus_keep_ghost)]
            {
                proof! {
                    same_admission(old(tree), tree);
                    append_flow(tree.order(), node, rows@, child, item, top, bottom);
                    let joined = rows@.push((child, item));
                    assert forall |i: int| 0 <= i < joined.len() implies {
                        let row = #[trigger] joined[i];
                        &&& tree.order().child(node, row.0)
                        &&& basic_item(tree, row.0) && valid_packed_index(tree, row.0) && published_item(tree, row.0) == row.1
                        &&& next.is_some() ==> (tree.order().interval)(row.0).1 <= (tree.order().interval)(next.unwrap()).0
                    } by {
                        if i < rows@.len() {
                            assert(joined[i] == rows@[i]);
                            assert(!tree.order().inside(child, joined[i].0));
                        } else { assert(joined[i] == (child, item)); }
                    }
                }
                rows = next_flow(rows, child, &item);
            }
            flow.push(item);
        }
        let (height, margins) = flow.finish();
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(follows(tree.order(), node, rows@, None));
            assert((height, margins)
                == crate::block_flow::finish(crate::block_flow::replay(flow_items(rows@), top, bottom)));
        }
        (A::word(height), Some(margins))
    } else {
        (0.0, None)
    };
    let regular = match y_size {
        Size::Pixels(y) => y,
        Size::Fill => viewport_height.unwrap_or(0.0),
        _ if is_block => intrinsic_extent::<A::Float>(height, 0.0, 0.0, pad),
        _ => leaf_height(tree, node, text, &width, pad),
    };
    let resolved = bounded_axis::<A::Float>(regular, None, None, if root { None } else { Some(pad) });
    if !A::Float::finite(resolved) { tree.warn_height(node); }
    let nested = publish_box(tree, node, &width, regular, resolved, is_block, height, nested, root, children_empty);
    #[cfg(verus_keep_ghost)]
    proof! {
        exterior_items(old(tree), tree, node);
        if is_block {
            assert forall |i: int| 0 <= i < rows@.len() implies {
                let row = #[trigger] rows@[i];
                &&& tree.order().child(node, row.0)
                &&& basic_item(tree, row.0) && valid_packed_index(tree, row.0) && published_item(tree, row.0) == row.1
            } by {
                let child = rows@[i].0;
                assert((tree.order().interval)(node).0 < (tree.order().interval)(child).0);
                assert(child != node);
            }
            assert(ready_flow_items(tree, node, rows@, None));
            assert(measured_flow(tree, node, root, rows@));
        }
    }
    *computed = computed.saturating_add(if width.maximum.is_some() { 5 } else { 4 });
    if is_block { *computed = computed.saturating_add(1); }
    let adjoining = item_adjoins(A::Float::is_zero(resolved),
        [A::Float::is_zero(before_pad), A::Float::is_zero(after_pad)], matches!(text, TextContent::None), true);
    let item = BlockItem::from_edges(A::scalar(A::Float::margin(before)), A::scalar(A::Float::margin(after)),
        A::scalar(resolved), adjoining, children_empty, nested);
    #[cfg(verus_keep_ghost)]
    proof! {
        {
            assert(basic_item(old(tree), node));
            let record = tree.layout_record(node);
            let layout = tree.layout_params(node);
            let margin = crate::dependencies::sizing_finish::block::saved_margin::<A::Float, A::Block>(record, tree.block_arena());
            assert(margin == nested);
            assert(record.values@[cycle_rules::slot_index(1, Kind::Final) as int] == resolved);
            assert(layout.margin.y == [before, after] && layout.padding.y == [before_pad, after_pad]);
            assert(item == published_item(tree, node));
        }
    }
    Some(item)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), root), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
        !(result is Rejected),
        if let Attempt::Measured(computed) = result {
            &&& computed >= 4
            &&& exists |rows: Seq<(A::Id, BlockItem<A::Block>)>| #[trigger] measured_flow(final(tree), root, true, rows)
        } else { true },
    no_unwind
))]
pub(crate) fn replay<A: Access + ?Sized>(tree: &mut A, root: A::Id, window: Xy<f32>) -> Attempt {
    if !matches!(tree.params(root).children_layout, ChildrenLayout::Block) || !A::Float::finite(window.y)
        || !supports(tree, root, window.x, true, DEPTH_LIMIT)
    {
        return Attempt::Unsupported;
    }
    A::BlockMemory::clear(tree.block_margins());
    #[cfg(verus_keep_ghost)]
    proof! { same_admission(old(tree), tree); }
    let mut computed = 0;
    if measure(tree, root, window.x, Some(window.y), DEPTH_LIMIT, &mut computed).is_none() {
        Attempt::Rejected
    } else {
        Attempt::Measured(computed)
    }
}
