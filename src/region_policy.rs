//! Decisions used when a structural edit reaches an already measured node.
#![allow(unexpected_cfgs)]
use super::structural_changes::StructuralChange;
use crate::declarations::{Axis, ChildrenLayout, LayoutParams, Size, X, Y};
use crate::node_flags::{NodeFlags, slot_index};
use crate::prepare_frame::summarize_child;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel as cycle_rules;
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules;
use cycle_rules::{Kind, SOLVED, UNSOLVED, read_state};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns starts_region(mark), no_unwind))]
pub fn starts_region(mark: StructuralChange) -> bool {
    matches!(mark, StructuralChange::Moved | StructuralChange::Subtree | StructuralChange::DormantGrid)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum AfterChildren { Keep, Refresh, Rebuild }

/// A cycle visited through an earlier root can expose a different provisional
/// value. Nested work therefore forces replay even without a direct signal.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns after_children(changed, saved_cycle, nested), no_unwind))]
pub fn after_children(changed: bool, saved_cycle: bool, nested: bool) -> AfterChildren {
    if saved_cycle && (changed || nested) { AfterChildren::Rebuild }
    else if changed { AfterChildren::Refresh }
    else { AfterChildren::Keep }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns can_refresh(block_item, finals_solved, reads_children), no_unwind))]
pub fn can_refresh(block_item: bool, finals_solved: bool, reads_children: bool) -> bool {
    !block_item && finals_solved && !reads_children
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns stack_reads_child_list(enabled, in_flow, flexible), no_unwind))]
pub fn stack_reads_child_list(enabled: bool, in_flow: bool, flexible: bool) -> bool {
    enabled && in_flow && flexible
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns attached_flow_child(in_flow, flow_parent), no_unwind))]
pub fn attached_flow_child(in_flow: bool, flow_parent: bool) -> bool {
    in_flow && flow_parent
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns affects_parent(cyclic, reads_children, block_item, in_parent_flow), no_unwind))]
pub fn affects_parent(cyclic: bool, reads_children: bool, block_item: bool, in_parent_flow: bool) -> bool {
    cyclic || reads_children || block_item || in_parent_flow
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns clean_branch_root(mark, cyclic), no_unwind))]
pub fn clean_branch_root(mark: StructuralChange, cyclic: bool) -> bool {
    matches!(mark, StructuralChange::Clean) && !cyclic
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const CHILD_FLAGS: u32 = NodeFlags::FLEX_CHILD_X | NodeFlags::FLEX_CHILD_Y
    | NodeFlags::GRID_SPANS | NodeFlags::DESCENDANTS_NEED_SOLVE;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const REFRESH_FLAGS: u32 = CHILD_FLAGS | NodeFlags::FIXED_LEAF;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns intrinsic(size), no_unwind))]
pub(crate) fn intrinsic(size: Option<Size>) -> bool {
    matches!(size, Some(Size::FitContent | Size::Auto))
}

/// For a parent outside block flow the Auto declarations are intrinsic.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns has_intrinsic(params), no_unwind))]
pub(crate) fn has_intrinsic(params: &LayoutParams) -> bool {
    intrinsic(Some(params.size.x)) || intrinsic(params.min_size.x) || intrinsic(params.max_size.x)
        || intrinsic(Some(params.size.y)) || intrinsic(params.min_size.y) || intrinsic(params.max_size.y)
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns flexible(primary, minimum, maximum), no_unwind))]
pub(crate) fn flexible(primary: Size, minimum: Option<Size>, maximum: Option<Size>) -> bool {
    primary.is_flex() || matches!(minimum, Some(Size::Fill | Size::Frac(_)))
        || matches!(maximum, Some(Size::Fill | Size::Frac(_)))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns stack_uses_child(params, axis), no_unwind))]
pub(crate) fn stack_uses_child(params: &LayoutParams, axis: Axis) -> bool {
    let flex = match axis {
        Axis::X => flexible(params.size.x, params.min_size.x, params.max_size.x),
        Axis::Y => flexible(params.size.y, params.min_size.y, params.max_size.y),
    };
    stack_reads_child_list(!params.disabled, !params.free_placement, flex)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Refreshed {
    pub flags: NodeFlags,
    pub placed_children: u32,
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait RefreshModel {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait RefreshModel {
    type Id: Copy;
    spec fn live(&self, id: Self::Id) -> bool;
    spec fn parent_flags(&self, id: Self::Id) -> NodeFlags;
    spec fn layout(&self, id: Self::Id) -> LayoutParams;
    spec fn siblings(&self, parent: Self::Id) -> Seq<Self::Id>;
}

/// Eligibility uses the retained Final states and the current physical child sequence.
pub(crate) open spec fn refresh_eligible<S: RefreshModel + ?Sized>(source: &S, parent: S::Id) -> bool {
    let params = source.layout(parent);
    let flags = source.parent_flags(parent).0;
    &&& flags & NodeFlags::BLOCK_ITEM == 0
    &&& read_state(flags, cycle_rules::slot_index(0, Kind::Final) as u32) == SOLVED
    &&& read_state(flags, cycle_rules::slot_index(1, Kind::Final) as u32) == SOLVED
    &&& !has_intrinsic(&params)
    &&& match params.children_layout {
        ChildrenLayout::Free => true,
        ChildrenLayout::Stack { axis, .. } =>
            read_state(flags, cycle_rules::slot_index(axis.index(), Kind::EvenShare) as u32) == UNSOLVED
            && forall |i: int| 0 <= i < source.siblings(parent).len() ==>
                !stack_uses_child(&source.layout(#[trigger] source.siblings(parent)[i]), axis),
        _ => false,
    }
}

pub(crate) open spec fn sibling_at<I>(ids: Seq<I>, index: int) -> Option<I> {
    if 0 <= index < ids.len() { Some(ids[index]) } else { None }
}

pub(crate) open spec fn share_is_independent(layout: ChildrenLayout, bits: u32, stack: Option<Axis>) -> bool {
    match layout {
        ChildrenLayout::Free => stack.is_none(),
        ChildrenLayout::Stack { axis, .. } => stack == Some(axis)
            && read_state(bits, cycle_rules::slot_index(axis.index(), Kind::EvenShare) as u32) == UNSOLVED,
        _ => false,
    }
}

pub(crate) open spec fn in_flow_count<A: RefreshModel + ?Sized>(source: &A, ids: Seq<A::Id>) -> nat
    decreases ids.len(),
{
    if ids.len() == 0 { 0 }
    else {
        let params = source.layout(ids.last());
        in_flow_count(source, ids.drop_last()) + if !params.disabled && !params.free_placement { 1nat } else { 0nat }
    }
}

fn first_position() -> (index: Ghost<int>)
    ensures index@ == 0,
    no_unwind
{
    Ghost(0int)
}

fn next_position(index: Ghost<int>) -> (next: Ghost<int>)
    ensures next@ == index@ + 1,
    no_unwind
{
    Ghost(index@ + 1)
}

fn remember<T: Copy>(value: T) -> (stored: Ghost<T>)
    ensures stored@ == value,
    no_unwind
{
    Ghost(value)
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait RefreshSource: RefreshModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(flags =>
        requires self.live(parent), ensures flags == self.parent_flags(parent),
        no_unwind
    ))]
    fn old_flags(&self, parent: Self::Id) -> NodeFlags;

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires self.live(id), ensures *out == self.layout(id), no_unwind
    ))]
    fn params(&self, id: Self::Id) -> &LayoutParams;

    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires self.live(parent), ensures next == sibling_at(self.siblings(parent), 0),
        no_unwind
    ))]
    fn first(&self, parent: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires self.live(child), sibling_at(self.siblings(parent@), index@) == Some(child),
        ensures next == sibling_at(self.siblings(parent@), index@ + 1),
        no_unwind
    ))]
    fn following(
        &self, child: Self::Id,
        #[cfg(verus_keep_ghost)] parent: Ghost<Self::Id>,
        #[cfg(verus_keep_ghost)] index: Ghost<int>,
    ) -> Option<Self::Id>;
}

/// Check an independent parent's actual cached states and raw declarations.
/// A successful refresh preserves the parent's sizing across its child-list edit.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires source.live(parent),
        forall |i: int| 0 <= i < source.siblings(parent).len() ==> source.live(#[trigger] source.siblings(parent)[i]),
    ensures
        out.is_some() == refresh_eligible(source, parent),
        out.is_some() ==> !has_intrinsic(&source.layout(parent)),
        out.is_some() ==> source.parent_flags(parent).0 & NodeFlags::BLOCK_ITEM == 0,
        out.is_some() ==> read_state(source.parent_flags(parent).0, cycle_rules::slot_index(0, Kind::Final) as u32) == SOLVED,
        out.is_some() ==> read_state(source.parent_flags(parent).0, cycle_rules::slot_index(1, Kind::Final) as u32) == SOLVED,
        out.is_some() ==> match source.layout(parent).children_layout {
            ChildrenLayout::Free => true,
            ChildrenLayout::Stack { axis, .. } =>
                read_state(source.parent_flags(parent).0, cycle_rules::slot_index(axis.index(), Kind::EvenShare) as u32) == UNSOLVED
                && forall |i: int| 0 <= i < source.siblings(parent).len() ==>
                    !stack_uses_child(&source.layout(#[trigger] source.siblings(parent)[i]), axis),
            _ => false,
        },
        out.is_some() ==> out.unwrap().flags.0 & !REFRESH_FLAGS == source.parent_flags(parent).0 & !REFRESH_FLAGS,
        out.is_some() ==> out.unwrap().placed_children ==
            vstd::math::min(in_flow_count(source, source.siblings(parent)) as int, u32::MAX as int),
    no_unwind
))]
pub(crate) fn refresh_parent<S: RefreshSource + ?Sized>(source: &S, parent: S::Id) -> Option<Refreshed> {
    let original = source.old_flags(parent);
    let block_item = original.0 & NodeFlags::BLOCK_ITEM != 0;
    let finals_solved = read_state(original.0, slot_index(X, Kind::Final) as u32) == SOLVED
        && read_state(original.0, slot_index(Y, Kind::Final) as u32) == SOLVED;
    if !can_refresh(block_item, finals_solved, false) { return None; }
    let params = source.params(parent);
    if has_intrinsic(params) { return None; }
    let stack = match params.children_layout {
        ChildrenLayout::Free => None,
        ChildrenLayout::Stack { axis, .. }
            if read_state(original.0, slot_index(axis, Kind::EvenShare) as u32) == UNSOLVED => Some(axis),
        _ => return None,
    };
    let mut next = source.first(parent);
    let mut count = 0;
    let has_children = next.is_some();
    let mut flags = if has_children { NodeFlags::DESCENDANTS_NEED_SOLVE } else { 0 };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(flags & !CHILD_FLAGS == 0) by(bit_vector)
            requires flags == if has_children { NodeFlags::DESCENDANTS_NEED_SOLVE } else { 0 };
    }
    #[cfg(verus_keep_ghost)]
    let mut index = first_position();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= index@ <= source.siblings(parent).len(),
            next == sibling_at(source.siblings(parent), index@),
            original == source.parent_flags(parent),
            !has_intrinsic(&source.layout(parent)),
            original.0 & NodeFlags::BLOCK_ITEM == 0,
            read_state(original.0, cycle_rules::slot_index(0, Kind::Final) as u32) == SOLVED,
            read_state(original.0, cycle_rules::slot_index(1, Kind::Final) as u32) == SOLVED,
            share_is_independent(source.layout(parent).children_layout, original.0, stack),
            flags & !CHILD_FLAGS == 0,
            count == vstd::math::min(in_flow_count(source, source.siblings(parent).take(index@)) as int, u32::MAX as int),
            forall |i: int| 0 <= i < source.siblings(parent).len() ==> source.live(#[trigger] source.siblings(parent)[i]),
            stack.is_some() ==> forall |i: int| 0 <= i < index@ ==>
                !stack_uses_child(&source.layout(#[trigger] source.siblings(parent)[i]), stack.unwrap()),
        decreases source.siblings(parent).len() - index@,
    ))]
    loop {
        let Some(child) = next else {
            let updated = (original.0 & !REFRESH_FLAGS) | flags;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(index@ == source.siblings(parent).len());
                assert(source.siblings(parent).take(index@) =~= source.siblings(parent));
                let original_bits = original.0;
                assert(updated & !REFRESH_FLAGS == original_bits & !REFRESH_FLAGS) by(bit_vector)
                    requires flags & !CHILD_FLAGS == 0, updated == (original_bits & !REFRESH_FLAGS) | flags;
            }
            return Some(Refreshed { flags: NodeFlags(updated), placed_children: count });
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(0 <= index@ < source.siblings(parent).len());
            assert(child == source.siblings(parent)[index@]);
            assert(source.live(child));
        }
        next = source.following(
            child,
            #[cfg(verus_keep_ghost)]
            remember(parent),
            #[cfg(verus_keep_ghost)]
            index,
        );
        let params = source.params(child);
        if let Some(axis) = stack {
            if stack_uses_child(params, axis) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    let ids = source.siblings(parent);
                    assert(ids[index@] == child);
                    assert(stack_uses_child(&source.layout(ids[index@]), axis));
                }
                return None;
            }
        }
        #[cfg(verus_keep_ghost)]
        let before = remember(flags);
        summarize_child(params, &mut count, &mut flags);
        #[cfg(verus_keep_ghost)]
        proof! {
            let ids = source.siblings(parent);
            let prefix = ids.take(index@);
            let extended = ids.take(index@ + 1);
            assert(extended.drop_last() =~= prefix);
            assert(extended.last() == child);
            assert(in_flow_count(source, extended) == in_flow_count(source, prefix)
                + if !params.disabled && !params.free_placement { 1nat } else { 0nat });
            let in_flow = !params.disabled && !params.free_placement;
            let flex_x = params.size.x.is_flex();
            let flex_y = params.size.y.is_flex();
            let spans = params.grid_span.x > 1 || params.grid_span.y > 1;
            let contribution = if in_flow {
                (if flex_x { NodeFlags::FLEX_CHILD_X } else { 0 })
                | (if flex_y { NodeFlags::FLEX_CHILD_Y } else { 0 })
                | (if spans { NodeFlags::GRID_SPANS } else { 0 })
            } else { 0 };
            assert(contribution & !CHILD_FLAGS == 0) by(bit_vector) requires
                contribution == (if in_flow {
                    (if flex_x { NodeFlags::FLEX_CHILD_X } else { 0 })
                    | (if flex_y { NodeFlags::FLEX_CHILD_Y } else { 0 })
                    | (if spans { NodeFlags::GRID_SPANS } else { 0 })
                } else { 0 });
            let previous = before@;
            if in_flow {
                assert(contribution == crate::prepare_frame::child_flag_mask(params));
            } else {
                assert(previous | 0u32 == previous) by(bit_vector);
            }
            assert(flags & !CHILD_FLAGS == 0) by(bit_vector)
                requires flags == previous | contribution, previous & !CHILD_FLAGS == 0, contribution & !CHILD_FLAGS == 0;
        }
        #[cfg(verus_keep_ghost)]
        {
            index = next_position(index);
        }
    }
}
