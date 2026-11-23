//! Decisions used when a structural edit reaches an already measured node.
#![allow(unexpected_cfgs)]
use super::structural_changes::StructuralChange;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns starts_region(mark)))]
pub fn starts_region(mark: StructuralChange) -> bool {
    matches!(mark, StructuralChange::Moved | StructuralChange::Subtree)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum AfterChildren { Keep, Refresh, Rebuild }

/// A cycle visited through an earlier root can expose a different provisional
/// value. Nested work therefore forces replay even without a direct signal.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns after_children(changed, saved_cycle, nested)))]
pub fn after_children(changed: bool, saved_cycle: bool, nested: bool) -> AfterChildren {
    if saved_cycle && (changed || nested) { AfterChildren::Rebuild }
    else if changed { AfterChildren::Refresh }
    else { AfterChildren::Keep }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns can_refresh(block_item, finals_solved, reads_children)))]
pub fn can_refresh(block_item: bool, finals_solved: bool, reads_children: bool) -> bool {
    !block_item && finals_solved && !reads_children
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns stack_reads_child_list(enabled, in_flow, flexible)))]
pub fn stack_reads_child_list(enabled: bool, in_flow: bool, flexible: bool) -> bool {
    enabled && in_flow && flexible
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns attached_flow_child(in_flow, flow_parent)))]
pub fn attached_flow_child(in_flow: bool, flow_parent: bool) -> bool {
    in_flow && flow_parent
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns affects_parent(cyclic, reads_children, block_item, in_parent_flow)))]
pub fn affects_parent(cyclic: bool, reads_children: bool, block_item: bool, in_parent_flow: bool) -> bool {
    cyclic || reads_children || block_item || in_parent_flow
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns clean_branch_root(mark, cyclic)))]
pub fn clean_branch_root(mark: StructuralChange, cyclic: bool) -> bool {
    matches!(mark, StructuralChange::Clean) && !cyclic
}
