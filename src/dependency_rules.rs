// Dependency choices shared by full measurement and incremental notification.
// The proof imports this file directly, including the executable rank arithmetic.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Form { Constant, Ratio, Fraction, Fill, Intrinsic }

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Input<I = ()> { None, OppositeFinal, ParentFinal, ParentShare(I), IntrinsicChildren }

impl Form {
    /// Primary source of a resolved size declaration. Intrinsic content may
    /// additionally read the opposite Final for its constraints or grid tracks.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.input(stack_item), no_unwind))]
    pub fn input(self, stack_item: bool) -> Input {
        self.input_for(if stack_item { Some(()) } else { None })
    }

    /// Keep the parent ID with a share request so the caller can issue it
    /// directly. Only a Fill inside a stack can produce that request.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.input_for(stack_parent), no_unwind))]
    pub fn input_for<I: Copy>(self, stack_parent: Option<I>) -> Input<I> {
        match self {
            Self::Constant => Input::None,
            Self::Ratio => Input::OppositeFinal,
            Self::Fill => match stack_parent {
                Some(parent) => Input::ParentShare(parent),
                None => Input::ParentFinal,
            },
            Self::Fraction => Input::ParentFinal,
            Self::Intrinsic => Input::IntrinsicChildren,
        }
    }

    /// An intrinsic parent may read its children while computing this declaration.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.reads_children(), no_unwind))]
    pub fn reads_children(self) -> bool { matches!(self, Self::Intrinsic) }

    /// A single pass finds both aspect ratios and cross-constrained intrinsic slots.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.reads_opposite_final(constrained), no_unwind))]
    pub fn reads_opposite_final(self, constrained: bool) -> bool {
        matches!(self, Self::Ratio) || (constrained && matches!(self, Self::Intrinsic))
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.contributes_to_intrinsic(), no_unwind))]
    pub fn contributes_to_intrinsic(self) -> bool {
        !matches!(self, Self::Fraction | Self::Fill)
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.contributes_to_share(), no_unwind))]
    pub fn contributes_to_share(self) -> bool {
        !matches!(self, Self::Fill)
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns reads_intrinsic_constraint(intrinsic_other, width_grid_cross), no_unwind))]
pub fn reads_intrinsic_constraint(intrinsic_other: bool, width_grid_cross: bool) -> bool {
    intrinsic_other || width_grid_cross
}

/// A child's available dimension always reads the same parent axis. A placed
/// item in a width grid also reads the grid's main axis to know its track counts.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns reads_parent_axis(same_axis, in_flow, grid_main), no_unwind))]
pub fn reads_parent_axis(same_axis: bool, in_flow: bool, grid_main: bool) -> bool {
    same_axis || (in_flow && grid_main)
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns next_level(level), no_unwind))]
pub fn next_level(level: u16) -> u16 {
    level.saturating_add(1)
}

/// Start measuring a slot with a fresh dependency level.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(previous =>
    ensures previous == *old(current), *final(current) == 0,
    no_unwind
))]
pub(crate) fn capture_level(current: &mut u16) -> u16 {
    let previous = *current;
    *current = 0;
    previous
}

/// Record a dependency of the enclosing slot, saturating at the rank sentinel.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    returns include_level(current, dependency),
    no_unwind
))]
pub(crate) fn include_level(current: u16, dependency: u16) -> u16 {
    let next = next_level(dependency);
    if current >= next { current } else { next }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires index < old(levels).len(),
    ensures final(levels)@ == old(levels)@.update(index as int, level),
    no_unwind
))]
pub(crate) fn publish_level(levels: &mut [u16], index: usize, level: u16) {
    levels[index] = level;
}

/// A specialized Final consumes its Regular, so its rank is one step later.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires regular < old(levels).len(), resolved < old(levels).len(), regular != resolved,
    ensures final(levels)@ == old(levels)@.update(regular as int, level)
        .update(resolved as int, next_level(level)),
    no_unwind
))]
pub fn publish_levels(levels: &mut [u16], regular: usize, resolved: usize, level: u16) {
    levels[regular] = level;
    levels[resolved] = next_level(level);
}

/// The final bucket is a sentinel. It forces fresh measurement before the
/// queue would need to order two inputs whose mathematical ranks are larger.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns queueable(level), no_unwind))]
pub fn queueable(level: u16) -> bool { level != u16::MAX }

/// Charge the next queued slot before attempting to compute it.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    ensures match next {
        Some(n) => computed < limit && n == computed + 1 && n <= limit,
        None => computed >= limit,
    },
    no_unwind
))]
pub fn charge_queue_slot(computed: u32, limit: u32) -> Option<u32> {
    if computed < limit { Some(computed + 1) } else { None }
}
