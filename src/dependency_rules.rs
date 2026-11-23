// Dependency choices shared by full measurement and incremental notification.
// The proof imports this file directly, including the executable rank arithmetic.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Form { Constant, Ratio, Fraction, Fill, Intrinsic }

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Input { None, OppositeFinal, ParentFinal, ParentShare, IntrinsicChildren }

impl Form {
    /// Primary source of a resolved size declaration. Intrinsic content may
    /// additionally read the opposite Final for its constraints or grid tracks.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.input(stack_item)))]
    pub fn input(self, stack_item: bool) -> Input {
        match self {
            Self::Constant => Input::None,
            Self::Ratio => Input::OppositeFinal,
            Self::Fill if stack_item => Input::ParentShare,
            Self::Fill | Self::Fraction => Input::ParentFinal,
            Self::Intrinsic => Input::IntrinsicChildren,
        }
    }

    /// An intrinsic parent may read its children while computing this declaration.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.reads_children()))]
    pub fn reads_children(self) -> bool { matches!(self, Self::Intrinsic) }

    /// A single pass finds both aspect ratios and cross-constrained intrinsic slots.
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.reads_opposite_final(constrained)))]
    pub fn reads_opposite_final(self, constrained: bool) -> bool {
        matches!(self, Self::Ratio) || (constrained && matches!(self, Self::Intrinsic))
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.contributes_to_intrinsic()))]
    pub fn contributes_to_intrinsic(self) -> bool {
        !matches!(self, Self::Fraction | Self::Fill)
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.contributes_to_share()))]
    pub fn contributes_to_share(self) -> bool {
        !matches!(self, Self::Fill)
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns reads_intrinsic_constraint(intrinsic_other, width_grid_cross)))]
pub fn reads_intrinsic_constraint(intrinsic_other: bool, width_grid_cross: bool) -> bool {
    intrinsic_other || width_grid_cross
}

/// A child's available dimension always reads the same parent axis. A placed
/// item in a width grid also reads the grid's main axis to know its track counts.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns reads_parent_axis(same_axis, in_flow, grid_main)))]
pub fn reads_parent_axis(same_axis: bool, in_flow: bool, grid_main: bool) -> bool {
    same_axis || (in_flow && grid_main)
}

/// A wrap's line extent replaces the enclosing Final on its cross axis. A
/// width-derived grid must have assigned both its tracks and the item's cell
/// before reading the other axis's available space.
macro_rules! request_parent_inputs {
    ($wrap_cross:expr; $other_axis:expr; $final:ident => $on_final:block; $on_flow:block) => {{
        if $wrap_cross $on_flow else {
            { let $final = false; $on_final }
            if $other_axis { let $final = true; $on_final }
        }
    }};
}

pub(crate) use request_parent_inputs;

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns next_level(level)))]
pub fn next_level(level: u16) -> u16 {
    level.saturating_add(1)
}

/// A specialized Final consumes its Regular, so its rank is one step later.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires regular < old(levels).len(), resolved < old(levels).len(), regular != resolved,
    ensures final(levels)@ == old(levels)@.update(regular as int, level)
        .update(resolved as int, next_level(level)),
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
#[cfg_attr(verus_keep_ghost, verus_spec(returns queueable(level)))]
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
