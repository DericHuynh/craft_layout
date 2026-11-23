// Direct numeric inputs read by an acyclic sizing slot, before slot-to-slot propagation.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, Default)]
pub struct AxisEdits {
    pub inner: bool,
    pub other_inner: bool,
    pub content: bool,
    pub margin: bool,
    pub weight: bool,
    pub regular_fraction: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub struct Context {
    pub in_flow: bool,
    pub placed_parent: bool,
    pub parent_stack_axis: bool,
    pub stack_axis: bool,
    pub width_grid: bool,
    pub grid_main: bool,
    pub wraps_text: bool,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, Default)]
pub struct Seeds {
    pub own_intrinsic: bool,
    pub own_fill: bool,
    pub own_final: bool,
    pub own_share: bool,
    pub parent_intrinsic: bool,
    pub parent_share: bool,
    pub child_available: bool,
}

impl AxisEdits {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.seeds(c)))]
    pub fn seeds(self, c: Context) -> Seeds {
        let child_available = self.inner || (c.width_grid && self.other_inner);
        let margin = self.margin && c.in_flow && c.placed_parent;
        let weight = self.weight && c.in_flow && c.parent_stack_axis;
        Seeds {
            own_intrinsic: self.content || child_available || (self.other_inner && c.wraps_text),
            own_fill: margin || weight,
            own_final: c.grid_main && (self.inner || self.other_inner),
            own_share: c.stack_axis && self.inner,
            parent_intrinsic: margin || (c.in_flow && self.regular_fraction),
            parent_share: c.parent_stack_axis && (margin || weight),
            child_available,
        }
    }
}

/// Host callbacks see both pixel maxima and the padding used to compute them.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns content_input_changed(image, custom, padding, maximum)))]
pub fn content_input_changed(image: bool, custom: bool, padding: bool, maximum: bool) -> bool {
    image || (custom && (padding || maximum))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires index < 8, returns declaration_changed(mask, index),
))]
pub fn declaration_changed(mask: u8, index: usize) -> bool {
    mask & (1u8 << index) != 0
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires index < 8,
    ensures forall|i:usize| i < 8 ==> #[trigger] declaration_changed(result, i)
        == (declaration_changed(mask, i) || changed && i == index)
))]
pub fn register_declaration(mask: u8, index: usize, changed: bool) -> u8 {
    let result = if changed { mask | (1u8 << index) } else { mask };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall|i:usize| i < 8 implies #[trigger] declaration_changed(result, i)
            == (declaration_changed(mask, i) || changed && i == index) by {
            assert(((mask | (1u8 << index)) & (1u8 << i) != 0)
                == (mask & (1u8 << i) != 0 || i == index)) by(bit_vector)
                requires index < 8, i < 8;
        }
    }
    result
}

/// A sizing edit either reaches the queue or a solve that already covers it.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Intake { Pending, Cycle, Region, Flow, Budget, Queue }

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns intake(pending, cyclic, structural, flow, at_limit)))]
pub fn intake(pending: bool, cyclic: bool, structural: bool, flow: bool, at_limit: bool) -> Intake {
    if pending { Intake::Pending }
    else if cyclic { Intake::Cycle }
    else if structural { Intake::Region }
    else if flow { Intake::Flow }
    else if at_limit { Intake::Budget }
    else { Intake::Queue }
}
