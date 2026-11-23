//! Dependencies of a declaration on an ordinary leaf during regional measurement.
#![allow(unexpected_cfgs)]
use super::dependency_rules::Form;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum LeafInput { Local, OppositeFinal, External }

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns input(form, constrained)))]
pub fn input(form: Form, constrained: bool) -> LeafInput {
    match form {
        Form::Constant => LeafInput::Local,
        Form::Intrinsic if !constrained => LeafInput::Local,
        Form::Intrinsic | Form::Ratio => LeafInput::OppositeFinal,
        Form::Fraction | Form::Fill => LeafInput::External,
    }
}

impl LeafInput {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.stable(opposite_known)))]
    pub fn stable(self, opposite_known: bool) -> bool {
        match self {
            Self::Local => true,
            Self::OppositeFinal => opposite_known,
            Self::External => false,
        }
    }
}
