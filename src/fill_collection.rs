// Ordered arithmetic while collecting the inputs to a Fill distribution.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
pub trait NumericModel: Copy {
    spec fn zero_bits() -> Self;
    spec fn sum(left: Self,right: Self) -> Self;
    spec fn charge(left: Self,right: Self) -> Self;
    spec fn clamp_nonnegative(value: Self) -> Self;
    spec fn max_weight(old: Option<Self>, weight: Self) -> Self;
}
}

#[cfg(not(verus_keep_ghost))]
pub trait NumericModel: Copy {}
#[cfg(not(verus_keep_ghost))]
impl NumericModel for f32 {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Numeric: NumericModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::zero_bits(), no_unwind))]
    fn zero() -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::sum(self,other), no_unwind))]
    fn add(self, other: Self) -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::charge(self,other), no_unwind))]
    fn subtract(self, other: Self) -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::clamp_nonnegative(self), no_unwind))]
    fn nonnegative(self) -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::max_weight(old,weight), no_unwind))]
    fn unconstrained(old: Option<Self>, weight: Self) -> Self;
}

#[cfg(not(verus_keep_ghost))]
impl Numeric for f32 {
    #[inline(always)]
    fn zero() -> Self {
        0.0
    }
    #[inline(always)]
    fn add(self, other: Self) -> Self {
        self + other
    }
    #[inline(always)]
    fn subtract(self, other: Self) -> Self {
        super::fill_budget::charge(self, other)
    }
    #[inline(always)]
    fn nonnegative(self) -> Self {
        super::fill_budget::nonnegative(self)
    }
    #[inline(always)]
    fn unconstrained(old: Option<Self>, weight: Self) -> Self {
        let abs_weight = if weight.is_nan() {
            f32::INFINITY
        } else {
            weight.abs()
        };
        old.map_or(abs_weight, |current| current.max(abs_weight))
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct FillCollection<F: Copy = f32> {
    pub budget: F,
    pub weight: F,
    pub worst: Option<F>,
}

impl<F: Numeric> FillCollection<F> {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns fresh(budget), no_unwind))]
    pub fn new(budget: F) -> Self {
        Self {
            budget,
            weight: F::zero(),
            worst: None,
        }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures *final(self) == charge(*old(self),F::sum(start,end)),
        no_unwind
    ))]
    pub fn margin(&mut self, start: F, end: F) {
        self.budget = self.budget.subtract(start.add(end));
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures *final(self) == charge(*old(self),size), no_unwind))]
    pub fn fixed(&mut self, size: F) {
        self.budget = self.budget.subtract(size);
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures *final(self) == add_weight(*old(self),weight), no_unwind))]
    pub fn weight(&mut self, weight: F) {
        self.weight = self.weight.add(weight);
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures *final(self) == record_worst(*old(self),weight), no_unwind))]
    pub fn mark_unconstrained(&mut self, weight: F) {
        self.worst = Some(F::unconstrained(self.worst, weight));
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns finish(self), no_unwind))]
    pub fn finish(self) -> (F, F, Option<F>) {
        (self.budget.nonnegative(), self.weight, self.worst)
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns has_constraint(content,min,max), no_unwind))]
pub fn has_constraint<F: Copy>(content: Option<F>, min: Option<F>, max: Option<F>) -> bool {
    content.is_some() || min.is_some() || max.is_some()
}
