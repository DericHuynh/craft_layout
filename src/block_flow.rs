// Block-axis flow shared by measurement, placement, and verification.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub trait ScalarModel: Copy {
        spec fn zero_value() -> Self;
        spec fn plus(left: Self, right: Self) -> Self;
        spec fn upper(left: Self, right: Self) -> Self;
        spec fn lower(left: Self, right: Self) -> Self;
    }
}

#[cfg(not(verus_keep_ghost))]
pub trait ScalarModel: Copy {}
#[cfg(not(verus_keep_ghost))]
impl ScalarModel for f32 {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Scalar: ScalarModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::zero_value()))]
    fn zero() -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::plus(self,other)))]
    fn add(self, other: Self) -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::upper(self,other)))]
    fn maximum(self, other: Self) -> Self;
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::lower(self,other)))]
    fn minimum(self, other: Self) -> Self;
}

#[cfg(not(verus_keep_ghost))]
impl Scalar for f32 {
    #[inline]
    fn zero() -> Self {
        0.0
    }
    #[inline]
    fn add(self, other: Self) -> Self {
        self + other
    }
    #[inline]
    fn maximum(self, other: Self) -> Self {
        self.max(other)
    }
    #[inline]
    fn minimum(self, other: Self) -> Self {
        self.min(other)
    }
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Default, PartialEq))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct CollapsedMargin<F: Copy = f32> {
    pub positive: F,
    pub negative: F,
}

impl<F: Copy> Copy for CollapsedMargin<F> {}
impl<F: Copy> Clone for CollapsedMargin<F> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<F: Scalar> CollapsedMargin<F> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns from_edge(value)))]
    pub fn new(value: F) -> Self {
        Self {
            positive: value.maximum(F::zero()),
            negative: value.minimum(F::zero()),
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures *final(self) == join(*old(self),other)))]
    pub fn merge(&mut self, other: Self) {
        self.positive = self.positive.maximum(other.positive);
        self.negative = self.negative.minimum(other.negative);
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns advance(self)))]
    fn size(self) -> F {
        self.positive.add(self.negative)
    }
}

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Clone, Copy, Default))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct BlockMargins<F: Copy = f32> {
    pub before: CollapsedMargin<F>,
    pub after: CollapsedMargin<F>,
    pub all_through: bool,
}

#[cfg(not(verus_keep_ghost))]
impl BlockMargins {
    pub fn is_implicit(self, children_empty: bool) -> bool {
        self.before == CollapsedMargin::default()
            && self.after == CollapsedMargin::default()
            && self.all_through == children_empty
    }
}

/// The collapsible edges and the height of one in-flow block.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct BlockItem<F: Copy = f32> {
    pub before: CollapsedMargin<F>,
    pub after: CollapsedMargin<F>,
    pub size: F,
    pub through: bool,
}

impl<F: Scalar> BlockItem<F> {
    /// Type and declaration checks decide whether the box itself separates its edges.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns item_from_edges(top,bottom,size,adjoins,children_empty,nested)))]
    pub fn from_edges(
        top: F,
        bottom: F,
        size: F,
        adjoins: bool,
        children_empty: bool,
        nested: Option<BlockMargins<F>>,
    ) -> Self {
        let mut before = CollapsedMargin::new(top);
        let mut after = CollapsedMargin::new(bottom);
        let children_through = match nested {
            Some(nested) => {
                before.merge(nested.before);
                after.merge(nested.after);
                nested.all_through
            }
            None => children_empty,
        };
        Self {
            before,
            after,
            size,
            through: adjoins && children_through,
        }
    }
}

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Copy))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct BlockFlow<F: Copy = f32> {
    pub end: F,
    pub pending: CollapsedMargin<F>,
    pub outgoing: BlockMargins<F>,
    pub collapse_top: bool,
    pub collapse_bottom: bool,
}

impl<F: Scalar> BlockFlow<F> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns initial::<F>(collapse_top,collapse_bottom)))]
    pub fn from_edges(collapse_top: bool, collapse_bottom: bool) -> Self {
        let end = F::zero();
        let blank = CollapsedMargin {
            positive: end,
            negative: end,
        };
        Self {
            end,
            pending: blank,
            outgoing: BlockMargins {
                before: blank,
                after: blank,
                all_through: true,
            },
            collapse_top,
            collapse_bottom,
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(start =>
        ensures (*final(self),start) == push(*old(self),item),
    ))]
    pub fn push(&mut self, item: BlockItem<F>) -> F {
        self.pending.merge(item.before);
        let top_adjoins_parent = self.outgoing.all_through && self.collapse_top;
        let start = self.end.add(if top_adjoins_parent {
            F::zero()
        } else {
            self.pending.size()
        });
        if item.through {
            self.pending.merge(item.after);
        } else {
            if top_adjoins_parent {
                self.outgoing.before = self.pending;
            }
            self.outgoing.all_through = false;
            self.end = start.add(item.size);
            self.pending = item.after;
        }
        start
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns finish(self)))]
    pub fn finish(mut self) -> (F, BlockMargins<F>) {
        if self.outgoing.all_through && self.collapse_top {
            self.outgoing.before = self.pending;
        } else if self.collapse_bottom {
            self.outgoing.after = self.pending;
        } else {
            self.end = self.end.add(self.pending.size());
        }
        (self.end.maximum(F::zero()), self.outgoing)
    }
}
