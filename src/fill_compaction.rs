// In-place Fill compaction. Verus checks this same code against a scalar pass.
#![allow(unexpected_cfgs)]
use core::marker::PhantomData;
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(not(verus_keep_ghost))]
use crate::fill_budget::share as budget_share;
#[cfg(not(verus_keep_ghost))]
use super::fill_collection::{FillCollection, Numeric};
#[cfg(verus_keep_ghost)]
use crate::stack_share::{
    add_weight, charge, finish, fresh, record_worst,
    kernel::{FillCollection, Numeric, NumericModel},
};
use crate::vec_memory::{CapacityMemory, VecMemory, append_bounded};
#[cfg(verus_keep_ghost)]
use crate::vec_memory::capacity_limit;
#[cfg(not(verus_keep_ghost))]
use crate::vec_memory::RustVec;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
    pub trait ProjectModel<T, D>: Copy {
        spec fn projected(self, item: T) -> D;
    }

    pub trait AccountModel<D, S>: Copy {
        spec fn accounted(self, state: S, data: D) -> S;
    }

    pub trait FloatModel: Copy {
        spec fn sum(a: f32, b: f32) -> f32;
        spec fn difference(a: f32, b: f32) -> f32;
        spec fn product(a: f32, b: f32) -> f32;
        spec fn less(a: f32, b: f32) -> bool;
        spec fn magnitude(value: f32) -> f32;
        spec fn is_finite(value: f32) -> bool;
        spec fn invalid() -> f32;
        spec fn positive_infinity() -> f32;
        spec fn available_share(budget: f32, frozen: f32, weight: f32) -> f32;
        spec fn unordered(value: f32) -> bool;
        spec fn minimum(a: f32, b: f32) -> f32;
        spec fn maximum(a: f32, b: f32) -> f32;
    }
}

#[cfg(not(verus_keep_ghost))]
pub trait ProjectModel<T, D>: Copy {}
#[cfg(not(verus_keep_ghost))]
pub trait AccountModel<D, S>: Copy {}
#[cfg(not(verus_keep_ghost))]
pub trait FloatModel: Copy {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Project<T, D>: ProjectModel<T, D> {
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.projected(item), no_unwind))]
    fn project(&self, item: T) -> D;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait Account<D, S>: AccountModel<D, S> {
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.accounted(state, data), no_unwind))]
    fn account(&self, state: S, data: D) -> S;
}

/// Primitive IEEE operations. The proofs use their results symbolically and
/// preserve every operand and the order in which the kernel combines them.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FloatOps: FloatModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::sum(a, b), no_unwind))]
    fn add(a: f32, b: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::difference(a, b), no_unwind))]
    fn subtract(a: f32, b: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::product(a, b), no_unwind))]
    fn multiply(a: f32, b: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::less(a, b), no_unwind))]
    fn below(a: f32, b: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::magnitude(value), no_unwind))]
    fn abs(value: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::is_finite(value), no_unwind))]
    fn finite(value: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::invalid(), no_unwind))]
    fn nan() -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::positive_infinity(), no_unwind))]
    fn infinity() -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::available_share(budget, frozen, weight), no_unwind))]
    fn share(budget: f32, frozen: f32, weight: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::unordered(value), no_unwind))]
    fn is_nan(value: f32) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::minimum(a, b), no_unwind))]
    fn min(a: f32, b: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::maximum(a, b), no_unwind))]
    fn max(a: f32, b: f32) -> f32;
}

#[cfg(not(verus_keep_ghost))]
#[derive(Clone, Copy)]
pub(crate) struct RustFloat;

#[cfg(not(verus_keep_ghost))]
impl FloatModel for RustFloat {}

#[cfg(not(verus_keep_ghost))]
impl FloatOps for RustFloat {
    #[inline(always)]
    fn share(budget: f32, frozen: f32, weight: f32) -> f32 { budget_share(budget, frozen, weight) }
    #[inline(always)]
    fn add(a: f32, b: f32) -> f32 { a + b }
    #[inline(always)]
    fn subtract(a: f32, b: f32) -> f32 { a - b }
    #[inline(always)]
    fn multiply(a: f32, b: f32) -> f32 { a * b }
    #[inline(always)]
    fn below(a: f32, b: f32) -> bool { a < b }
    #[inline(always)]
    fn abs(value: f32) -> f32 { value.abs() }
    #[inline(always)]
    fn finite(value: f32) -> bool { value.is_finite() }
    #[inline(always)]
    fn nan() -> f32 { f32::NAN }
    #[inline(always)]
    fn infinity() -> f32 { f32::INFINITY }
    #[inline(always)]
    fn is_nan(value: f32) -> bool { value.is_nan() }
    #[inline(always)]
    fn min(a: f32, b: f32) -> f32 { a.min(b) }
    #[inline(always)]
    fn max(a: f32, b: f32) -> f32 { a.max(b) }
}

/// The collected budget and the resolver use one binary32 arithmetic model.
#[repr(transparent)]
#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct FillNumber<F: FloatModel> {
    value: f32,
    float: PhantomData<F>,
}

impl<F: FloatModel> FillNumber<F> {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::new(value), no_unwind))]
    pub(crate) fn new(value: f32) -> Self {
        Self { value, float: PhantomData }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl<F: FloatModel> NumericModel for FillNumber<F> {
        closed spec fn zero_bits() -> Self { Self::new(0.0) }
        closed spec fn sum(a: Self, b: Self) -> Self { Self::new(F::sum(a.value, b.value)) }
        closed spec fn charge(a: Self, b: Self) -> Self { Self::new(F::difference(a.value, b.value)) }
        closed spec fn clamp_nonnegative(a: Self) -> Self {
            if F::less(0.0, a.value) { a } else { Self::new(0.0) }
        }
        closed spec fn max_weight(old: Option<Self>, weight: Self) -> Self {
            let absolute = if F::unordered(weight.value) { F::positive_infinity() } else { F::magnitude(weight.value) };
            match old {
                Some(current) => Self::new(F::maximum(current.value, absolute)),
                None => Self::new(absolute),
            }
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl<F: FloatModel> super::fill_collection::NumericModel for FillNumber<F> {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<F: FloatOps> Numeric for FillNumber<F> {
    #[inline(always)]
    fn zero() -> Self { Self::new(0.0) }

    #[inline(always)]
    fn add(self, other: Self) -> Self { Self::new(F::add(self.value, other.value)) }

    #[inline(always)]
    fn subtract(self, other: Self) -> Self { Self::new(F::subtract(self.value, other.value)) }

    #[inline(always)]
    fn nonnegative(self) -> Self {
        if F::below(0.0, self.value) { self } else { Self::new(0.0) }
    }

    #[inline(always)]
    fn unconstrained(old: Option<Self>, weight: Self) -> Self {
        let absolute = if F::is_nan(weight.value) { F::infinity() } else { F::abs(weight.value) };
        match old {
            Some(current) => Self::new(F::max(current.value, absolute)),
            None => Self::new(absolute),
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
const EVEN_SHARE_EPSILON: f32 = 1e-3;

/// The resolved bounds and weight of a Fill child.
#[derive(Debug, Clone, Copy, Default)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct FillChild {
    min: f32,
    max: f32,
    pub weight: f32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) const fn empty_fill() -> FillChild {
    FillChild { min: 0.0, max: 0.0, weight: 0.0 }
}

impl FillChild {
    #[cfg(all(test, not(verus_keep_ghost)))]
    #[inline]
    pub(crate) fn new(
        content: Option<f32>, min: Option<f32>, max: Option<f32>, capped_by_content: bool, weight: f32,
    ) -> Self {
        Self::new_with::<RustFloat>(content, min, max, capped_by_content, weight)
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        returns FillChild::bounds::<F>(content, min, max, capped_by_content, weight),
        no_unwind
    ))]
    pub(crate) fn new_with<F: FloatOps>(
        content: Option<f32>, min: Option<f32>, max: Option<f32>, capped_by_content: bool, weight: f32,
    ) -> Self {
        // f32::min/max ignore a NaN bound. Fold the intrinsic constraint into
        // the interval once, preserving the minimum's precedence.
        let mut min = if let Some(min) = min { min } else { F::nan() };
        let mut max = if let Some(max) = max { max } else { F::nan() };
        if let Some(content) = content {
            if !F::is_nan(content) {
                if capped_by_content { max = F::min(max, content); }
                else { min = F::max(min, F::min(content, max)); }
            }
        }
        Self { min, max, weight }
    }

    #[cfg(all(test, not(verus_keep_ghost)))]
    pub(crate) fn size(&self, target: f32) -> f32 {
        self.clamp::<RustFloat>(target)
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.clamped::<F>(target), no_unwind))]
    fn clamp<F: FloatOps>(&self, target: f32) -> f32 {
        // An absent bound is NaN, so its comparison is false. A NaN target
        // produces a NaN violation and never freezes.
        let capped = if F::below(self.max, target) { self.max } else { target };
        if F::below(capped, self.min) { self.min } else { capped }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.resolved::<F>(share), no_unwind))]
    fn resolve<F: FloatOps>(self, share: f32) -> (f32, f32) {
        let target = F::multiply(share, self.weight);
        let size = self.clamp::<F>(target);
        (size, F::subtract(size, target))
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    impl FillChild {
        pub(crate) closed spec fn bounds<F: FloatModel>(
            content: Option<f32>, min: Option<f32>, max: Option<f32>, capped: bool, weight: f32,
        ) -> FillChild {
            let min = match min { Some(value) => value, None => F::invalid() };
            let max = match max { Some(value) => value, None => F::invalid() };
            match content {
                Some(value) => if F::unordered(value) {
                    FillChild { min, max, weight }
                } else if capped {
                    FillChild { min, max: F::minimum(max, value), weight }
                } else {
                    FillChild { min: F::maximum(min, F::minimum(value, max)), max, weight }
                },
                None => FillChild { min, max, weight },
            }
        }

        closed spec fn clamped<F: FloatModel>(&self, target: f32) -> f32 {
            let capped = if F::less(self.max, target) { self.max } else { target };
            if F::less(capped, self.min) { self.min } else { capped }
        }

        closed spec fn resolved<F: FloatModel>(&self, share: f32) -> (f32, f32) {
            let target = F::product(share, self.weight);
            let size = self.clamped::<F>(target);
            (size, F::difference(size, target))
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const INLINE_CAPACITY: usize = 8;

/// The inline buffer's length stops at capacity even when the caller spills
/// later children to a Vec. Prefix slicing never depends on the total child count.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct InlineConstraints<T> {
    items: [T; INLINE_CAPACITY],
    len: usize,
}

#[cfg(verus_keep_ghost)]
verus! {
    impl<T> InlineConstraints<T> {
        pub(crate) closed spec fn valid(self) -> bool { self.len <= INLINE_CAPACITY }
        pub(crate) closed spec fn view(self) -> Seq<T> { self.items@.take(self.len as int) }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(buf =>
    ensures buf.valid(), buf.view() == Seq::<T>::empty(),
    no_unwind
))]
pub(crate) fn inline_constraints<T: Copy>(items: [T; INLINE_CAPACITY]) -> InlineConstraints<T> {
    #[cfg(verus_keep_ghost)]
    proof! { assert(items@.take(0) =~= Seq::<T>::empty()); }
    InlineConstraints { items, len: 0 }
}

impl<T: Copy> InlineConstraints<T> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(accepted =>
        requires old(self).valid(),
        ensures final(self).valid(), accepted == (old(self).view().len() < INLINE_CAPACITY),
            final(self).view() == if accepted { old(self).view().push(item) } else { old(self).view() },
        no_unwind
    ))]
    pub(crate) fn push(&mut self, item: T) -> bool {
        if self.len == INLINE_CAPACITY {
            return false;
        }
        self.items[self.len] = item;
        self.len += 1;
        #[cfg(verus_keep_ghost)]
        proof! { assert(self.view() =~= old(self).view().push(item)); }
        true
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(prefix =>
        requires old(self).valid(),
        ensures final(self).valid(), prefix@ == old(self).view(), final(prefix)@ == final(self).view(),
        no_unwind
    ))]
    pub(crate) fn as_mut_slice(&mut self) -> &mut [T] {
        let items: &mut [T] = &mut self.items;
        items.split_at_mut(self.len).0
    }
}

/// The first spill copies the inline records as a block. The optional reserve
/// only anticipates further growth and does not affect the visible sequence.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait SpillMemory {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(spill)@ == old(spill)@,
        no_unwind
    ))]
    fn reserve_for_spill(spill: &mut Vec<FillChild>);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(spill).len() == 0, prefix.len() <= INLINE_CAPACITY,
        ensures final(spill)@ == prefix@,
        no_unwind
    ))]
    fn copy_inline(spill: &mut Vec<FillChild>, prefix: &[FillChild]);
}

#[cfg(not(verus_keep_ghost))]
pub(crate) struct VecSpill;

#[cfg(not(verus_keep_ghost))]
impl SpillMemory for VecSpill {
    #[inline]
    fn reserve_for_spill(spill: &mut Vec<FillChild>) {
        let _ = spill.try_reserve(2 * INLINE_CAPACITY);
    }

    #[inline]
    fn copy_inline(spill: &mut Vec<FillChild>, prefix: &[FillChild]) {
        spill.extend_from_slice(prefix);
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(spill).len() == 0, old(inline).valid(),
    ensures final(spill)@ == old(inline).view(), final(inline).valid(),
        final(inline).view() == old(inline).view(),
    no_unwind
))]
fn seed_spill<M: SpillMemory>(spill: &mut Vec<FillChild>, inline: &mut InlineConstraints<FillChild>) {
    M::reserve_for_spill(spill);
    let prefix = inline.as_mut_slice();
    M::copy_inline(spill, prefix);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum Terms<N: Copy> {
    Fixed(N),
    Unconstrained(N),
    Constrained(N, FillChild),
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct ChildTerms<N: Copy> {
    pub margins: [N; 2],
    pub terms: Terms<N>,
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) trait ChildrenModel {
        type Child: Copy;
        type Number: Numeric;
        type Fixed;

        #[verifier::prophetic]
        spec fn fixed(&self) -> Self::Fixed;
        spec fn live(&self, child: Self::Child) -> bool;
        spec fn ordered_rows(&self, next: Option<Self::Child>, end: Option<Self::Child>)
            -> Seq<Option<ChildTerms<Self::Number>>>;
        spec fn remaining(&self, next: Option<Self::Child>, end: Option<Self::Child>) -> nat;
        spec fn remaining_constraints(&self, next: Option<Self::Child>, end: Option<Self::Child>) -> nat;
    }

    #[verifier::prophetic]
    pub(crate) open spec fn same_rows<I: ChildrenModel + ?Sized>(before: &I, after: &I) -> bool {
        &&& before.fixed() == after.fixed()
        &&& forall |child: I::Child| #[trigger] after.live(child) == before.live(child)
        &&& forall |next: Option<I::Child>, end: Option<I::Child>|
            #[trigger] after.ordered_rows(next, end) == before.ordered_rows(next, end)
        &&& forall |next: Option<I::Child>, end: Option<I::Child>|
            #[trigger] after.remaining(next, end) == before.remaining(next, end)
        &&& forall |next: Option<I::Child>, end: Option<I::Child>|
            #[trigger] after.remaining_constraints(next, end) == before.remaining_constraints(next, end)
    }

    pub(crate) open spec fn has_resolved_constraint<N: Copy>(row: Option<ChildTerms<N>>) -> bool {
        row matches Some(child) && child.terms matches Terms::Constrained(_, _)
    }

    closed spec fn collected(spill: Seq<FillChild>, inline: InlineConstraints<FillChild>) -> Seq<FillChild> {
        if spill.len() == 0 { inline.view() } else { spill }
    }

    /// Preserve margin/size/weight order and the exact order of bounded rows.
    pub(crate) closed spec fn collect_rows<N: NumericModel>(rows: Seq<Option<ChildTerms<N>>>,
        totals: FillCollection<N>, bounds: Seq<FillChild>,
    ) -> (FillCollection<N>, Seq<FillChild>)
        decreases rows.len(),
    {
        if rows.len() == 0 {
            (totals, bounds)
        } else {
            let next = match rows.first() {
                None => (totals, bounds),
                Some(row) => {
                    let charged = charge(totals, N::sum(row.margins[0], row.margins[1]));
                    match row.terms {
                        Terms::Fixed(size) => (charge(charged, size), bounds),
                        Terms::Unconstrained(weight) => (record_worst(add_weight(charged, weight), weight), bounds),
                        Terms::Constrained(weight, fill) => (add_weight(charged, weight), bounds.push(fill)),
                    }
                }
            };
            collect_rows(rows.drop_first(), next.0, next.1)
        }
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait ChildrenModel {
    type Child: Copy;
    type Number: Numeric;
}

/// Reads one live child up to the line's exclusive end, and lends the empty
/// cached spill only when the first constraints do not fit inline.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Children: ChildrenModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires self.live(child),
        ensures out.is_none() == (self.ordered_rows(Some(child), end).len() == 0),
            out matches Some((next, row)) ==> {
            &&& self.ordered_rows(Some(child), end) == seq![row] + self.ordered_rows(next, end)
            &&& self.remaining(next, end) < self.remaining(Some(child), end)
            &&& self.remaining_constraints(next, end) + (if has_resolved_constraint(row) { 1nat } else { 0nat })
                == self.remaining_constraints(Some(child), end)
            &&& next.is_some() ==> self.live(next.unwrap())
        },
        no_unwind
    ))]
    fn read(&self, child: Self::Child, end: Option<Self::Child>) -> Option<(Option<Self::Child>, Option<ChildTerms<Self::Number>>)>;

    #[cfg_attr(verus_keep_ghost, verus_spec(spill =>
        ensures spill.len() == 0, same_rows(old(self), final(self)),
        no_unwind
    ))]
    fn take_spill(&mut self) -> Vec<FillChild>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires spill.len() == 0,
        ensures same_rows(old(self), final(self)),
        no_unwind
    ))]
    fn return_spill(&mut self, spill: Vec<FillChild>);
}

#[cfg(not(verus_keep_ghost))]
pub(crate) fn distribute<I: Children<Number = FillNumber<RustFloat>>>(
    source: &mut I, first: Option<I::Child>, end: Option<I::Child>, budget: f32,
) -> f32 {
    distribute_with::<I, RustFloat, VecSpill, RustVec>(source, first, end, budget)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(output =>
    requires first.is_some() ==> old(source).live(first.unwrap()),
        old(source).ordered_rows(None, end).len() == 0,
        old(spill).len() == 0, old(inline).valid(), old(inline).view().len() == 0,
        old(source).remaining_constraints(first, end) <= capacity_limit::<FillChild>(),
    ensures final(inline).valid(), same_rows(old(source), final(source)), ({
        let folded = collect_rows(old(source).ordered_rows(first, end), fresh(budget), Seq::empty());
        &&& collected(final(spill)@, *final(inline)) == folded.1
        &&& output == finish(folded.0)
        &&& folded.1.len() <= old(source).remaining_constraints(first, end)
    }),
    no_unwind
))]
fn collect_with<I: Children, S: SpillMemory, V: CapacityMemory>(source: &mut I, first: Option<I::Child>,
    end: Option<I::Child>, budget: I::Number, spill: &mut Vec<FillChild>, inline: &mut InlineConstraints<FillChild>,
) -> (I::Number, I::Number, Option<I::Number>) {
    let mut collection = FillCollection::new(budget);
    let mut next = first;
    #[cfg(verus_keep_ghost)]
    proof! { assert(collected(spill@, *inline) =~= Seq::<FillChild>::empty()); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant next.is_some() ==> source.live(next.unwrap()), inline.valid(),
            same_rows(old(source), source),
            spill.len() > 0 ==> inline.view().len() == INLINE_CAPACITY,
            collected(spill@, *inline).len() + source.remaining_constraints(next, end)
                == old(source).remaining_constraints(first, end),
            old(source).remaining_constraints(first, end) <= capacity_limit::<FillChild>(),
            source.ordered_rows(None, end).len() == 0,
            collect_rows(source.ordered_rows(next, end), collection, collected(spill@, *inline))
                == collect_rows(old(source).ordered_rows(first, end), fresh(budget), Seq::empty()),
        decreases source.remaining(next, end),
    ))]
    loop {
        let step = match next {
            Some(child) => source.read(child, end),
            None => None,
        };
        let Some((following, row)) = step else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(source.ordered_rows(next, end).len() == 0);
                assert(collect_rows(source.ordered_rows(next, end), collection, collected(spill@, *inline))
                    == (collection, collected(spill@, *inline)));
            }
            return collection.finish();
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let input = source.ordered_rows(next, end);
            assert(input.len() > 0 && input.first() == row);
            assert(input.drop_first() =~= source.ordered_rows(following, end));
        }
        next = following;
        if let Some(row) = row {
            collection.margin(row.margins[0], row.margins[1]);
            match row.terms {
                Terms::Fixed(size) => collection.fixed(size),
                Terms::Unconstrained(weight) => {
                    collection.weight(weight);
                    collection.mark_unconstrained(weight);
                }
                Terms::Constrained(weight, fill) => {
                    collection.weight(weight);
                    if !inline.push(fill) {
                        if spill.is_empty() {
                            *spill = source.take_spill();
                            seed_spill::<S>(spill, inline);
                        }
                        append_bounded::<FillChild, V>(spill, fill);
                    }
                }
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) closed spec fn share_for_rows<F: FloatOps>(rows: Seq<Option<ChildTerms<FillNumber<F>>>>, budget: f32) -> f32 {
    let gathered = collect_rows(rows, fresh(FillNumber::<F>::new(budget)), Seq::empty());
    let (budget, weight, worst) = finish(gathered.0);
    resolved_share::<F>(gathered.1, budget.value, weight.value,
        match worst { Some(value) => Some(value.value), None => None })
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(share =>
    requires first.is_some() ==> old(source).live(first.unwrap()),
        old(source).ordered_rows(None, end).len() == 0,
        old(source).remaining_constraints(first, end) <= capacity_limit::<FillChild>(),
    ensures same_rows(old(source), final(source)),
        share == share_for_rows::<F>(old(source).ordered_rows(first, end), budget),
    no_unwind
))]
pub(crate) fn distribute_with<I, F, S, V>(source: &mut I, first: Option<I::Child>, end: Option<I::Child>, budget: f32) -> f32
where
    I: Children<Number = FillNumber<F>>,
    F: FloatOps,
    S: SpillMemory,
    V: CapacityMemory + VecMemory,
{
    let mut spill = V::empty();
    let empty = empty_fill();
    let mut inline = inline_constraints([empty, empty, empty, empty, empty, empty, empty, empty]);
    let (budget, weight, worst) = collect_with::<I, S, V>(source, first, end, FillNumber::<F>::new(budget), &mut spill, &mut inline);
    let worst = match worst { Some(value) => Some(value.value), None => None };
    if spill.is_empty() {
        return resolve_fill_share_with::<F>(inline.as_mut_slice(), budget.value, weight.value, worst);
    }
    let share = resolve_fill_share_with::<F>(spill.as_mut_slice(), budget.value, weight.value, worst);
    V::clear(&mut spill);
    source.return_spill(spill);
    share
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (exists |i: int| 0 <= i < N && (#[trigger] lanes[i]).0),
    no_unwind
))]
fn any_frozen<D, const N: usize>(lanes: &[(bool, D); N]) -> bool {
    let mut i = 0;
    let mut frozen = false;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= N, frozen == (exists |j: int| 0 <= j < i && (#[trigger] lanes[j]).0),
        decreases N - i,
    ))]
    while i < N {
        frozen |= lanes[i].0;
        i += 1;
    }
    frozen
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(group =>
    requires start + 4 <= items.len(),
    ensures group@ == items@.subrange(start as int, start + 4),
    no_unwind
))]
fn read_group<T: Copy>(items: &[T], start: usize) -> [T; 4] {
    let block = items.split_at(start).1.split_at(4).0;
    let group = [block[0], block[1], block[2], block[3]];
    #[cfg(verus_keep_ghost)]
    proof! { assert(group@ =~= items@.subrange(start as int, start + 4)); }
    group
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires start + N <= old(active).len(),
    ensures final(active).len() == old(active).len(),
        final(active)@.subrange(start as int, start + N) == group@,
        forall |i: int| 0 <= i < final(active).len() && !(start <= i < start + N)
            ==> final(active)[i] == old(active)[i],
    no_unwind
))]
fn write_group<T: Copy, const N: usize>(active: &mut [T], start: usize, group: &[T; N]) {
    let mut lane = 0;
    let target = active.split_at_mut(start).1.split_at_mut(N).0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant lane <= N, target.len() == N,
            forall |i: int| 0 <= i < lane ==> #[trigger] target[i] == group[i],
        decreases N - lane,
    ))]
    while lane < N {
        target[lane] = group[lane];
        lane += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(target@ =~= group@); }
    #[cfg(verus_keep_ghost)]
    proof! { assert(active@.subrange(start as int, start + N) =~= group@); }
}

/// All lanes have already read the original group, so preceding survivors may
/// overlap their source. The unmodified suffix is available for the next group.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        write <= read, read + N <= old(active).len(),
        forall |i: int| 0 <= i < N ==> group[i] == old(active)[read + i],
    ensures
        result.0 == write + survivors(group@, lanes@, N as nat).len(),
        write <= result.0 <= read + N, final(active).len() == old(active).len(),
        final(active)@.subrange(write as int, result.0 as int) == survivors(group@, lanes@, N as nat),
        forall |i: int| 0 <= i < final(active).len() && !(write <= i < result.0)
            ==> final(active)[i] == old(active)[i],
        result.1 == total(*update, lanes@, N as nat, initial),
    no_unwind
))]
fn compact_group<T: Copy, S: Copy, D: Copy, U: Account<D, S>, const N: usize>(
    active: &mut [T], write: usize, read: usize, group: [T; N], lanes: [(bool, D); N], initial: S, update: &U,
) -> (usize, S) {
    let mut next = write;
    let mut state = initial;
    let mut lane = 0;
    if !any_frozen(&lanes) {
        if write != read {
            write_group(active, write, &group);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            all_kept(group@, lanes@, N as nat, *update, initial);
            assert(active@.subrange(write as int, (write + N) as int) =~= group@);
        }
        return (write + N, initial);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            write <= read, read + N <= active.len(), active.len() == old(active).len(), lane <= N,
            write <= next <= write + lane,
            next == write + survivors(group@, lanes@, lane as nat).len(),
            active@.subrange(write as int, next as int) == survivors(group@, lanes@, lane as nat),
            forall |i: int| 0 <= i < active.len() && !(write <= i < next) ==> active[i] == old(active)[i],
            forall |i: int| 0 <= i < N ==> group[i] == old(active)[read + i],
            state == total(*update, lanes@, lane as nat, initial),
        decreases N - lane,
    ))]
    while lane < N {
        if lanes[lane].0 {
            state = update.account(state, lanes[lane].1);
        } else {
            active[next] = group[lane];
            next += 1;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(active@.subrange(write as int, next as int)
                    =~= survivors(group@, lanes@, (lane + 1) as nat));
            }
        }
        lane += 1;
    }
    (next, state)
}

/// Classify four independent children together for vectorization. Each call to
/// update consumes a frozen child in document order, including the scalar tail.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures ({
        let items = old(active)@;
        let ds = decisions(items, classify);
        &&& final(active).len() == items.len()
        &&& result.0 <= items.len()
        &&& final(active)@.take(result.0 as int) == survivors(items, ds, items.len())
        &&& result.1 == total(update, ds, items.len(), initial)
    }),
    no_unwind
))]
fn compact<T: Copy, S: Copy, D: Copy, C: Project<T, (bool, D)>, U: Account<D, S>>(
    active: &mut [T], initial: S, classify: C, update: U,
) -> (usize, S) {
    let mut read = 0;
    let mut write = 0;
    let mut state = initial;
    let groups_end = active.len() / 4 * 4;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            read <= groups_end <= active.len(), read % 4 == 0, groups_end % 4 == 0,
            active.len() == old(active).len(), write <= read <= active.len(),
            active@.take(write as int) == survivors(old(active)@, decisions(old(active)@, classify), read as nat),
            state == total(update, decisions(old(active)@, classify), read as nat, initial),
            forall |i: int| read <= i < active.len() ==> active[i] == old(active)[i],
        decreases active.len() - read,
    ))]
    while read < groups_end {
        let group = read_group(active, read);
        let lanes = [classify.project(group[0]), classify.project(group[1]),
            classify.project(group[2]), classify.project(group[3])];
        #[cfg(verus_keep_ghost)]
        proof! {
            append_block(old(active)@, decisions(old(active)@, classify), read as nat, group@, lanes@, 4, update, initial);
        }
        let next = compact_group(active, write, read, group, lanes, state, &update);
        write = next.0;
        state = next.1;
        read += 4;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(active@.take(write as int) =~= survivors(old(active)@, decisions(old(active)@, classify), read as nat));
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            active.len() == old(active).len(), write <= read <= active.len(),
            active@.take(write as int) == survivors(old(active)@, decisions(old(active)@, classify), read as nat),
            state == total(update, decisions(old(active)@, classify), read as nat, initial),
            forall |i: int| read <= i < active.len() ==> active[i] == old(active)[i],
        decreases active.len() - read,
    ))]
    while read < active.len() {
        let group = [active[read]];
        let lanes = [classify.project(group[0])];
        #[cfg(verus_keep_ghost)]
        proof! {
            append_block(old(active)@, decisions(old(active)@, classify), read as nat, group@, lanes@, 1, update, initial);
        }
        let next = compact_group(active, write, read, group, lanes, state, &update);
        write = next.0;
        state = next.1;
        read += 1;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(active@.take(write as int) =~= survivors(old(active)@, decisions(old(active)@, classify), read as nat));
        }
    }
    (write, state)
}

/// Resolve four lanes independently, then add each result in sibling order.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == ordered_fold(items@, items.len() as nat, initial, project, update),
    no_unwind
))]
fn fold<T: Copy, D: Copy, S: Copy, P: Project<T, D>, U: Account<D, S>>(
    items: &[T], initial: S, project: P, update: U,
) -> S {
    let mut read = 0;
    let mut state = initial;
    let groups_end = items.len() / 4 * 4;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant read <= groups_end <= items.len(), read % 4 == 0, groups_end % 4 == 0,
            state == ordered_fold(items@, read as nat, initial, project, update),
        decreases items.len() - read,
    ))]
    while read < groups_end {
        let group = read_group(items, read);
        let a = project.project(group[0]);
        let b = project.project(group[1]);
        let c = project.project(group[2]);
        let d = project.project(group[3]);
        state = update.account(update.account(update.account(update.account(state, a), b), c), d);
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(ordered_fold, 5); }
        read += 4;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant read <= items.len(),
            state == ordered_fold(items@, read as nat, initial, project, update),
        decreases items.len() - read,
    ))]
    while read < items.len() {
        state = update.account(state, project.project(items[read]));
        read += 1;
    }
    state
}

/// Continue the Fill loop only on a strictly shorter, in-bounds prefix.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures
        result.is_some() == (remaining < old(active).len()),
        result.is_some() ==> result.unwrap()@ == old(active)@.take(remaining as int),
    no_unwind
))]
pub(crate) fn retain_after_freeze<T>(active: &mut [T], remaining: usize) -> Option<&mut [T]> {
    if remaining < active.len() {
        Some(active.split_at_mut(remaining).0)
    } else {
        None
    }
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
struct ViolationPass<F> {
    share: f32,
    _float: PhantomData<F>,
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
struct FreezePass<F> {
    share: f32,
    positive: bool,
    _float: PhantomData<F>,
}

type Totals = (f32, f32);

#[cfg(verus_keep_ghost)]
verus! {
    impl<F: FloatModel> ProjectModel<FillChild, f32> for ViolationPass<F> {
        closed spec fn projected(self, child: FillChild) -> f32 { child.resolved::<F>(self.share).1 }
    }

    impl<F: FloatModel> AccountModel<f32, f32> for ViolationPass<F> {
        closed spec fn accounted(self, total: f32, violation: f32) -> f32 { F::sum(total, violation) }
    }

    impl<F: FloatModel> ProjectModel<FillChild, (bool, Totals)> for FreezePass<F> {
        closed spec fn projected(self, child: FillChild) -> (bool, Totals) {
            let (size, violation) = child.resolved::<F>(self.share);
            let frozen = if self.positive { F::less(EVEN_SHARE_EPSILON, violation) }
                         else { F::less(violation, F::difference(0.0, EVEN_SHARE_EPSILON)) };
            (frozen, (size, child.weight))
        }
    }

    impl<F: FloatModel> AccountModel<Totals, Totals> for FreezePass<F> {
        closed spec fn accounted(self, totals: Totals, data: Totals) -> Totals {
            (F::sum(totals.0, data.0), F::difference(totals.1, data.1))
        }
    }
}

#[cfg(not(verus_keep_ghost))]
impl<F: FloatModel> ProjectModel<FillChild, f32> for ViolationPass<F> {}
#[cfg(not(verus_keep_ghost))]
impl<F: FloatModel> AccountModel<f32, f32> for ViolationPass<F> {}
#[cfg(not(verus_keep_ghost))]
impl<F: FloatModel> ProjectModel<FillChild, (bool, Totals)> for FreezePass<F> {}
#[cfg(not(verus_keep_ghost))]
impl<F: FloatModel> AccountModel<Totals, Totals> for FreezePass<F> {}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<F: FloatOps> Project<FillChild, f32> for ViolationPass<F> {
    #[inline(always)]
    fn project(&self, child: FillChild) -> f32 { child.resolve::<F>(self.share).1 }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<F: FloatOps> Account<f32, f32> for ViolationPass<F> {
    #[inline(always)]
    fn account(&self, total: f32, violation: f32) -> f32 { F::add(total, violation) }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<F: FloatOps> Project<FillChild, (bool, Totals)> for FreezePass<F> {
    #[inline(always)]
    fn project(&self, child: FillChild) -> (bool, Totals) {
        let (size, violation) = child.resolve::<F>(self.share);
        let frozen = if self.positive { F::below(EVEN_SHARE_EPSILON, violation) }
                     else { F::below(violation, F::subtract(0.0, EVEN_SHARE_EPSILON)) };
        (frozen, (size, child.weight))
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<F: FloatOps> Account<Totals, Totals> for FreezePass<F> {
    #[inline(always)]
    fn account(&self, (total, weight): Totals, (size, frozen_weight): Totals) -> Totals {
        (F::add(total, size), F::subtract(weight, frozen_weight))
    }
}

#[cfg(all(test, not(verus_keep_ghost)))]
pub(crate) fn resolve_fill_share(fills: &mut [FillChild], budget: f32, weight: f32, worst: Option<f32>) -> f32 {
    resolve_fill_share_with::<RustFloat>(fills, budget, weight, worst)
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) closed spec fn single_share<F: FloatOps>(
    child: FillChild, budget: f32, weight: f32, worst: Option<f32>,
) -> Option<f32> {
    let share = F::available_share(budget, 0.0, weight);
    match worst {
        None => Some(share),
        Some(unconstrained) => if !F::is_finite(F::product(share, unconstrained)) {
            None
        } else {
            let pair = child.resolved::<F>(share);
            if F::less(EVEN_SHARE_EPSILON, F::magnitude(pair.1)) {
                Some(F::available_share(budget, F::sum(0.0, pair.0), F::difference(weight, child.weight)))
            } else { Some(share) }
        },
    }
}

/// The scalar passes consume the original ordered constraints. Every
/// recursive step freezes at least one and never changes survivor order.
pub(crate) closed spec fn ordered_share<F: FloatOps>(
    active: Seq<FillChild>, budget: f32, totals: Totals, worst: Option<f32>, previous: f32,
) -> f32
    decreases active.len(),
{
    if active.len() == 0 && worst.is_none() {
        previous
    } else {
        let share = F::available_share(budget, totals.0, totals.1);
        if active.len() == 0 {
            share
        } else {
            let initial = match worst {
                Some(weight) => if !F::is_finite(F::product(share, weight)) { F::invalid() } else { 0.0 },
                None => 0.0,
            };
            let violation = ViolationPass::<F> { share, _float: PhantomData };
            let net = ordered_fold(active, active.len(), initial, violation, violation);
            if F::less(F::magnitude(net), EVEN_SHARE_EPSILON) {
                share
            } else {
                let freeze = FreezePass::<F> { share, positive: F::less(0.0, net), _float: PhantomData };
                let choices = decisions(active, freeze);
                let next = survivors(active, choices, active.len());
                if next.len() < active.len() {
                    ordered_share::<F>(next, budget, total(freeze, choices, active.len(), totals), worst, share)
                } else { share }
            }
        }
    }
}

pub(crate) open spec fn resolved_share<F: FloatOps>(
    active: Seq<FillChild>, budget: f32, weight: f32, worst: Option<f32>,
) -> f32 {
    let short = if active.len() == 1 { single_share::<F>(active[0], budget, weight, worst) } else { None };
    match short {
        Some(share) => share,
        None => ordered_share::<F>(active, budget, (0.0, weight), worst, 0.0),
    }
}

fn save_value<T: Copy>(value: T) -> (before: Ghost<T>)
    ensures before@ == value,
    no_unwind
{
    Ghost(value)
}

fn save_fill_prefix(active: &[FillChild]) -> (before: Ghost<Seq<FillChild>>)
    ensures before@ == active@,
    no_unwind
{
    Ghost(active@)
}

}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == single_share::<F>(child, budget, unfrozen_weight, max_unconstrained_weight),
    no_unwind
))]
pub(crate) fn single_constraint_share<F: FloatOps>(child: FillChild, budget: f32, unfrozen_weight: f32,
    max_unconstrained_weight: Option<f32>,
) -> Option<f32> {
    let share = F::share(budget, 0.0, unfrozen_weight);
    let Some(unconstrained) = max_unconstrained_weight else { return Some(share); };
    if !F::finite(F::multiply(share, unconstrained)) { return None; }
    // The single violation determines which direction freezes. Once
    // it freezes, only unconstrained children receive the next share.
    let (size, violation) = child.resolve::<F>(share);
    if F::below(EVEN_SHARE_EPSILON, F::abs(violation)) {
        let frozen_total = F::add(0.0, size);
        let remaining_weight = F::subtract(unfrozen_weight, child.weight);
        return Some(F::share(budget, frozen_total, remaining_weight));
    }
    Some(share)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == resolved_share::<F>(old(fills)@, budget, weight, max_unconstrained_weight),
    no_unwind
))]
pub(crate) fn resolve_fill_share_with<F: FloatOps>(
    fills: &mut [FillChild], budget: f32, weight: f32, max_unconstrained_weight: Option<f32>,
) -> f32 {
    let mut unfrozen_weight = weight;
    if fills.len() == 1 {
        if let Some(share) = single_constraint_share::<F>(fills[0], budget, unfrozen_weight, max_unconstrained_weight) {
            return share;
        }
    }
    let mut active = fills;
    let mut frozen_total = 0.0;
    let mut share = 0.0;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant resolved_share::<F>(old(fills)@, budget, weight, max_unconstrained_weight)
            == ordered_share::<F>(active@, budget, (frozen_total, unfrozen_weight), max_unconstrained_weight, share),
        decreases active.len(),
    ))]
    while !active.is_empty() || max_unconstrained_weight.is_some() {
        #[cfg(verus_keep_ghost)]
        let previous = save_value(share);
        share = F::share(budget, frozen_total, unfrozen_weight);
        if active.is_empty() {
            return share;
        }
        // Unconstrained children never freeze. Their target minus itself is zero
        // for finite targets and NaN otherwise.
        let initial_violation = if let Some(weight) = max_unconstrained_weight {
            if F::finite(F::multiply(share, weight)) { 0.0 } else { F::nan() }
        } else { 0.0 };
        let violation = ViolationPass::<F> { share, _float: PhantomData };
        let total_violation = fold(active, initial_violation, violation, violation);
        if F::below(F::abs(total_violation), EVEN_SHARE_EPSILON) {
            return share;
        }

        // Retain constraints in sibling order so later shares use identical rounding.
        let freeze = FreezePass::<F> { share, positive: F::below(0.0, total_violation), _float: PhantomData };
        #[cfg(verus_keep_ghost)]
        let before = save_fill_prefix(active);
        #[cfg(verus_keep_ghost)]
        let prior = save_value((frozen_total, unfrozen_weight));
        let (remaining, totals) = compact(active, (frozen_total, unfrozen_weight), freeze, freeze);
        frozen_total = totals.0;
        unfrozen_weight = totals.1;
        let Some(prefix) = retain_after_freeze(active, remaining) else {
            return share;
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(ordered_share::<F>(before@, budget, prior@, max_unconstrained_weight, previous@)
                == ordered_share::<F>(prefix@, budget, totals, max_unconstrained_weight, share));
        }
        active = prefix;
    }
    share
}
