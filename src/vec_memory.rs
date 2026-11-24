//! Copy storage primitives at the Rust standard library boundary.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// The allocation premise covers the addressable capacity requested by `Vec`
/// and successful allocation. Copying a record runs no caller destructor.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait VecMemory {
    #[cfg_attr(verus_keep_ghost, verus_spec(items => ensures items@ == Seq::<T>::empty(), no_unwind))]
    fn empty<T: Copy>() -> Vec<T>;

    #[cfg_attr(verus_keep_ghost, verus_spec(previous =>
        ensures previous@ == old(items)@, final(items)@ == Seq::<T>::empty(),
        no_unwind
    ))]
    fn take<T: Copy>(items: &mut Vec<T>) -> Vec<T>;

    #[cfg_attr(verus_keep_ghost, verus_spec(slots =>
        ensures forall |i: int| 0 <= i < N ==> (#[trigger] slots@[i]).is_none(),
        no_unwind
    ))]
    fn empty_slots<T: Copy, const N: usize>() -> [Option<T>; N];

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(items)@ == old(items)@.push(item),
        no_unwind
    ))]
    fn append<T: Copy>(items: &mut Vec<T>, item: T);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(items)@ == Seq::<T>::empty(),
        no_unwind
    ))]
    fn clear<T: Copy>(items: &mut Vec<T>);

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(items)@ == old(items)@.take(vstd::math::min(len as int, old(items).len() as int)),
        no_unwind
    ))]
    fn truncate<T: Copy>(items: &mut Vec<T>, len: usize);
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait CapacityModel {
    spec fn capacity<T>(items: &Vec<T>) -> nat;
}

pub(crate) open spec fn capacity_limit<T>() -> int {
    if core::mem::size_of::<T>() == 0 { usize::MAX as int }
    else { isize::MAX as int / core::mem::size_of::<T>() as int }
}

/// A push into reserved storage writes one aligned element within the
/// allocation and advances the length, including for a zero-sized item.
pub proof fn reserved_write_bounds(length: usize, capacity: usize, size: usize)
    requires length < capacity, capacity * size <= isize::MAX,
    ensures
        length + 1 <= capacity,
        length * size + size <= capacity * size,
        length * size <= isize::MAX,
{
    let len = length as int;
    let cap = capacity as int;
    let width = size as int;
    assert(len * width + width == (len + 1) * width) by (nonlinear_arith);
    assert((len + 1) * width <= cap * width) by (nonlinear_arith)
        requires len < cap, width >= 0;
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait CapacityModel {}

/// The reserve call is the only allocating operation in bounded append.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait CapacityMemory: CapacityModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(capacity =>
        ensures capacity == Self::capacity(items), items.len() <= capacity,
        no_unwind
    ))]
    fn current_capacity<T>(items: &Vec<T>) -> usize;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(items).len() + additional <= capacity_limit::<T>(),
        ensures final(items)@ == old(items)@,
            Self::capacity(final(items)) >= old(items).len() + additional,
        no_unwind
    ))]
    fn reserve_exact<T: Copy>(items: &mut Vec<T>, additional: usize);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(items).len() < Self::capacity(old(items)),
        ensures final(items)@ == old(items)@.push(item),
            Self::capacity(final(items)) == Self::capacity(old(items)),
        no_unwind
    ))]
    fn push_reserved<T: Copy>(items: &mut Vec<T>, item: T);
}

/// Optional storage leaves the current contents intact if allocation fails.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FallibleVecMemory: CapacityMemory {
    #[cfg_attr(verus_keep_ghost, verus_spec(reserved =>
        ensures final(items)@ == old(items)@,
            reserved ==> Self::capacity(final(items)) >= old(items).len() + additional,
        no_unwind
    ))]
    fn try_reserve<T: Copy>(items: &mut Vec<T>, additional: usize) -> bool;
}

#[inline(always)]
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(added =>
    ensures final(items)@ == if added { old(items)@.push(item) } else { old(items)@ },
    no_unwind
))]
pub(crate) fn try_append<T: Copy, M: FallibleVecMemory>(items: &mut Vec<T>, item: T) -> bool {
    if !M::try_reserve(items, 1) { return false; }
    M::push_reserved(items, item);
    true
}

#[cfg(not(verus_keep_ghost))]
pub(crate) struct RustVec;

#[cfg(not(verus_keep_ghost))]
impl VecMemory for RustVec {
    #[inline(always)]
    fn empty<T: Copy>() -> Vec<T> { Vec::new() }

    #[inline(always)]
    fn take<T: Copy>(items: &mut Vec<T>) -> Vec<T> { core::mem::take(items) }

    #[inline(always)]
    fn empty_slots<T: Copy, const N: usize>() -> [Option<T>; N] { [None; N] }

    #[inline(always)]
    fn append<T: Copy>(items: &mut Vec<T>, item: T) {
        if items.len() < max_copy_capacity::<T>() {
            append_bounded::<T, Self>(items, item);
        } else {
            // The capacity of an additional element is outside the allocation premise.
            items.push(item);
        }
    }

    #[inline(always)]
    fn clear<T: Copy>(items: &mut Vec<T>) { items.clear(); }

    #[cfg(feature = "incremental")]
    #[inline(always)]
    fn truncate<T: Copy>(items: &mut Vec<T>, len: usize) { items.truncate(len); }
}

#[cfg(not(verus_keep_ghost))]
impl CapacityModel for RustVec {}

#[cfg(not(verus_keep_ghost))]
impl CapacityMemory for RustVec {
    #[inline(always)]
    fn current_capacity<T>(items: &Vec<T>) -> usize { items.capacity() }

    #[inline(always)]
    fn reserve_exact<T: Copy>(items: &mut Vec<T>, additional: usize) { items.reserve_exact(additional); }

    #[inline(always)]
    fn push_reserved<T: Copy>(items: &mut Vec<T>, item: T) { items.push(item); }
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
impl FallibleVecMemory for RustVec {
    #[inline(always)]
    fn try_reserve<T: Copy>(items: &mut Vec<T>, additional: usize) -> bool {
        items.try_reserve(additional).is_ok()
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(limit => ensures limit == capacity_limit::<T>(), no_unwind))]
pub(crate) fn max_copy_capacity<T>() -> usize {
    let size = core::mem::size_of::<T>();
    if size == 0 { usize::MAX } else { isize::MAX as usize / size }
}

/// Grow geometrically while clamping the request to the byte-addressable capacity.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(items).len() < capacity_limit::<T>(),
    ensures final(items)@ == old(items)@.push(item),
    no_unwind
))]
pub(crate) fn append_bounded<T: Copy, M: CapacityMemory>(items: &mut Vec<T>, item: T) {
    let len = items.len();
    if len == M::current_capacity(items) {
        let element_size = core::mem::size_of::<T>();
        let limit = max_copy_capacity::<T>();
        let grown = if len <= limit / 2 { len * 2 } else { limit };
        let initial = if element_size == 1 { 8 } else if element_size <= 1024 { 4 } else { 1 };
        let base = if limit < initial { limit } else { initial };
        let needed = if grown < base { base } else { grown };
        let needed = if needed <= len { len + 1 } else { needed };
        M::reserve_exact(items, needed - len);
    }
    M::push_reserved(items, item);
}
