//! Bounded native descent and the ordered spill to the sizing worklist.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Up to this many dependency edges can use the native stack before all
// remaining requests for that slot are evaluated on the explicit worklist.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const NATIVE_DEPTH: u8 = 24;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    ensures if budget == 0 { next.is_none() }
        else { next.is_some() && next.unwrap() + 1 == budget },
    no_unwind
))]
pub fn descend(budget: u8) -> Option<u8> {
    if budget == 0 { None } else { Some(budget - 1) }
}

/// Reverse only the requests appended for the current slot, so that popping
/// visits those requests in the order the scheduler emitted them.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires start <= old(entries).len(),
    ensures final(entries).len() == old(entries).len(),
        forall |i:int| 0 <= i < start ==> #[trigger] final(entries)[i] == old(entries)[i],
        forall |i:int| start <= i < old(entries).len() ==>
            #[trigger] final(entries)[i] == old(entries)[start + old(entries).len() - i - 1],
    no_unwind
))]
// Keep the writes visible to Verus so it can check both swapped ranges.
#[allow(clippy::manual_swap)]
pub fn reverse_requests<T: Copy>(entries: &mut [T], start: usize) {
    let end = entries.len();
    let mut left = start;
    let mut right = end;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant start <= left <= right <= end, end == entries.len(), end == old(entries).len(),
            left - start == end - right,
            forall |i:int| 0 <= i < start || left <= i < right ==> #[trigger] entries[i] == old(entries)[i],
            forall |i:int| start <= i < left || right <= i < end ==>
                #[trigger] entries[i] == old(entries)[start + end - i - 1],
        decreases right-left,
    ))]
    while right - left > 1 {
        right -= 1;
        let item = entries[left];
        entries[left] = entries[right];
        entries[right] = item;
        left += 1;
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    /// Every native child receives the smaller budget returned by descend.
    pub proof fn native_depth_bound(budgets: Seq<u8>, budget: u8)
        requires
            budgets.len() > 0, budgets[0] == budget,
            forall |i:int| 0 < i < budgets.len() ==>
                (#[trigger] budgets[i]) + 1 == budgets[i-1],
        ensures budgets.len() + budgets.last() == budget + 1,
            budgets.len() <= budget + 1,
        decreases budgets.len(),
    {
        if budgets.len() > 1 {
            let prefix = budgets.drop_last();
            assert forall |i:int| 0 < i < prefix.len() implies
                (#[trigger] prefix[i]) + 1 == prefix[i-1] by {
                assert(prefix[i] == budgets[i]);
            }
            native_depth_bound(prefix, budget);
            let last = budgets.len() - 1;
            assert(prefix.last() == budgets[last-1]);
            assert(budgets.last() == budgets[last]);
        } else {
            assert(budgets.last() == budgets[0]);
        }
    }
}
