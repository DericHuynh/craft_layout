// In-place Fill compaction. Verus checks this same code against a scalar pass.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == (exists |i: int| 0 <= i < N && (#[trigger] lanes[i]).0),
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

/// All lanes have already read the original group, so preceding survivors may
/// overlap their source. The unmodified suffix is available for the next group.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires
        write <= read, read + N <= old(active).len(), accumulator(*update),
        forall |i: int| 0 <= i < N ==> group[i] == old(active)[read + i],
    ensures
        result.0 == write + survivors(group@, lanes@, N as nat).len(),
        write <= result.0 <= read + N, final(active).len() == old(active).len(),
        final(active)@.subrange(write as int, result.0 as int) == survivors(group@, lanes@, N as nat),
        forall |i: int| 0 <= i < final(active).len() && !(write <= i < result.0)
            ==> final(active)[i] == old(active)[i],
        result.1 == total(*update, lanes@, N as nat, initial),
))]
fn compact_group<T: Copy, S: Copy, D: Copy, U: Fn(S, D) -> S, const N: usize>(
    active: &mut [T], write: usize, read: usize, group: [T; N], lanes: [(bool, D); N], initial: S, update: &U,
) -> (usize, S) {
    let mut next = write;
    let mut state = initial;
    let mut lane = 0;
    if !any_frozen(&lanes) {
        if write != read {
            active[write..write + N].copy_from_slice(&group);
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
            accumulator(*update),
            state == total(*update, lanes@, lane as nat, initial),
        decreases N - lane,
    ))]
    while lane < N {
        if lanes[lane].0 {
            state = update(state, lanes[lane].1);
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
    requires classifier(classify), accumulator(update),
    ensures ({
        let items = old(active)@;
        let ds = decisions(items, classify);
        &&& final(active).len() == items.len()
        &&& result.0 <= items.len()
        &&& final(active)@.take(result.0 as int) == survivors(items, ds, items.len())
        &&& result.1 == total(update, ds, items.len(), initial)
    }),
))]
pub fn compact<T: Copy, S: Copy, D: Copy, C: Fn(T) -> (bool, D), U: Fn(S, D) -> S>(
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
            classifier(classify), accumulator(update),
            active@.take(write as int) == survivors(old(active)@, decisions(old(active)@, classify), read as nat),
            state == total(update, decisions(old(active)@, classify), read as nat, initial),
            forall |i: int| read <= i < active.len() ==> active[i] == old(active)[i],
        decreases active.len() - read,
    ))]
    while read < groups_end {
        let block = &active[read..read + 4];
        let group = [block[0], block[1], block[2], block[3]];
        let lanes = [classify(group[0]), classify(group[1]), classify(group[2]), classify(group[3])];
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
            classifier(classify), accumulator(update),
            active@.take(write as int) == survivors(old(active)@, decisions(old(active)@, classify), read as nat),
            state == total(update, decisions(old(active)@, classify), read as nat, initial),
            forall |i: int| read <= i < active.len() ==> active[i] == old(active)[i],
        decreases active.len() - read,
    ))]
    while read < active.len() {
        let group = [active[read]];
        let lanes = [classify(group[0])];
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
    requires projection(project), accumulator(update),
    ensures result == ordered_fold(items@, items.len() as nat, initial, project, update),
))]
pub fn fold<T: Copy, D, S, P: Fn(T) -> D, U: Fn(S, D) -> S>(
    items: &[T], initial: S, project: P, update: U,
) -> S {
    let mut read = 0;
    let mut state = initial;
    let groups_end = items.len() / 4 * 4;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant read <= groups_end <= items.len(), read % 4 == 0, groups_end % 4 == 0, projection(project), accumulator(update),
            state == ordered_fold(items@, read as nat, initial, project, update),
        decreases items.len() - read,
    ))]
    while read < groups_end {
        let block = &items[read..read + 4];
        let a = project(block[0]);
        let b = project(block[1]);
        let c = project(block[2]);
        let d = project(block[3]);
        state = update(update(update(update(state, a), b), c), d);
        #[cfg(verus_keep_ghost)]
        proof! { reveal_with_fuel(ordered_fold, 5); }
        read += 4;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant read <= items.len(), projection(project), accumulator(update),
            state == ordered_fold(items@, read as nat, initial, project, update),
        decreases items.len() - read,
    ))]
    while read < items.len() {
        state = update(state, project(items[read]));
        read += 1;
    }
    state
}

/// A pass that failed to freeze any constraints ends the outer Fill loop.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires remaining <= before,
    ensures result == (remaining < before),
))]
pub fn continue_freezing(before: usize, remaining: usize) -> bool {
    remaining != before
}
