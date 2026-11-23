//! A SIMD-sized block of decisions has the same ordered effects as scalar Fill.
use vstd::prelude::*;
#[path = "../src/fill_compaction.rs"]
pub mod kernel;

verus! {

pub open spec fn decision<T, D, C: Fn(T) -> (bool, D)>(classify: C, item: T) -> (bool, D) {
    choose |r: (bool, D)| call_ensures(classify, (item,), r)
}

pub open spec fn account<S, D, U: Fn(S, D) -> S>(update: U, state: S, data: D) -> S {
    choose |r: S| call_ensures(update, (state, data), r)
}

pub open spec fn classifier<T, D, C: Fn(T) -> (bool, D)>(classify: C) -> bool {
    &&& forall |x: T| #[trigger] call_requires(classify, (x,))
    &&& forall |x: T, r: (bool, D)| #[trigger] call_ensures(classify, (x,), r) ==> r == decision(classify, x)
}

pub open spec fn accumulator<S, D, U: Fn(S, D) -> S>(update: U) -> bool {
    &&& forall |s: S, d: D| #[trigger] call_requires(update, (s, d))
    &&& forall |s: S, d: D, r: S| #[trigger] call_ensures(update, (s, d), r) ==> r == account(update, s, d)
}

// Scalar reference for a sequence of already-resolved lanes. No algebraic
// properties of the accounting operation are required.
pub open spec fn survivors<T, D>(items: Seq<T>, decisions: Seq<(bool, D)>, n: nat) -> Seq<T>
    decreases n,
{
    if n == 0 { Seq::empty() }
    else {
        let prior = survivors(items, decisions, (n - 1) as nat);
        if decisions[n - 1].0 { prior } else { prior.push(items[n - 1]) }
    }
}

pub open spec fn total<S, D, U: Fn(S, D) -> S>(update: U, decisions: Seq<(bool, D)>, n: nat, initial: S) -> S
    decreases n,
{
    if n == 0 { initial }
    else {
        let prior = total(update, decisions, (n - 1) as nat, initial);
        if decisions[n - 1].0 { account(update, prior, decisions[n - 1].1) } else { prior }
    }
}

pub open spec fn decisions<T, D, C: Fn(T) -> (bool, D)>(items: Seq<T>, classify: C) -> Seq<(bool, D)> {
    Seq::new(items.len(), |i: int| decision(classify, items[i]))
}

pub proof fn all_kept<T, S, D, U: Fn(S, D) -> S>(items: Seq<T>, ds: Seq<(bool, D)>, n: nat, update: U, initial: S)
    requires n <= items.len(), n <= ds.len(), forall |i: int| 0 <= i < n ==> !(#[trigger] ds[i]).0,
    ensures survivors(items,ds,n) == items.take(n as int), total(update,ds,n,initial) == initial,
    decreases n,
{
    if n > 0 {
        all_kept(items,ds,(n-1) as nat,update,initial);
        assert(survivors(items,ds,n) =~= items.take(n as int));
    }
}

pub proof fn append_block<T, S, D, U: Fn(S, D) -> S>(
    items: Seq<T>, ds: Seq<(bool, D)>, start: nat, block: Seq<T>, local: Seq<(bool, D)>, n: nat,
    update: U, initial: S,
)
    requires
        start + n <= items.len(), ds.len() == items.len(), n <= block.len(), n <= local.len(),
        forall |j: int| 0 <= j < n ==> #[trigger] block[j] == items[start + j],
        forall |j: int| 0 <= j < n ==> #[trigger] local[j] == ds[start + j],
    ensures
        survivors(items, ds, start + n) == survivors(items, ds, start) + survivors(block, local, n),
        total(update, ds, start + n, initial) == total(update, local, n, total(update, ds, start, initial)),
    decreases n,
{
    if n > 0 {
        append_block(items, ds, start, block, local, (n - 1) as nat, update, initial);
        assert(local[n - 1] == ds[start + n - 1]);
        assert(block[n - 1] == items[start + n - 1]);
        assert(survivors(items, ds, start + n) =~= survivors(items, ds, start) + survivors(block, local, n));
    } else {
        assert(survivors(items, ds, start) =~= survivors(items, ds, start) + Seq::empty());
    }
}

pub open spec fn projected<T, D, P: Fn(T) -> D>(project: P, item: T) -> D {
    choose |r: D| call_ensures(project, (item,), r)
}

pub open spec fn projection<T, D, P: Fn(T) -> D>(project: P) -> bool {
    &&& forall |x: T| #[trigger] call_requires(project, (x,))
    &&& forall |x: T, r: D| #[trigger] call_ensures(project, (x,), r) ==> r == projected(project, x)
}

// A left fold makes the order of every floating-point addition observable.
pub open spec fn ordered_fold<T, D, S, P: Fn(T) -> D, U: Fn(S, D) -> S>(
    items: Seq<T>, n: nat, initial: S, project: P, update: U,
) -> S
    decreases n,
{
    if n == 0 { initial } else {
        account(update, ordered_fold(items, (n - 1) as nat, initial, project, update),
            projected(project, items[n - 1]))
    }
}

pub proof fn continuing_passes_are_bounded(counts: Seq<nat>)
    requires counts.len() > 0,
        forall |i: int| 0 < i < counts.len() ==> #[trigger] counts[i] < counts[i - 1],
    ensures counts.len() - 1 + counts.last() <= counts[0],
    decreases counts.len(),
{
    if counts.len() > 1 {
        continuing_passes_are_bounded(counts.drop_last());
        assert(counts.last() < counts[counts.len() - 2]);
    }
}
}
