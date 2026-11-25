//! Accounting for regional structural measurement on a finite visible forest.
use vstd::prelude::*;
#[path = "../src/region_list.rs"]
mod kernel;
#[path = "../src/incremental/regional.rs"]
pub(crate) mod regional;
#[path = "../src/incremental/plan.rs"]
mod plan;
pub(crate) use plan::SubtreeCounts;
#[path = "../src/incremental/register.rs"]
mod register;

verus! {

/// Each node occupies one preorder position followed by the entire child forest.
/// A direct rebuild stops planning here. Raising the region after examining children
/// must produce the same list as choosing the parent immediately.
pub enum Forest {
    Empty,
    Node { direct: bool, raise: bool, children: Box<Forest>, siblings: Box<Forest> },
}

pub open spec fn length(f: Forest) -> nat
    decreases f,
{
    match f {
        Forest::Empty => 0,
        Forest::Node { children, siblings, .. } => 1 + length(*children) + length(*siblings),
    }
}

pub type Interval = (nat, nat); // half-open preorder range
pub struct Plan {
    pub regions: Seq<Interval>,
    pub retained: Set<nat>,
}

pub open spec fn planned(f: Forest, start: nat) -> Plan
    decreases f,
{
    match f {
        Forest::Empty => Plan { regions: Seq::empty(), retained: Set::empty() },
        Forest::Node { direct, raise, children, siblings } => {
            let end = start + 1 + length(*children);
            let kids = planned(*children, start + 1);
            let tail = planned(*siblings, end);
            if direct || raise {
                Plan { regions: seq![(start, end)] + tail.regions, retained: tail.retained }
            } else {
                Plan { regions: kids.regions + tail.regions,
                    retained: kids.retained.insert(start).union(tail.retained) }
            }
        },
    }
}

// This uses the append / truncate / push order of plan_subtree. Unrelated
// previously selected siblings occupy an arbitrary prefix of the same buffer.
pub open spec fn collect(f: Forest, start: nat, prior: Seq<Interval>) -> Seq<Interval>
    decreases f,
{
    match f {
        Forest::Empty => prior,
        Forest::Node { direct, raise, children, siblings } => {
            let end = start + 1 + length(*children);
            let prefix = if direct {
                prior.push((start, end))
            } else {
                let children = collect(*children, start + 1, prior);
                if raise { children.take(prior.len() as int).push((start, end)) } else { children }
            };
            collect(*siblings, end, prefix)
        },
    }
}

pub proof fn rollback_preserves_other_regions(f: Forest, start: nat, prior: Seq<Interval>)
    ensures collect(f, start, prior) == prior + planned(f, start).regions,
    decreases f,
{
    match f {
        Forest::Empty => { assert(prior =~= prior + Seq::empty()); }
        Forest::Node { direct, raise, children, siblings } => {
            let end = start + 1 + length(*children);
            let kids = collect(*children, start + 1, prior);
            rollback_preserves_other_regions(*children, start + 1, prior);
            assert(kids.take(prior.len() as int) =~= prior);
            let prefix = if direct || raise { prior.push((start, end)) } else { kids };
            rollback_preserves_other_regions(*siblings, end, prefix);
            assert(collect(f, start, prior) =~= prior + planned(f, start).regions);
        }
    }
}

pub open spec fn required(f: Forest, start: nat, pos: nat) -> bool
    decreases f,
{
    match f {
        Forest::Empty => false,
        Forest::Node { direct, raise, children, siblings } => {
            let end = start + 1 + length(*children);
            (pos == start && (direct || raise)) || required(*children, start + 1, pos)
                || required(*siblings, end, pos)
        },
    }
}

pub open spec fn within(r: Interval, pos: nat) -> bool { r.0 <= pos < r.1 }

pub open spec fn measured(plan: Plan, pos: nat) -> bool {
    exists |i: int| 0 <= i < plan.regions.len() && within(#[trigger] plan.regions[i], pos)
}

pub open spec fn ordered(regions: Seq<Interval>, low: nat, high: nat) -> bool {
    &&& forall |i: int| 0 <= i < regions.len() ==> {
        let r = #[trigger] regions[i]; low <= r.0 < r.1 <= high
    }
    &&& forall |i: int, j: int| 0 <= i < j < regions.len() ==>
        (#[trigger] regions[i]).1 <= (#[trigger] regions[j]).0
}

proof fn neighboring_lists(left: Seq<Interval>, right: Seq<Interval>, low: nat, mid: nat, high: nat)
    requires ordered(left, low, mid), ordered(right, mid, high), low <= mid <= high,
    ensures ordered(left + right, low, high),
{
    let both = left + right;
    assert forall |i: int, j: int| 0 <= i < j < both.len() implies
        (#[trigger] both[i]).1 <= (#[trigger] both[j]).0 by {
        if i < left.len() { assert(both[i] == left[i]); }
        else { assert(both[i] == right[i - left.len()]); }
        if j < left.len() { assert(both[j] == left[j]); }
        else { assert(both[j] == right[j - left.len()]); }
    }
}

proof fn membership_appends(a: Plan, b: Plan, combined: Plan, p: nat)
    requires combined.regions == a.regions + b.regions,
    ensures measured(combined, p) == (measured(a, p) || measured(b, p)),
{
    if measured(combined, p) {
        let i = choose |i: int| 0 <= i < combined.regions.len() && within(#[trigger] combined.regions[i], p);
        if i < a.regions.len() { assert(a.regions[i] == combined.regions[i]); }
        else { assert(b.regions[i - a.regions.len()] == combined.regions[i]); }
    }
    if measured(a, p) {
        let i = choose |i: int| 0 <= i < a.regions.len() && within(#[trigger] a.regions[i], p);
        assert(a.regions[i] == combined.regions[i]);
    }
    if measured(b, p) {
        let i = choose |i: int| 0 <= i < b.regions.len() && within(#[trigger] b.regions[i], p);
        assert(b.regions[i] == combined.regions[a.regions.len() + i]);
    }
}

/// The plan measures each required node, visits no measurement region twice,
/// and counts each live preorder position exactly once (regional or retained).
pub proof fn complete_partition(f: Forest, start: nat, p: nat)
    ensures ({
        let plan = planned(f, start);
        &&& ordered(plan.regions, start, start + length(f))
        &&& (measured(plan, p) || plan.retained.contains(p)) == (start <= p < start + length(f))
        &&& !(measured(plan, p) && plan.retained.contains(p))
        &&& required(f, start, p) ==> measured(plan, p)
    }),
    decreases f,
{
    match f {
        Forest::Empty => {}
        Forest::Node { direct, raise, children, siblings } => {
            let end = start + 1 + length(*children);
            let kids = planned(*children, start + 1);
            let tail = planned(*siblings, end);
            let plan = planned(f, start);
            complete_partition(*children, start + 1, p);
            complete_partition(*siblings, end, p);
            if direct || raise {
                let head = Plan { regions: seq![(start, end)], retained: Set::empty() };
                assert(head.regions[0] == (start, end));
                membership_appends(head, tail, plan, p);
                neighboring_lists(head.regions, tail.regions, start, end, start + length(f));
            } else {
                membership_appends(kids, tail, plan, p);
                neighboring_lists(kids.regions, tail.regions, start, end, start + length(f));
            }
        }
    }
}

}
