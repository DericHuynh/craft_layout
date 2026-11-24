//! Greedy wrapping and replay over a finite linked sequence of children.
use vstd::prelude::*;

#[path = "../src/wrap_lines.rs"]
pub(crate) mod kernel;
use kernel::{LineSource, WrapLine};

verus! {

pub struct Item<I, M> {
    pub id: I,
    pub in_flow: bool,
    pub marked: bool,
    pub fill: bool,
    pub base: M,
    pub main: M,
    pub cross: M,
}

pub open spec fn at<I,M>(items: Seq<Item<I,M>>, i: int) -> Option<I> {
    if 0 <= i < items.len() { Some(items[i].id) } else { None }
}

pub open spec fn valid_chain<I,M>(items: Seq<Item<I,M>>) -> bool {
    forall |i:int, j:int| 0 <= i < items.len() && 0 <= j < items.len() &&
        #[trigger] items[i].id == #[trigger] items[j].id ==> i == j
}

pub open spec fn present<I,M>(items: Seq<Item<I,M>>, id: I) -> bool {
    exists |i:int| 0 <= i < items.len() && #[trigger] at(items,i) == Some(id)
}

pub open spec fn index<I,M>(items: Seq<Item<I,M>>, id: I) -> int {
    choose |i:int| 0 <= i < items.len() && #[trigger] at(items,i) == Some(id)
}

pub open spec fn indexed<I,M>(items: Seq<Item<I,M>>, id: I) -> Item<I,M> {
    items[index(items,id)]
}

pub proof fn locate<I,M>(items: Seq<Item<I,M>>, i: nat, id: I)
    requires valid_chain(items), i <= items.len(), at(items, i as int) == Some(id)
    ensures i < items.len(), present(items, id), index(items, id) == i
{
    assert(exists |j:int| 0 <= j < items.len() && at(items,j) == Some(id));
    let j = index(items,id);
    assert(items[j].id == items[i as int].id);
}

pub struct Metrics<M> {
    pub count: nat,
    pub main: M,
    pub cross: M,
    pub has_fill: bool,
}

pub open spec fn summary<S: LineSource>(s: &S, limit: Option<S::Metric>, n: nat) -> Metrics<S::Metric>
    decreases n,
{
    if n == 0 { Metrics { count: 0, main: s.zero(), cross: s.zero(), has_fill: false } }
    else {
        let prior = summary(s,limit,(n-1) as nat);
        let item = s.items()[n-1];
        if !item.in_flow { prior }
        else {
            let fill = limit.is_some() && item.fill;
            let extent = if fill { item.base } else { item.main };
            Metrics {
                count: if prior.count < u32::MAX { prior.count + 1 } else { u32::MAX as nat },
                main: if prior.count == 0 { extent } else { s.summed(prior.main,extent) },
                cross: if limit.is_none() { s.cross_max(prior.cross,item.cross) } else { prior.cross },
                has_fill: prior.has_fill || fill,
            }
        }
    }
}

pub open spec fn stop_at<S: LineSource>(s: &S, limit: Option<S::Metric>, j: int) -> bool {
    let previous = summary(s,limit,j as nat);
    let item = s.items()[j];
    item.in_flow && previous.count > 0 && match limit {
        None => item.marked,
        Some(available) => {
            let extent = if item.fill { item.base } else { item.main };
            s.overflows(s.summed(previous.main,extent),available)
        }
    }
}

pub open spec fn endpoint<S: LineSource>(s: &S, limit: Option<S::Metric>, i: nat) -> bool {
    &&& i <= s.items().len()
    &&& i == s.items().len() || stop_at(s,limit,i as int)
    &&& forall |j:int| 0 <= j < i ==> !#[trigger] stop_at(s,limit,j)
}

pub open spec fn scanned<S: LineSource>(s: &S, limit: Option<S::Metric>, line: WrapLine<S::Id,S::Metric>) -> bool {
    exists |i:nat| endpoint(s,limit,i) && line.next == #[trigger] at(s.items(),i as int) && {
        let m = summary(s,limit,i);
        line.count == m.count && line.main == m.main && line.cross == m.cross && line.has_fill == m.has_fill
            && (s.items().len() > 0 ==> i > 0)
    }
}

pub proof fn finish_scan<S: LineSource>(s: &S, limit: Option<S::Metric>, i: nat, line: WrapLine<S::Id,S::Metric>)
    requires endpoint(s,limit,i), line.next == at(s.items(),i as int),
        line.count == summary(s,limit,i).count, line.main == summary(s,limit,i).main,
        line.cross == summary(s,limit,i).cross, line.has_fill == summary(s,limit,i).has_fill,
    ensures scanned(s,limit,line),
{
    assert(summary(s,limit,0).count == 0);
    assert(s.items().len() > 0 ==> i > 0);
    assert(at(s.items(),i as int) == line.next);
}

/// Updating the next boundary on a freshly prepared list establishes the
/// recorded-line invariant. A previous boundary at the head is harmless.
pub proof fn writing_boundary_records_line<S: LineSource>(replay: &S, end:nat, before: Seq<bool>)
    requires end <= before.len(), before.len() == replay.items().len(),
        forall |i:int| 0 < i < end ==> !#[trigger] before[i],
        forall |i:int| 0 <= i < before.len() ==>
            (#[trigger] replay.items()[i]).marked == (before[i] || i == end),
    ensures recorded(replay,end),
{
}

pub open spec fn same_children<F: LineSource, R: LineSource<Id=F::Id>>(fresh: &F, replay: &R) -> bool {
    &&& fresh.items().len() == replay.items().len()
    &&& forall |i:int| 0 <= i < fresh.items().len() ==>
        (#[trigger] fresh.items()[i]).id == (#[trigger] replay.items()[i]).id
        && fresh.items()[i].in_flow == replay.items()[i].in_flow
}

proof fn same_count<F: LineSource, R: LineSource<Id=F::Id>>(fresh: &F, replay: &R, available: F::Metric, n: nat)
    requires same_children(fresh,replay), n <= fresh.items().len(),
    ensures summary(fresh,Some(available),n).count == summary(replay,None,n).count,
    decreases n,
{
    if n > 0 {
        assert(fresh.items()[n-1].in_flow == replay.items()[n-1].in_flow);
        same_count(fresh,replay,available,(n-1) as nat);
    }
}

/// The parent passes its next endpoint to the mark writer. The leading
/// sibling may already be marked as the endpoint of the preceding line.
pub open spec fn recorded<S: LineSource>(s: &S, end: nat) -> bool {
    &&& end < s.items().len() ==> s.items()[end as int].marked
    &&& forall |i:int| 0 < i < end ==> !(#[trigger] s.items()[i]).marked
}

pub proof fn marked_replay_selects_fresh_endpoint<F: LineSource, R: LineSource<Id=F::Id>>(
    fresh: &F, replay: &R, available: F::Metric, end: nat,
)
    requires same_children(fresh,replay), endpoint(fresh,Some(available),end), recorded(replay,end),
    ensures endpoint(replay,None,end),
        at(fresh.items(),end as int) == at(replay.items(),end as int),
        summary(fresh,Some(available),end).count == summary(replay,None,end).count,
{
    same_count(fresh,replay,available,end);
    if end < fresh.items().len() {
        assert(fresh.items()[end as int].in_flow == replay.items()[end as int].in_flow);
        assert(fresh.items()[end as int].id == replay.items()[end as int].id);
    }
    assert forall |i:int| 0 <= i < end implies !#[trigger] stop_at(replay,None,i) by {
        if i == 0 { assert(summary(replay,None,0).count == 0); }
    }
}

proof fn unique_endpoint<S: LineSource>(s: &S, limit: Option<S::Metric>, i: nat, j: nat)
    requires endpoint(s,limit,i), endpoint(s,limit,j),
    ensures i == j,
{
    if i < j { assert(stop_at(s,limit,i as int)); }
    if j < i { assert(stop_at(s,limit,j as int)); }
}

/// The verified scanner need not repeat the sizing computation during replay.
/// Main geometry uses resolved sizes, cross geometry uses pre-grow sizes, and
/// both are folded over exactly the items whose bases were selected by fitting.
pub proof fn scan_replay_matches_sizing<F: LineSource, R: LineSource<Id=F::Id>>(
    fresh: &F, replay: &R, available: F::Metric, sized: WrapLine<F::Id,F::Metric>,
    placed: WrapLine<R::Id,R::Metric>, end: nat,
)
    requires same_children(fresh,replay), endpoint(fresh,Some(available),end), recorded(replay,end),
        scanned(fresh,Some(available),sized), scanned(replay,None,placed),
    ensures placed.next == sized.next, placed.count == sized.count,
        placed.main == summary(replay,None,end).main, placed.cross == summary(replay,None,end).cross,
{
    marked_replay_selects_fresh_endpoint(fresh,replay,available,end);
    let f = choose |i:nat| endpoint(fresh,Some(available),i) && sized.next == #[trigger] at(fresh.items(),i as int)
        && sized.count == summary(fresh,Some(available),i).count
        && sized.main == summary(fresh,Some(available),i).main
        && sized.cross == summary(fresh,Some(available),i).cross
        && sized.has_fill == summary(fresh,Some(available),i).has_fill;
    let r = choose |i:nat| endpoint(replay,None,i) && placed.next == #[trigger] at(replay.items(),i as int)
        && placed.count == summary(replay,None,i).count
        && placed.main == summary(replay,None,i).main
        && placed.cross == summary(replay,None,i).cross
        && placed.has_fill == summary(replay,None,i).has_fill;
    unique_endpoint(fresh,Some(available),end,f);
    unique_endpoint(replay,None,end,r);
}

pub fn start_scan() -> (out: Ghost<nat>)
    ensures out@ == 0,
    no_unwind
{
    Ghost(0nat)
}

pub fn advance(i: Ghost<nat>) -> (out: Ghost<nat>)
    ensures out@ == i@ + 1,
    no_unwind
{
    Ghost(i@ + 1)
}

}
