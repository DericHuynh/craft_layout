//! Block-axis coordinates and adjoining margin groups.
use vstd::prelude::*;

#[path = "../src/block_flow.rs"]
pub mod kernel;
use kernel::{BlockFlow, BlockItem, BlockMargins, CollapsedMargin, ScalarModel};

verus! {

pub open spec fn empty<F: ScalarModel>() -> CollapsedMargin<F> {
    CollapsedMargin { positive: F::zero_value(), negative: F::zero_value() }
}

pub open spec fn from_edge<F: ScalarModel>(value: F) -> CollapsedMargin<F> {
    CollapsedMargin { positive: F::upper(value,F::zero_value()), negative: F::lower(value,F::zero_value()) }
}

pub open spec fn advance<F: ScalarModel>(m: CollapsedMargin<F>) -> F {
    F::plus(m.positive,m.negative)
}

pub open spec fn join<F: ScalarModel>(a: CollapsedMargin<F>, b: CollapsedMargin<F>) -> CollapsedMargin<F> {
    CollapsedMargin { positive: F::upper(a.positive,b.positive), negative: F::lower(a.negative,b.negative) }
}

pub open spec fn item_from_edges<F: ScalarModel>(top: F, bottom: F, size: F,
    adjoins: bool, children_empty: bool, nested: Option<BlockMargins<F>>) -> BlockItem<F>
{
    let before = from_edge(top);
    let after = from_edge(bottom);
    match nested {
        Some(edges) => BlockItem {
            before: join(before,edges.before), after: join(after,edges.after),
            size, through: adjoins && edges.all_through,
        },
        None => BlockItem { before, after, size, through: adjoins && children_empty },
    }
}

pub open spec fn initial<F: ScalarModel>(top: bool, bottom: bool) -> BlockFlow<F> {
    BlockFlow { end: F::zero_value(), pending: empty(), outgoing: BlockMargins {
        before: empty(), after: empty(), all_through: true }, collapse_top: top, collapse_bottom: bottom }
}

pub open spec fn push<F: ScalarModel>(state: BlockFlow<F>, item: BlockItem<F>) -> (BlockFlow<F>, F) {
    let group = join(state.pending,item.before);
    let lead = state.outgoing.all_through && state.collapse_top;
    let start = F::plus(state.end,if lead { F::zero_value() } else { advance(group) });
    let next = if item.through {
        BlockFlow { pending: join(group,item.after), ..state }
    } else {
        BlockFlow { pending: item.after, end: F::plus(start,item.size),
            outgoing: BlockMargins { before: if lead { group } else { state.outgoing.before },
                all_through: false, ..state.outgoing },
            ..state }
    };
    (next,start)
}

pub open spec fn finish<F: ScalarModel>(state: BlockFlow<F>) -> (F, BlockMargins<F>) {
    let lead = state.outgoing.all_through && state.collapse_top;
    (F::upper(if lead || state.collapse_bottom { state.end } else { F::plus(state.end,advance(state.pending)) },
        F::zero_value()),
     BlockMargins {
        before: if lead { state.pending } else { state.outgoing.before },
        after: if !lead && state.collapse_bottom { state.pending } else { state.outgoing.after },
        all_through: state.outgoing.all_through,
     })
}

// Independently split each prefix into its first adjoining group and its
// outstanding trailing group. A through box contributes both edges to the
// current group. A solid box separates the two edges.
pub open spec fn all_through<F: Copy>(items: Seq<BlockItem<F>>) -> bool
    decreases items.len(),
{
    items.len() == 0 || (items.last().through && all_through(items.drop_last()))
}

pub open spec fn leading<F: Copy>(items: Seq<BlockItem<F>>) -> Seq<CollapsedMargin<F>>
    decreases items.len(),
{
    if items.len() == 0 { Seq::empty() }
    else {
        let prior = items.drop_last();
        let first = leading(prior);
        let item = items.last();
        if !all_through(prior) { first } else if item.through { first.push(item.before).push(item.after) }
        else { first.push(item.before) }
    }
}

pub open spec fn trailing<F: Copy>(items: Seq<BlockItem<F>>) -> Seq<CollapsedMargin<F>>
    decreases items.len(),
{
    if items.len() == 0 { Seq::empty() }
    else if items.last().through { trailing(items.drop_last()).push(items.last().before).push(items.last().after) }
    else { seq![items.last().after] }
}

/// No assumption that addition associates. Extrema are computed before
/// converting an adjoining group to its net margin.
pub open spec fn fold<F: ScalarModel>(terms: Seq<CollapsedMargin<F>>) -> CollapsedMargin<F>
    decreases terms.len(),
{
    if terms.len() == 0 { empty() } else { join(fold(terms.drop_last()),terms.last()) }
}

proof fn fold_push<F: ScalarModel>(terms: Seq<CollapsedMargin<F>>, edge: CollapsedMargin<F>)
    ensures fold(terms.push(edge)) == join(fold(terms),edge),
{
    assert(terms.push(edge).drop_last() =~= terms);
    assert(terms.push(edge).last() == edge);
}

pub open spec fn position<F: ScalarModel>(end: F, prior: Seq<BlockItem<F>>, before: CollapsedMargin<F>, top: bool) -> F {
    F::plus(end,if top && all_through(prior) { F::zero_value() }
        else { advance(join(fold(trailing(prior)),before)) })
}

pub open spec fn extent<F: ScalarModel>(items: Seq<BlockItem<F>>, top: bool) -> F
    decreases items.len(),
{
    if items.len() == 0 { F::zero_value() }
    else {
        let prior = items.drop_last();
        let end = extent(prior,top);
        let item = items.last();
        if item.through { end } else { F::plus(position(end,prior,item.before,top),item.size) }
    }
}

pub open spec fn replay<F: ScalarModel>(items: Seq<BlockItem<F>>, top: bool, bottom: bool) -> BlockFlow<F>
    decreases items.len(),
{
    if items.len() == 0 { initial(top,bottom) } else { push(replay(items.drop_last(),top,bottom),items.last()).0 }
}

pub open spec fn fits<F: ScalarModel>(m: CollapsedMargin<F>, valid: spec_fn(F) -> bool, rank: spec_fn(F) -> int) -> bool {
    valid(m.positive) && valid(m.negative) && rank(m.negative) <= rank(F::zero_value()) <= rank(m.positive)
}

pub open spec fn extrema_order<F: ScalarModel>(valid: spec_fn(F) -> bool, rank: spec_fn(F) -> int) -> bool {
    &&& valid(F::zero_value())
    &&& forall |a:F,b:F| valid(a) && valid(b) ==>
        #[trigger] F::upper(a,b) == (if rank(a) > rank(b) { a } else { b })
    &&& forall |a:F,b:F| valid(a) && valid(b) ==>
        #[trigger] F::lower(a,b) == (if rank(a) < rank(b) { a } else { b })
}

pub proof fn merging_keeps_valid_edges<F: ScalarModel>(left: CollapsedMargin<F>, right: CollapsedMargin<F>,
    valid: spec_fn(F)->bool, rank: spec_fn(F)->int)
    requires extrema_order(valid,rank), fits(left,valid,rank), fits(right,valid,rank),
    ensures fits(join(left,right),valid,rank),
{
}

pub proof fn nested_item_keeps_valid_edges<F: ScalarModel>(top:F,bottom:F,size:F,adjoins:bool,
    children_empty:bool,nested:Option<BlockMargins<F>>,valid:spec_fn(F)->bool,rank:spec_fn(F)->int)
    requires extrema_order(valid,rank), valid(top), valid(bottom),
        nested.is_some() ==> fits(nested.unwrap().before,valid,rank) && fits(nested.unwrap().after,valid,rank),
    ensures ({
        let item = item_from_edges(top,bottom,size,adjoins,children_empty,nested);
        fits(item.before,valid,rank) && fits(item.after,valid,rank)
    }),
{
    assert(fits(from_edge(top),valid,rank) && fits(from_edge(bottom),valid,rank));
    if let Some(nested) = nested {
        merging_keeps_valid_edges(from_edge(top),nested.before,valid,rank);
        merging_keeps_valid_edges(from_edge(bottom),nested.after,valid,rank);
    }
}

/// Every selected extremum comes from an adjoining edge or from the initial
/// zero. The result dominates all positive contributions and is bounded above
/// by all negative contributions.
pub proof fn fold_selects_group_extrema<F: ScalarModel>(terms: Seq<CollapsedMargin<F>>,
    valid: spec_fn(F)->bool, rank: spec_fn(F)->int)
    requires extrema_order(valid,rank),
        forall |j:int| 0 <= j < terms.len() ==> #[trigger] fits(terms[j],valid,rank),
    ensures ({
        let m = fold(terms);
        &&& fits(m,valid,rank)
        &&& forall |j:int| 0 <= j < terms.len() ==>
            rank((#[trigger] terms[j]).positive) <= rank(m.positive)
                && rank(m.negative) <= rank(terms[j].negative)
        &&& (m.positive == F::zero_value() ||
            exists |j:int| 0 <= j < terms.len() && (#[trigger] terms[j]).positive == m.positive)
        &&& (m.negative == F::zero_value() ||
            exists |j:int| 0 <= j < terms.len() && (#[trigger] terms[j]).negative == m.negative)
    }),
    decreases terms.len(),
{
    if terms.len() > 0 {
        let rest = terms.drop_last();
        let last = terms.last();
        assert(last == terms[terms.len()-1]);
        assert forall |j:int| 0 <= j < rest.len() implies #[trigger] fits(rest[j],valid,rank) by {
            assert(rest[j] == terms[j]);
        }
        fold_selects_group_extrema(rest,valid,rank);
        let earlier = fold(rest);
        assert(fits(last,valid,rank) && fits(earlier,valid,rank));
        assert forall |j:int| 0 <= j < terms.len() implies
            rank((#[trigger] terms[j]).positive) <= rank(fold(terms).positive)
                && rank(fold(terms).negative) <= rank(terms[j].negative) by {
            if j < rest.len() { assert(terms[j] == rest[j]); }
        }
        assert forall |j:int| 0 <= j < rest.len() implies rest[j] == #[trigger] terms[j] by {};
        if earlier.positive != F::zero_value() {
            let j = choose |j:int| 0 <= j < rest.len() && (#[trigger] rest[j]).positive == earlier.positive;
            assert(terms[j] == rest[j]);
        }
        if earlier.negative != F::zero_value() {
            let j = choose |j:int| 0 <= j < rest.len() && (#[trigger] rest[j]).negative == earlier.negative;
            assert(terms[j] == rest[j]);
        }
    }
}

pub proof fn through_joins_boundary_groups<F: Copy>(items: Seq<BlockItem<F>>)
    requires all_through(items),
    ensures leading(items) == trailing(items),
    decreases items.len(),
{
    if items.len() > 0 {
        through_joins_boundary_groups(items.drop_last());
    }
}

pub proof fn flow_replays_grouped_blocks<F: ScalarModel>(items: Seq<BlockItem<F>>, top: bool, bottom: bool,
    valid: spec_fn(F)->bool, rank: spec_fn(F)->int)
    requires extrema_order(valid,rank),
        forall |j:int| 0 <= j < items.len() ==> {
            let i = #[trigger] items[j];
            fits(i.before,valid,rank) && fits(i.after,valid,rank)
        },
    ensures ({
        let state = replay(items,top,bottom);
        &&& state.end == extent(items,top)
        &&& state.pending == fold(trailing(items))
        &&& state.outgoing.before == if top && !all_through(items) { fold(leading(items)) } else { empty() }
        &&& state.outgoing.after == empty()
        &&& state.outgoing.all_through == all_through(items)
        &&& state.collapse_top == top && state.collapse_bottom == bottom
    }),
    decreases items.len(),
{
    if items.len() > 0 {
        let rest = items.drop_last();
        let last = items.last();
        assert(last == items[items.len()-1]);
        assert forall |j:int| 0 <= j < rest.len() implies {
            let i = #[trigger] rest[j]; fits(i.before,valid,rank) && fits(i.after,valid,rank)
        } by { assert(rest[j] == items[j]); }
        flow_replays_grouped_blocks(rest,top,bottom,valid,rank);
        if all_through(rest) { through_joins_boundary_groups(rest); }
        assert(join(empty::<F>(),last.after) == last.after) by {
            assert(F::upper(F::zero_value(),last.after.positive) ==
                if rank(F::zero_value()) > rank(last.after.positive) { F::zero_value() } else { last.after.positive });
            assert(F::lower(F::zero_value(),last.after.negative) ==
                if rank(F::zero_value()) < rank(last.after.negative) { F::zero_value() } else { last.after.negative });
        }
        let prev = trailing(rest);
        let flow = replay(rest,top,bottom);
        assert(flow.pending == fold(prev));
        assert(replay(items,top,bottom) == push(flow,last).0);
        if last.through {
            fold_push(prev,last.before);
            fold_push(prev.push(last.before),last.after);
            assert(trailing(items) == prev.push(last.before).push(last.after));
            assert(replay(items,top,bottom).pending == join(join(fold(prev),last.before),last.after));
        } else {
            let none = Seq::<CollapsedMargin<F>>::empty();
            fold_push(none,last.after);
            assert(none.push(last.after) =~= seq![last.after]);
            assert(trailing(items) == seq![last.after]);
            assert(replay(items,top,bottom).pending == last.after);
            if top && all_through(rest) {
                fold_push(prev,last.before);
            }
        }
    }
    let state = replay(items,top,bottom);
    assert(state.end == extent(items,top));
    assert(state.pending == fold(trailing(items)));
    assert(state.outgoing.before == if top && !all_through(items) { fold(leading(items)) } else { empty() });
    assert(state.outgoing.after == empty());
    assert(state.outgoing.all_through == all_through(items));
    assert(state.collapse_top == top && state.collapse_bottom == bottom);
}

// A region may publish these same summaries to a retained parent or compact
// them in the arena. The summaries themselves satisfy the edge invariant.
pub proof fn outgoing_edges_can_be_reused<F: ScalarModel>(items: Seq<BlockItem<F>>, top:bool,bottom:bool,
    valid:spec_fn(F)->bool,rank:spec_fn(F)->int)
    requires extrema_order(valid,rank),
        forall |j:int| 0 <= j < items.len() ==> {
            let i = #[trigger] items[j];
            fits(i.before,valid,rank) && fits(i.after,valid,rank)
        },
    ensures ({
        let state = replay(items,top,bottom);
        let result = finish(state).1;
        &&& fits(state.pending,valid,rank)
        &&& fits(state.outgoing.before,valid,rank)
        &&& fits(state.outgoing.after,valid,rank)
        &&& fits(result.before,valid,rank) && fits(result.after,valid,rank)
    }),
    decreases items.len(),
{
    if items.len() > 0 {
        let rest = items.drop_last();
        assert forall |j:int| 0 <= j < rest.len() implies {
            let i = #[trigger] rest[j];
            fits(i.before,valid,rank) && fits(i.after,valid,rank)
        } by { assert(rest[j] == items[j]); }
        outgoing_edges_can_be_reused(rest,top,bottom,valid,rank);
        let old = replay(rest,top,bottom);
        let last = items.last();
        assert(last == items[items.len()-1]);
        merging_keeps_valid_edges(old.pending,last.before,valid,rank);
        merging_keeps_valid_edges(join(old.pending,last.before),last.after,valid,rank);
    }
}

/// Measurement and placement see the same coordinate for the next block
/// when they have the same previously resolved sibling inputs.
pub proof fn next_block_coordinate<F: ScalarModel>(items: Seq<BlockItem<F>>, next: BlockItem<F>,
    top: bool, bottom: bool, valid: spec_fn(F)->bool, rank: spec_fn(F)->int)
    requires extrema_order(valid,rank),
        forall |j:int| 0 <= j < items.len() ==> {
            let i = #[trigger] items[j];
            fits(i.before,valid,rank) && fits(i.after,valid,rank)
        },
    ensures push(replay(items,top,bottom),next).1 == position(extent(items,top),items,next.before,top),
{
    flow_replays_grouped_blocks(items,top,bottom,valid,rank);
}

/// Finish emits each eligible boundary group to the parent, and otherwise
/// includes the trailing group in the physical height. A wholly through group
/// collapses out the top only once when both policies allow it.
pub proof fn finish_matches_grouped_blocks<F: ScalarModel>(items:Seq<BlockItem<F>>,top:bool,bottom:bool,
    valid:spec_fn(F)->bool,rank:spec_fn(F)->int)
    requires extrema_order(valid,rank),
        forall |j:int| 0 <= j < items.len() ==> {
            let i = #[trigger] items[j];
            fits(i.before,valid,rank) && fits(i.after,valid,rank)
        },
    ensures ({
        let (height,edges) = finish(replay(items,top,bottom));
        let exits_top = top && all_through(items);
        &&& edges.before == if top { fold(leading(items)) } else { empty() }
        &&& edges.after == if !exits_top && bottom { fold(trailing(items)) } else { empty() }
        &&& edges.all_through == all_through(items)
        &&& height == F::upper(if exits_top || bottom { extent(items,top) }
            else { F::plus(extent(items,top),advance(fold(trailing(items)))) },F::zero_value())
    }),
{
    flow_replays_grouped_blocks(items,top,bottom,valid,rank);
    if all_through(items) { through_joins_boundary_groups(items); }
}

}
