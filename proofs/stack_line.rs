//! Ordered sibling placement and resumption from an unrounded forward edge.
use vstd::prelude::*;
#[path = "../src/stack_line.rs"]
mod kernel;
use kernel::{Scalar, ScalarModel};

verus! {

pub open spec fn adjusted<F: ScalarModel>(value: F, margin: F) -> F {
    if F::zero(margin) { value } else { F::sum(value, margin) }
}

pub open spec fn advance<F: ScalarModel>(start: F, size: F, trailing: F, gap: F) -> F {
    F::sum(start, F::sum(adjusted(size, trailing), gap))
}

pub open spec fn full_step<F: ScalarModel>(
    cursor: F, flipped: bool, range: [F; 2], size: F, margin: [F; 2], gap: F,
) -> ([F; 2], F) {
    if flipped {
        let start = adjusted(cursor, margin[1]);
        let end = F::difference(F::sum(range[0], range[1]), start);
        ([F::difference(end, size), end], advance(start, size, margin[0], gap))
    } else {
        let start = adjusted(cursor, margin[0]);
        ([start, F::sum(start, size)], advance(start, size, margin[1], gap))
    }
}

pub open spec fn start_step<F: ScalarModel>(
    cursor: F, cross_start: F, horizontal: bool, size: [F; 2], gap: F,
) -> ([[F; 2]; 2], F) {
    let x = if horizontal { cursor } else { cross_start };
    let y = if horizontal { cross_start } else { cursor };
    ([[x, F::sum(x, size[0])], [y, F::sum(y, size[1])]],
        F::sum(cursor, F::sum(if horizontal { size[0] } else { size[1] }, gap)))
}

// The shortcut uses the same physical edges and cursor as ordinary forward
// placement. No associativity, zero-addition identity or finite bounds apply.
fn forward_start_refines_full<F: Scalar>(
    mut cursor: F, cross_start: F, horizontal: bool, size: [F; 2], gap: F, zero: F, range: [F; 2],
) -> (result: [[F; 2]; 2])
    requires F::zero(zero),
    ensures ({
        let main: int = if horizontal { 0 } else { 1 };
        let cross = 1 - main;
        &&& result[main] == full_step(cursor, false, range, size[main], [zero, zero], gap).0
        &&& result[cross] == [adjusted(cross_start, zero), F::sum(adjusted(cross_start, zero), size[cross])]
    }),
{
    let mut ordinary_cursor = cursor;
    let size_main = if horizontal { size[0] } else { size[1] };
    let ordinary = kernel::place(&mut ordinary_cursor, false, range, size_main, [zero, zero], gap);
    let edges = kernel::place_start(&mut cursor, cross_start, horizontal, size, gap);
    assert(cursor == ordinary_cursor);
    assert(if horizontal { edges[0] == ordinary } else { edges[1] == ordinary });
    edges
}

// Rows are in document order. Only enabled, in-flow children advance the
// cursor. The caller supplies the shortcut's cross-axis eligibility.
pub struct Row<F> {
    pub in_flow: bool,
    pub start_aligned: bool,
    pub cross_start: F,
    pub size: [F; 2],
    pub margin: [F; 2],
}

pub open spec fn step<F: ScalarModel>(
    row: Row<F>, cursor: F, range: [F; 2], gap: F, horizontal: bool, flipped: bool, optimize: bool,
) -> ([F; 2], F) {
    let main: int = if horizontal { 0 } else { 1 };
    if optimize && !flipped && row.start_aligned && F::zero(row.margin[0]) && F::zero(row.margin[1]) {
        let (edges, next) = start_step(cursor, row.cross_start, horizontal, row.size, gap);
        (edges[main], next)
    } else {
        full_step(cursor, flipped, range, row.size[main], row.margin, gap)
    }
}

/// A fold of the in-flow siblings in document order. The final cursor includes
/// the gap following the last in-flow item, so it is ready for the next item.
pub open spec fn run<F: ScalarModel>(
    rows: Seq<Row<F>>, initial: F, range: [F; 2], gap: F, horizontal: bool, flipped: bool, optimize: bool,
) -> (Seq<[F; 2]>, F)
    decreases rows.len(),
{
    if rows.len() == 0 { (Seq::empty(), initial) } else {
        let (earlier, cursor) = run(rows.drop_last(), initial, range, gap, horizontal, flipped, optimize);
        let row = rows.last();
        if row.in_flow {
            let (edges, next) = step(row, cursor, range, gap, horizontal, flipped, optimize);
            (earlier.push(edges), next)
        } else { (earlier, cursor) }
    }
}

pub proof fn shortcuts_preserve_sibling_order<F: ScalarModel>(
    rows: Seq<Row<F>>, initial: F, range: [F; 2], gap: F, horizontal: bool, flipped: bool,
)
    ensures run(rows, initial, range, gap, horizontal, flipped, true)
         == run(rows, initial, range, gap, horizontal, flipped, false),
    decreases rows.len(),
{
    if rows.len() != 0 {
        shortcuts_preserve_sibling_order(rows.drop_last(), initial, range, gap, horizontal, flipped);
    }
}

// The public append path reads the published start of its predecessor. Under
// its unsnapped, forward guard this is the unrounded start in full_step.
pub proof fn resume_from_published_start<F: ScalarModel>(
    prefix: Seq<Row<F>>, predecessor: Row<F>, tail: Seq<Row<F>>, initial: F,
    range: [F; 2], gap: F, horizontal: bool,
)
    requires predecessor.in_flow,
    ensures ({
        let old = run(prefix.push(predecessor), initial, range, gap, horizontal, false, true);
        let main: int = if horizontal { 0 } else { 1 };
        let resumed = advance(old.0.last()[0], predecessor.size[main], predecessor.margin[1], gap);
        let suffix = run(tail, resumed, range, gap, horizontal, false, true);
        let whole = run(prefix.push(predecessor) + tail, initial, range, gap, horizontal, false, false);
        &&& old.0.len() > 0
        &&& old.1 == resumed
        &&& whole == (old.0 + suffix.0, suffix.1)
    }),
    decreases tail.len(),
{
    let anchored = prefix.push(predecessor);
    assert(anchored.drop_last() =~= prefix);
    shortcuts_preserve_sibling_order(anchored, initial, range, gap, horizontal, false);
    let old = run(anchored, initial, range, gap, horizontal, false, false);
    if tail.len() == 0 {
        assert(anchored + tail =~= anchored);
        assert(old.0 + Seq::<[F; 2]>::empty() =~= old.0);
    } else {
        resume_from_published_start(prefix, predecessor, tail.drop_last(), initial, range, gap, horizontal);
        assert((anchored + tail).drop_last() =~= anchored + tail.drop_last());
        let previous = run(tail.drop_last(), old.1, range, gap, horizontal, false, true);
        let row = tail.last();
        if row.in_flow {
            let edges = step(row, previous.1, range, gap, horizontal, false, true).0;
            assert(old.0 + previous.0.push(edges) =~= (old.0 + previous.0).push(edges));
        }
    }
}
}
