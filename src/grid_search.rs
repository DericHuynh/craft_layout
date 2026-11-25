// The production row-major scanner and its checked loop invariants.
#![allow(unexpected_cfgs)]

use super::{grid_sparse::{self, Inputs}, grid_state, grid_words};
use grid_words::ZeroCounts;
use crate::vec_memory::{CapacityMemory, VecMemory};
#[cfg(not(verus_keep_ghost))]
use crate::vec_memory::RustVec;
#[cfg(verus_keep_ghost)]
use crate::vec_memory::capacity_limit;

#[path = "grid_multiword.rs"]
mod grid_multiword;
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(blocked =>
    ensures forall |j:u32| j<64 ==> #[trigger] bit(blocked,j as int)
        == (exists |r:int| 0<=r<rows.len() && #[trigger] bit(rows@[r],j as int)),
    no_unwind
))]
fn blocked_columns(rows: &[u64]) -> u64 {
    let mut blocked = 0u64;
    let mut i = 0;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |j:u32| j<64 implies !#[trigger] bit(0,j as int) by {
            assert(((0u64 >> j) & 1) == 0) by(bit_vector);
        }
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= rows.len(), forall |j:u32| j<64 ==> #[trigger] bit(blocked,j as int)
            == (exists |r:int| 0<=r<i && #[trigger] bit(rows@[r],j as int)),
        decreases rows.len()-i,
    ))]
    while i < rows.len() {
        blocked = grid_words::union(blocked, rows[i]);
        i += 1;
    }
    blocked
}

/// Combine the spanned rows for two consecutive one-word candidates.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(blocked =>
    requires 0 < height < rows.len(),
    ensures forall |j:u32| j<64 ==> #[trigger] bit(blocked.0,j as int)
        == (exists |r:int| 0<=r<height && #[trigger] bit(rows@[r],j as int)),
        forall |j:u32| j<64 ==> #[trigger] bit(blocked.1,j as int)
        == (exists |r:int| 1<=r<=height && #[trigger] bit(rows@[r],j as int)),
    no_unwind
))]
fn blocked_pair(rows: &[u64], height: usize) -> (u64, u64) {
    // Adjacent windows differ only at their boundary rows.
    let (head, _) = rows.split_at(height);
    let (_, middle) = head.split_at(1);
    let shared = blocked_columns(middle);
    let left = grid_words::union(shared, rows[0]);
    let right = grid_words::union(shared, rows[height]);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(middle@ =~= rows@.subrange(1, height as int));
        paired_window_union(rows@, middle@, height as int, shared, left, right);
    }
    (left, right)
}

#[cfg(verus_keep_ghost)]
verus! {
    closed spec fn row_collision(board: Board, line: int, pos: int, h: int, w: int, next: int) -> bool {
        &&& pos < next
        &&& exists |r: int, k: int| line <= r < line+h && pos <= k < pos+w && k < next
            && #[trigger] occupied_run(board, r, k, next)
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 0 < stride, n_lines * stride == mem.len(), line < n_lines,
        h > 0, w > 0, pos + w <= usize::MAX, pos + w <= stride * 64,
    ensures match result {
        None => fits(packed(mem@,stride as int),(line as int,pos as int),h as int,w as int),
        Some(next) => row_collision(packed(mem@,stride as int), line as int, pos as int, h as int, w as int, next as int),
    },
    no_unwind
))]
fn probe_rows<C: ZeroCounts>(mem: &[u64], stride: usize, n_lines: usize, line: usize, pos: usize, h: usize, w: usize) -> Option<usize> {
    let end = pos + (w - 1);
    let first = pos / 64;
    let last = end / 64;
    let start_mask = grid_words::word_range((pos % 64) as u32, 63);
    let end_mask = grid_words::word_range(0, (end % 64) as u32);
    let spanned_end = line.saturating_add(h);
    let stop = if spanned_end < n_lines { spanned_end } else { n_lines };
    let mut r = line;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant line <= r <= stop <= n_lines, stop == vstd::math::min(line + h,n_lines as int),
            stride>0, n_lines*stride == mem.len(), h>0, w>0, pos+w<=usize::MAX, pos+w<=stride*64,
            masks(pos as int,w as int,first as int,last as int,start_mask,end_mask),
            forall |y:int,c:int| line <= y < r && pos <= c < pos+w ==>
                !#[trigger] packed(mem@,stride as int).contains((y,c)),
        decreases stop-r,
    ))]
    while r < stop {
        #[cfg(verus_keep_ghost)]
        proof! { row_block_bounds(r as int,stride as int,n_lines as int); }
        let offset = r * stride;
        let row = mem.split_at(offset).1.split_at(stride).0;
        #[cfg(verus_keep_ghost)]
        proof! { assert(row@ =~= mem@.subrange(offset as int, offset + stride)); }
        if let Some((word, delta)) = grid_words::probe_row::<C>(row, first, last, start_mask, end_mask) {
            #[cfg(verus_keep_ghost)]
            proof! {
                collided_row(mem@,stride as int,r as int,pos as int,w as int,row@,
                    first as int,last as int,start_mask,end_mask,word as int,delta);
            }
            let next = (word * 64).saturating_add(delta as usize);
            #[cfg(verus_keep_ghost)]
            proof! {
                let b=packed(mem@,stride as int);
                let end = (word as int)*64+(delta as int);
                let k=choose |k:int| pos<=k<pos+w && k<end && #[trigger] occupied_run(b,r as int,k,end);
                assert(line <= r < line + h);
                assert(occupied_run(b,r as int,k,next as int));
                assert(k < next && pos < next);
                assert(row_collision(b, line as int, pos as int, h as int, w as int, next as int));
            }
            return Some(next);
        }
        #[cfg(verus_keep_ghost)]
        proof! { clear_row(mem@,stride as int,r as int,pos as int,w as int,row@,
            first as int,last as int,start_mask,end_mask); }
        r += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let b=packed(mem@,stride as int);
        assert forall |q:Cell| #[trigger] b.contains(q) implies !covers((line as int,pos as int),h as int,w as int,q) by {
            if covers((line as int,pos as int),h as int,w as int,q) && q.0 >= n_lines {
                empty_after(mem@,stride as int,n_lines as int,q.0,q.1);
            }
        }
    }
    None
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires stride>0, n_lines*stride == mem.len(), n_lines<usize::MAX,
        1<=w<=columns<=stride*64, h>0, start.0<=n_lines, start.1<=columns,
    ensures result.0 <= n_lines + 1,
        first_fit(packed(mem@,stride as int),columns as int,h as int,w as int,
            (start.0 as int,start.1 as int),(result.0 as int,result.1 as int)),
    no_unwind
))]
fn find_grid_cell_with_counts<C: ZeroCounts>(mem: &[u64], columns: usize, stride: usize, n_lines: usize,
    start: (usize, usize), h: usize, w: usize) -> (usize, usize) {
    // Resolve the row representation once, so the multiword scanner has no
    // register pressure from the one-word lookahead.
    if stride == 1 {
        find_grid_cell_impl::<C, true>(mem, columns, stride, n_lines, start, h, w)
    } else {
        find_grid_cell_impl::<C, false>(mem, columns, stride, n_lines, start, h, w)
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires stride>0, n_lines*stride == mem.len(), n_lines<usize::MAX,
        1<=w<=columns<=stride*64, h>0, start.0<=n_lines, start.1<=columns,
        ONE_WORD == (stride == 1),
    ensures result.0 <= n_lines + 1,
        first_fit(packed(mem@,stride as int),columns as int,h as int,w as int,
            (start.0 as int,start.1 as int),(result.0 as int,result.1 as int)),
    no_unwind
))]
fn find_grid_cell_impl<C: ZeroCounts, const ONE_WORD: bool>(mem: &[u64], columns: usize, stride: usize, n_lines: usize,
    start: (usize, usize), h: usize, w: usize) -> (usize, usize) {
    let (mut line, mut pos) = start;
    let last_start = columns - w;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant stride>0, n_lines*stride == mem.len(), n_lines<usize::MAX, ONE_WORD == (stride == 1),
            1<=w<=columns<=stride*64, h>0, last_start==columns-w,
            line<=n_lines || (line==n_lines+1 && pos==0),
            !before((line as int,pos as int),(start.0 as int,start.1 as int)),
            passed(packed(mem@,stride as int),columns as int,h as int,w as int,
                (start.0 as int,start.1 as int),(line as int,pos as int)),
        decreases n_lines+1-line, usize::MAX-pos,
    ))]
    loop {
        if pos > last_start {
            #[cfg(verus_keep_ghost)]
            proof! { wrap_cursor(packed(mem@,stride as int),columns as int,h as int,w as int,
                (start.0 as int,start.1 as int),(line as int,pos as int)); }
            line += 1;
            pos = 0;
            continue;
        }
        if line >= n_lines {
            #[cfg(verus_keep_ghost)]
            proof! {
                let b=packed(mem@,stride as int);
                assert forall |q:Cell| #[trigger] b.contains(q) implies !covers((line as int,pos as int),h as int,w as int,q) by {
                    if covers((line as int,pos as int),h as int,w as int,q) {
                        empty_after(mem@,stride as int,n_lines as int,q.0,q.1);
                    }
                }
            }
            return (line, pos);
        }
        if ONE_WORD {
            // A long live board can amortize the lookahead. Forward cursors
            // usually compact to a few rows, where a single probe is cheaper.
            if n_lines >= 8 && pos == 0 && h < n_lines - line {
                let pair = mem.split_at(line).1.split_at(h + 1).0;
                let (first, second) = blocked_pair(pair, h);
                let (left, right) = grid_words::first_pair_starts::<C>((!first, !second), w as u32);
                #[cfg(verus_keep_ghost)]
                proof! {
                    assert(pair@ =~= mem@.subrange(line as int, line + h + 1));
                    open_paired_rows(mem@, line as int, h as int, pair@, first, second);
                    single_word_first_fit(packed(mem@,1),columns as int,h as int,w as int,
                        (start.0 as int,start.1 as int),(line as int,0),!first,left as int);
                }
                if left as usize <= last_start { return (line, left as usize); }
                line += 1;
                #[cfg(verus_keep_ghost)]
                proof! {
                    single_word_first_fit(packed(mem@,1),columns as int,h as int,w as int,
                        (start.0 as int,start.1 as int),(line as int,0),!second,right as int);
                }
                if right as usize <= last_start { return (line, right as usize); }
                line += 1;
                continue;
            }
            // One bit tests every spanned row at a given column.
            let available = n_lines - line;
            let spanned = if h < available { h } else { available };
            let rows = mem.split_at(line).1.split_at(spanned).0;
            let blocked = blocked_columns(rows);
            let next = grid_words::first_word_start::<C>(blocked, pos as u32, w as u32) as usize;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(rows@ =~= mem@.subrange(line as int, line + spanned));
                one_word_open(mem@,line as int,h as int,rows@,blocked);
                single_word_first_fit(packed(mem@,1),columns as int,h as int,w as int,
                    (start.0 as int,start.1 as int),(line as int,pos as int),!blocked,next as int);
            }
            if next <= last_start { return (line, next); }
            line += 1;
            pos = 0;
        } else if let Some(next) = probe_rows::<C>(mem, stride, n_lines, line, pos, h, w) {
            #[cfg(verus_keep_ghost)]
            proof! {
                let b = packed(mem@,stride as int);
                let (r,k) = choose |r:int,k:int| line <= r < line+h && pos<=k<pos+w
                    && k<next && #[trigger] occupied_run(b,r,k,next as int);
                skip_collision(b,columns as int,h as int,w as int,(start.0 as int,start.1 as int),
                    (line as int,pos as int),r,k,next as int);
            }
            pos = next;
        } else {
            return (line, pos);
        }
    }
}

#[cfg(all(test, not(verus_keep_ghost)))]
pub fn find_grid_cell(mem: &[u64], columns: usize, stride: usize, n_lines: usize,
    start: (usize, usize), h: usize, w: usize) -> (usize, usize) {
    find_grid_cell_with_counts::<grid_words::IntrinsicZeroCounts>(mem, columns, stride, n_lines, start, h, w)
}

/// Occupy an entire rectangle. Each supplied row is a complete word-aligned
/// row, and the same column range is marked on all of them.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires stride>0, old(rows).len()%stride==0, w>0, pos+w<=usize::MAX, pos+w<=stride*64,
    ensures final(rows)@.len()==old(rows)@.len(),
        forall |i:int,j:u32| 0<=i<final(rows)@.len() && j<64 ==> #[trigger] bit(final(rows)@[i],j as int)
            == (bit(old(rows)@[i],j as int) || pos <= (i%(stride as int))*64+j < pos+w),
    no_unwind
))]
pub fn occupy_span(rows: &mut [u64], stride: usize, pos: usize, w: usize) {
    let end = pos + (w - 1);
    let first = pos / 64;
    let last = end / 64;
    let start_mask = grid_words::word_range((pos % 64) as u32, 63);
    let end_mask = grid_words::word_range(0, (end % 64) as u32);
    if stride == 1 {
        let mask = start_mask & end_mask;
        let mut i = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant i<=rows.len(), rows@.len()==old(rows)@.len(), stride==1, pos+w<=64, w>0,
                masks(pos as int,w as int,0,0,start_mask,end_mask), mask==start_mask & end_mask,
                forall |k:int,j:u32| 0<=k<rows@.len() && j<64 ==> #[trigger] bit(rows@[k],j as int)
                    == (bit(old(rows)@[k],j as int) || (k<i && pos <= j < pos+w)),
            decreases rows.len()-i,
        ))]
        while i < rows.len() {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall |j:u32| j<64 implies #[trigger] bit(mask,j as int)==(pos<=j<pos+w) by {
                    word_matches_span(0,0,j,pos as int,w as int,start_mask,end_mask);
                }
            }
            rows[i] = grid_words::union(rows[i], mask);
            i += 1;
        }
        return;
    }
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i<=rows.len(), i%stride==0, rows.len()%stride==0, stride>1, rows@.len()==old(rows)@.len(),
            masks(pos as int,w as int,first as int,last as int,start_mask,end_mask), last<stride,
            forall |k:int| i<=k<rows@.len() ==> #[trigger] rows@[k] == old(rows)@[k],
            forall |k:int,j:u32| 0<=k<i && j<64 ==> #[trigger] bit(rows@[k],j as int)
                == (bit(old(rows)@[k],j as int) || pos <= (k%(stride as int))*64+j < pos+w),
        decreases rows.len()-i,
    ))]
    while i < rows.len() {
        #[cfg(verus_keep_ghost)]
        proof! { aligned_block(i as int,rows.len() as int,stride as int); }
        let (row, _) = rows.split_at_mut(i).1.split_at_mut(stride);
        grid_words::occupy_row(row, first, last, start_mask, end_mask);
        #[cfg(verus_keep_ghost)]
        proof! {
            assert forall |k:int,j:u32| i<=k<i+stride && j<64 implies #[trigger] bit(rows@[k],j as int)
                == (bit(old(rows)@[k],j as int) || pos <= (k%(stride as int))*64+j < pos+w) by {
                let mask=mark_mask(k-i,first as int,last as int,start_mask,end_mask);
                let prior=old(rows)@[k];
                assert(rows@[k] == (prior | mask));
                assert(((((prior | mask) >> j) & 1) != 0)
                    == ((((prior >> j) & 1) != 0) || (((mask >> j) & 1) != 0))) by(bit_vector);
                word_matches_span(prior,k-i,j,pos as int,w as int,start_mask,end_mask);
            }
        }
        i += stride;
    }
}

/// Compact backfill cache entries can only send the scanner to an earlier
/// position. A larger span uses its smaller cached span as a lower bound.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const CACHED_SPANS: usize = 8;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(index =>
    requires span>0,
    ensures index<8, index+1<=span, index+1==vstd::math::min(span as int,CACHED_SPANS as int),
    no_unwind
))]
pub fn cache_index(span: usize) -> usize {
    (if span < CACHED_SPANS { span } else { CACHED_SPANS }) - 1
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(key =>
    ensures !before((row as int,edge as int),(key.0 as int,key.1 as int)),
        key.0==vstd::math::min(row as int,u16::MAX as int),
        key.1==vstd::math::min(edge as int,u16::MAX as int),
    no_unwind
))]
pub fn cache_edge(row: usize, edge: usize) -> (u16, u16) {
    let max = u16::MAX as usize;
    (
        if row < max { row as u16 } else { u16::MAX },
        if edge < max { edge as u16 } else { u16::MAX },
    )
}

/// The next row-major cursor for the span-free grid.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires col<columns,
    ensures (next.0 as int,next.1 as int)==if col+1==columns {
        (vstd::math::min(row+1, usize::MAX as int),0int)
    } else { (row as int,col+1) }, next.1 < columns,
    no_unwind
))]
pub fn next_cell(row: usize, col: usize, columns: usize) -> (usize, usize) {
    if col + 1 == columns { (row.saturating_add(1), 0) } else { (row, col + 1) }
}

#[cfg(verus_keep_ghost)]
verus! {

/// The row-major model uses the original stable sibling order. Out-of-flow
/// items consume no cell. The probe cursor is independent of old cell words.
pub(crate) closed spec fn sequential_run<I>(
    items: grid_sparse::GridItems<I>, next: Option<I>, steps: nat, row: usize, col: usize, columns: usize,
) -> (usize, grid_sparse::CellWrites<I>)
    decreases steps,
{
    match next {
        Some(child) if steps > 0 => {
            let item = items[child];
            if item.1.is_some() {
                let cell = (row as u128, col);
                let after = if col + 1 == columns {
                    (vstd::math::min(row + 1, usize::MAX as int) as usize, 0usize)
                } else { (row, (col + 1) as usize) };
                let suffix = sequential_run(items, item.0, (steps - 1) as nat, after.0, after.1, columns);
                (suffix.0, seq![(child, cell)] + suffix.1)
            } else {
                sequential_run(items, item.0, (steps - 1) as nat, row, col, columns)
            }
        }
        _ => (vstd::math::min(row + if col == 0 { 0int } else { 1int }, usize::MAX as int) as usize, Seq::empty()),
    }
}

}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(rows =>
    requires columns > 0, first.is_some() ==> old(source).live(first.unwrap()),
    ensures ({
        let run = sequential_run(old(source).ordered_items(), first, old(source).remaining(first), 0, 0, columns);
        &&& grid_sparse::same_items(old(source), final(source))
        &&& final(source).cell_writes() == old(source).cell_writes() + run.1
        &&& rows == run.0
    }),
    no_unwind
))]
pub(crate) fn assign_sequential<I: Inputs>(source: &mut I, first: Option<I::Id>, columns: usize) -> usize {
    let mut next = first;
    let mut row = 0usize;
    let mut col = 0usize;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            col < columns, next.is_some() ==> source.live(next.unwrap()),
            grid_sparse::same_items(old(source), source),
            ({
                let original = sequential_run(old(source).ordered_items(), first,
                    old(source).remaining(first), 0, 0, columns);
                let suffix = sequential_run(source.ordered_items(), next, source.remaining(next), row, col, columns);
                &&& original.0 == suffix.0
                &&& source.cell_writes() + suffix.1 == old(source).cell_writes() + original.1
            }),
        decreases source.remaining(next),
    ))]
    loop {
        let Some(child) = next else {
            #[cfg(verus_keep_ghost)]
            proof! {
                let remaining = sequential_run(source.ordered_items(), next, source.remaining(next), row, col, columns);
                assert(next.is_none());
                assert(remaining.1 == Seq::<(I::Id, (u128, usize))>::empty());
                assert(source.cell_writes() + remaining.1 =~= source.cell_writes());
                assert(remaining.0 == vstd::math::min(row + if col == 0 { 0int } else { 1int }, usize::MAX as int));
            }
            return row.saturating_add(if col == 0 { 0 } else { 1 });
        };
        let (following, span) = source.inspect(child);
        next = following;
        if span.is_some() {
            source.publish(child, (row as u128, col));
            let (next_row, next_col) = next_cell(row, col, columns);
            row = next_row;
            col = next_col;
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {

/// A failed one-row probe may have published a prefix. The sparse fallback
/// overwrites that prefix as part of its complete assignment.
pub(crate) closed spec fn one_row_run<I>(
    items: grid_sparse::GridItems<I>, next: Option<I>, steps: nat, col: usize, rows: usize, columns: usize,
) -> (Option<usize>, grid_sparse::CellWrites<I>)
    decreases steps,
{
    match next {
        Some(child) if steps > 0 => {
            let item = items[child];
            match item.1 {
                Some((height, width)) => {
                    let width = vstd::math::max(width as int, 1);
                    let height = vstd::math::max(height as int, 1);
                    if col + width > columns {
                        (None, Seq::empty())
                    } else {
                        let suffix = one_row_run(items, item.0, (steps - 1) as nat, (col + width) as usize,
                            vstd::math::max(rows as int, height) as usize, columns);
                        (suffix.0, seq![(child, (0u128, col))] + suffix.1)
                    }
                }
                None => one_row_run(items, item.0, (steps - 1) as nat, col, rows, columns),
            }
        }
        _ => (Some(rows), Seq::empty()),
    }
}

}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires first.is_some() ==> old(source).live(first.unwrap()),
    ensures ({
        let run = one_row_run(old(source).ordered_items(), first, old(source).remaining(first), 0, 0, columns);
        &&& grid_sparse::same_items(old(source), final(source))
        &&& final(source).cell_writes() == old(source).cell_writes() + run.1
        &&& result == run.0
    }),
    no_unwind
))]
pub(crate) fn assign_one_row<I: Inputs>(source: &mut I, first: Option<I::Id>, columns: usize) -> Option<usize> {
    let mut next = first;
    let mut col = 0;
    let mut rows = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant next.is_some() ==> source.live(next.unwrap()),
            grid_sparse::same_items(old(source), source),
            ({
                let original = one_row_run(old(source).ordered_items(), first,
                    old(source).remaining(first), 0, 0, columns);
                let suffix = one_row_run(source.ordered_items(), next, source.remaining(next), col, rows, columns);
                &&& original.0 == suffix.0
                &&& source.cell_writes() + suffix.1 == old(source).cell_writes() + original.1
            }),
        decreases source.remaining(next),
    ))]
    loop {
        let Some(child) = next else {
            #[cfg(verus_keep_ghost)]
            proof! {
                let remaining = one_row_run(source.ordered_items(), next, source.remaining(next), col, rows, columns);
                assert(next.is_none());
                assert(remaining.0 == Some(rows));
                assert(remaining.1 == Seq::<(I::Id, (u128, usize))>::empty());
                assert(source.cell_writes() + remaining.1 =~= source.cell_writes());
            }
            return Some(rows);
        };
        let (following, span) = source.inspect(child);
        next = following;
        if let Some((height, width)) = span {
            let Some((next_col, next_rows)) = grid_state::extend_one_row(col, rows, width, height, columns) else {
                return None;
            };
            source.publish(child, (0, col));
            col = next_col;
            rows = next_rows;
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
    trait BitmapCapacity {
        spec fn capacity_model(words: &Vec<u64>) -> usize;
    }
}

#[cfg(not(verus_keep_ghost))]
trait BitmapCapacity {}

/// The bitmap operations whose standard-library specifications omit unwinding.
#[cfg_attr(verus_keep_ghost, verus_verify)]
trait BitmapStorage: BitmapCapacity {
    #[cfg_attr(verus_keep_ghost, verus_spec(capacity =>
        ensures capacity == Self::capacity_model(words), words.len() <= capacity,
        no_unwind
    ))]
    fn capacity(words: &Vec<u64>) -> usize;

    #[cfg_attr(verus_keep_ghost, verus_spec(reserved =>
        requires old(words).len() + additional <= grid_state::MAX_PACKED_WORDS,
            old(words).len() + additional <= (isize::MAX as int) / 8,
        ensures final(words)@ == old(words)@,
            reserved ==> Self::capacity_model(final(words)) >= old(words).len() + additional,
        no_unwind
    ))]
    fn try_reserve_exact(words: &mut Vec<u64>, additional: usize) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(words).len() < needed <= Self::capacity_model(old(words)),
        ensures
            final(words)@.len() == needed,
            final(words)@.take(old(words)@.len() as int) == old(words)@,
            forall |i: int| old(words).len() <= i < needed ==> #[trigger] final(words)@[i] == 0u64,
        no_unwind
    ))]
    fn resize_zeroed(words: &mut Vec<u64>, needed: usize);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires prefix <= old(words).len(),
        ensures final(words)@ == old(words)@.subrange(prefix as int, old(words)@.len() as int),
        no_unwind
    ))]
    fn discard_prefix(words: &mut Vec<u64>, prefix: usize);
}

#[cfg(not(verus_keep_ghost))]
struct VecBitmap;

#[cfg(not(verus_keep_ghost))]
impl BitmapCapacity for VecBitmap {}

#[cfg(not(verus_keep_ghost))]
impl BitmapStorage for VecBitmap {
    #[inline]
    fn capacity(words: &Vec<u64>) -> usize { words.capacity() }

    #[inline]
    fn try_reserve_exact(words: &mut Vec<u64>, additional: usize) -> bool {
        words.try_reserve_exact(additional).is_ok()
    }

    #[inline]
    fn resize_zeroed(words: &mut Vec<u64>, needed: usize) {
        // The reservation already covers this length. Cloning a u64 cannot call user code.
        words.resize(needed, 0);
    }

    #[inline]
    fn discard_prefix(words: &mut Vec<u64>, prefix: usize) {
        words.copy_within(prefix.., 0);
        words.truncate(words.len() - prefix);
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(reserved =>
    requires needed <= grid_state::MAX_PACKED_WORDS, needed <= (isize::MAX as int) / 8,
    ensures final(words)@ == old(words)@,
        reserved ==> S::capacity_model(final(words)) >= needed,
    no_unwind
))]
fn try_reserve_bitmap_with<S: BitmapStorage>(words: &mut Vec<u64>, needed: usize) -> bool {
    let current = S::capacity(words);
    if needed <= current {
        return true;
    }
    let capacity = grid_state::packed_growth_words(current, needed);
    let additional = capacity - words.len();
    S::try_reserve_exact(words, additional)
}

/// Extend zero occupancy through the last row of a rectangle and mark it.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placed =>
    requires stride>0, first < end, end*stride<=(isize::MAX as int)/8, old(occupied).len()%stride==0,
        end*stride <= grid_state::MAX_PACKED_WORDS,
        w>0, pos+w<=usize::MAX, pos+w<=stride*64,
    ensures placed ==> final(occupied)@.len()==vstd::math::max(old(occupied)@.len() as int,end*stride)
        && packed(final(occupied)@,stride as int)==place(packed(old(occupied)@,stride as int),
            (first as int,pos as int),end-first,w as int),
        !placed ==> final(occupied)@ == old(occupied)@,
    no_unwind
))]
fn place_span<S: BitmapStorage>(occupied: &mut Vec<u64>, stride: usize, first: usize, end: usize, pos: usize, w: usize) -> bool {
    #[cfg(verus_keep_ghost)]
    proof! { row_block_bounds(first as int,stride as int,end as int); }
    let begin = first * stride;
    let limit = end * stride;
    if limit > occupied.len() {
        if !try_reserve_bitmap_with::<S>(occupied, limit) {
            return false;
        }
        S::resize_zeroed(occupied, limit);
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(limit - begin == (end-first)*stride) by(nonlinear_arith)
            requires begin==first*stride, limit==end*stride;
        assert(occupied@.len()==vstd::math::max(old(occupied)@.len() as int,end*stride));
        vstd::arithmetic::mul::lemma_mul_is_commutative((end-first) as int,stride as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(limit-begin,stride as int,end-first,0);
        assert((limit-begin)%(stride as int)==0);
    }
    let mem = occupied.as_mut_slice();
    let (span, _) = mem.split_at_mut(begin).1.split_at_mut(limit - begin);
    occupy_span(span, stride, pos, w);
    #[cfg(verus_keep_ghost)]
    proof! {
        let old_mem=old(occupied)@;
        let was=packed(old_mem,stride as int);
        let now=packed(mem@,stride as int);
        let rect=(first as int,pos as int);
        assert forall |q:Cell| #[trigger] now.contains(q) == place(was,rect,end-first,w as int).contains(q) by {
            let (r,c)=q;
            if r>=0 && 0<=c<stride*64 {
                locate_cell(r,c,stride as int,first as int,end as int);
                let index=r*stride+c/64;
                let j=(c%64) as u32;
                assert(c==(c/64)*64+j);
                if begin<=index<limit {
                    let prior=if index<old_mem.len() { old_mem[index] } else { 0u64 };
                    assert(((0u64 >> j) & 1)==0) by(bit_vector);
                    assert(bit(mem@[index],j as int) == (bit(prior,j as int)
                        || pos <= ((index-begin)%(stride as int))*64+j < pos+w));
                    assert((index-begin)%(stride as int)==c/64);
                    assert(now.contains(q)==(was.contains(q)||covers(rect,end-first,w as int,q)));
                } else {
                    if index<old_mem.len() {
                        assert(mem@[index]==old_mem[index]);
                    } else if index<mem.len() {
                        assert(mem@[index]==0u64);
                        assert(((0u64 >> j) & 1)==0) by(bit_vector);
                    }
                }
            }
        }
        assert(now =~= place(was,rect,end-first,w as int));
    }
    true
}

/// Cursors and cached first-fit bounds for the spanned grid path.
/// The occupied vector remains the caller's reusable scratch storage.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct SpanCursor {
    pub rows: usize,
    pub first_row: usize,
    pub forward: (usize, usize),
    pub limits: [[(u16, u16); CACHED_SPANS]; CACHED_SPANS],
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result => ensures
    result.rows==0, result.first_row==0, result.forward==(0usize,0usize),
    forall|h:int,w:int| 0<=h<CACHED_SPANS && 0<=w<CACHED_SPANS
        ==> #[trigger] result.limits[h][w]==(0u16,0u16),
    forall|shape: grid_state::PackedShape, backfill: bool| shape.valid()
        ==> #[trigger] result.valid(Seq::empty(), shape, backfill),
    no_unwind
))]
pub(crate) const fn new_span_cursor() -> SpanCursor {
    let empty = (0u16, 0u16);
    let row = [empty, empty, empty, empty, empty, empty, empty, empty];
    let cursor = SpanCursor { rows: 0, first_row: 0, forward: (0, 0), limits: [row, row, row, row, row, row, row, row] };
    cursor
}

#[cfg(verus_keep_ghost)]
verus! {
    impl SpanCursor {
        pub(crate) open spec fn valid(self, occupied: Seq<u64>, shape: grid_state::PackedShape, backfill: bool) -> bool {
            &&& self.first_row <= self.rows <= shape.row_budget
            &&& (self.rows - self.first_row) * shape.stride == occupied.len()
            &&& backfill ==> self.first_row == 0 && valid_limits(self.limits, self.rows as int, shape.columns as int)
            &&& !backfill ==> self.first_row <= self.forward.0 <= self.rows
                && self.forward.1 <= shape.columns
                && (self.forward.0 == self.rows ==> self.forward.1 == 0)
        }
    }
}

impl SpanCursor {
    #[cfg(all(test, not(verus_keep_ghost)))]
    #[inline]
    pub(crate) fn try_place(
        &mut self, occupied: &mut Vec<u64>, shape: grid_state::PackedShape, height: u16, width: u16,
        backfill: bool,
    ) -> Option<(usize, usize)> {
        self.try_place_with::<grid_words::IntrinsicZeroCounts, VecBitmap>(occupied, shape, height, width, backfill)
    }

    /// Check the largest possible new row count before the bitmap can grow.
    /// A rejection leaves the cursor and scratch vector untouched.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(cell =>
        requires shape.valid(), old(self).valid(old(occupied)@, shape, backfill),
        ensures
            final(self).valid(final(occupied)@, shape, backfill),
            match cell {
                Some(cell) => span_step(*old(self), old(occupied)@, *final(self), final(occupied)@,
                    shape.columns, shape.stride,
                    vstd::math::max(height as int, 1) as usize,
                    vstd::math::min(vstd::math::max(width as int, 1), shape.columns as int) as usize,
                    backfill, cell),
                None => *final(self) == *old(self) && final(occupied)@ == old(occupied)@,
            },
        no_unwind
    ))]
    fn try_place_with<C: ZeroCounts, S: BitmapStorage>(
        &mut self, occupied: &mut Vec<u64>, shape: grid_state::PackedShape, height: u16, width: u16,
        backfill: bool,
    ) -> Option<(usize, usize)> {
        grid_state::charge_height(self.rows as u64, height, shape.row_budget)?;
        let h = if height == 0 { 1 } else { height as usize };
        let w = if width == 0 { 1 } else { width as usize };
        let w = if w < shape.columns { w } else { shape.columns };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(self.rows + h <= shape.row_budget);
            assert(shape.row_budget > 0);
            vstd::arithmetic::mul::lemma_mul_inequality(self.rows + h + 1,
                shape.row_budget + 1, shape.stride as int);
        }
        self.place::<C, S>(occupied, shape.columns, shape.stride, h, w, backfill)
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(cell =>
        requires
            stride>0, 1<=w<=columns<=stride*64, h>0,
            old(self).first_row<=old(self).rows, old(self).rows+h+1<=usize::MAX,
            (old(self).rows+h+1)*stride<=(isize::MAX as int)/8,
            (old(self).rows+h+1)*stride<=grid_state::MAX_PACKED_WORDS,
            (old(self).rows-old(self).first_row)*stride == old(occupied).len(),
            backfill ==> old(self).first_row==0 && valid_limits(old(self).limits, old(self).rows as int, columns as int),
            !backfill ==>
                old(self).first_row <= old(self).forward.0 <= old(self).rows
                && old(self).forward.1 <= columns
                && (old(self).forward.0 == old(self).rows ==> old(self).forward.1 == 0),
        ensures match cell {
            Some(cell) => span_step(*old(self),old(occupied)@,*final(self),final(occupied)@,
                columns,stride,h,w,backfill,cell),
            None => *final(self) == *old(self) && final(occupied)@ == old(occupied)@,
        }, final(self).rows <= old(self).rows + h,
        no_unwind
    ))]
    fn place<C: ZeroCounts, S: BitmapStorage>(&mut self, occupied: &mut Vec<u64>, columns: usize, stride: usize, h: usize, w: usize,
        backfill: bool) -> Option<(usize, usize)>
    {
        let rows = self.rows - self.first_row;
        let mem = occupied.as_slice();
        let (relative, col) = if backfill {
            let (row, col) = self.limits[cache_index(h)][cache_index(w)];
            let start = (row as usize, col as usize);
            #[cfg(verus_keep_ghost)]
            proof! { assert((start.0 as int,start.1 as int)==span_start(self.first_row,self.forward,self.limits,h,w,backfill)); }
            // Crowded rows can amortize the pairwise occupancy scan. Keep
            // tall spans on the early-collision path.
            if rows >= 8 && stride > 1 && stride <= usize::MAX / 64 && h <= 16 && w <= 16 {
                #[cfg(verus_keep_ghost)]
                proof! {
                    vstd::arithmetic::mul::lemma_mul_inequality(rows+1,self.rows+h+1,stride as int);
                    assert(rows*stride + stride == (rows+1)*stride) by(nonlinear_arith);
                }
                grid_multiword::find_grid_cell::<C>(mem, columns, stride, rows, start, h, w)
            } else {
                find_grid_cell_with_counts::<C>(mem, columns, stride, rows, start, h, w)
            }
        } else {
            let start = (self.forward.0 - self.first_row, self.forward.1);
            #[cfg(verus_keep_ghost)]
            proof! { assert((start.0 as int,start.1 as int)==span_start(self.first_row,self.forward,self.limits,h,w,backfill)); }
            find_grid_cell_with_counts::<C>(mem, columns, stride, rows, start, h, w)
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let cursor = span_start(self.first_row, self.forward, self.limits, h, w, backfill);
            if backfill {
                let i = vstd::math::min(h as int, CACHED_SPANS as int) - 1;
                let j = vstd::math::min(w as int, CACHED_SPANS as int) - 1;
                assert(self.limits[i][j].0 < rows || cursor == (0int, 0int));
            }
            first_fit_stays_within_rows(mem@, stride as int, rows as int,
                columns as int, h as int, w as int, cursor, (relative as int, col as int));
        }
        let row = self.first_row + relative;
        let end = row + h;
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::arithmetic::mul::lemma_mul_inequality(end-self.first_row,old(self).rows+h+1,stride as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                occupied.len() as int, stride as int, self.rows-self.first_row, 0,
            );
        }
        if !place_span::<S>(occupied, stride, relative, end - self.first_row, col, w) {
            return None;
        }
        if self.rows < end { self.rows = end; }

        if backfill {
            if h <= CACHED_SPANS && w <= CACHED_SPANS {
                self.limits[h - 1][w - 1] = cache_edge(row, col + w);
            }
        } else {
            self.forward = (row, col + w);
            if relative >= self.rows - row {
                #[cfg(verus_keep_ghost)]
                proof! {
                    vstd::arithmetic::mul::lemma_mul_inequality(relative as int,self.rows-self.first_row,stride as int);
                    physical_suffix(occupied@,stride as int,relative as int);
                }
                S::discard_prefix(occupied, relative * stride);
                self.first_row = row;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            span_cursor_length(old(self).first_row as int,self.first_row as int,self.rows as int,
                old(self).rows as int,end as int,stride as int);
            if self.first_row==old(self).first_row { suffix_zero(packed(occupied@,stride as int)); }
        }
        Some((row, col))
    }
}

/// Tally cross spans before entering the packed path when the cached child
/// count cannot establish a cheaper worst-case bound.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires budget <= grid_state::MAX_PACKED_WORDS,
        next.is_some() ==> source.live(next.unwrap()),
    no_unwind
))]
pub(crate) fn spans_fit<I: Inputs>(source: &I, mut next: Option<I::Id>, budget: u64) -> bool {
    let mut height = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant height <= budget, budget <= grid_state::MAX_PACKED_WORDS,
            next.is_some() ==> source.live(next.unwrap()),
        decreases source.remaining(next),
    ))]
    while let Some(child) = next {
        let (following, span) = source.inspect(child);
        next = following;
        if let Some((cross, _)) = span {
            let Some(total) = grid_state::charge_height(height, cross, budget) else {
                return false;
            };
            height = total;
        }
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(rows =>
    requires shape.valid(), old(scratch).len() == 0,
        first.is_some() ==> old(source).live(first.unwrap()),
    ensures grid_sparse::same_items(old(source), final(source)),
        grid_sparse::extends_writes(old(source).cell_writes(), final(source).cell_writes()),
        rows.is_some() ==> grid_sparse::writes_run(old(source), final(source), first),
        rows.is_some() ==> grid_sparse::complete_writes(final(source).cell_writes(),
            grid_sparse::placement_ids(old(source).ordered_items(), first, old(source).remaining(first))),
        match rows {
            Some(lines) => {
                let result = frame::canonical_run(old(source).ordered_items(), first, old(source).remaining(first),
                    frame::empty_grid(), shape.columns, backfill);
                lines as int == result.0.rows && final(source).cell_writes() == old(source).cell_writes() + result.1
            }
            None => true,
        },
    no_unwind
))]
fn assign_with<I: Inputs, C: ZeroCounts, S: BitmapStorage>(source: &mut I, scratch: &mut Vec<u64>,
    first: Option<I::Id>, count: usize, shape: grid_state::PackedShape, backfill: bool,
) -> Option<usize> {
    if backfill {
        // Each in-flow child occupies at least one cell, including children with spans.
        let words = grid_state::backfill_reserve_words(count, shape.columns, shape.stride);
        let _ = try_reserve_bitmap_with::<S>(scratch, words);
    }
    let mut cursor = new_span_cursor();
    let mut next = first;
    #[cfg(verus_keep_ghost)]
    let mut canonical = frame::start_canonical_grid();
    #[cfg(verus_keep_ghost)]
    proof! {
        let snapshot = frame::Snapshot { cursor, occupied: scratch@ };
        assert(snapshot.empty());
        frame::packed_represents_empty(snapshot, frame::packed_layout(shape, backfill));
        assert(scratch@ =~= Seq::<u64>::empty());
        let log = source.cell_writes();
        assert(log.take(log.len() as int) =~= log);
        assert(grid_sparse::written_ids(log.skip(log.len() as int)) =~= Seq::<I::Id>::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant shape.valid(), cursor.valid(scratch@, shape, backfill),
            grid_sparse::same_items(old(source), source),
            next.is_some() ==> source.live(next.unwrap()),
            grid_sparse::extends_writes(old(source).cell_writes(), source.cell_writes()),
            grid_sparse::written_ids(source.cell_writes().skip(old(source).cell_writes().len() as int))
                + grid_sparse::placement_ids(source.ordered_items(), next, source.remaining(next))
                == grid_sparse::placement_ids(old(source).ordered_items(), first, old(source).remaining(first)),
            frame::packed_represents(frame::Snapshot { cursor, occupied: scratch@ },
                frame::packed_layout(shape, backfill), canonical@),
            ({
                let tail = frame::canonical_run(source.ordered_items(), next, source.remaining(next), canonical@, shape.columns, backfill);
                let expected = frame::canonical_run(old(source).ordered_items(), first, old(source).remaining(first),
                    frame::empty_grid(), shape.columns, backfill);
                tail.0 == expected.0 && source.cell_writes() + tail.1 == old(source).cell_writes() + expected.1
            }),
        decreases source.remaining(next),
    ))]
    loop {
        let Some(child) = next else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(grid_sparse::placement_ids(source.ordered_items(), next, source.remaining(next))
                    == Seq::<I::Id>::empty());
                frame::canonical_run_end(source.ordered_items(), source.remaining(next), canonical@, shape.columns, backfill);
                assert(source.cell_writes() + Seq::<(I::Id, (u128, usize))>::empty() =~= source.cell_writes());
            }
            return Some(cursor.rows);
        };
        let (following, span) = source.inspect(child);
        #[cfg(verus_keep_ghost)]
        proof! {
            frame::canonical_run_step(source.ordered_items(), child, source.remaining(next), canonical@, shape.columns, backfill);
        }
        next = following;
        if let Some((height, width)) = span {
            #[cfg(verus_keep_ghost)]
            let before = frame::save_packed(&cursor, scratch);
            let Some((row, col)) = cursor.try_place_with::<C, S>(scratch, shape, height, width, backfill) else {
                return None;
            };
            #[cfg(verus_keep_ghost)]
            {
                let after = frame::save_packed(&cursor, scratch);
                canonical = frame::grow_canonical_grid(canonical, before, after, shape, backfill, height, width, (row, col));
            }
            #[cfg(verus_keep_ghost)]
            proof! { grid_sparse::write_keeps_prefix(old(source).cell_writes(), source.cell_writes(), child, (row as u128, col)); }
            source.publish(child, (row as u128, col));
        }
    }
}

/// The scratch vector stays empty between searches. Its retained capacity is
/// a storage optimization, independent of the published cell words.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait GridBuffers: Inputs {
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.first_item(), no_unwind))]
    fn first_child(&self) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(words =>
        ensures words.len() == 0, grid_sparse::same_items(old(self), final(self)),
            final(self).cell_writes() == old(self).cell_writes(),
        no_unwind
    ))]
    fn take_bitmap(&mut self) -> Vec<u64>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires words.len() == 0,
        ensures grid_sparse::same_items(old(self), final(self)),
            final(self).cell_writes() == old(self).cell_writes(),
        no_unwind
    ))]
    fn return_bitmap(&mut self, words: Vec<u64>);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum GridRows {
    Narrow(usize),
    Wide(u128),
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn encoded_grid_rows(rows: int) -> GridRows {
    if rows <= usize::MAX as int { GridRows::Narrow(rows as usize) } else { GridRows::Wide(rows as u128) }
}

pub(crate) open spec fn spanned_result<I>(items: grid_sparse::GridItems<I>, first: Option<I>,
    remaining: nat, columns: usize, backfill: bool,
) -> (GridRows, grid_sparse::CellWrites<I>) {
    let result = frame::canonical_run(items, first, remaining, frame::empty_grid(), columns, backfill);
    (encoded_grid_rows(result.0.rows), result.1)
}

/// The rows and last cell writes of the native dispatch. Scratch capacity
/// can change earlier provisional writes but cannot change this result.
pub(crate) open spec fn assignment_result<I>(items: grid_sparse::GridItems<I>, first: Option<I>,
    remaining: nat, columns: usize, count: u32, spans: bool, backfill: bool,
) -> (GridRows, grid_sparse::CellWrites<I>) {
    match grid_state::assignment_path(columns, count as usize, spans) {
        grid_state::AssignmentPath::Sequential => {
            let result = sequential_run(items, first, remaining, 0, 0, columns);
            (GridRows::Narrow(result.0), result.1)
        }
        grid_state::AssignmentPath::OneRow => {
            let result = one_row_run(items, first, remaining, 0, 0, columns);
            match result.0 {
                Some(rows) => (GridRows::Narrow(rows), result.1),
                None => spanned_result(items, first, remaining, columns, backfill),
            }
        }
        grid_state::AssignmentPath::Search => spanned_result(items, first, remaining, columns, backfill),
    }
}

pub(crate) open spec fn assignment_published<I: grid_sparse::InputModel>(before: &I, after: &I,
    columns: usize, count: u32, spans: bool, backfill: bool, rows: GridRows,
) -> bool {
    let first = before.first_item();
    let result = assignment_result(before.ordered_items(), first, before.remaining(first), columns, count, spans, backfill);
    &&& rows == result.0
    &&& result.1.len() <= after.cell_writes().len()
    &&& after.cell_writes().skip(after.cell_writes().len() - result.1.len()) == result.1
    &&& match grid_state::assignment_path(columns, count as usize, spans) {
        grid_state::AssignmentPath::Sequential => after.cell_writes() == before.cell_writes() + result.1,
        grid_state::AssignmentPath::OneRow
            if one_row_run(before.ordered_items(), first, before.remaining(first), 0, 0, columns).0.is_some()
            => after.cell_writes() == before.cell_writes() + result.1,
        _ => true,
    }
}

closed spec fn spanned_output<I: grid_sparse::InputModel>(before: &I, after: &I,
    columns: usize, backfill: bool, rows: GridRows,
) -> bool {
    let first = before.first_item();
    let result = spanned_result(before.ordered_items(), first, before.remaining(first), columns, backfill);
    &&& rows == result.0
    &&& result.1.len() <= after.cell_writes().len()
    &&& after.cell_writes().skip(after.cell_writes().len() - result.1.len()) == result.1
}

fn save_grid_writes<I: grid_sparse::InputModel>(source: &I) -> (saved: Ghost<grid_sparse::CellWrites<I::Id>>)
    ensures saved@ == source.cell_writes(),
    no_unwind
{
    Ghost(source.cell_writes())
}

proof fn retain_assignment_suffix<I>(before: grid_sparse::CellWrites<I>, added: grid_sparse::CellWrites<I>)
    ensures (before + added).skip((before + added).len() - added.len()) == added,
{
    assert((before + added).skip(before.len() as int) =~= added);
}

}

impl GridRows {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns encoded_grid_rows(rows as int), no_unwind))]
    fn from_wide(rows: u128) -> Self {
        if rows <= usize::MAX as u128 { Self::Narrow(rows as usize) } else { Self::Wide(rows) }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn as_float(self) -> f32 {
        match self { Self::Narrow(rows) => rows as f32, Self::Wide(rows) => rows as f32 }
    }
}

#[cfg(not(verus_keep_ghost))]
#[inline]
pub(crate) fn assign_grid<I: GridBuffers>(
    source: &mut I, columns: usize, count: u32, spans: bool, backfill: bool,
) -> GridRows {
    assign_grid_with::<I, grid_words::IntrinsicZeroCounts, VecBitmap, RustVec>(
        source, columns, count, spans, backfill,
    )
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(rows =>
    requires columns > 0, old(source).first_item().is_some() ==> old(source).live(old(source).first_item().unwrap()),
        old(source).remaining_placements(old(source).first_item()) <= capacity_limit::<grid_sparse::Occupied>(),
    ensures grid_sparse::same_items(old(source), final(source)),
        assignment_published(old(source), final(source), columns, count, spans, backfill, rows),
    no_unwind
))]
fn assign_grid_with<I: GridBuffers, C: ZeroCounts, B: BitmapStorage, M: CapacityMemory + VecMemory>(
    source: &mut I, columns: usize, count: u32, spans: bool, backfill: bool,
) -> GridRows {
    use grid_state::AssignmentPath;
    match grid_state::assignment_path(columns, count as usize, spans) {
        AssignmentPath::Sequential => {
            let first = source.first_child();
            let rows = assign_sequential(source, first, columns);
            #[cfg(verus_keep_ghost)]
            proof! {
                let result = sequential_run(old(source).ordered_items(), first, old(source).remaining(first), 0, 0, columns);
                retain_assignment_suffix(old(source).cell_writes(), result.1);
            }
            return GridRows::Narrow(rows);
        }
        AssignmentPath::OneRow => {
            let first = source.first_child();
            if let Some(rows) = assign_one_row(source, first, columns) {
                #[cfg(verus_keep_ghost)]
                proof! {
                    let result = one_row_run(old(source).ordered_items(), first, old(source).remaining(first), 0, 0, columns);
                    retain_assignment_suffix(old(source).cell_writes(), result.1);
                }
                return GridRows::Narrow(rows);
            }
        }
        AssignmentPath::Search => {}
    }
    let rows = assign_spans::<I, C, B, M>(source, columns, count, backfill);
    #[cfg(verus_keep_ghost)]
    proof! { reveal(spanned_output); }
    rows
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(rows =>
    requires columns > 0, old(source).first_item().is_some() ==> old(source).live(old(source).first_item().unwrap()),
        old(source).remaining_placements(old(source).first_item()) <= capacity_limit::<grid_sparse::Occupied>(),
    ensures grid_sparse::same_items(old(source), final(source)),
        spanned_output(old(source), final(source), columns, backfill, rows),
    no_unwind
))]
fn assign_spans<I: GridBuffers, C: ZeroCounts, B: BitmapStorage, M: CapacityMemory + VecMemory>(
    source: &mut I, columns: usize, count: u32, backfill: bool,
) -> GridRows {
    let shape = grid_state::packed_shape(columns);
    if !grid_state::worst_height_fits(count, shape.row_budget) {
        let first = source.first_child();
        if !spans_fit(source, first, shape.row_budget) {
            let first = source.first_child();
            let rows = grid_sparse::assign::<I, M>(source, first, columns, backfill);
            #[cfg(verus_keep_ghost)]
            proof! {
                let result = frame::canonical_run(old(source).ordered_items(), first, old(source).remaining(first),
                    frame::empty_grid(), columns, backfill);
                retain_assignment_suffix(old(source).cell_writes(), result.1);
            }
            return GridRows::from_wide(rows);
        }
    }
    let mut bitmap = source.take_bitmap();
    let first = source.first_child();
    #[cfg(verus_keep_ghost)]
    let before_packed = save_grid_writes(source);
    let rows = assign_with::<I, C, B>(source, &mut bitmap, first, count as usize, shape, backfill);
    M::clear(&mut bitmap);
    source.return_bitmap(bitmap);
    match rows {
        Some(rows) => {
            #[cfg(verus_keep_ghost)]
            proof! {
                let result = frame::canonical_run(old(source).ordered_items(), first, old(source).remaining(first),
                    frame::empty_grid(), columns, backfill);
                retain_assignment_suffix(before_packed@, result.1);
            }
            GridRows::Narrow(rows)
        }
        None => {
            let first = source.first_child();
            #[cfg(verus_keep_ghost)]
            let before_sparse = save_grid_writes(source);
            let rows = grid_sparse::assign::<I, M>(source, first, columns, backfill);
            #[cfg(verus_keep_ghost)]
            proof! {
                let result = frame::canonical_run(old(source).ordered_items(), first, old(source).remaining(first),
                    frame::empty_grid(), columns, backfill);
                retain_assignment_suffix(before_sparse@, result.1);
            }
            GridRows::from_wide(rows)
        }
    }
}

#[cfg(all(test, not(verus_keep_ghost)))]
mod tests {
    use super::*;

    struct RefuseGrowth;

    impl BitmapCapacity for RefuseGrowth {}

    impl BitmapStorage for RefuseGrowth {
        fn capacity(words: &Vec<u64>) -> usize { words.len() }
        fn try_reserve_exact(_: &mut Vec<u64>, _: usize) -> bool { false }
        fn resize_zeroed(_: &mut Vec<u64>, _: usize) { unreachable!() }
        fn discard_prefix(_: &mut Vec<u64>, _: usize) { unreachable!() }
    }

    #[test]
    fn refused_packed_growth_preserves_the_cursor_and_board() {
        let shape = grid_state::packed_shape(2);
        let mut cursor = new_span_cursor();
        let mut occupied = Vec::new();
        assert_eq!(cursor.try_place(&mut occupied, shape, 1, 2, true), Some((0, 0)));
        let first_bitmap = occupied.clone();
        let first_limits = cursor.limits;

        assert_eq!(cursor.try_place_with::<grid_words::IntrinsicZeroCounts, RefuseGrowth>(
            &mut occupied, shape, 1, 1, true,
        ), None);
        assert_eq!(occupied, first_bitmap);
        assert_eq!((cursor.rows, cursor.first_row, cursor.forward), (1, 0, (0, 0)));
        assert_eq!(cursor.limits, first_limits);
        assert_eq!(cursor.try_place(&mut occupied, shape, 1, 1, true), Some((1, 0)));
    }

    struct FixedCapacityBitmap;

    impl BitmapCapacity for FixedCapacityBitmap {}

    impl BitmapStorage for FixedCapacityBitmap {
        fn capacity(words: &Vec<u64>) -> usize { words.capacity() }
        fn try_reserve_exact(_: &mut Vec<u64>, _: usize) -> bool { false }
        fn resize_zeroed(words: &mut Vec<u64>, len: usize) { words.resize(len, 0); }
        fn discard_prefix(words: &mut Vec<u64>, count: usize) { words.drain(..count); }
    }

    struct GridProbe {
        bitmap: Vec<u64>,
        writes: Vec<(usize, (u128, usize))>,
    }

    impl grid_sparse::InputModel for GridProbe {
        type Id = usize;
    }

    impl Inputs for GridProbe {
        fn inspect(&self, child: usize) -> (Option<usize>, Option<(u16, u16)>) {
            let spans = [Some((1, 3)), None, Some((1, 2)), Some((2, 1))];
            let next = child + 1;
            ((next < spans.len()).then_some(next), spans[child])
        }

        fn publish(&mut self, child: usize, cell: (u128, usize)) {
            self.writes.push((child, cell));
        }
    }

    impl GridBuffers for GridProbe {
        fn first_child(&self) -> Option<usize> { Some(0) }

        fn take_bitmap(&mut self) -> Vec<u64> {
            std::mem::take(&mut self.bitmap)
        }

        fn return_bitmap(&mut self, bitmap: Vec<u64>) {
            self.bitmap = bitmap;
        }
    }

    #[test]
    fn sparse_retry_rewrites_the_full_grid_after_packed_writes() {
        for backfill in [false, true] {
            let mut probe = GridProbe { bitmap: Vec::with_capacity(1), writes: Vec::new() };
            let rows = assign_grid_with::<_, grid_words::IntrinsicZeroCounts, FixedCapacityBitmap, RustVec>(
                &mut probe, 3, 3, true, backfill,
            );
            assert!(matches!(rows, GridRows::Narrow(3)));
            assert_eq!(probe.writes, [(0, (0, 0)), (0, (0, 0)), (2, (1, 0)), (3, (1, 2))]);
            assert!(probe.bitmap.is_empty());
            assert_eq!(probe.bitmap.capacity(), 1);
        }
    }
}
