// The production row-major scanner and its checked loop invariants.
#![allow(unexpected_cfgs)]

use super::grid_words;

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
))]
fn blocked_pair(rows: &[u64], height: usize) -> (u64, u64) {
    // Adjacent windows differ only at their boundary rows.
    let middle = &rows[1..height];
    let shared = blocked_columns(middle);
    let left = grid_words::union(shared, rows[0]);
    let right = grid_words::union(shared, rows[height]);
    #[cfg(verus_keep_ghost)]
    proof! {
        paired_window_union(rows@, middle@, height as int, shared, left, right);
    }
    (left, right)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 0 < stride, n_lines * stride == mem.len(), line < n_lines,
        h > 0, w > 0, pos + w <= usize::MAX, pos + w <= stride * 64,
    ensures match result {
        None => fits(packed(mem@,stride as int),(line as int,pos as int),h as int,w as int),
        Some(next) => pos < next && exists |r:int,k:int| line <= r < line+h && pos<=k<pos+w
            && k<next && #[trigger] occupied_run(packed(mem@,stride as int),r,k,next as int),
    },
))]
fn probe_rows(mem: &[u64], stride: usize, n_lines: usize, line: usize, pos: usize, h: usize, w: usize) -> Option<usize> {
    let end = pos + (w - 1);
    let first = pos / 64;
    let last = end / 64;
    let start_mask = grid_words::word_range((pos % 64) as u32, 63);
    let end_mask = grid_words::word_range(0, (end % 64) as u32);
    let stop = line.saturating_add(h).min(n_lines);
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
        let row = &mem[offset..offset + stride];
        if let Some((word, delta)) = grid_words::probe_row(row, first, last, start_mask, end_mask) {
            #[cfg(verus_keep_ghost)]
            proof! {
                collided_row(mem@,stride as int,r as int,pos as int,w as int,row@,
                    first as int,last as int,start_mask,end_mask,word as int,delta);
            }
            let next = (word * 64).saturating_add(delta as usize);
            #[cfg(verus_keep_ghost)]
            proof! {
                let b=packed(mem@,stride as int);
                let end = word*64+delta;
                let k=choose |k:int| pos<=k<pos+w && k<end && #[trigger] occupied_run(b,r as int,k,end);
                assert(occupied_run(b,r as int,k,next as int));
                assert(k < next && pos < next);
                assert(exists |row:int,col:int| line <= row < line+h && pos <= col < pos+w
                    && col < next && #[trigger] occupied_run(b,row,col,next as int));
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
))]
pub fn find_grid_cell(mem: &[u64], columns: usize, stride: usize, n_lines: usize,
    start: (usize, usize), h: usize, w: usize) -> (usize, usize) {
    // Resolve the row representation once, so the multiword scanner has no
    // register pressure from the one-word lookahead.
    if stride == 1 {
        find_grid_cell_impl::<true>(mem, columns, stride, n_lines, start, h, w)
    } else {
        find_grid_cell_impl::<false>(mem, columns, stride, n_lines, start, h, w)
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
))]
fn find_grid_cell_impl<const ONE_WORD: bool>(mem: &[u64], columns: usize, stride: usize, n_lines: usize,
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
                let pair = &mem[line..line + h + 1];
                let (first, second) = blocked_pair(pair, h);
                let (left, right) = grid_words::first_pair_starts((!first, !second), w as u32);
                #[cfg(verus_keep_ghost)]
                proof! {
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
            let rows = &mem[line..line.saturating_add(h).min(n_lines)];
            let blocked = blocked_columns(rows);
            let next = grid_words::first_word_start(blocked, pos as u32, w as u32) as usize;
            #[cfg(verus_keep_ghost)]
            proof! {
                one_word_open(mem@,line as int,h as int,rows@,blocked);
                single_word_first_fit(packed(mem@,1),columns as int,h as int,w as int,
                    (start.0 as int,start.1 as int),(line as int,pos as int),!blocked,next as int);
            }
            if next <= last_start { return (line, next); }
            line += 1;
            pos = 0;
        } else if let Some(next) = probe_rows(mem, stride, n_lines, line, pos, h, w) {
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

/// Occupy an entire rectangle. Each supplied row is a complete word-aligned
/// row, and the same column range is marked on all of them.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires stride>0, old(rows).len()%stride==0, w>0, pos+w<=usize::MAX, pos+w<=stride*64,
    ensures final(rows)@.len()==old(rows)@.len(),
        forall |i:int,j:u32| 0<=i<final(rows)@.len() && j<64 ==> #[trigger] bit(final(rows)@[i],j as int)
            == (bit(old(rows)@[i],j as int) || pos <= (i%(stride as int))*64+j < pos+w),
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
        let row = &mut rows[i..i + stride];
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
))]
pub fn cache_index(span: usize) -> usize {
    span.min(CACHED_SPANS) - 1
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(key =>
    ensures !before((row as int,edge as int),(key.0 as int,key.1 as int)),
        key.0==vstd::math::min(row as int,u16::MAX as int),
        key.1==vstd::math::min(edge as int,u16::MAX as int),
))]
pub fn cache_edge(row: usize, edge: usize) -> (u16, u16) {
    (row.min(u16::MAX as usize) as u16, edge.min(u16::MAX as usize) as u16)
}

/// The next row-major cursor for the span-free grid.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires col<columns, row<usize::MAX,
    ensures (next.0 as int,next.1 as int)==if col+1==columns {
        (row+1,0int)
    } else { (row as int,col+1) },
))]
pub fn next_cell(row: usize, col: usize, columns: usize) -> (usize, usize) {
    if col + 1 == columns { (row + 1, 0) } else { (row, col + 1) }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires prefix <= old(occupied).len(),
    ensures final(occupied)@ == old(occupied)@.subrange(prefix as int, old(occupied)@.len() as int),
))]
pub fn compact_rows(occupied: &mut Vec<u64>, prefix: usize) {
    occupied.copy_within(prefix.., 0);
    occupied.truncate(occupied.len() - prefix);
}

/// Extend zero occupancy through the last row of a rectangle and mark it.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires stride>0, first < end, end*stride<=usize::MAX, old(occupied).len()%stride==0,
        w>0, pos+w<=usize::MAX, pos+w<=stride*64,
    ensures final(occupied)@.len()==vstd::math::max(old(occupied)@.len() as int,end*stride),
        packed(final(occupied)@,stride as int)==place(packed(old(occupied)@,stride as int),
            (first as int,pos as int),end-first,w as int),
))]
pub fn place_span(occupied: &mut Vec<u64>, stride: usize, first: usize, end: usize, pos: usize, w: usize) {
    #[cfg(verus_keep_ghost)]
    proof! { row_block_bounds(first as int,stride as int,end as int); }
    let begin = first * stride;
    let limit = end * stride;
    if limit > occupied.len() {
        occupied.resize(limit, 0);
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
    occupy_span(&mut mem[begin..limit], stride, pos, w);
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
))]
pub const fn new_span_cursor() -> SpanCursor {
    SpanCursor { rows: 0, first_row: 0, forward: (0, 0), limits: [[(0, 0); CACHED_SPANS]; CACHED_SPANS] }
}

impl SpanCursor {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(cell =>
        requires
            stride>0, 1<=w<=columns<=stride*64, h>0,
            old(self).first_row<=old(self).rows, old(self).rows+h+1<=usize::MAX,
            (old(self).rows+h+1)*stride<=usize::MAX,
            (old(self).rows-old(self).first_row)*stride == old(occupied).len(),
            backfill ==> old(self).first_row==0 && valid_limits(old(self).limits, old(self).rows as int, columns as int),
            !backfill ==> old(self).first_row<=old(self).forward.0<=old(self).rows && old(self).forward.1<=columns,
        ensures span_step(*old(self),old(occupied)@,*final(self),final(occupied)@,
            columns,stride,h,w,backfill,cell),
    ))]
    pub fn place(&mut self, occupied: &mut Vec<u64>, columns: usize, stride: usize, h: usize, w: usize,
        backfill: bool) -> (usize, usize)
    {
        let rows = self.rows - self.first_row;
        let mem = occupied.as_slice();
        let (relative, col) = if backfill {
            let (row, col) = self.limits[cache_index(h)][cache_index(w)];
            let start = (usize::from(row), usize::from(col));
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
                grid_multiword::find_grid_cell(mem, columns, stride, rows, start, h, w)
            } else {
                find_grid_cell(mem, columns, stride, rows, start, h, w)
            }
        } else {
            let start = (self.forward.0 - self.first_row, self.forward.1);
            #[cfg(verus_keep_ghost)]
            proof! { assert((start.0 as int,start.1 as int)==span_start(self.first_row,self.forward,self.limits,h,w,backfill)); }
            find_grid_cell(mem, columns, stride, rows, start, h, w)
        };
        let row = self.first_row + relative;
        let end = row + h;
        #[cfg(verus_keep_ghost)]
        proof! {
            vstd::arithmetic::mul::lemma_mul_inequality(end-self.first_row,old(self).rows+h+1,stride as int);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                occupied.len() as int, stride as int, self.rows-self.first_row, 0,
            );
        }
        place_span(occupied, stride, relative, end - self.first_row, col, w);
        self.rows = self.rows.max(end);

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
                compact_rows(occupied, relative * stride);
                self.first_row = row;
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            span_cursor_length(old(self).first_row as int,self.first_row as int,self.rows as int,
                old(self).rows as int,end as int,stride as int);
            if self.first_row==old(self).first_row { suffix_zero(packed(occupied@,stride as int)); }
        }
        (row, col)
    }
}
