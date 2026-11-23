// A row-major first-fit scan of adjacent occupancy words.
#![allow(unexpected_cfgs)]

use super::grid_words;
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Accumulate two adjacent columns of occupancy together. Their contiguous
/// loads and independent ORs let the compiler use a single vector reduction.
#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(pair =>
    requires 0 < stride, word < stride, PAIR ==> word + 1 < stride,
        line <= stop <= rows, rows * stride == mem.len(),
        mem.len() + stride <= usize::MAX,
    ensures
        row_open(packed(mem@, stride as int), line as int, stop-line, word as int, !pair[0]),
        PAIR ==> row_open(packed(mem@, stride as int), line as int, stop-line, word+1, !pair[1]),
        !PAIR ==> pair[1] == u64::MAX,
))]
fn blocked_words<const PAIR: bool>(
    mem: &[u64],
    stride: usize,
    rows: usize,
    line: usize,
    stop: usize,
    word: usize,
) -> [u64; 2] {
    let _ = rows;
    let mut pair = [0, if PAIR { 0 } else { u64::MAX }];
    #[cfg(verus_keep_ghost)]
    proof! {
        empty_word(packed(mem@, stride as int), line as int, word as int);
        if PAIR { empty_word(packed(mem@, stride as int), line as int, word+1); }
    }
    #[cfg(verus_keep_ghost)]
    proof! { vstd::arithmetic::mul::lemma_mul_inequality(line as int,rows as int,stride as int); }
    let mut r = line;
    let mut index = line * stride + word;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 0 < stride, word < stride, PAIR ==> word+1<stride,
            line <= r <= stop <= rows, rows*stride==mem.len(), mem.len()+stride<=usize::MAX,
            index == r*stride+word,
            row_open(packed(mem@, stride as int), line as int, r-line, word as int, !pair[0]),
            PAIR ==> row_open(packed(mem@, stride as int), line as int, r-line, word+1, !pair[1]),
            !PAIR ==> pair[1] == u64::MAX,
        decreases stop-r,
    ))]
    while r < stop {
        #[cfg(verus_keep_ghost)]
        proof! { row_block_bounds(r as int, stride as int, rows as int); }
        let left = grid_words::union(pair[0], mem[index]);
        let right = if PAIR {
            grid_words::union(pair[1], mem[index + 1])
        } else {
            u64::MAX
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            extend_open_word(mem@, stride as int, line as int, r as int, word as int, pair[0], left);
            if PAIR { extend_open_word(mem@, stride as int, line as int, r as int, word+1, pair[1], right); }
        }
        pair = [left, right];
        index += stride;
        r += 1;
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((r-1)*stride+stride==r*stride) by(nonlinear_arith);
        }
    }
    pair
}

/// The first opening that strictly crosses the word boundary must use
/// the free suffix on the left and the free prefix on the right.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires 1 <= span <= 16, min < 64,
    ensures
        next <= 64,
        next < 64 ==> min <= next && 64 < next+span
            && open_across(!lo, !hi, next as int, span as int),
        forall |p:int| min<=p<next && 64<p+span ==> !#[trigger] open_across(!lo,!hi,p,span as int),
))]
fn first_crossing(lo: u64, hi: u64, span: u32, min: u32) -> u32 {
    let left = lo.leading_zeros();
    let right = hi.trailing_zeros();
    let first = (64 - left).max(65 - span).max(min);
    let next = if first == 64 || span > (64 - first) + right {
        64
    } else {
        first
    };
    #[cfg(verus_keep_ghost)]
    proof! { first_crossing_from_counts(lo,hi,span,min,left,right,first,next); }
    next
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 < stride <= usize::MAX / 64, rows*stride == mem.len(),
        mem.len()+stride <= usize::MAX, line < rows, h>0, 1<=span<=16,
        columns.0<=columns.1, columns.1+span<=stride*64,
    ensures
        row_first(packed(mem@,stride as int), line as int,h as int,span as int,columns.0 as int,columns.1 as int,result),
))]
fn scan_row(
    mem: &[u64],
    stride: usize,
    rows: usize,
    line: usize,
    h: usize,
    span: u32,
    columns: (usize, usize),
) -> Option<usize> {
    let (pos, last_start) = columns;
    let stop = rows.min(line.saturating_add(h));
    let mut word = pos / 64;
    let mut min = (pos % 64) as u32;
    let mut previous: Option<u64> = None;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1<stride<=usize::MAX/64, rows*stride == mem.len(), mem.len()+stride <= usize::MAX,
            columns==(pos,last_start),
            line<rows, h>0, 1<=span<=16, pos<=last_start, last_start+span<=stride*64,
            stop==vstd::math::min(line+h, rows as int), line<=stop<=rows,
            word<=stride+1, min<64, word*64+min>=pos,
            match previous {
                None => word*64+min==pos,
                Some(v) => min==0 && word>=2 && (word-1)*64>=pos &&
                    row_open(packed(mem@,stride as int),line as int,h as int, word-1,!v),
            },
            row_passed(packed(mem@,stride as int), line as int,h as int,span as int,pos as int,last_start as int,
                if previous.is_some() { (word-1)*64+65-span } else { pos as int }),
        decreases stride+1-word,
    ))]
    while word < stride {
        let [lo, hi] = if word + 1 < stride {
            blocked_words::<true>(mem, stride, rows, line, stop, word)
        } else {
            blocked_words::<false>(mem, stride, rows, line, stop, word)
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            open_word_after_last_row(mem@,stride as int,rows as int,line as int,h as int,stop as int,word as int, !lo);
            if word+1<stride {
                open_word_after_last_row(mem@,stride as int,rows as int,line as int,h as int,stop as int,word+1, !hi);
            }
        }
        // A start in the preceding word can spill into this pair and
        // precedes any start contained in one of its two words.
        if let Some(prior) = previous {
            let cross = first_crossing(prior, lo, span, 0);
            #[cfg(verus_keep_ghost)]
            proof! {
                check_crossing(packed(mem@,stride as int),stride as int,line as int,h as int,span,
                    pos as int,last_start as int,word-1,0,!prior,!lo,cross);
            }
            if cross < 64 {
                let col = (word - 1) * 64 + cross as usize;
                return if col <= last_start { Some(col) } else { None };
            }
        }
        if word * 64 > last_start {
            return None;
        }
        let mask = grid_words::word_range(min, 63);
        let (left, right) = grid_words::first_pair_starts((!lo & mask, !hi), span);
        #[cfg(verus_keep_ghost)]
        proof! {
            check_internal(packed(mem@,stride as int),line as int,h as int,span,
                pos as int,last_start as int,word as int,min,!lo,mask,left);
        }
        if left < 64 {
            let col = word * 64 + left as usize;
            return if col <= last_start { Some(col) } else { None };
        }
        let cross = first_crossing(lo, hi, span, min);
        #[cfg(verus_keep_ghost)]
        proof! {
            if word+1==stride { assert(!hi==0) by(bit_vector) requires hi==u64::MAX; }
            check_crossing(packed(mem@,stride as int),stride as int,line as int,h as int,span,
                pos as int,last_start as int,word as int,min,!lo,!hi,cross);
        }
        if cross < 64 {
            let col = word * 64 + cross as usize;
            return if col <= last_start { Some(col) } else { None };
        }
        if word + 1 == stride {
            return None;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            assert((!hi & u64::MAX)==!hi) by(bit_vector);
            assert forall |i:u32| i<64 implies #[trigger] bit(u64::MAX,i as int) by {
                assert(((u64::MAX >> i) & 1)==1) by(bit_vector) requires i<64;
            }
            check_internal(packed(mem@,stride as int),line as int,h as int,span,
                pos as int,last_start as int,word+1,0,!hi,u64::MAX,right);
        }
        if right < 64 {
            let col = (word + 1) * 64 + right as usize;
            return if col <= last_start { Some(col) } else { None };
        }
        previous = Some(hi);
        word += 2;
        min = 0;
    }
    None
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 < stride <= usize::MAX/64, rows*stride == mem.len(), rows<usize::MAX,
        mem.len()+stride <= usize::MAX, 1<=w<=16, w<=columns<=stride*64,
        h>0, start.0<=rows, start.1<=columns,
    ensures result.0 <= rows+1,
        first_fit(packed(mem@,stride as int),columns as int,h as int,w as int,
            (start.0 as int,start.1 as int),(result.0 as int,result.1 as int)),
))]
pub(super) fn find_grid_cell(
    mem: &[u64],
    columns: usize,
    stride: usize,
    rows: usize,
    start: (usize, usize),
    h: usize,
    w: usize,
) -> (usize, usize) {
    let (mut line, mut pos) = start;
    let last_start = columns - w;
    if pos > last_start {
        #[cfg(verus_keep_ghost)]
        proof! {
            wrap_cursor(packed(mem@,stride as int),columns as int,h as int,w as int,
                (start.0 as int,start.1 as int),(line as int,pos as int));
        }
        line += 1;
        pos = 0;
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 1<stride<=usize::MAX/64, rows*stride == mem.len(), rows<usize::MAX,
            mem.len()+stride <= usize::MAX, 1<=w<=16, w<=columns<=stride*64,
            h>0, pos<=last_start, last_start==columns-w,
            line<=rows+1, !before((line as int,pos as int),(start.0 as int,start.1 as int)),
            passed(packed(mem@,stride as int),columns as int,h as int,w as int,
                (start.0 as int,start.1 as int),(line as int,pos as int)),
        decreases rows+1-line,
    ))]
    while line < rows {
        let next = scan_row(mem, stride, rows, line, h, w as u32, (pos, last_start));
        #[cfg(verus_keep_ghost)]
        proof! {
            finish_row_scan(packed(mem@,stride as int),columns as int,h as int,w as int,
                (start.0 as int,start.1 as int),(line as int,pos as int),next);
        }
        if let Some(next) = next {
            return (line, next);
        }
        line += 1;
        pos = 0;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let b=packed(mem@,stride as int);
        assert forall |q:Cell| #[trigger] b.contains(q) implies !covers((line as int,pos as int),h as int,w as int,q) by {
            if covers((line as int,pos as int),h as int,w as int,q) {
                empty_after(mem@,stride as int,rows as int,q.0,q.1);
            }
        }
    }
    (line, pos)
}

#[cfg(test)]
mod tests {
    use super::find_grid_cell;

    #[test]
    fn picks_the_first_cross_word_start_and_respects_the_legal_tail() {
        let mut occupied = [u64::MAX; 24];
        for row in occupied.chunks_exact_mut(3).take(2) {
            row[0] &= !(1 << 63);
            row[1] &= !(1 | (1 << 63));
            row[2] &= !3;
        }
        assert_eq!(find_grid_cell(&occupied, 130, 3, 8, (0, 0), 2, 2), (0, 63));
        assert_eq!(
            find_grid_cell(&occupied, 130, 3, 8, (0, 64), 2, 3),
            (0, 127)
        );
        assert_eq!(find_grid_cell(&occupied, 129, 3, 8, (0, 64), 2, 3), (8, 0));
    }
}
