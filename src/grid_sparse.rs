//! Rectangle-based first-fit search for grids with a large packed footprint.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Occupied {
    pub rows: (u64, u64),
    pub cols: (usize, usize),
}

/// At a collision, the occupied rectangle's right edge is the earliest
/// possible fit on this row. Its bottom edge bounds that same skip on later rows.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires row < bottom, col < right, row <= max_row,
        forall |i:int| 0 <= i < occupied.len() ==> #[trigger] valid_rectangle(occupied@[i], max_row),
    ensures col <= result.0, row <= result.1 <= max_row,
        result.0 == col ==> clear_at(occupied@, row as int, col as int, bottom-row, right-col),
        result.0 > col ==> row < result.1 && blocked_until(occupied@,
            bottom-row, right-col, row as int, result.1 as int, col as int, result.0 as int),
    no_unwind
))]
fn probe(occupied: &[Occupied], row: u64, col: usize, bottom: u64, right: usize, max_row: u64) -> (usize, u64) {
    let mut next = col;
    let mut end = max_row;
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= occupied.len(), col <= next, row <= end <= max_row,
            row < bottom, col < right,
            forall |j:int| 0 <= j < occupied.len() ==> #[trigger] valid_rectangle(occupied@[j], max_row),
            next == col ==> end == max_row
                && clear_at(occupied@.take(i as int), row as int, col as int, bottom-row, right-col),
            next > col ==> row < end,
            blocked_until(occupied@.take(i as int),
                bottom-row, right-col, row as int, end as int, col as int, next as int),
        decreases occupied.len() - i,
    ))]
    while i < occupied.len() {
        let rect = occupied[i];
        if row < rect.rows.1 && rect.rows.0 < bottom && col < rect.cols.1 && rect.cols.0 < right {
            #[cfg(verus_keep_ghost)]
            let (old_next, old_end) = (next, end);
            if next < rect.cols.1 { next = rect.cols.1; }
            if end > rect.rows.1 { end = rect.rows.1; }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(valid_rectangle(rect,max_row));
                accept_collision(occupied@, i as int, row as int, col as int, bottom as int,
                    right as int, old_next as int, old_end as int, next as int, end as int);
            }
        } else {
            #[cfg(verus_keep_ghost)]
            proof! {
                reject_collision(occupied@, i as int, row as int, col as int, bottom as int,
                    right as int, next as int, end as int);
            }
        }
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(occupied@.take(i as int) =~= occupied@); }
    (next, end)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires 1 <= w <= columns, h > 0, max_row + h <= u64::MAX,
        start.0 <= max_row, start.0 == max_row ==> start.1 == 0,
        forall |i:int| 0 <= i < occupied.len() ==> #[trigger] valid_rectangle(occupied@[i], max_row),
    ensures result.0 <= max_row,
        first_fit(sparse_board(occupied@), columns as int, h as int, w as int,
            (start.0 as int, start.1 as int), (result.0 as int, result.1 as int)),
    no_unwind
))]
pub fn find_cell(occupied: &[Occupied], columns: usize, start: (u64, usize), max_row: u64, h: u64, w: usize) -> (u64, usize) {
    let (mut row, mut first) = start;
    let last = columns - w;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= max_row, row == max_row ==> first == 0, last == columns-w,
            h>0, w>0, max_row+h<=u64::MAX,
            forall |j:int| 0 <= j < occupied.len() ==> #[trigger] valid_rectangle(occupied@[j], max_row),
            !before((row as int, first as int), (start.0 as int, start.1 as int)),
            sparse_passed(occupied@, columns as int, h as int, w as int,
                (start.0 as int, start.1 as int), (row as int, first as int)),
        decreases max_row-row,
    ))]
    loop {
        let mut col = first;
        let mut next_row = max_row;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant row <= next_row <= max_row, first <= col, last == columns-w,
                h>0, w>0, max_row+h<=u64::MAX,
                forall |j:int| 0 <= j < occupied.len() ==> #[trigger] valid_rectangle(occupied@[j], max_row),
                !before((row as int, first as int), (start.0 as int, start.1 as int)),
                sparse_passed(occupied@, columns as int, h as int, w as int,
                    (start.0 as int, start.1 as int), (row as int, first as int)),
                col == first ==> next_row == max_row,
                col > first ==> row < next_row,
                blocked_until(occupied@, h as int, w as int, row as int, next_row as int, first as int, col as int),
            decreases usize::MAX-col,
        ))]
        while col <= last {
            let (next, end) = probe(occupied, row, col, row + h, col + w, max_row);
            if next == col {
                #[cfg(verus_keep_ghost)]
                proof! {
                    found_cell(occupied@, columns as int, h as int, w as int,
                        (start.0 as int,start.1 as int), (row as int,first as int), col as int, next_row as int);
                    sparse_is_first_fit(occupied@, max_row, columns as int, h as int, w as int,
                        (start.0 as int,start.1 as int), (row as int,col as int));
                }
                return (row, col);
            }
            #[cfg(verus_keep_ghost)]
            let previous_row = next_row;
            if next_row > end { next_row = end; }
            #[cfg(verus_keep_ghost)]
            proof! {
                merge_skips(occupied@, h as int, w as int, row as int, previous_row as int,
                    end as int, next_row as int, first as int, col as int, next as int);
            }
            col = next;
        }
        // The forward cursor may start partway across its first row. Only a
        // complete row can skip to the earliest blocker expiration.
        let resume = if first == 0 { next_row } else { row + 1 };
        #[cfg(verus_keep_ghost)]
        proof! {
            exhausted_row(occupied@, columns as int, h as int, w as int,
                (start.0 as int,start.1 as int), (row as int,first as int),
                col as int, next_row as int, resume as int);
        }
        row = resume;
        first = 0;
    }
}
