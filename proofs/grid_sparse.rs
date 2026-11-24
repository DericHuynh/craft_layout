//! A rectangle conflict excludes a whole range of candidate columns and rows.
use super::*;
use grid_sparse::Occupied;
use vstd::prelude::*;

verus! {

pub open spec fn valid_rectangle(rect: Occupied, max_row: u128) -> bool {
    rect.rows.0 < rect.rows.1 <= max_row && rect.cols.0 < rect.cols.1
}

pub open spec fn overlaps(rect: Occupied, row: int, col: int, h: int, w: int) -> bool {
    row < rect.rows.1 && rect.rows.0 < row+h && col < rect.cols.1 && rect.cols.0 < col+w
}

pub open spec fn clear_at(rects: Seq<Occupied>, row: int, col: int, h: int, w: int) -> bool {
    forall |i:int| 0 <= i < rects.len() ==> !#[trigger] overlaps(rects[i], row, col, h, w)
}

pub open spec fn blocked_until(rects: Seq<Occupied>, h: int, w: int, row: int, limit: int, lo: int, hi: int) -> bool {
    forall |r:int,c:int| row <= r < limit && lo <= c < hi ==> !#[trigger] clear_at(rects, r, c, h, w)
}

pub open spec fn sparse_passed(rects: Seq<Occupied>, columns: int, h: int, w: int, start: Cell, cursor: Cell) -> bool {
    forall |p:Cell| legal(p, columns, w) && !before(p,start) && before(p,cursor)
        ==> !#[trigger] clear_at(rects, p.0, p.1, h, w)
}

pub open spec fn first_sparse_fit(rects: Seq<Occupied>, columns: int, h: int, w: int, start: Cell, result: Cell) -> bool {
    !before(result,start) && legal(result,columns,w) && clear_at(rects,result.0,result.1,h,w)
        && sparse_passed(rects,columns,h,w,start,result)
}

pub open spec fn sparse_board(rects: Seq<Occupied>) -> Board {
    ISet::new(|p:Cell| exists |i:int| 0 <= i < rects.len()
        && (#[trigger] rects[i]).rows.0 <= p.0 < rects[i].rows.1
        && rects[i].cols.0 <= p.1 < rects[i].cols.1)
}

/// The rectangle list represents the same board update as the packed
/// search, independent of the list capacity and the expired scan prefix.
pub proof fn sparse_board_adds(rects: Seq<Occupied>, rect: Occupied, cell: Cell, h: int, w: int)
    requires rect.rows.0 == cell.0, rect.rows.1 == cell.0 + h,
        rect.cols.0 == cell.1, rect.cols.1 == cell.1 + w,
    ensures sparse_board(rects.push(rect)) == place(sparse_board(rects), cell, h, w),
{
    let before = sparse_board(rects);
    let after = sparse_board(rects.push(rect));
    assert forall |p: Cell| #[trigger] after.contains(p) == place(before, cell, h, w).contains(p) by {
        if after.contains(p) {
            let i = choose |i: int| 0 <= i < rects.push(rect).len()
                && (#[trigger] rects.push(rect)[i]).rows.0 <= p.0 < rects.push(rect)[i].rows.1
                && rects.push(rect)[i].cols.0 <= p.1 < rects.push(rect)[i].cols.1;
            if i == rects.len() {
                assert(covers(cell, h, w, p));
            } else {
                assert(rects.push(rect)[i] == rects[i]);
                assert(before.contains(p));
            }
        }
        if before.contains(p) {
            let i = choose |i: int| 0 <= i < rects.len()
                && (#[trigger] rects[i]).rows.0 <= p.0 < rects[i].rows.1
                && rects[i].cols.0 <= p.1 < rects[i].cols.1;
            assert(rects.push(rect)[i] == rects[i]);
            assert(after.contains(p));
        }
        if covers(cell, h, w, p) {
            assert(rects.push(rect)[rects.len() as int] == rect);
            assert(after.contains(p));
        }
    }
    assert(after =~= place(before, cell, h, w));
}

pub open spec fn expires_before(rect: Occupied, start: Cell) -> bool {
    rect.rows.1 <= start.0 || (rect.rows.1 == start.0 + 1 && rect.cols.1 <= start.1)
}

pub proof fn expiry_keeps(rect: Occupied, prior: Cell, next: Cell)
    requires expires_before(rect, prior), !before(next, prior),
    ensures expires_before(rect, next),
{}

pub proof fn expired_prefix_preserves_first_fit(rects: Seq<Occupied>, prefix: int, columns: int,
    h: int, w: int, start: Cell, result: Cell)
    requires 0 <= prefix <= rects.len(),
        forall |i: int| 0 <= i < prefix ==> #[trigger] expires_before(rects[i], start),
        first_fit(sparse_board(rects.subrange(prefix, rects.len() as int)), columns, h, w, start, result),
    ensures first_fit(sparse_board(rects), columns, h, w, start, result),
{
    let tail = rects.subrange(prefix, rects.len() as int);
    let board = sparse_board(rects);
    let live = sparse_board(tail);
    assert forall |q: Cell| !before(q,start) implies #[trigger] board.contains(q) == live.contains(q) by {
        if board.contains(q) {
            let i = choose |i: int| 0 <= i < rects.len()
                && (#[trigger] rects[i]).rows.0 <= q.0 < rects[i].rows.1
                && rects[i].cols.0 <= q.1 < rects[i].cols.1;
            if i < prefix {
                assert(expires_before(rects[i], start));
                assert(before(q, start));
            }
            assert(i >= prefix && tail[i - prefix] == rects[i]);
        }
        if live.contains(q) {
            let i = choose |i: int| 0 <= i < tail.len()
                && (#[trigger] tail[i]).rows.0 <= q.0 < tail[i].rows.1
                && tail[i].cols.0 <= q.1 < tail[i].cols.1;
            assert(rects[i + prefix] == tail[i]);
        }
    }
    assert forall |q: Cell| #[trigger] board.contains(q) implies !covers(result,h,w,q) by {
        if covers(result,h,w,q) {
            assert(live.contains(q));
        }
    }
    assert forall |p:Cell| legal(p,columns,w) && !before(p,start) && before(p,result)
        implies !#[trigger] fits(board,p,h,w) by {
        assert(!fits(live,p,h,w));
        let q = choose |q: Cell| #[trigger] live.contains(q) && covers(p,h,w,q);
        assert(board.contains(q));
    }
}

proof fn fit_equivalence(rects:Seq<Occupied>, max_row:u128, p:Cell, h:int, w:int)
    requires h>0, w>0,
        forall |i:int| 0 <= i < rects.len() ==> #[trigger] valid_rectangle(rects[i],max_row),
    ensures clear_at(rects,p.0,p.1,h,w) == fits(sparse_board(rects),p,h,w),
{
    let board = sparse_board(rects);
    if clear_at(rects,p.0,p.1,h,w) {
        assert forall |q:Cell| #[trigger] board.contains(q) implies !covers(p,h,w,q) by {
            let i = choose |i:int| 0 <= i < rects.len()
                && (#[trigger] rects[i]).rows.0 <= q.0 < rects[i].rows.1
                && rects[i].cols.0 <= q.1 < rects[i].cols.1;
            if covers(p,h,w,q) {
                assert(overlaps(rects[i],p.0,p.1,h,w));
            }
        }
    } else {
        let i = choose |i:int| 0 <= i < rects.len() && #[trigger] overlaps(rects[i],p.0,p.1,h,w);
        assert(valid_rectangle(rects[i],max_row));
        let row = vstd::math::max(p.0, rects[i].rows.0 as int);
        let col = vstd::math::max(p.1, rects[i].cols.0 as int);
        assert(board.contains((row,col)));
        assert(covers(p,h,w,(row,col)));
    }
}

pub proof fn sparse_is_first_fit(rects:Seq<Occupied>, max_row:u128, columns:int, h:int, w:int,
    start:Cell, result:Cell)
    requires h>0, w>0, first_sparse_fit(rects,columns,h,w,start,result),
        forall |i:int| 0 <= i < rects.len() ==> #[trigger] valid_rectangle(rects[i],max_row),
    ensures first_fit(sparse_board(rects),columns,h,w,start,result),
{
    let board = sparse_board(rects);
    fit_equivalence(rects,max_row,result,h,w);
    assert forall |p:Cell| legal(p,columns,w) && !before(p,start) && before(p,result)
        implies !#[trigger] fits(board,p,h,w) by {
        fit_equivalence(rects,max_row,p,h,w);
        assert(!clear_at(rects,p.0,p.1,h,w));
    }
}

proof fn keep_blocker(rects: Seq<Occupied>, i: int, r: int, c: int, h: int, w: int)
    requires 0 <= i < rects.len(), !clear_at(rects.take(i),r,c,h,w),
    ensures !clear_at(rects.take(i+1),r,c,h,w),
{
    let at = choose |at:int| 0 <= at < i && #[trigger] overlaps(rects.take(i)[at],r,c,h,w);
    assert(overlaps(rects.take(i+1)[at],r,c,h,w));
}

pub proof fn accept_collision(rects: Seq<Occupied>, i: int, row: int, col: int, bottom: int,
    right: int, prior: int, prior_end: int, next: int, end: int)
    requires 0 <= i < rects.len(), row < bottom, col < right,
        overlaps(rects[i],row,col,bottom-row,right-col), col <= prior,
        next == vstd::math::max(prior,rects[i].cols.1 as int), end <= prior_end,
        row < end <= rects[i].rows.1,
        blocked_until(rects.take(i), bottom-row, right-col, row, prior_end, col, prior),
    ensures blocked_until(rects.take(i+1),bottom-row,right-col,row,end,col,next),
{
    assert forall |r:int,c:int| row <= r < end && col <= c < next implies
        !#[trigger] clear_at(rects.take(i+1),r,c,bottom-row,right-col) by {
        if c < prior {
            keep_blocker(rects,i,r,c,bottom-row,right-col);
        } else {
            assert(overlaps(rects.take(i+1)[i],r,c,bottom-row,right-col));
        }
    }
}

pub proof fn reject_collision(rects: Seq<Occupied>, i: int, row: int, col: int, bottom: int,
    right: int, next: int, end: int)
    requires 0 <= i < rects.len(), col <= next,
        !overlaps(rects[i],row,col,bottom-row,right-col),
        next == col ==> clear_at(rects.take(i),row,col,bottom-row,right-col),
        blocked_until(rects.take(i),bottom-row,right-col,row,end,col,next),
    ensures next == col ==> clear_at(rects.take(i+1),row,col,bottom-row,right-col),
        blocked_until(rects.take(i+1),bottom-row,right-col,row,end,col,next),
{
    if col == next {
        assert forall |j:int| 0 <= j < rects.take(i+1).len()
            implies !#[trigger] overlaps(rects.take(i+1)[j],row,col,bottom-row,right-col) by {
            if j < i {
                assert(rects.take(i+1)[j] == rects.take(i)[j]);
                assert(!overlaps(rects.take(i)[j],row,col,bottom-row,right-col));
            } else {
                assert(rects.take(i+1)[j] == rects[i]);
            }
        }
    }
    assert forall |r:int,c:int| row <= r < end && col <= c < next implies
        !#[trigger] clear_at(rects.take(i+1),r,c,bottom-row,right-col) by {
        keep_blocker(rects,i,r,c,bottom-row,right-col);
    }
}

pub proof fn merge_skips(rects: Seq<Occupied>, h: int, w: int, row: int, prior_limit: int,
    added_limit: int, limit: int, start: int, col: int, next: int)
    requires limit <= prior_limit, limit <= added_limit, start <= col <= next,
        blocked_until(rects,h,w,row,prior_limit,start,col),
        blocked_until(rects,h,w,row,added_limit,col,next),
    ensures blocked_until(rects,h,w,row,limit,start,next),
{
    assert forall |r:int,c:int| row <= r < limit && start <= c < next
        implies !#[trigger] clear_at(rects,r,c,h,w) by {
        if c < col { assert(!clear_at(rects,r,c,h,w)); }
        else { assert(!clear_at(rects,r,c,h,w)); }
    }
}

pub proof fn found_cell(rects: Seq<Occupied>, columns: int, h: int, w: int,
    start: Cell, cursor: Cell, col: int, limit: int)
    requires legal((cursor.0,col),columns,w), !before(cursor,start), cursor.1 <= col,
        sparse_passed(rects,columns,h,w,start,cursor), clear_at(rects,cursor.0,col,h,w),
        col > cursor.1 ==> cursor.0 < limit,
        blocked_until(rects,h,w,cursor.0,limit,cursor.1,col),
    ensures first_sparse_fit(rects,columns,h,w,start,(cursor.0,col)),
{
    assert forall |p:Cell| legal(p,columns,w) && !before(p,start) && before(p,(cursor.0,col))
        implies !#[trigger] clear_at(rects,p.0,p.1,h,w) by {
        if before(p,cursor) { assert(!clear_at(rects,p.0,p.1,h,w)); }
        else { assert(!clear_at(rects,p.0,p.1,h,w)); }
    }
}

pub proof fn exhausted_row(rects: Seq<Occupied>, columns: int, h: int, w: int, start: Cell,
    cursor: Cell, col: int, limit: int, resume: int)
    requires col+w > columns, cursor.1 <= col,
        col > cursor.1 ==> cursor.0 < limit,
        resume == if cursor.1 == 0 { limit } else { cursor.0+1 },
        sparse_passed(rects,columns,h,w,start,cursor),
        blocked_until(rects,h,w,cursor.0,limit,cursor.1,col),
    ensures sparse_passed(rects,columns,h,w,start,(resume,0)),
{
    assert forall |p:Cell| legal(p,columns,w) && !before(p,start) && before(p,(resume,0))
        implies !#[trigger] clear_at(rects,p.0,p.1,h,w) by {
        if before(p,cursor) { assert(!clear_at(rects,p.0,p.1,h,w)); }
        else { assert(!clear_at(rects,p.0,p.1,h,w)); }
    }
}

} // verus!
