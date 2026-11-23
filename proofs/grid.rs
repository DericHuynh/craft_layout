//! Packed occupancy and row-major first-fit grid placement.
use vstd::prelude::*;

#[path = "../src/grid_words.rs"]
mod grid_words;

#[path = "../src/grid_search.rs"]
pub(crate) mod grid_search;

#[path = "grid_sparse.rs"]
mod sparse;
use sparse::*;

#[path = "../src/grid_sparse.rs"]
mod grid_sparse;

#[path = "grid_frame.rs"]
pub mod frame;

verus! {

pub proof fn or_identities()
    ensures forall |v:u64| (#[trigger] (v | 0u64)) == v,
        forall |v:u64| (#[trigger] (v | u64::MAX)) == u64::MAX,
{
    assert forall |v:u64| (#[trigger] (v | 0u64)) == v by { assert((v | 0u64) == v) by(bit_vector); }
    assert forall |v:u64| (#[trigger] (v | u64::MAX)) == u64::MAX by { assert((v | u64::MAX) == u64::MAX) by(bit_vector); }
}

pub open spec fn mark_mask(i:int, first:int, last:int, start_mask:u64, end_mask:u64) -> u64 {
    if i<first || i>last { 0 } else if i==first && i==last { start_mask & end_mask }
    else if i==first { start_mask } else if i==last { end_mask } else { u64::MAX }
}

pub open spec fn overlap(word:u64, i:int, first:int, last:int, start_mask:u64, end_mask:u64) -> u64 {
    if i == first && i == last { word & start_mask & end_mask }
    else if i == first { word & start_mask }
    else if i == last { word & end_mask } else { word }
}

pub open spec fn bit(word: u64, i: int) -> bool {
    0 <= i < 64 && ((word >> (i as u32)) & 1) != 0
}

pub open spec fn collision_run(occupied:u64, collisions:u64, next:u32) -> bool {
    1 <= next <= 64 && exists |last:u32| last < next && bit(collisions,last as int)
        && (forall |j:u32| last <= j < next ==> #[trigger] bit(occupied,j as int))
}

pub open spec fn open_range(word: u64, pos: int, width: int) -> bool {
    0 <= pos && pos + width <= 64
        && forall |i: int| pos <= i < pos + width ==> #[trigger] bit(word, i)
}

pub open spec fn runs_of(runs: u64, open: u64, width: int) -> bool {
    forall |i: int| 0 <= i < 64 ==> #[trigger] bit(runs, i) == open_range(open, i, width)
}

pub open spec fn first_word_run(open: u64, next: u32, span: u32) -> bool {
    next <= 64 && (next < 64 ==> open_range(open, next as int, span as int))
        && (forall |i:int| 0 <= i < next ==> !#[trigger] open_range(open, i, span as int))
}

pub proof fn extend_runs(open: u64, runs: u64, width: u32, shift: u32)
    requires 1 <= width <= 64, shift <= width, width + shift <= 64, runs_of(runs, open, width as int),
    ensures runs_of(runs & (runs >> shift), open, width + shift),
{
    assert(shift < 64);
    assert forall |j:int| 0 <= j < 64 implies
        #[trigger] bit(runs & (runs >> shift), j) == open_range(open, j, width + shift) by {
        let i = j as u32;
        assert((((runs & (runs >> shift)) >> i) & 1) != 0
            == ((((runs >> i) & 1) != 0) && (i.wrapping_add(shift) < 64) && (((runs >> i.wrapping_add(shift)) & 1) != 0)))
            by(bit_vector) requires i < 64, shift < 64;
        assert(bit(runs & (runs >> shift), j) == (bit(runs, j) && bit(runs, j + shift as int)));
        if bit(runs, j) && bit(runs, j + shift as int) {
            assert forall |k:int| j <= k < j + width + shift implies #[trigger] bit(open, k) by {
                if k >= j + width { assert(j + shift <= k < j + shift + width); }
            }
        }
    }
}

/// Relate each physical word and bit to its candidate column. The same
/// boundary masks drive both collision detection and occupied-cell updates.
pub proof fn word_matches_span(word:u64, i:int, j:u32, pos:int, width:int, start:u64, end:u64)
    requires pos>=0, width>0, i>=0, j<64,
        forall |k:u32| k<64 ==> #[trigger] bit(start,k as int) == (k>=pos%64),
        forall |k:u32| k<64 ==> #[trigger] bit(end,k as int) == (k<=(pos+width-1)%64),
    ensures
        bit(mark_mask(i,pos/64,(pos+width-1)/64,start,end), j as int) ==
            (pos <= i*64+j < pos+width),
        pos/64 <= i <= (pos+width-1)/64 ==>
            (bit(overlap(word,i,pos/64,(pos+width-1)/64,start,end),j as int)
                == (bit(word,j as int) && pos <= i*64+j < pos+width)),
{
    let first=pos/64;
    let last=(pos+width-1)/64;
    assert(0<=pos%64<64 && pos == first*64 + pos%64);
    assert(0<=(pos+width-1)%64<64 && pos+width-1 == last*64 + (pos+width-1)%64);
    assert(bit(start,j as int) == (j>=pos%64));
    assert(bit(end,j as int) == (j<=(pos+width-1)%64));
    assert(((0u64 >> j) & 1) == 0 && ((u64::MAX >> j) & 1) == 1) by(bit_vector) requires j<64;
    assert((((start & end) >> j) & 1 != 0) == (((start >> j) & 1 != 0) && ((end >> j) & 1 != 0))) by(bit_vector);
    assert((((word & start) >> j) & 1 != 0) == (((word >> j) & 1 != 0) && ((start >> j) & 1 != 0))) by(bit_vector);
    assert((((word & end) >> j) & 1 != 0) == (((word >> j) & 1 != 0) && ((end >> j) & 1 != 0))) by(bit_vector);
    assert((((word & start & end) >> j) & 1 != 0) ==
        (((word >> j) & 1 != 0) && ((start >> j) & 1 != 0) && ((end >> j) & 1 != 0))) by(bit_vector);
}

/// Locations and scan cursors use (row, column) order. Rows beyond the stored
/// occupancy are empty. A cursor may sit one past the last legal start.
pub type Cell = (int, int);
pub type Board = ISet<Cell>;

pub open spec fn before(a:Cell, b:Cell) -> bool {
    a.0 < b.0 || (a.0 == b.0 && a.1 < b.1)
}

pub open spec fn legal(p:Cell, columns:int, width:int) -> bool {
    0 <= p.0 && 0 <= p.1 && p.1 + width <= columns
}

pub open spec fn covers(p:Cell, height:int, width:int, cell:Cell) -> bool {
    p.0 <= cell.0 < p.0 + height && p.1 <= cell.1 < p.1 + width
}

pub open spec fn fits(board:Board, p:Cell, h:int, w:int) -> bool {
    forall |cell:Cell| #[trigger] board.contains(cell) ==> !covers(p,h,w,cell)
}

pub open spec fn passed(board:Board, columns:int, h:int, w:int, start:Cell, cursor:Cell) -> bool {
    forall |p:Cell| legal(p, columns, w) && !before(p,start) && before(p,cursor)
        ==> !#[trigger] fits(board,p,h,w)
}

pub open spec fn first_fit(board:Board, columns:int, h:int, w:int, start:Cell, result:Cell) -> bool {
    !before(result,start) && legal(result,columns,w) && fits(board,result,h,w)
        && passed(board,columns,h,w,start,result)
}

/// The multiword scanner has found an occupied cell inside the candidate
/// rectangle. Every contiguous occupied column after it also rules out a
/// start, up to the first free bit or the end of that word.
pub proof fn skip_collision(board:Board, columns:int, h:int, w:int, start:Cell, cursor:Cell,
    row:int, collision:int, next:int)
    requires
        passed(board,columns,h,w,start,cursor), legal(cursor, columns,w),
        cursor.0 <= row < cursor.0+h, cursor.1 <= collision < cursor.1+w, collision < next,
        forall |k:int| collision <= k < next ==> #[trigger] board.contains((row,k)),
    ensures passed(board,columns,h,w,start,(cursor.0,next)), cursor.1 < next,
{
    assert forall |p:Cell| legal(p,columns,w) && !before(p,start) && before(p,(cursor.0,next))
        implies !#[trigger] fits(board,p,h,w) by {
        if !before(p,cursor) {
            let k = if p.1 <= collision { collision } else { p.1 };
            assert(board.contains((row,k)) && covers(p,h,w,(row,k)));
        }
    }
}

/// Moving to a fresh line when the cursor lies beyond the last legal column
/// does not discard any candidate.
pub proof fn wrap_cursor(board:Board, columns:int, h:int,w:int,start:Cell,cursor:Cell)
    requires passed(board,columns,h,w,start,cursor), cursor.1 + w > columns,
    ensures passed(board,columns,h,w,start,(cursor.0+1,0)),
{}

/// A packed one-word row is the union of all spanned rows. Its AND-shift
/// search picks the same first legal column as testing each cell.
pub proof fn single_word_first_fit(board:Board, columns:int,h:int,w:int,start:Cell,cursor:Cell,
    open:u64, next:int)
    requires
        1 <= w <= columns <= 64, h > 0, legal(cursor,columns,w), !before(cursor,start),
        passed(board,columns,h,w,start,cursor),
        forall |col:int| 0 <= col < columns ==> (#[trigger] bit(open,col)
            == (forall |r:int| cursor.0 <= r < cursor.0+h ==> !#[trigger] board.contains((r,col)))),
        cursor.1 <= next <= 64, next < 64 ==> open_range(open,next,w),
        forall |i:int| cursor.1 <= i < next ==> !#[trigger] open_range(open,i,w),
    ensures
        next+w <= columns ==> first_fit(board,columns,h,w,start,(cursor.0,next)),
        next+w > columns ==> passed(board,columns,h,w,start,(cursor.0+1,0)),
{
    assert forall |c:int| 0 <= c && c+w <= columns implies
        fits(board,(cursor.0,c),h,w) == #[trigger] open_range(open,c,w) by {
        if fits(board,(cursor.0,c),h,w) {
            assert forall |i:int| c <= i < c+w implies #[trigger] bit(open,i) by {
                assert forall |r:int| cursor.0 <= r < cursor.0+h implies !#[trigger] board.contains((r,i)) by {};
            }
        } else if open_range(open,c,w) {
            let cell = choose |cell:Cell| #[trigger] board.contains(cell) && covers((cursor.0,c),h,w,cell);
            assert(bit(open,cell.1));
        }
    }
    let end = if next+w <= columns { (cursor.0,next) } else { (cursor.0+1,0) };
    assert forall |p:Cell| legal(p,columns,w) && !before(p,start) && before(p,end)
        implies !#[trigger] fits(board,p,h,w) by {
        if !before(p,cursor) {
            assert(!open_range(open,p.1,w));
        }
    }
}

/// Every collision-free exit, including the all-empty tail of the board,
/// yields the unique cell-by-cell result from the incoming cursor.
pub proof fn finish_search(board:Board, columns:int,h:int,w:int,start:Cell,found:Cell, other:Cell)
    requires
        !before(found,start), legal(found,columns,w), passed(board,columns,h,w,start,found),
        fits(board,found,h,w), first_fit(board,columns,h,w,start,other),
    ensures first_fit(board,columns,h,w,start,found), found == other,
{}

pub open spec fn place(board:Board,p:Cell,h:int,w:int) -> Board {
    ISet::new(|cell:Cell| board.contains(cell) || covers(p,h,w,cell))
}

/// After a successful placement, the cached trailing edge is a lower bound
/// for every equally large or larger span. Subsequent placements only grow
/// occupancy. Saturating each cache coordinate at u16::MAX moves it earlier.
pub proof fn cache_lower_bound(board:Board, later:Board, cols:int, h:int,w:int,p:Cell,
    large_h:int,large_w:int,cache:Cell)
    requires
        h>0, w>0, large_h>=h, large_w>=w,
        first_fit(board,cols,h,w,(0,0),p),
        forall |c:Cell| place(board,p,h,w).contains(c) ==> #[trigger] later.contains(c),
        !before((p.0,p.1+w),cache),
    ensures passed(later,cols,large_h,large_w,(0,0),cache),
{
    assert forall |q:Cell| legal(q,cols,large_w) && !before(q,(0,0)) && before(q,cache)
        implies !#[trigger] fits(later,q,large_h,large_w) by {
        if before(q,p) {
            assert(!fits(board,q,h,w));
            let c = choose |c:Cell| #[trigger] board.contains(c) && covers(q,h,w,c);
            assert(place(board,p,h,w).contains(c));
            assert(later.contains(c) && covers(q,large_h,large_w,c));
        } else {
            assert(covers(p,h,w,q));
            assert(place(board,p,h,w).contains(q));
            assert(later.contains(q) && covers(q,large_h,large_w,q));
        }
    }
}

pub open spec fn suffix(board:Board, dropped:int) -> Board {
    ISet::new(|c:Cell| c.0>=0 && board.contains((c.0+dropped,c.1)))
}

/// Rebase a non-backfilling search on a compacted suffix. All probes and
/// hence the first-fit result translate by the number of discarded rows.
pub proof fn compacted_first_fit(board:Board,dropped:int,cols:int,h:int,w:int,start:Cell,result:Cell)
    requires 0 <= dropped <= start.0, first_fit(board,cols,h,w,start,result),
    ensures first_fit(suffix(board,dropped),cols,h,w,(start.0-dropped,start.1),(result.0-dropped,result.1)),
{
    let new = suffix(board,dropped);
    assert forall |q:Cell| q.0>=0 implies #[trigger] fits(new,q,h,w)
        == fits(board,(q.0+dropped,q.1),h,w) by {
        if !fits(new,q,h,w) {
            let c = choose |c:Cell| #[trigger] new.contains(c) && covers(q,h,w,c);
            assert(board.contains((c.0+dropped,c.1)));
        }
        if !fits(board,(q.0+dropped,q.1),h,w) {
            let c = choose |c:Cell| #[trigger] board.contains(c) && covers((q.0+dropped,q.1),h,w,c);
            assert(new.contains((c.0-dropped,c.1)));
        }
    }
    assert forall |q:Cell| legal(q,cols,w) && !before(q,(start.0-dropped,start.1))
        && before(q,(result.0-dropped,result.1)) implies !#[trigger] fits(new,q,h,w) by {
        assert(!fits(board,(q.0+dropped,q.1),h,w));
    }
}

/// When all spanned items fit on the first row, it is enough to track
/// the trailing column and maximum height. This holds for either backfill mode.
pub proof fn single_line_first_fit(board:Board, cols:int, h:int, w:int, tail:int, start:Cell)
    requires 0<=tail, w>0, h>0, tail+w<=cols, start.0==0, 0<=start.1<=tail,
        forall |c:int| 0<=c<tail ==> #[trigger] board.contains((0,c)),
        forall |p:Cell| #[trigger] board.contains(p) ==> p.1<tail,
    ensures first_fit(board,cols,h,w,start,(0,tail)),
        forall |c:int| 0<=c<tail+w ==> #[trigger] place(board,(0,tail),h,w).contains((0,c)),
        forall |p:Cell| #[trigger] place(board,(0,tail),h,w).contains(p) ==> p.1<tail+w,
{
    assert forall |q:Cell| legal(q,cols,w) && !before(q,start) && before(q,(0,tail))
        implies !#[trigger] fits(board,q,h,w) by {
        assert(q.0==0 && board.contains((0,q.1)) && covers(q,h,w,(0,q.1)));
    }
}

pub open spec fn packed(mem:Seq<u64>, stride:int) -> Board {
    ISet::new(|cell:Cell| {
        let (r,c) = cell;
        let index = r*stride + c/64;
        r>=0 && 0<=c<stride*64 && index < mem.len() && bit(mem[index],c%64)
    })
}

pub open spec fn masks(pos:int,width:int,first:int,last:int,start:u64,end:u64) -> bool {
    pos>=0 && width>0 && first==pos/64 && last==(pos+width-1)/64
        && (forall |k:u32| k<64 ==> #[trigger] bit(start,k as int) == (k>=pos%64))
        && (forall |k:u32| k<64 ==> #[trigger] bit(end,k as int) == (k<=(pos+width-1)%64))
}

pub proof fn row_block_bounds(row:int,stride:int,lines:int)
    requires 0<=row<lines, stride>0,
    ensures 0<=row*stride, row*stride+stride==(row+1)*stride, (row+1)*stride <= lines*stride,
{
    assert(0<=row*stride && row*stride+stride==(row+1)*stride && (row+1)*stride<=lines*stride)
        by(nonlinear_arith) requires 0<=row<lines, stride>0;
}

pub proof fn clear_row(mem:Seq<u64>,stride:int,r:int,p:int,w:int, row:Seq<u64>,
        first:int,last:int,start:u64,end:u64)
    requires stride>0, r>=0, 0 <= r*stride, r*stride+stride<=mem.len(),
        row==mem.subrange(r*stride,r*stride+stride), masks(p,w,first,last,start,end),
        last<stride,
        forall |i:int| first<=i<=last ==> #[trigger] overlap(row[i],i,first,last,start,end)==0,
    ensures forall |c:int| p<=c<p+w ==> !#[trigger] packed(mem,stride).contains((r,c)),
{
    assert forall |c:int| p<=c<p+w implies !#[trigger] packed(mem,stride).contains((r,c)) by {
        let i=c/64;
        let j=(c%64) as u32;
        assert(p/64<=i<=(p+w-1)/64 && c==i*64+j);
        assert(overlap(row[i],i,first,last,start,end)==0);
        word_matches_span(row[i],i,j,p,w,start,end);
        assert(((0u64 >> j) & 1) == 0) by(bit_vector);
        assert(mem[r*stride+i]==row[i]);
    }
}

pub open spec fn occupied_run(board:Board,r:int,k:int,next:int) -> bool {
    forall |c:int| k<=c<next ==> #[trigger] board.contains((r,c))
}

pub proof fn collided_row(mem:Seq<u64>,stride:int,r:int,p:int,w:int,row:Seq<u64>,
        first:int,last:int,start:u64,end:u64,word:int,next:u32)
    requires stride>0, r>=0, 0 <= r*stride, r*stride+stride<=mem.len(), last<stride,
        row==mem.subrange(r*stride,r*stride+stride), masks(p,w,first,last,start,end),
        first<=word<=last, collision_run(row[word],overlap(row[word],word,first,last,start,end),next),
    ensures
        p < word*64+next <= stride*64,
        exists |k:int| p<=k<p+w && k<word*64+next
            && #[trigger] occupied_run(packed(mem,stride),r,k,word*64+next),
{
    let k=choose |k:u32| k<next && bit(overlap(row[word],word,first,last,start,end),k as int)
        && (forall |j:u32| k<=j<next ==> #[trigger] bit(row[word],j as int));
    word_matches_span(row[word],word,k,p,w,start,end);
    assert(mem[r*stride+word]==row[word]);
    assert forall |c:int| word*64+k<=c<word*64+next implies #[trigger] packed(mem,stride).contains((r,c)) by {
        let j=(c%64) as u32;
        assert(c/64==word && c==word*64+j);
        assert(bit(row[word],j as int));
    }
    assert(occupied_run(packed(mem,stride),r,word*64+k,word*64+next));
}

pub proof fn empty_after(mem:Seq<u64>,stride:int,lines:int,r:int,c:int)
    requires stride>0, lines*stride==mem.len(), r>=lines, lines>=0, c>=0,
    ensures !packed(mem,stride).contains((r,c)),
{
    assert(lines*stride<=r*stride) by(nonlinear_arith) requires stride>0, r>=lines;
}

pub proof fn one_word_open(mem:Seq<u64>,line:int,h:int,rows:Seq<u64>,blocked:u64)
    requires 0 <= line < mem.len(), h>0,
        rows==mem.subrange(line,vstd::math::min(line+h,mem.len() as int)),
        forall |j:u32| j<64 ==> #[trigger] bit(blocked,j as int)
            == (exists |r:int| 0<=r<rows.len() && #[trigger] bit(rows[r],j as int)),
    ensures forall |c:int| 0<=c<64 ==> (#[trigger] bit(!blocked,c)
        == (forall |r:int| line<=r<line+h ==> !#[trigger] packed(mem,1).contains((r,c)))),
{
    assert forall |c:int| 0<=c<64 implies (#[trigger] bit(!blocked,c)
        == (forall |r:int| line<=r<line+h ==> !#[trigger] packed(mem,1).contains((r,c)))) by {
        let j=c as u32;
        assert(((((!blocked) >> j) & 1) != 0) == (((blocked >> j) & 1) == 0)) by(bit_vector) requires j<64;
        assert(bit(blocked,j as int) == !bit(!blocked,c));
        if bit(blocked,c) {
            let r=choose |r:int| 0<=r<rows.len() && #[trigger] bit(rows[r],j as int);
            assert(mem[line+r]==rows[r] && packed(mem,1).contains((line+r,c)));
        } else {
            assert forall |r:int| line<=r<line+h implies !#[trigger] packed(mem,1).contains((r,c)) by {
                if r<mem.len() {
                    assert(rows[r-line]==mem[r] && !bit(rows[r-line],j as int));
                }
            }
        }
    }
}

pub proof fn paired_window_union(rows:Seq<u64>, middle:Seq<u64>, h:int,
    shared:u64, left:u64, right:u64)
    requires 0<h<rows.len(), middle==rows.subrange(1,h),
        forall |j:u32| j<64 ==> #[trigger] bit(shared,j as int)
            == (exists |r:int| 0<=r<middle.len() && #[trigger] bit(middle[r],j as int)),
        forall |j:u32| j<64 ==> #[trigger] bit(left,j as int) == (bit(shared,j as int) || bit(rows[0],j as int)),
        forall |j:u32| j<64 ==> #[trigger] bit(right,j as int) == (bit(shared,j as int) || bit(rows[h],j as int)),
    ensures forall |j:u32| j<64 ==> #[trigger] bit(left,j as int)
            == (exists |r:int| 0<=r<h && #[trigger] bit(rows[r],j as int)),
        forall |j:u32| j<64 ==> #[trigger] bit(right,j as int)
            == (exists |r:int| 1<=r<=h && #[trigger] bit(rows[r],j as int)),
{
    assert forall |j:u32| j<64 implies #[trigger] bit(shared,j as int)
        == (exists |r:int| 0<r<h && #[trigger] bit(rows[r],j as int)) by {
        if bit(shared,j as int) {
            let r=choose |r:int| 0<=r<middle.len() && #[trigger] bit(middle[r],j as int);
            assert(middle[r]==rows[r+1]);
            assert(bit(rows[r+1],j as int));
        } else if exists |r:int| 0<r<h && #[trigger] bit(rows[r],j as int) {
            let r=choose |r:int| 0<r<h && #[trigger] bit(rows[r],j as int);
            assert(middle[r-1]==rows[r]);
            assert(bit(middle[r-1],j as int));
        }
    }
    assert forall |j:u32| j<64 implies #[trigger] bit(left,j as int)
        == (exists |r:int| 0<=r<h && #[trigger] bit(rows[r],j as int)) by {};
    assert forall |j:u32| j<64 implies #[trigger] bit(right,j as int)
        == (exists |r:int| 1<=r<=h && #[trigger] bit(rows[r],j as int)) by {};
}

pub proof fn open_paired_rows(mem:Seq<u64>,line:int,h:int,rows:Seq<u64>,left:u64,right:u64)
    requires 0<=line, 0<h, line+h<mem.len(), rows==mem.subrange(line,line+h+1),
        forall |j:u32| j<64 ==> #[trigger] bit(left,j as int)
            == (exists |r:int| 0<=r<h && #[trigger] bit(rows[r],j as int)),
        forall |j:u32| j<64 ==> #[trigger] bit(right,j as int)
            == (exists |r:int| 1<=r<=h && #[trigger] bit(rows[r],j as int)),
    ensures forall |c:int| 0<=c<64 ==> (#[trigger] bit(!left,c)
            == (forall |r:int| line<=r<line+h ==> !#[trigger] packed(mem,1).contains((r,c)))),
        forall |c:int| 0<=c<64 ==> (#[trigger] bit(!right,c)
            == (forall |r:int| line+1<=r<line+1+h ==> !#[trigger] packed(mem,1).contains((r,c)))),
{
    let first=mem.subrange(line,line+h);
    let second=mem.subrange(line+1,line+h+1);
    assert forall |j:u32| j<64 implies #[trigger] bit(left,j as int)
        == (exists |r:int| 0<=r<first.len() && #[trigger] bit(first[r],j as int)) by {
        if bit(left,j as int) {
            let r=choose |r:int| 0<=r<h && #[trigger] bit(rows[r],j as int);
            assert(first[r]==rows[r]);
            assert(bit(first[r],j as int));
        } else if exists |r:int| 0<=r<first.len() && #[trigger] bit(first[r],j as int) {
            let r=choose |r:int| 0<=r<first.len() && #[trigger] bit(first[r],j as int);
            assert(first[r]==rows[r]);
            assert(bit(rows[r],j as int));
        }
    }
    assert forall |j:u32| j<64 implies #[trigger] bit(right,j as int)
        == (exists |r:int| 0<=r<second.len() && #[trigger] bit(second[r],j as int)) by {
        if bit(right,j as int) {
            let r=choose |r:int| 1<=r<=h && #[trigger] bit(rows[r],j as int);
            assert(second[r-1]==rows[r]);
            assert(bit(second[r-1],j as int));
        } else if exists |r:int| 0<=r<second.len() && #[trigger] bit(second[r],j as int) {
            let r=choose |r:int| 0<=r<second.len() && #[trigger] bit(second[r],j as int);
            assert(second[r]==rows[r+1]);
            assert(bit(rows[r+1],j as int));
        }
    }
    one_word_open(mem,line,h,first,left);
    one_word_open(mem,line+1,h,second,right);
}

pub proof fn aligned_block(i:int,n:int,stride:int)
    requires 0<=i<n, stride>0, i%stride==0, n%stride==0,
    ensures i+stride<=n, (i+stride)%stride==0,
        forall |k:int| i<=k<i+stride ==> #[trigger] (k%stride)==k-i,
{
    use vstd::arithmetic::div_mod::*;
    lemma_fundamental_div_mod(i,stride);
    lemma_fundamental_div_mod(n,stride);
    let q=i/stride;
    let end=n/stride;
    assert(stride*q==i && stride*end==n);
    use vstd::arithmetic::mul::*;
    lemma_mul_is_commutative(q,stride);
    lemma_mul_is_commutative(end,stride);
    if end <= q { lemma_mul_inequality(end,q,stride); }
    assert(q+1<=end);
    lemma_mul_inequality(q+1,end,stride);
    lemma_mul_is_commutative(q+1,stride);
    assert(stride*(q+1)==i+stride) by(nonlinear_arith) requires stride*q==i;
    lemma_fundamental_div_mod_converse(i+stride,stride,q+1,0);
    assert forall |k:int| i<=k<i+stride implies #[trigger] (k%stride)==k-i by {
        lemma_fundamental_div_mod_converse(k,stride,q,k-i);
    }
}

/// An aligned copy of the suffix followed by truncation has exactly the
/// packed cell model used by the absolute-to-relative compaction theorem.
pub proof fn physical_suffix(mem:Seq<u64>,stride:int,drop:int)
    requires stride>0, drop>=0, 0<=drop*stride<=mem.len(),
    ensures packed(mem.subrange(drop*stride,mem.len() as int),stride)
        == suffix(packed(mem,stride),drop),
{
    let moved=mem.subrange(drop*stride,mem.len() as int);
    assert forall |q:Cell| packed(moved,stride).contains(q) == #[trigger] suffix(packed(mem,stride),drop).contains(q) by {
        let (r,c)=q;
        assert((r+drop)*stride == r*stride+drop*stride) by(nonlinear_arith);
        if r>=0 && 0<=c<stride*64 {
            assert(r*stride>=0) by(nonlinear_arith) requires r>=0,stride>0;
            let offset=r*stride+c/64;
            if offset<moved.len() { assert(moved[offset]==mem[drop*stride+offset]); }
        }
    }
    assert(packed(moved,stride) =~= suffix(packed(mem,stride),drop));
}

pub open spec fn occupied_prefix(columns:int,tail:Cell) -> Board {
    ISet::new(|p:Cell| legal(p,columns,1) && before(p,tail))
}

/// Induction step for span-free placement. Filling a cursor grows the occupied
/// prefix by exactly one cell, under both forward and backfilling policies.
pub proof fn in_order_step(cols:int, p:Cell)
    requires legal(p,cols,1),
    ensures ({
        let filled=occupied_prefix(cols,p);
        let next=if p.1+1==cols { (p.0+1,0int) } else { (p.0,p.1+1) };
        first_fit(filled,cols,1,1,(0,0),p) && first_fit(filled,cols,1,1,p,p)
            && place(filled,p,1,1)==occupied_prefix(cols,next)
    }),
{
    let filled=occupied_prefix(cols,p);
    let next=if p.1+1==cols { (p.0+1,0int) } else { (p.0,p.1+1) };
    assert forall |q:Cell| legal(q,cols,1) && before(q,p) implies !#[trigger] fits(filled,q,1,1) by {
        assert(filled.contains(q) && covers(q,1,1,q));
    }
    assert(place(filled,p,1,1) =~= occupied_prefix(cols,next));
}

pub proof fn locate_cell(r:int,c:int,stride:int,first:int,end:int)
    requires r>=0, 0<=c<stride*64, stride>0, 0<=first<end,
    ensures r*stride+c/64>=0,
        (first*stride<=r*stride+c/64<end*stride)==(first<=r<end),
        first<=r<end ==> (r*stride+c/64-first*stride)%stride==c/64,
{
    use vstd::arithmetic::div_mod::*;
    use vstd::arithmetic::mul::*;
    let word=c/64;
    let i=r*stride+word;
    assert(0<=word<stride);
    assert(0<=r*stride) by(nonlinear_arith) requires 0<=r, stride>0;
    if r<first {
        lemma_mul_inequality(r+1,first,stride);
    } else if r>=end {
        lemma_mul_inequality(end,r,stride);
    } else {
        lemma_mul_inequality(first,r,stride);
        lemma_mul_inequality(r+1,end,stride);
        assert((r-first)*stride+word==i-first*stride) by(nonlinear_arith) requires i==r*stride+word;
        lemma_mul_is_commutative(r-first,stride);
        lemma_fundamental_div_mod_converse(i-first*stride,stride,r-first,word);
    }
    assert((r+1)*stride==r*stride+stride) by(nonlinear_arith);
}

pub type Limits = [[(u16,u16); grid_search::CACHED_SPANS]; grid_search::CACHED_SPANS];

pub open spec fn valid_limits(limits:Limits,rows:int,columns:int)->bool {
    forall|i:int,j:int| 0<=i<grid_search::CACHED_SPANS && 0<=j<grid_search::CACHED_SPANS ==> {
        let p=#[trigger] limits[i][j];
        p.0<=rows && p.1<=columns
    }
}

pub open spec fn span_start(first:usize,forward:(usize,usize),limits:Limits,h:usize,w:usize,
    backfill:bool)->Cell
{
    if backfill {
        let p=limits[vstd::math::min(h as int,grid_search::CACHED_SPANS as int)-1]
                    [vstd::math::min(w as int,grid_search::CACHED_SPANS as int)-1];
        (p.0 as int,p.1 as int)
    } else { (forward.0-first,forward.1 as int) }
}

pub open spec fn updated_limit(limits:Limits,h:usize,w:usize,cell:(usize,usize),backfill:bool,
    i:int,j:int)->(u16,u16)
{
    if backfill && i+1==h && j+1==w {
        (vstd::math::min(cell.0 as int,u16::MAX as int) as u16,
         vstd::math::min(cell.1+w,u16::MAX as int) as u16)
    } else { limits[i][j] }
}

pub open spec fn compacted(row:int, first:int, rows:int, backfill:bool)->bool {
    !backfill && row-first >= rows-row
}

pub proof fn span_cursor_length(first:int, skip:int, rows:int, old_rows:int, end:int, stride:int)
    requires rows==vstd::math::max(old_rows,end),
        first<=old_rows, first<=end, first<=skip<=rows, stride>0,
    ensures
        vstd::math::max((old_rows-first)*stride,(end-first)*stride)==(rows-first)*stride,
        (rows-first)*stride-(skip-first)*stride==(rows-skip)*stride,
{
    if old_rows >= end {
        vstd::arithmetic::mul::lemma_mul_inequality(end-first,old_rows-first,stride);
    } else {
        vstd::arithmetic::mul::lemma_mul_inequality(old_rows-first,end-first,stride);
    }
    assert((rows-first)*stride-(skip-first)*stride==(rows-skip)*stride) by(nonlinear_arith);
}

pub proof fn suffix_zero(b:Board)
    requires forall|p:Cell| #[trigger] b.contains(p) ==> p.0>=0,
    ensures suffix(b,0)==b,
{
    assert(suffix(b,0) =~= b);
}

pub open spec fn span_step(
    old:grid_search::SpanCursor, original:Seq<u64>, new:grid_search::SpanCursor, occupied:Seq<u64>,
    columns:usize, stride:usize, h:usize, w:usize, backfill:bool, cell:(usize,usize),
)->bool
{
    &&& first_fit(packed(original,stride as int),columns as int,h as int,w as int,
        span_start(old.first_row,old.forward,old.limits,h,w,backfill),
        (cell.0-old.first_row,cell.1 as int))
    &&& old.first_row<=cell.0<=old.rows+1
    &&& cell.1+w<=columns
    &&& new.rows==vstd::math::max(old.rows as int,cell.0+h)
    &&& new.first_row==if compacted(cell.0 as int,old.first_row as int,new.rows as int,backfill) {
        cell.0
    } else { old.first_row }
    &&& new.forward==if backfill {old.forward} else {(cell.0, (cell.1+w) as usize)}
    &&& forall|i:int,j:int| 0<=i<grid_search::CACHED_SPANS && 0<=j<grid_search::CACHED_SPANS ==>
        #[trigger] new.limits[i][j]==updated_limit(old.limits,h,w,cell,backfill,i,j)
    &&& (new.rows-new.first_row)*stride==occupied.len()
    &&& packed(occupied,stride as int)==suffix(place(packed(original,stride as int),
        (cell.0-old.first_row,cell.1 as int),h as int,w as int),
        new.first_row-old.first_row)
    &&& backfill ==> valid_limits(new.limits,new.rows as int,columns as int)
}

}

verus! {

/// The word at one horizontal position, after combining the rows of a span.
pub open spec fn row_open(board:Board, line:int, h:int, word:int, open:u64) -> bool {
    forall |i:u32| i<64 ==> (#[trigger] bit(open,i as int) ==
        (forall |r:int| line<=r<line+h ==> !#[trigger] board.contains((r,word*64+i))))
}

pub proof fn empty_word(board:Board,line:int,word:int)
    ensures row_open(board,line,0,word,!0u64),
{
    assert forall |i:u32| i<64 implies #[trigger] bit(!0u64,i as int) by {
        assert(((!0u64 >> i) & 1) != 0) by(bit_vector) requires i<64;
    }
}

pub proof fn extend_open_word(mem:Seq<u64>,stride:int,line:int,r:int,word:int,old:u64,next:u64)
    requires 0<=line<=r, 0<=word<stride, 0<=r*stride, r*stride+stride<=mem.len(),
        row_open(packed(mem,stride),line,r-line,word,!old),
        forall |j:u32| j<64 ==> #[trigger] bit(next,j as int)
            == (bit(old,j as int) || bit(mem[r*stride+word],j as int)),
    ensures row_open(packed(mem,stride),line,r+1-line,word,!next),
{
    let b = packed(mem,stride);
    assert forall |i:u32| i<64 implies
        #[trigger] bit(!next,i as int) ==
            (forall |y:int| line<=y<r+1 ==> !#[trigger] b.contains((y,word*64+i))) by {
        let c = word*64+i;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(c,64,word,i as int);
        assert(b.contains((r,c)) == bit(mem[r*stride+word],i as int));
        assert((((!old >> i) & 1) != 0) == (((old >> i) & 1) == 0)) by(bit_vector) requires i<64;
        assert((((!next >> i) & 1) != 0) == (((next >> i) & 1) == 0)) by(bit_vector) requires i<64;
        assert(bit(old,i as int) || bit(mem[r*stride+word],i as int) <==> bit(next,i as int));
        assert(bit(!old,i as int) == (forall |y:int| line<=y<r ==> !#[trigger] b.contains((y,c))));
        if bit(!next,i as int) {
            assert forall |y:int| line<=y<r+1 implies !#[trigger] b.contains((y,c)) by {};
        } else if bit(old,i as int) {
            let y=choose |y:int| line<=y<r && #[trigger] b.contains((y,c));
            assert(b.contains((y,c)));
        } else {
            assert(b.contains((r,c)));
        }
    }
}

pub proof fn open_word_after_last_row(mem:Seq<u64>,stride:int,rows:int,line:int,h:int,stop:int,word:int,open:u64)
    requires 0<=line<=stop<=rows, rows*stride==mem.len(), stride>0, 0<=word<stride,
        stop==vstd::math::min(line+h,rows),
        row_open(packed(mem,stride),line,stop-line,word,open),
    ensures row_open(packed(mem,stride),line,h,word,open),
{
    let b = packed(mem,stride);
    assert forall |i:u32| i<64 implies #[trigger] bit(open,i as int) ==
        (forall |y:int| line<=y<line+h ==> !#[trigger] b.contains((y,word*64+i))) by {
        assert(bit(open,i as int) == (forall |y:int| line<=y<stop ==> !#[trigger] b.contains((y,word*64+i))));
        if bit(open,i as int) {
            assert forall |y:int| line<=y<line+h implies !#[trigger] b.contains((y,word*64+i)) by {
                if y>=stop { empty_after(mem,stride,rows,y,word*64+i); }
            }
        }
    }
}

pub open spec fn open_across(lo:u64,hi:u64,p:int,span:int) -> bool {
    (forall |i:int| p<=i<64 ==> #[trigger] bit(lo,i))
    && (forall |i:int| 0<=i<p+span-64 ==> #[trigger] bit(hi,i))
}

pub proof fn first_crossing_from_counts(lo:u64,hi:u64,span:u32,min:u32,left:u32,right:u32,first:u32,next:u32)
    requires
        1 <= span <= 16, min < 64, left<=64, right<=64,
        forall |j:u32| j<64 && 64-left<=j ==> !#[trigger] bit(lo,j as int),
        left<64 ==> bit(lo,63-left),
        forall |j:u32| j<right ==> !#[trigger] bit(hi,j as int),
        right<64 ==> bit(hi,right as int),
        first == vstd::math::max(vstd::math::max(64-left,65-span),min as int),
        next == if first==64 || span > 64-first+right { 64 } else { first },
    ensures
        next<=64,
        next<64 ==> min<=next && 64<next+span && open_across(!lo,!hi,next as int,span as int),
        forall |p:int| min<=p<next && 64<p+span ==> !#[trigger] open_across(!lo,!hi,p,span as int),
{
    assert forall |j:u32| j<64 implies #[trigger] bit(!lo,j as int) == !bit(lo,j as int) by {
        assert((((!lo >> j) & 1) != 0) == (((lo >> j) & 1) == 0)) by(bit_vector) requires j<64;
    }
    assert forall |j:u32| j<64 implies #[trigger] bit(!hi,j as int) == !bit(hi,j as int) by {
        assert((((!hi >> j) & 1) != 0) == (((hi >> j) & 1) == 0)) by(bit_vector) requires j<64;
    }
    if next<64 {
        assert forall |i:int| next<=i<64 implies #[trigger] bit(!lo,i) by {
            let j=i as u32;
            assert(!bit(lo,j as int));
        }
        assert forall |i:int| 0<=i<next+span-64 implies #[trigger] bit(!hi,i) by {
            let j=i as u32;
            assert(!bit(hi,j as int));
        }
    }
    assert forall |p:int| min<=p<next && 64<p+span implies !#[trigger] open_across(!lo,!hi,p,span as int) by {
        if p<first {
            assert(p <= 63-left);
            let j=(63-left) as u32;
            assert(!bit(!lo,j as int));
        } else {
            assert(right<p+span-64 && right<64);
            assert(!bit(!hi,right as int));
        }
    }
}

pub open spec fn row_passed(board:Board,line:int,h:int,w:int,start:int,last:int,until:int) -> bool {
    forall |p:int| start<=p<=last && p<until ==> !#[trigger] fits(board,(line,p),h,w)
}

pub open spec fn row_first(board:Board,line:int,h:int,w:int,start:int,last:int,result:Option<usize>) -> bool {
    match result {
        Some(col) => start<=col<=last && fits(board,(line,col as int),h,w)
            && row_passed(board,line,h,w,start,last,col as int),
        None => row_passed(board,line,h,w,start,last,last+1),
    }
}

pub proof fn check_internal(board:Board,line:int,h:int,span:u32,pos:int,last:int,word:int,min:u32,
    open:u64,mask:u64,next:u32)
    requires
        1<=span<=16, min<64, 0<=word, pos<=word*64+min,
        row_open(board,line,h,word,open),
        row_passed(board,line,h,span as int,pos,last,word*64+min),
        forall |i:u32| i<64 ==> #[trigger] bit(mask,i as int) == (i>=min),
        first_word_run(open & mask,next,span),
    ensures
        next==64 ==> row_passed(board,line,h,span as int,pos,last,word*64+65-span),
        next<64 && word*64+next<=last ==> word*64+next<=usize::MAX ==> row_first(
            board,line,h,span as int,pos,last,Some((word*64+next) as usize)),
        next<64 && word*64+next>last ==> row_first(board,line,h,span as int,pos,last,None),
{
    let w=span as int;
    assert forall |i:u32| i<64 implies #[trigger] bit(open & mask,i as int)
        == (i>=min && bit(open,i as int)) by {
        assert(bit(mask,i as int)==(i>=min));
        assert((((open & mask) >> i) & 1 != 0) ==
            (((mask >> i) & 1 != 0) && ((open >> i) & 1 != 0))) by(bit_vector);
    }
    assert forall |p:int| min<=p && p+w<=64 implies
        #[trigger] fits(board,(line,word*64+p),h,w) == #[trigger] open_range(open & mask,p,w) by {
        if fits(board,(line,word*64+p),h,w) {
            assert forall |j:int| p<=j<p+w implies #[trigger] bit(open & mask,j) by {
                let i=j as u32;
                assert forall |r:int| line<=r<line+h implies !#[trigger] board.contains((r,word*64+i)) by {};
            }
        } else if open_range(open & mask,p,w) {
            let c = choose |c:Cell| board.contains(c) && covers((line,word*64+p),h,w,c);
            let i=(c.1-word*64) as u32;
            assert(bit(open & mask,i as int));
            assert(!board.contains((c.0,word*64+i)));
        }
    }
    if next<64 {
        assert(bit(open & mask,next as int));
        assert(min<=next && next+span<=64);
        assert(fits(board,(line,word*64+next),h,w));
    }
    let until=if next==64 { word*64+65-w } else { word*64+next };
    assert forall |p:int| pos<=p<=last && p<until implies !#[trigger] fits(board,(line,p),h,w) by {
        if p>=word*64+min {
            let i=p-word*64;
            assert(!open_range(open & mask,i,w));
        }
    }
}

pub proof fn check_crossing(board:Board,stride:int,line:int,h:int,span:u32,pos:int,last:int,word:int,min:u32,
    lo:u64,hi:u64,next:u32)
    requires
        1<=span<=16, min<64, 0<=word<stride, pos<=word*64+min, min==0 || pos==word*64+min, last+span<=stride*64,
        row_open(board,line,h,word,lo),
        word+1<stride ==> row_open(board,line,h,word+1,hi),
        word+1==stride ==> hi==0,
        row_passed(board,line,h,span as int,pos,last,word*64+65-span),
        next<=64, next<64 ==> min<=next && 64<next+span && open_across(lo,hi,next as int,span as int),
        forall |p:int| min<=p<next && 64<p+span ==> !#[trigger] open_across(lo,hi,p,span as int),
    ensures
        next==64 ==> row_passed(board,line,h,span as int,pos,last,(word+1)*64),
        next<64 && word*64+next<=last ==> word*64+next<=usize::MAX ==> row_first(
            board,line,h,span as int,pos,last,Some((word*64+next) as usize)),
        next<64 && word*64+next>last ==> row_first(board,line,h,span as int,pos,last,None),
{
    let w=span as int;
    assert forall |p:int| min<=p<64 && 64<p+w && word*64+p<=last implies
        #[trigger] fits(board,(line,word*64+p),h,w) == #[trigger] open_across(lo,hi,p,w) by {
        assert(word+1<stride);
        if fits(board,(line,word*64+p),h,w) {
            assert forall |j:int| p<=j<64 implies #[trigger] bit(lo,j) by {
                let i=j as u32;
                assert forall |r:int| line<=r<line+h implies !#[trigger] board.contains((r,word*64+i)) by {};
            }
            assert forall |j:int| 0<=j<p+w-64 implies #[trigger] bit(hi,j) by {
                let i=j as u32;
                assert forall |r:int| line<=r<line+h implies !#[trigger] board.contains((r,(word+1)*64+i)) by {};
            }
        } else if open_across(lo,hi,p,w) {
            let c=choose |c:Cell| board.contains(c) && covers((line,word*64+p),h,w,c);
            if c.1<(word+1)*64 {
                let i=(c.1-word*64) as u32;
                assert(bit(lo,i as int));
                assert(!board.contains((c.0,word*64+i)));
            } else {
                let i=(c.1-(word+1)*64) as u32;
                assert(bit(hi,i as int));
                assert(!board.contains((c.0,(word+1)*64+i)));
            }
        }
    }
    let until=word*64+next;
    assert forall |p:int| pos<=p<=last && p<until implies !#[trigger] fits(board,(line,p),h,w) by {
        if p>=word*64+65-w {
            let i=p-word*64;
            if i<min {
                // This is possible only for the first visited word and is
                // excluded by the caller's prefix cutoff.
                assert(false);
            }
            assert(!open_across(lo,hi,i,w));
        }
    }
}

pub proof fn finish_row_scan(board:Board,columns:int,h:int,w:int,start:Cell,cursor:Cell,next:Option<usize>)
    requires legal(cursor,columns,w), !before(cursor,start),
        passed(board,columns,h,w,start,cursor),
        row_first(board,cursor.0,h,w,cursor.1,columns-w,next),
    ensures match next {
        Some(c) => first_fit(board,columns,h,w,start,(cursor.0,c as int)),
        None => passed(board,columns,h,w,start,(cursor.0+1,0)),
    },
{
    let end=match next { Some(c) => (cursor.0,c as int), None => (cursor.0+1,0) };
    assert forall |p:Cell| legal(p,columns,w) && !before(p,start) && before(p,end)
        implies !#[trigger] fits(board,p,h,w) by {
        if !before(p,cursor) {
            assert(p.0==cursor.0 && cursor.1<=p.1<=columns-w);
        }
    }
}

} // verus!
