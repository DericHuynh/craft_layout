//! Rectangle-based first-fit search for grids with a large packed footprint.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use crate::vec_memory::{CapacityMemory, VecMemory, append_bounded};
#[cfg(verus_keep_ghost)]
use crate::vec_memory::capacity_limit;
#[cfg(all(test, not(verus_keep_ghost)))]
use crate::vec_memory::RustVec;

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Occupied {
    pub rows: (u128, u128),
    pub cols: (usize, usize),
}

#[cfg(verus_keep_ghost)]
verus! {
    pub(crate) type GridItems<I> = Map<I, (Option<I>, Option<(u16, u16)>)>;
    pub(crate) type CellWrites<I> = Seq<(I, (u128, usize))>;

    pub(crate) open spec fn clamped_height(height: u16) -> int {
        vstd::math::max(height as int, 1)
    }

    pub(crate) open spec fn clamped_width(width: usize, columns: usize) -> int {
        vstd::math::min(vstd::math::max(width as int, 1), columns as int)
    }

    pub(crate) open spec fn cell_rectangle(cell: (u128, usize), columns: usize, height: u16, width: usize) -> Occupied {
        Occupied {
            rows: (cell.0, (cell.0 + clamped_height(height)) as u128),
            cols: (cell.1, (cell.1 + clamped_width(width, columns)) as usize),
        }
    }

    pub(crate) trait InputModel {
        type Id: Copy;

        spec fn first_item(&self) -> Option<Self::Id>;
        spec fn ordered_items(&self) -> GridItems<Self::Id>;
        spec fn cell_writes(&self) -> CellWrites<Self::Id>;
        spec fn live(&self, child: Self::Id) -> bool;
        spec fn remaining(&self, next: Option<Self::Id>) -> nat;
        spec fn remaining_placements(&self, next: Option<Self::Id>) -> nat;
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait InputModel {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
/// The IDs which receive cells in this stable suffix. Disabled and free
/// siblings still advance the cursor.
pub(crate) open spec fn placement_ids<I>(items: GridItems<I>, next: Option<I>, steps: nat) -> Seq<I>
    decreases steps,
{
    match next {
        Some(child) if steps > 0 => {
            let item = items[child];
            let tail = placement_ids(items, item.0, (steps - 1) as nat);
            if item.1.is_some() { seq![child] + tail } else { tail }
        }
        _ => Seq::empty(),
    }
}

pub(crate) open spec fn written_ids<I>(writes: CellWrites<I>) -> Seq<I> {
    Seq::new(writes.len(), |i: int| writes[i].0)
}

pub(crate) open spec fn extends_writes<I>(before: CellWrites<I>, after: CellWrites<I>) -> bool {
    before.len() <= after.len() && after.take(before.len() as int) == before
}

pub(crate) proof fn write_keeps_prefix<I>(before: CellWrites<I>, after: CellWrites<I>, child: I, cell: (u128, usize))
    requires extends_writes(before, after),
    ensures extends_writes(before, after.push((child, cell))),
        written_ids(after.push((child, cell)).skip(before.len() as int))
            == written_ids(after.skip(before.len() as int)).push(child),
{
    assert(after.push((child, cell)).take(before.len() as int) =~= before);
    assert(after.push((child, cell)).skip(before.len() as int)
        =~= after.skip(before.len() as int).push((child, cell)));
    assert(written_ids(after.push((child, cell)).skip(before.len() as int))
        =~= written_ids(after.skip(before.len() as int)).push(child));
}

/// When a probe retries, any provisional writes precede the complete
/// assignment. Consumers observe the final write for each eligible child.
pub(crate) open spec fn complete_writes<I>(writes: CellWrites<I>, expected: Seq<I>) -> bool {
    &&& expected.len() <= writes.len()
    &&& written_ids(writes.skip(writes.len() - expected.len())) == expected
}

pub(crate) open spec fn writes_run<I: InputModel>(before: &I, after: &I, first: Option<I::Id>) -> bool {
    extends_writes(before.cell_writes(), after.cell_writes()) &&
    written_ids(after.cell_writes().skip(before.cell_writes().len() as int))
        == placement_ids(before.ordered_items(), first, before.remaining(first))
}

pub(crate) open spec fn same_items<I: InputModel + ?Sized>(before: &I, after: &I) -> bool {
    &&& before.first_item() == after.first_item()
    &&& before.ordered_items() == after.ordered_items()
    &&& forall |next: Option<I::Id>| #[trigger] after.remaining(next) == before.remaining(next)
    &&& forall |next: Option<I::Id>| #[trigger] after.remaining_placements(next) == before.remaining_placements(next)
    &&& forall |id: I::Id| #[trigger] after.live(id) == before.live(id)
}
}

/// The native adapter binds this to stable sibling links, span reads, and
/// cell publication. The suffix rank counts the remaining siblings.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Inputs: InputModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires self.live(child),
        ensures out == self.ordered_items()[child],
            self.remaining(out.0) + 1 == self.remaining(Some(child)),
            self.remaining_placements(out.0) + (if out.1.is_some() { 1nat } else { 0nat })
                == self.remaining_placements(Some(child)),
            out.0.is_some() ==> self.live(out.0.unwrap()),
        no_unwind
    ))]
    fn inspect(&self, child: Self::Id) -> (Option<Self::Id>, Option<(u16, u16)>);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).live(child),
        ensures same_items(old(self), final(self)),
            final(self).cell_writes() == old(self).cell_writes().push((child, cell)),
        no_unwind
    ))]
    fn publish(&mut self, child: Self::Id, cell: (u128, usize));
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Cursor {
    pub rows: u128,
    pub start: (u128, usize),
    // Only forward search may skip these rectangles. Backfill starts at row zero.
    pub first_live: usize,
}

#[cfg(verus_keep_ghost)]
verus! {
spec fn sparse_view(cursor: Cursor, occupied: Seq<Occupied>) -> frame::CanonicalGrid {
    frame::CanonicalGrid { board: sparse_board(occupied), rows: cursor.rows as int,
        forward: (cursor.start.0 as int, cursor.start.1 as int) }
}

impl Cursor {
    pub closed spec fn valid(self, occupied: Seq<Occupied>, columns: usize) -> bool {
        &&& self.rows <= occupied.len() * (u16::MAX as int)
        &&& self.start.0 <= self.rows && self.start.1 <= columns
        &&& self.start.0 == self.rows ==> self.start.1 == 0
        &&& self.first_live <= occupied.len()
        &&& forall |i: int| 0 <= i < self.first_live ==> #[trigger] expires_before(occupied[i], (self.start.0 as int, self.start.1 as int))
        &&& forall |i: int| 0 <= i < occupied.len() ==>
            #[trigger] valid_rectangle(occupied[i], self.rows)
    }
}
}

#[cold]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(rows =>
    requires columns > 0, old(source).remaining_placements(next) <= capacity_limit::<Occupied>(),
        next.is_some() ==> old(source).live(next.unwrap()),
    ensures same_items(old(source), final(source)), writes_run(old(source), final(source), next),
        complete_writes(final(source).cell_writes(),
            placement_ids(old(source).ordered_items(), next, old(source).remaining(next))),
        ({
            let result = frame::canonical_run(old(source).ordered_items(), next, old(source).remaining(next),
                frame::empty_grid(), columns, backfill);
            rows as int == result.0.rows && final(source).cell_writes() == old(source).cell_writes() + result.1
        }),
    no_unwind
))]
pub(crate) fn assign<I: Inputs, S: CapacityMemory + VecMemory>(
    source: &mut I, next: Option<I::Id>, columns: usize, backfill: bool,
) -> u128 {
    assign_with::<I, S>(source, &mut S::empty(), next, columns, backfill)
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(rows =>
    requires columns > 0, old(occupied).len() == 0,
        old(source).remaining_placements(first) <= capacity_limit::<Occupied>(),
        first.is_some() ==> old(source).live(first.unwrap()),
    ensures rows <= final(occupied).len() * (u16::MAX as int),
        same_items(old(source), final(source)), writes_run(old(source), final(source), first),
        complete_writes(final(source).cell_writes(),
            placement_ids(old(source).ordered_items(), first, old(source).remaining(first))),
        ({
            let result = frame::canonical_run(old(source).ordered_items(), first, old(source).remaining(first),
                frame::empty_grid(), columns, backfill);
            rows as int == result.0.rows && final(source).cell_writes() == old(source).cell_writes() + result.1
        }),
    no_unwind
))]
fn assign_with<I: Inputs, S: CapacityMemory>(source: &mut I, occupied: &mut Vec<Occupied>, first: Option<I::Id>,
    columns: usize, backfill: bool,
) -> u128 {
    let mut cursor = new_cursor();
    let mut next = first;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(occupied@ =~= Seq::<Occupied>::empty());
        assert(sparse_board(occupied@) =~= ISet::<Cell>::empty());
        assert(sparse_view(cursor, occupied@) == frame::empty_grid());
        let log = source.cell_writes();
        assert(log.take(log.len() as int) =~= log);
        assert(written_ids(log.skip(log.len() as int)) =~= Seq::<I::Id>::empty());
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant columns > 0, cursor.valid(occupied@, columns),
            same_items(old(source), source),
            occupied.len() + source.remaining_placements(next) <= capacity_limit::<Occupied>(),
            next.is_some() ==> source.live(next.unwrap()),
            extends_writes(old(source).cell_writes(), source.cell_writes()),
            written_ids(source.cell_writes().skip(old(source).cell_writes().len() as int))
                + placement_ids(source.ordered_items(), next, source.remaining(next))
                == placement_ids(old(source).ordered_items(), first, old(source).remaining(first)),
            ({
                let tail = frame::canonical_run(source.ordered_items(), next, source.remaining(next),
                    sparse_view(cursor, occupied@), columns, backfill);
                let expected = frame::canonical_run(old(source).ordered_items(), first, old(source).remaining(first),
                    frame::empty_grid(), columns, backfill);
                tail.0 == expected.0 &&
                    source.cell_writes() + tail.1 == old(source).cell_writes() + expected.1
            }),
        decreases source.remaining(next),
    ))]
    loop {
        let Some(child) = next else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(placement_ids(source.ordered_items(), next, source.remaining(next))
                    == Seq::<I::Id>::empty());
                frame::canonical_run_end(source.ordered_items(), source.remaining(next),
                    sparse_view(cursor, occupied@), columns, backfill);
                assert(source.cell_writes() + Seq::<(I::Id, (u128, usize))>::empty() =~= source.cell_writes());
            }
            return cursor.rows;
        };
        let (following, span) = source.inspect(child);
        #[cfg(verus_keep_ghost)]
        proof! {
            frame::canonical_run_step(source.ordered_items(), child, source.remaining(next),
                sparse_view(cursor, occupied@), columns, backfill);
        }
        next = following;
        if let Some((height, width)) = span {
            let cell = cursor.place_with::<S>(occupied, columns, height, width as usize, backfill);
            #[cfg(verus_keep_ghost)]
            proof! { write_keeps_prefix(old(source).cell_writes(), source.cell_writes(), child, cell); }
            source.publish(child, cell);
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(cursor =>
    ensures cursor.rows == 0, cursor.start == (0u128, 0usize), forall |columns: usize| cursor.valid(Seq::empty(), columns),
    no_unwind
))]
pub const fn new_cursor() -> Cursor {
    Cursor { rows: 0, start: (0, 0), first_live: 0 }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(end =>
    requires first <= occupied.len(),
        forall |i: int| 0 <= i < first ==> #[trigger] expires_before(occupied@[i], (start.0 as int, start.1 as int)),
    ensures first <= end <= occupied.len(),
        forall |i: int| 0 <= i < end ==> #[trigger] expires_before(occupied@[i], (start.0 as int, start.1 as int)),
    no_unwind
))]
fn skip_expired(occupied: &[Occupied], first: usize, start: (u128, usize)) -> usize {
    let mut next = first;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant first <= next <= occupied.len(),
            forall |i: int| 0 <= i < next ==> #[trigger] expires_before(occupied@[i], (start.0 as int, start.1 as int)),
        decreases occupied.len() - next,
    ))]
    while next < occupied.len() {
        let rect = occupied[next];
        if rect.rows.1 > start.0 && (rect.rows.1 - 1 != start.0 || rect.cols.1 > start.1) {
            break;
        }
        next += 1;
    }
    next
}

impl Cursor {
    #[cfg(all(test, not(verus_keep_ghost)))]
    #[inline]
    pub fn place(&mut self, occupied: &mut Vec<Occupied>, columns: usize, height: u16, width: usize,
        backfill: bool,
    ) -> (u128, usize) {
        self.place_with::<RustVec>(occupied, columns, height, width, backfill)
    }

    /// Append one rectangle. A row can grow by at most the incoming span, so
    /// even usize::MAX rectangles cannot overflow the u128 row coordinate.
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(cell =>
        requires old(self).valid(old(occupied)@, columns), columns > 0,
            old(occupied).len() < capacity_limit::<Occupied>(),
        ensures final(self).valid(final(occupied)@, columns),
            final(occupied)@ == old(occupied)@.push(cell_rectangle(cell, columns, height, width)),
            final(self).rows == vstd::math::max(old(self).rows as int, cell_rectangle(cell, columns, height, width).rows.1 as int),
            final(self).rows <= old(self).rows + clamped_height(height),
            final(self).start == if backfill { old(self).start }
                else { (cell.0, cell_rectangle(cell, columns, height, width).cols.1) },
            first_fit(sparse_board(old(occupied)@), columns as int, clamped_height(height),
                clamped_width(width, columns),
                if backfill { (0int, 0int) } else { (old(self).start.0 as int, old(self).start.1 as int) },
                (cell.0 as int, cell.1 as int)),
            ({
                let expected = frame::grid_step(sparse_view(*old(self), old(occupied)@), columns as int, backfill,
                    clamped_height(height), clamped_width(width, columns));
                &&& (cell.0 as int, cell.1 as int) == expected.1
                &&& sparse_view(*final(self), final(occupied)@) == expected.0
            }),
        no_unwind
    ))]
    fn place_with<S: CapacityMemory>(&mut self, occupied: &mut Vec<Occupied>, columns: usize, height: u16, width: usize,
        backfill: bool,
    ) -> (u128, usize) {
        #[cfg(verus_keep_ghost)]
        let requested_span = (height, width);
        let start = if backfill { (0, 0) } else { self.start };
        let height = if height == 0 { 1 } else { height };
        let h = height as u128;
        let width = if width == 0 { 1 } else { width };
        let width = if width < columns { width } else { columns };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(occupied@.len() == occupied.len());
            assert(occupied.len() <= u64::MAX);
            assert(self.rows <= occupied.len() * (u16::MAX as int));
            assert(self.rows + h <= u128::MAX);
        }
        let board = occupied.as_slice();
        let (first, live) = if backfill {
            (0, board)
        } else {
            let first = skip_expired(board, self.first_live, start);
            (first, board.split_at(first).1)
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(live@ =~= board@.subrange(first as int, board.len() as int));
            assert forall |i:int| 0 <= i < live.len() implies #[trigger] valid_rectangle(live@[i], self.rows) by {
                assert(live@[i] == board@[first+i]);
            }
        }
        let (row, col) = find_cell(live, columns, start, self.rows, h, width);
        #[cfg(verus_keep_ghost)]
        proof! {
            expired_prefix_preserves_first_fit(board@, first as int, columns as int, h as int, width as int,
                (start.0 as int, start.1 as int), (row as int, col as int));
        }
        let bottom = row + h;
        let right = col + width;
        if self.rows < bottom { self.rows = bottom; }
        if !backfill {
            self.start = (row, right);
            self.first_live = first;
        }
        let rect = Occupied { rows: (row, bottom), cols: (col, right) };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(rect == cell_rectangle((row, col), columns, requested_span.0, requested_span.1));
        }
        append_bounded::<Occupied, S>(occupied, rect);
        #[cfg(verus_keep_ghost)]
        proof! {
            frame::canonical_fit(sparse_view(*old(self), old(occupied)@), columns as int, backfill,
                clamped_height(requested_span.0), clamped_width(requested_span.1, columns), (row as int, col as int));
            sparse_board_adds(old(occupied)@, rect, (row as int, col as int), h as int, width as int);
            let forward = (self.start.0 as int, self.start.1 as int);
            let prior_forward = (old(self).start.0 as int, old(self).start.1 as int);
            assert forall |i:int| 0 <= i < self.first_live implies #[trigger] expires_before(occupied@[i], forward) by {
                assert(occupied@[i] == old(occupied)@[i]);
                if !backfill {
                    assert(!before(forward, prior_forward));
                    expiry_keeps(occupied@[i], prior_forward, forward);
                }
            }
            assert forall |i: int| 0 <= i < occupied.len() implies
                #[trigger] valid_rectangle(occupied@[i], self.rows) by {
                if i < old(occupied).len() {
                    assert(valid_rectangle(old(occupied)@[i], old(self).rows));
                }
            }
        }
        (row, col)
    }
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
fn probe(occupied: &[Occupied], row: u128, col: usize, bottom: u128, right: usize, max_row: u128) -> (usize, u128) {
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
    requires 1 <= w <= columns, h > 0, max_row + h <= u128::MAX,
        start.0 <= max_row, start.0 == max_row ==> start.1 == 0,
        forall |i:int| 0 <= i < occupied.len() ==> #[trigger] valid_rectangle(occupied@[i], max_row),
    ensures result.0 <= max_row,
        first_fit(sparse_board(occupied@), columns as int, h as int, w as int,
            (start.0 as int, start.1 as int), (result.0 as int, result.1 as int)),
    no_unwind
))]
pub fn find_cell(occupied: &[Occupied], columns: usize, start: (u128, usize), max_row: u128, h: u128, w: usize) -> (u128, usize) {
    let (mut row, mut first) = start;
    let last = columns - w;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant row <= max_row, row == max_row ==> first == 0, last == columns-w,
            h>0, w>0, max_row+h<=u128::MAX,
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
                h>0, w>0, max_row+h<=u128::MAX,
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
