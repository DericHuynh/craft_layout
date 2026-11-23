//! The rows handed to a SIMD snapper are exactly the pending leaf prefix.
use vstd::prelude::*;

#[path = "../src/placement_batch.rs"]
mod kernel;
use kernel::{Buffer, CAPACITY, Run};

verus! {

pub open spec fn marked(mask: u8, lane: usize) -> bool { (mask >> lane) & 1u8 != 0 }

pub open spec fn clean_tail(run: Run) -> bool {
    forall |j: usize| run.len <= j < CAPACITY ==> !#[trigger] marked(run.dirty, j)
}

pub proof fn empty_mask()
    ensures forall |j: usize| j < CAPACITY ==> !#[trigger] marked(0u8, j),
{
    assert forall |j: usize| j < CAPACITY implies !#[trigger] marked(0u8, j) by {
        assert(((0u8 >> j) & 1u8) == 0u8) by(bit_vector);
    }
}

pub open spec fn rows<I,E>(buffer: Buffer<I,E>, run: Run) -> Seq<(I,E,bool)> {
    Seq::new(run.len as nat, |n: int| (buffer.ids[n], buffer.edges[n], marked(run.dirty, n as usize)))
}

// A boundary flushes the preceding leaf run before the next callback.
pub open spec fn leaves<I,E>(events: Seq<Option<(I,E,bool)>>, n: nat) -> Seq<(I,E,bool)>
    decreases n,
{
    if n == 0 { Seq::empty() } else {
        let earlier = leaves(events, (n - 1) as nat);
        match events[n-1] { Some(row) => earlier.push(row), None => earlier }
    }
}

fn ordered_batches<I: Copy, E: Copy>(
    events: &[Option<(I,E,bool)>], initial_id: I, initial_edge: E,
) -> (emitted: Ghost<Seq<(I,E,bool)>>)
    ensures emitted@ == leaves(events@, events.len() as nat),
{
    let mut buffer = kernel::empty_buffer(initial_id, initial_edge);
    let ghost mut published = Seq::<(I,E,bool)>::empty();
    proof {
        empty_mask();
        assert(rows(buffer, buffer.pending) =~= Seq::<(I,E,bool)>::empty());
    }
    let mut i = 0;
    while i < events.len()
        invariant
            i <= events.len(), buffer.pending.len < CAPACITY, clean_tail(buffer.pending),
            published + rows(buffer, buffer.pending) == leaves(events@, i as nat),
        decreases events.len() - i,
    {
        let run = match events[i] {
            Some((id, edge, dirty)) => buffer.push(id, edge, dirty),
            None => Some(buffer.drain()),
        };
        if let Some(completed) = run {
            proof {
                assert(rows(buffer, buffer.pending) =~= Seq::<(I,E,bool)>::empty());
                empty_mask();
                published = published + rows(buffer, completed);
            }
        }
        proof {
            if let Some(row) = events[i as int] {
                assert((published + rows(buffer, buffer.pending)) =~= leaves(events@, i as nat).push(row));
            }
        }
        i += 1;
    }
    let last = buffer.drain();
    Ghost(published + rows(buffer, last))
}

// Read the same two prefixes and consume the dirty mask as the publisher does.
// `edges` may already hold the snapped coordinates for this run.
fn visit_ready_rows<I: Copy, E: Copy>(
    ids: &[I; CAPACITY], edges: &mut [E; CAPACITY], run: Run,
) -> (emitted: Ghost<Seq<(I,E,bool)>>)
    requires run.len <= CAPACITY,
    ensures emitted@.len() == run.len,
        forall |j: int| 0 <= j < run.len ==> #[trigger] emitted@[j]
            == (ids[j], old(edges)[j], marked(run.dirty, j as usize)),
{
    let ids = run.ids(ids);
    let edges = run.edges(edges);
    let mask = run.dirty;
    let mut rest = mask;
    let mut i = 0;
    let ghost mut out = Seq::<(I,E,bool)>::empty();
    assert(mask >> 0usize == mask) by(bit_vector);
    while i < ids.len()
        invariant i <= run.len <= CAPACITY, out.len() == i,
            ids.len() == run.len, edges.len() == run.len,
            mask == run.dirty, rest == mask >> i,
            forall |j: int| 0 <= j < i ==> #[trigger] out[j] == (ids[j], edges[j], marked(run.dirty, j as usize)),
        decreases run.len - i,
    {
        let id = ids[i];
        let edge = edges[i];
        let dirty = kernel::pop_dirty(&mut rest);
        proof {

            assert(marked(mask >> i, 0) == marked(mask, i)) by(bit_vector);
            assert(dirty == marked(mask, i));
            assert(((mask >> i) >> 1u8) == (mask >> (i+1) as usize)) by(bit_vector) requires i < 8;
            out = out.push((id, edge, dirty));
        }
        i += 1;
    }
    Ghost(out)
}

}
