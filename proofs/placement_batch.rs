//! The rows handed to a SIMD snapper are exactly the pending leaf prefix.
use vstd::prelude::*;

#[path = "../src/placement_batch.rs"]
pub(crate) mod kernel;
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

pub open spec fn published_rows<I,E>(ids: Seq<I>, snapped: Seq<E>, mask: u8, origin: [f32; 2])
    -> Seq<(I,E,bool,[f32; 2])> {
    Seq::new(ids.len(), |i: int| (ids[i], snapped[i], marked(mask, i as usize), origin))
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

}
