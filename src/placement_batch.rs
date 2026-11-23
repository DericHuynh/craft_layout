//! Pending leaf rectangles form a prefix of the eight lanes supplied to the snapper.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use super::{clean_tail, empty_mask, marked, rows};

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const CAPACITY: usize = 8;

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Run {
    pub len: usize,
    pub dirty: u8,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct Buffer<I, E> {
    pub ids: [I; CAPACITY],
    pub edges: [E; CAPACITY],
    pub pending: Run,
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out.pending.len == 0, out.pending.dirty == 0))]
pub fn empty_buffer<I: Copy, E: Copy>(id: I, edges: E) -> Buffer<I,E> {
    Buffer { ids: [id; CAPACITY], edges: [edges; CAPACITY], pending: Run { len: 0, dirty: 0 } }
}

impl<I: Copy, E: Copy> Buffer<I, E> {
    /// Return a run to publish on the eighth item and reset the cursor for the
    /// next leaf. The published prefix stays in the arrays until the next push.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(completed =>
        requires old(self).pending.len < CAPACITY, clean_tail(old(self).pending),
        ensures final(self).pending.len < CAPACITY, clean_tail(final(self).pending),
            match completed {
                Some(run) => run.len == CAPACITY && old(self).pending.len + 1 == CAPACITY
                    && final(self).pending.len == 0 && final(self).pending.dirty == 0
                    && rows(*final(self), run) == rows(*old(self), old(self).pending).push((id, edges, dirty)),
                None => final(self).pending.len == old(self).pending.len + 1
                    && rows(*final(self), final(self).pending) == rows(*old(self), old(self).pending).push((id, edges, dirty)),
            },
        no_unwind
    ))]
    pub fn push(&mut self, id: I, edges: E, dirty: bool) -> Option<Run> {
        let lane = self.pending.len;
        self.ids[lane] = id;
        self.edges[lane] = edges;
        if dirty { self.pending.dirty |= 1u8 << lane; }
        self.pending.len += 1;
        #[cfg(verus_keep_ghost)]
        proof! {
            let prior = old(self).pending.dirty;
            let mask = self.pending.dirty;
            assert(!marked(prior, lane));
            assert(marked(mask, lane) == dirty) by(bit_vector)
                requires lane < 8, mask == if dirty { prior | (1u8 << lane) } else { prior }, !marked(prior, lane);
            assert forall |j: usize| j < 8 && j != lane implies #[trigger] marked(mask, j) == marked(prior, j) by {
                assert((mask >> j) & 1u8 == (prior >> j) & 1u8) by(bit_vector)
                    requires j < 8, lane < 8, j != lane, mask == if dirty { prior | (1u8 << lane) } else { prior };
            }
            assert forall |j: usize| self.pending.len <= j < CAPACITY implies !#[trigger] marked(mask, j) by {
                assert(!marked(prior, j));
            }
            empty_mask();
            assert(rows(*self, self.pending) =~= rows(*old(self), old(self).pending).push((id, edges, dirty)));
        }
        if self.pending.len == CAPACITY { Some(self.drain()) } else { None }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(run =>
        requires old(self).pending.len <= CAPACITY,
        ensures run == old(self).pending, final(self).pending.len == 0, final(self).pending.dirty == 0,
            final(self).ids == old(self).ids, final(self).edges == old(self).edges,
        no_unwind
    ))]
    pub fn drain(&mut self) -> Run {
        let run = self.pending;
        self.pending = Run { len: 0, dirty: 0 };
        run
    }
}

impl Run {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires self.len <= CAPACITY, ensures out@ == ids@.take(self.len as int)
    ))]
    pub fn ids<I>(self, ids: &[I; CAPACITY]) -> &[I] { &ids[..self.len] }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires self.len <= CAPACITY,
        ensures out@ == old(edges)@.take(self.len as int)
    ))]
    pub fn edges<E>(self, edges: &mut [E; CAPACITY]) -> &mut [E] { &mut edges[..self.len] }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == marked(*old(mask), 0), *final(mask) == *old(mask) >> 1u8,
    no_unwind
))]
pub fn pop_dirty(mask: &mut u8) -> bool {
    let dirty = *mask & 1 != 0;
    #[cfg(verus_keep_ghost)]
    proof! { let word = *mask; assert(word >> 0usize == word) by(bit_vector); }
    *mask >>= 1;
    dirty
}
