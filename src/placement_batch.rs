//! Pending leaf rectangles form a prefix of the eight lanes supplied to the snapper.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use super::{clean_tail, empty_mask, marked, rows};
#[cfg(verus_keep_ghost)]
use super::published_rows;
#[cfg(verus_keep_ghost)]
use crate::placement::node::NodeModel;

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
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.pending.len == 0, out.pending.dirty == 0, clean_tail(out.pending),
    no_unwind
))]
pub fn empty_buffer<I: Copy, E: Copy>(id: I, edges: E) -> Buffer<I,E> {
    #[cfg(verus_keep_ghost)]
    proof! { empty_mask(); }
    Buffer {
        ids: [id, id, id, id, id, id, id, id],
        edges: [edges, edges, edges, edges, edges, edges, edges, edges],
        pending: Run { len: 0, dirty: 0 },
    }
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
                    && final(self).ids@.take(run.len as int) == old(self).ids@.take(old(self).pending.len as int).push(id)
                    && rows(*final(self), run) == rows(*old(self), old(self).pending).push((id, edges, dirty)),
                None => final(self).pending.len == old(self).pending.len + 1
                    && final(self).ids@.take(final(self).pending.len as int) == old(self).ids@.take(old(self).pending.len as int).push(id)
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
            assert(self.ids@.take(self.pending.len as int) =~= old(self).ids@.take(lane as int).push(id));
            assert(rows(*self, self.pending) =~= rows(*old(self), old(self).pending).push((id, edges, dirty)));
        }
        if self.pending.len == CAPACITY { Some(self.drain()) } else { None }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(run =>
        requires old(self).pending.len <= CAPACITY,
        ensures run == old(self).pending, run.len <= CAPACITY,
            final(self).pending.len == 0, final(self).pending.dirty == 0, clean_tail(final(self).pending),
            final(self).ids == old(self).ids, final(self).edges == old(self).edges,
        no_unwind
    ))]
    pub fn drain(&mut self) -> Run {
        let run = self.pending;
        self.pending = Run { len: 0, dirty: 0 };
        #[cfg(verus_keep_ghost)]
        proof! { empty_mask(); }
        run
    }
}

impl Run {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(empty => ensures empty == (self.len == 0), no_unwind))]
    pub fn is_empty(self) -> bool { self.len == 0 }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires self.len <= old(edges).len(),
        ensures out@ == old(edges)@.take(self.len as int),
            final(edges)@ == final(out)@ + old(edges)@.skip(self.len as int),
        no_unwind
    ))]
    pub fn edges<E>(self, edges: &mut [E]) -> &mut [E] { edges.split_at_mut(self.len).0 }

    /// Round only this run's active rectangles and publish in leaf order.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires self.len <= CAPACITY,
        ensures final(target).links() == old(target).links(),
            final(target).hidden() == old(target).hidden(),
                final(target).plain() == old(target).plain(),
            final(target).written() == old(target).written() + ids@.take(self.len as int),
            forall|id: I| !ids@.take(self.len as int).contains(id)
                ==> #[trigger] final(target).mark(id) == old(target).mark(id),
            final(target).output() == old(target).output() + published_rows(
            ids@.take(self.len as int), old(target).snapped(old(edges)@.take(self.len as int)), self.dirty, origin,
        ),
            final(edges)@ == old(target).snapped(old(edges)@.take(self.len as int))
                + old(edges)@.skip(self.len as int),
        no_unwind
    ))]
    pub fn publish<I: Copy, E: Copy, S: BatchTarget<I, E>>(
        self, ids: &[I; CAPACITY], edges: &mut [E; CAPACITY], target: &mut S, origin: [f32; 2],
    ) {
        let pending_edges = self.edges(edges);
        target.snap(pending_edges);
        let mask = self.dirty;
        let mut dirty = mask;
        let mut i = 0;
        #[cfg(verus_keep_ghost)]
        proof! { assert(mask >> 0usize == mask) by(bit_vector); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant
                i <= self.len <= CAPACITY,
                pending_edges.len() == self.len,
                pending_edges@ == old(target).snapped(old(edges)@.take(self.len as int)),
                mask == self.dirty, dirty == mask >> i,
                target.links() == old(target).links(),
                target.hidden() == old(target).hidden(), target.plain() == old(target).plain(),
                target.written() == old(target).written() + ids@.take(i as int),
                forall|id: I| !ids@.take(i as int).contains(id)
                    ==> #[trigger] target.mark(id) == old(target).mark(id),
                target.output() == old(target).output() + published_rows(
                    ids@.take(i as int), pending_edges@.take(i as int), self.dirty, origin,
                ),
            decreases self.len - i,
        ))]
        while i < self.len {
            let reset = pop_dirty(&mut dirty);
            #[cfg(verus_keep_ghost)]
            let marks = saved_marks(target);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(marked(mask >> i, 0) == marked(mask, i)) by(bit_vector);
                assert(((mask >> i) >> 1u8) == (mask >> (i+1) as usize)) by(bit_vector) requires i < 8;
                let before = published_rows(ids@.take(i as int), pending_edges@.take(i as int), self.dirty, origin);
                let after = published_rows(ids@.take(i + 1), pending_edges@.take(i + 1), self.dirty, origin);
                assert(after =~= before.push((ids[i as int], pending_edges[i as int], reset, origin)));
                assert(ids@.take(i + 1) =~= ids@.take(i as int).push(ids[i as int]));
                assert((old(target).written() + ids@.take(i as int)).push(ids[i as int])
                    =~= old(target).written() + ids@.take(i + 1));
            }
            target.write(ids[i], pending_edges[i], reset, origin);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall |id: I| !ids@.take(i + 1).contains(id) implies
                    #[trigger] target.mark(id) == old(target).mark(id) by {
                    assert(!ids@.take(i as int).contains(id));
                    assert(ids@.take(i + 1)[i as int] == ids[i as int]);
                    assert(ids@.take(i + 1).contains(ids[i as int]));
                    assert(id != ids[i as int]);
                    assert(target.mark(id) == (marks@)(id));
                };
            }
            i += 1;
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub trait OutputModel<I, E>: NodeModel<I> {
    spec fn output(&self) -> Seq<(I, E, bool, [f32; 2])>;
    spec fn snapped(&self, edges: Seq<E>) -> Seq<E>;
}

fn saved_marks<I, T: NodeModel<I>>(target: &T) -> (out: Ghost<spec_fn(I) -> Option<crate::placement::PlacementWork>>)
    ensures out@ == (|id: I| target.mark(id)),
    no_unwind
{ Ghost(|id: I| target.mark(id)) }
}

#[cfg(not(verus_keep_ghost))]
pub trait OutputModel<I, E> {}

/// The snapper and the adapter receiving the leaf rectangles must both return normally.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait BatchTarget<I, E>: OutputModel<I, E> {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).output() == old(self).output(), final(self).links() == old(self).links(),
            final(self).hidden() == old(self).hidden(),
                final(self).plain() == old(self).plain(),
            final(self).written() == old(self).written(),
            forall|id: I| #[trigger] final(self).mark(id) == old(self).mark(id),
            final(edges)@ == old(self).snapped(old(edges)@),
            final(edges).len() == old(edges).len(),
        no_unwind
    ))]
    fn snap(&mut self, edges: &mut [E]);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).output() == old(self).output().push((id, edges, dirty, origin)),
            final(self).links() == old(self).links(),
            final(self).hidden() == old(self).hidden(),
                final(self).plain() == old(self).plain(),
            final(self).written() == old(self).written().push(id),
            forall|other: I| other != id ==> #[trigger] final(self).mark(other) == old(self).mark(other),
        no_unwind
    ))]
    fn write(&mut self, id: I, edges: E, dirty: bool, origin: [f32; 2]);
}

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
