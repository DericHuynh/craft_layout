//! Keep track of a comparison against an ordered snapshot.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::{Kind, N_SLOTS, SlotBits, slot_index};
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::{Kind, N_SLOTS, SlotBits, slot_index};
use crate::declarations::ChildrenLayout;
use crate::vec_memory::{FallibleVecMemory, VecMemory, try_append};
use crate::prepare_nodes::RecordModel;

pub type OutputRecord<I> = (I, [u32; 8]);

/// The only host operation needed by the checked comparison.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait OutputIdentity: Copy {
    #[cfg_attr(verus_keep_ghost, verus_spec(equal => ensures equal == (self == other), no_unwind))]
    fn equals(self, other: Self) -> bool;
}

#[cfg(not(verus_keep_ghost))]
impl<I: Copy + Eq> OutputIdentity for I {
    #[inline]
    fn equals(self, other: Self) -> bool { self == other }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(equal => ensures equal == (*a == *b), no_unwind))]
pub(crate) fn same_words<const N: usize>(a: &[u32; N], b: &[u32; N]) -> bool {
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= N, forall |k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases N - i,
    ))]
    while i < N {
        if a[i] != b[i] { return false; }
        i += 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(a@ =~= b@);
        assert(*a =~= *b);
    }
    true
}

/// Read exact representations from a fixed record, clearing its optional
/// private scratch word before it is compared against a fresh solve.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures forall |j: int| 0 <= j < N ==> #[trigger] result@[j] ==
        if ignored == Some(j as usize) { 0 } else { values@[j].word() },
    no_unwind
))]
fn projected_words<T: SlotBits, const N: usize>(
    values: &[T; N], ignored: Option<usize>, mut words: [u32; N],
) -> [u32; N] {
    let mut i = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant i <= N, forall |j: int| 0 <= j < i ==> #[trigger] words@[j] ==
            if ignored == Some(j as usize) { 0 } else { values@[j].word() },
        decreases N - i,
    ))]
    while i < N {
        words[i] = if let Some(omitted) = ignored {
            if omitted == i { 0 } else { values[i].bits() }
        } else {
            values[i].bits()
        };
        i += 1;
    }
    words
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns scratch_slot(layout), no_unwind))]
pub(crate) fn scratch_slot(layout: ChildrenLayout) -> Option<usize> {
    match layout {
        // A collapsed-margin index is an address into the current arena.
        ChildrenLayout::Block => Some(slot_index(0, Kind::EvenShare)),
        // This word can hold a retained measurement constraint.
        ChildrenLayout::Free | ChildrenLayout::Stack { .. } => Some(slot_index(1, Kind::Flow)),
        ChildrenLayout::Wrap { .. } | ChildrenLayout::Grid { .. } => None,
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures forall |j: int| 0 <= j < N_SLOTS ==> #[trigger] result@[j] ==
        if scratch_slot(layout) == Some(j as usize) { 0 } else { values@[j].word() },
    no_unwind
))]
pub(crate) fn sizing_projection<T: SlotBits>(layout: ChildrenLayout, values: &[T; N_SLOTS]) -> [u32; N_SLOTS] {
    projected_words(values, scratch_slot(layout), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
}

pub(crate) type SizingRecord<I, const N: usize> = (I, [u32; N]);

#[cfg(not(verus_keep_ghost))]
pub(crate) trait SizingModel<const N: usize>: RecordModel {}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait SizingModel<const N: usize>: RecordModel {
    spec fn check_order(&self) -> Seq<Self::Id>;
    spec fn words(&self, node: Self::Id) -> [u32; N];
}

pub(crate) open spec fn record_live<S: RecordModel + ?Sized>(source: &S, node: S::Id) -> bool {
    (source.order().live)(node)
}

pub(crate) open spec fn ordered_node<I>(nodes: Seq<I>, index: int) -> Option<I> {
    if 0 <= index < nodes.len() { Some(nodes[index]) } else { None }
}

pub(crate) open spec fn ordered_sizes<S: SizingModel<N> + ?Sized, const N: usize>(source: &S)
    -> Seq<SizingRecord<S::Id, N>>
{
    Seq::new(source.check_order().len(), |i: int| (source.check_order()[i], source.words(source.check_order()[i])))
}

fn initial_sizes<I, const N: usize>(rows: &Vec<SizingRecord<I, N>>) -> (before: Ghost<Seq<SizingRecord<I, N>>>)
    ensures before@ == rows@,
    no_unwind
{
    Ghost(rows@)
}

fn zero() -> (i: Ghost<int>)
    ensures i@ == 0,
    no_unwind
{
    Ghost(0int)
}

fn advance(i: Ghost<int>) -> (next: Ghost<int>)
    ensures next@ == i@ + 1,
    no_unwind
{
    Ghost(i@ + 1)
}
}

/// Read-only primitives for the checked comparison. A sizing solve preserves
/// tree links and live identities even when none of the old values agree.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait SizingSource<const N: usize>: SizingModel<N> {
    #[cfg_attr(verus_keep_ghost, verus_spec(node =>
        ensures node == ordered_node(self.check_order(), 0),
            node.is_some() ==> record_live(self, node.unwrap()),
        no_unwind
    ))]
    fn first_size(&self) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires record_live(self, node), ordered_node(self.check_order(), index@) == Some(node),
        ensures next == ordered_node(self.check_order(), index@ + 1),
            next.is_some() ==> record_live(self, next.unwrap()),
        no_unwind
    ))]
    fn next_size(
        &self, node: Self::Id,
        #[cfg(verus_keep_ghost)] index: Ghost<int>,
    ) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires record_live(self, node), ensures result == self.words(node), no_unwind
    ))]
    fn sizing_words(&self, node: Self::Id) -> [u32; N];
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(complete =>
    requires forall |i: int| 0 <= i < old(rows).len() ==> record_live(source, (#[trigger] old(rows)@[i]).0),
    ensures complete ==> final(rows)@ == old(rows)@ + ordered_sizes(source),
        forall |i: int| 0 <= i < final(rows).len() ==> record_live(source, (#[trigger] final(rows)@[i]).0),
        !complete ==> exists |n: int| 0 <= n < source.check_order().len()
            && final(rows)@ == old(rows)@ + #[trigger] ordered_sizes(source).take(n),
    no_unwind
))]
pub(crate) fn capture_sizes<S: SizingSource<N> + ?Sized, M: FallibleVecMemory, const N: usize>(
    source: &S, rows: &mut Vec<SizingRecord<S::Id, N>>,
) -> bool {
    let mut next = source.first_size();
    #[cfg(verus_keep_ghost)]
    let original = initial_sizes(rows);
    #[cfg(verus_keep_ghost)]
    let mut index = zero();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant 0 <= index@ <= source.check_order().len(), next == ordered_node(source.check_order(), index@),
            original@ == old(rows)@,
            rows@ == original@ + ordered_sizes(source).take(index@),
            next.is_some() ==> record_live(source, next.unwrap()),
            forall |i: int| 0 <= i < rows.len() ==> record_live(source, (#[trigger] rows@[i]).0),
        decreases source.check_order().len() - index@,
    ))]
    loop {
        let Some(node) = next else {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(index@ == source.check_order().len());
                assert(ordered_sizes(source).take(index@) =~= ordered_sizes(source));
            }
            return true;
        };
        #[cfg(verus_keep_ghost)]
        proof! { assert(node == source.check_order()[index@]); }
        let row = (node, source.sizing_words(node));
        #[cfg(verus_keep_ghost)]
        let prior = initial_sizes(rows);
        if !try_append::<_, M>(rows, row) {
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(exists |n: int| 0 <= n < source.check_order().len()
                    && rows@ == old(rows)@ + #[trigger] ordered_sizes(source).take(n)) by {
                    assert(0 <= index@ < source.check_order().len());
                    assert(rows@ == old(rows)@ + ordered_sizes(source).take(index@));
                }
            }
            return false;
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let ordered = ordered_sizes(source);
            assert(ordered[index@] == row);
            assert(ordered.take(index@).push(row) =~= ordered.take(index@ + 1));
            assert(rows@ =~= original@ + ordered.take(index@ + 1));
            assert forall |i: int| 0 <= i < rows.len() implies record_live(source, (#[trigger] rows@[i]).0) by {
                if i < prior@.len() { assert(rows@[i] == prior@[i]); }
                else { assert(rows@[i] == row); }
            }
        }
        next = source.next_size(
            node,
            #[cfg(verus_keep_ghost)]
            index,
        );
        #[cfg(verus_keep_ghost)]
        { index = advance(index); }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(same =>
    requires forall |i: int| 0 <= i < rows.len() ==> record_live(source, (#[trigger] rows@[i]).0),
    ensures same == (forall |i: int| 0 <= i < rows.len() ==> source.words((#[trigger] rows@[i]).0) == rows@[i].1),
    no_unwind
))]
pub(crate) fn sizes_agree<S: SizingSource<N> + ?Sized, const N: usize>(
    source: &S, rows: &[SizingRecord<S::Id, N>],
) -> bool {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= rows.len(),
            forall |i: int| 0 <= i < rows.len() ==> record_live(source, (#[trigger] rows@[i]).0),
            forall |i: int| 0 <= i < index ==> source.words((#[trigger] rows@[i]).0) == rows@[i].1,
        decreases rows.len() - index,
    ))]
    while index < rows.len() {
        let (node, words) = &rows[index];
        if !same_words(&source.sizing_words(*node), words) { return false; }
        index += 1;
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Scratch<I, const N: usize> {
    pub values: Vec<SizingRecord<I, N>>,
    pub rectangles: Vec<OutputRecord<I>>,
    pub hint: usize,
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait ReferenceModel<const N: usize>: SizingModel<N> {}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) enum FrameEvent {
    AdapterFull,
    CanonicalFull,
    Placement(bool),
    RememberTopology,
}

pub(crate) trait ReferenceModel<const N: usize>: SizingModel<N> {
    spec fn candidate_view(&self) -> Seq<OutputRecord<Self::Id>>;
    spec fn last_reference_view(&self) -> Seq<OutputRecord<Self::Id>>;
    spec fn frame_events(&self) -> Seq<FrameEvent>;
    spec fn retains_view(&self) -> bool;
}
}

/// Rectangle capture reads the candidate geometry without publishing it. A
/// full reference solve always publishes its result through the real adapter.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Reference<W: Copy, const N: usize>: SizingSource<N> + ReferenceModel<N> {
    #[cfg_attr(verus_keep_ghost, verus_spec(buffers =>
        ensures buffers.values.len() == 0, buffers.rectangles.len() == 0,
            final(self).order() == old(self).order(), final(self).check_order() == old(self).check_order(),
            ordered_sizes(final(self)) == ordered_sizes(old(self)),
            final(self).candidate_view() == old(self).candidate_view(),
            final(self).frame_events() == old(self).frame_events(),
        no_unwind
    ))]
    fn take_scratch(&mut self) -> Scratch<Self::Id, N>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires buffers.values.len() == 0, buffers.rectangles.len() == 0,
        ensures final(self).order() == old(self).order(), final(self).check_order() == old(self).check_order(),
            ordered_sizes(final(self)) == ordered_sizes(old(self)),
            final(self).last_reference_view() == old(self).last_reference_view(),
            final(self).frame_events() == old(self).frame_events(),
        no_unwind
    ))]
    fn recycle_scratch(&mut self, buffers: Scratch<Self::Id, N>);

    #[cfg_attr(verus_keep_ghost, verus_spec(complete =>
        requires old(self).order().ordered(), old(self).order().closed_subtrees(),
        ensures final(self).order() == old(self).order(), final(self).check_order() == old(self).check_order(),
            final(self).frame_events() == old(self).frame_events(),
            complete ==> final(expected)@ == old(expected)@ + old(self).candidate_view(),
        no_unwind
    ))]
    fn capture_rectangles(&mut self, expected: &mut Vec<OutputRecord<Self::Id>>) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(agrees =>
        requires old(self).order().ordered(), old(self).order().closed_subtrees(),
        ensures final(self).order() == old(self).order(), final(self).check_order() == old(self).check_order(),
            final(self).frame_events() == old(self).frame_events().push(FrameEvent::CanonicalFull),
            final(expected)@ == old(expected)@,
            agrees == (old(expected)@ == final(self).last_reference_view()),
        no_unwind
    ))]
    fn compare_reference(&mut self, window: W, expected: &mut Vec<OutputRecord<Self::Id>>) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).order().ordered(), old(self).order().closed_subtrees(),
        ensures final(self).order() == old(self).order(), final(self).check_order() == old(self).check_order(),
            final(self).frame_events() == old(self).frame_events().push(FrameEvent::CanonicalFull),
        no_unwind
    ))]
    fn publish_reference(&mut self, window: W);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct CheckedResult {
    pub agrees: bool,
    #[cfg(verus_keep_ghost)]
    pub complete: bool,
}

/// Optional capture failure still publishes exactly one canonical layout.
/// A successful check requires the entire candidate to have been captured.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires old(source).order().ordered(), old(source).order().closed_subtrees(),
    ensures final(source).order() == old(source).order(),
        final(source).frame_events() == old(source).frame_events().push(FrameEvent::CanonicalFull),
        result.agrees == (result.complete && ordered_sizes(final(source)) == ordered_sizes(old(source))
            && final(source).last_reference_view() == old(source).candidate_view()),
    no_unwind
))]
pub(crate) fn checked<W: Copy, S: Reference<W, N> + ?Sized, M: FallibleVecMemory + VecMemory, const N: usize>(
    source: &mut S, window: W,
) -> CheckedResult {
    let mut buffers = source.take_scratch();
    let _ = M::try_reserve(&mut buffers.values, buffers.hint);
    let mut complete = capture_sizes::<_, M, N>(source, &mut buffers.values);
    if complete {
        let _ = M::try_reserve(&mut buffers.rectangles, buffers.values.len());
        complete = source.capture_rectangles(&mut buffers.rectangles);
    }
    let matches_view = if complete {
        source.compare_reference(window, &mut buffers.rectangles)
    } else {
        source.publish_reference(window);
        false
    };
    let matches = complete && matches_view && sizes_agree(source, buffers.values.as_slice());
    #[cfg(verus_keep_ghost)]
    proof! {
        if complete {
            let before = ordered_sizes(old(source));
            let reference = ordered_sizes(source);
            assert(buffers.values@ == before);
            assert(buffers.rectangles@ == old(source).candidate_view());
            if matches_view {
                let same = forall |i: int| 0 <= i < before.len() ==> source.words((#[trigger] before[i]).0) == before[i].1;
                assert(matches == same);
                assert(same == (reference == before)) by {
                    assert forall |i: int| 0 <= i < before.len() implies {
                        &&& (#[trigger] reference[i]).0 == before[i].0
                        &&& reference[i].1 == source.words(before[i].0)
                    } by {};
                    if same { assert(reference =~= before); }
                }
            }
            assert(matches == (reference == before && source.last_reference_view() == old(source).candidate_view()));
        }
    }
    M::clear(&mut buffers.values);
    M::clear(&mut buffers.rectangles);
    source.recycle_scratch(buffers);
    CheckedResult {
        agrees: matches,
        #[cfg(verus_keep_ghost)]
        complete,
    }
}

/// Once a mismatch is found, subsequent writes cannot make the frame agree.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub struct ViewCheck {
    pub cursor: usize,
    pub agrees: bool,
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(state => ensures state.cursor == 0 && state.agrees, no_unwind))]
pub fn start() -> ViewCheck { ViewCheck { cursor: 0, agrees: true } }

impl ViewCheck {
    /// Capture can stop when optional scratch storage is unavailable. The
    /// caller then keeps the full solve and reports the check as unsuccessful.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).cursor == old(self).cursor,
            final(self).agrees ==> old(self).agrees && final(expected)@ == old(expected)@.push(record),
            !final(self).agrees ==> final(expected)@ == old(expected)@,
        no_unwind
    ))]
    pub(crate) fn capture_record<I: Copy, M: FallibleVecMemory>(
        &mut self, expected: &mut Vec<OutputRecord<I>>, record: OutputRecord<I>,
    ) {
        if self.agrees && !try_append::<_, M>(expected, record) { self.agrees = false; }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.position(), no_unwind))]
    pub fn position(self) -> usize { self.cursor }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).agrees == (old(self).agrees && matches_next && old(self).cursor < usize::MAX),
            final(self).cursor == old(self).cursor + if final(self).agrees { 1int } else { 0int },
        no_unwind
    ))]
    pub fn compare(&mut self, matches_next: bool) {
        if self.agrees && matches_next {
            if let Some(next) = self.cursor.checked_add(1) {
                self.cursor = next;
                return;
            }
        }
        self.agrees = false;
    }

    /// Compare an entire published record, rejecting an extra callback
    /// before reading its expected identity or coordinates.
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).agrees == (
            old(self).agrees && old(self).cursor < expected.len()
                && expected@[old(self).cursor as int] == record
        ),
            final(self).cursor == old(self).cursor + if final(self).agrees { 1int } else { 0int },
        no_unwind
    ))]
    pub fn compare_record<I: OutputIdentity>(&mut self, expected: &[OutputRecord<I>], record: OutputRecord<I>) {
        let at = self.position();
        let matches_next = at < expected.len()
            && expected[at].0.equals(record.0)
            && same_words(&expected[at].1, &record.1);
        self.compare(matches_next);
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.finished(expected), no_unwind))]
    pub fn finished(self, expected: usize) -> bool {
        self.agrees && self.cursor == expected
    }

}
