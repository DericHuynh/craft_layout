//! Compare placement emitted by the two sizing runs without publishing twice.
#![allow(unexpected_cfgs)]
#[cfg(not(verus_keep_ghost))]
use crate::*;
#[cfg(not(verus_keep_ghost))]
use crate::vec_memory::RustVec;
use crate::vec_memory::FallibleVecMemory;
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::SlotBits;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::SlotBits;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(not(verus_keep_ghost))]
#[path = "../view_check.rs"]
mod view_check;
#[cfg(verus_keep_ghost)]
use super::kernel as view_check;
use view_check::{OutputIdentity, ViewCheck};

pub(crate) use view_check::OutputRecord;
#[cfg(not(verus_keep_ghost))]
pub(super) use view_check::{Reference, ReferenceModel, Scratch, SizingModel, SizingSource, checked, sizing_projection};

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn rectangle_words<W: SlotBits>(rect: [[W; 2]; 2], local: [[W; 2]; 2]) -> Seq<u32> {
    seq![rect[0][0].word(), rect[0][1].word(), rect[1][0].word(), rect[1][1].word(),
        local[0][0].word(), local[0][1].word(), local[1][0].word(), local[1][1].word()]
}

pub(crate) open spec fn records_rectangle<I, W: SlotBits>(
    record: OutputRecord<I>, id: I, rect: [[W; 2]; 2], local: [[W; 2]; 2],
) -> bool {
    record.0 == id && record.1@ == rectangle_words(rect, local)
}

pub(crate) trait WriterModel<I> {
    spec fn writes(&self) -> Seq<OutputRecord<I>>;
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait WriterModel<I> {}

/// A call to the host's rectangle sink, modeled by its exact arguments.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Writer<I, W: SlotBits>: WriterModel<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).writes().len() == old(self).writes().len() + 1,
            final(self).writes().drop_last() == old(self).writes(),
            records_rectangle(final(self).writes().last(), id, rect, local),
        no_unwind
    ))]
    fn write_rect(&mut self, id: I, rect: [[W; 2]; 2], local: [[W; 2]; 2]);
}

#[cfg(not(verus_keep_ghost))]
impl<T: TreeAdapter + ?Sized> WriterModel<T::NodeId> for T {}

#[cfg(not(verus_keep_ghost))]
impl<T: TreeAdapter + ?Sized> Writer<T::NodeId, f32> for T {
    #[inline]
    fn write_rect(&mut self, id: T::NodeId, absolute: [[f32; 2]; 2], local: [[f32; 2]; 2]) {
        crate::placement_adapter::publish(self, id, absolute, local);
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(record =>
    ensures records_rectangle(record, id, rect, local), no_unwind
))]
fn packed_record<I, W: SlotBits>(id: I, rect: [[W; 2]; 2], local: [[W; 2]; 2]) -> OutputRecord<I> {
    let [[left, right], [top, bottom]] = rect;
    let [[local_left, local_right], [local_top, local_bottom]] = local;
    let words = [left.bits(), right.bits(), top.bits(), bottom.bits(),
        local_left.bits(), local_right.bits(), local_top.bits(), local_bottom.bits()];
    #[cfg(verus_keep_ghost)]
    proof! { assert(words@ =~= rectangle_words(rect, local)); }
    (id, words)
}

/// A captured rectangle stays in scratch. A reference rectangle reaches the
/// host exactly once, even after a mismatch has already been detected.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures if comparing {
        let written = final(writer).writes();
        let before = old(check);
        &&& final(expected)@ == old(expected)@
        &&& written.len() == old(writer).writes().len() + 1
        &&& written.drop_last() == old(writer).writes()
        &&& records_rectangle(written.last(), id, rect, local)
        &&& final(check).agrees == (before.agrees && before.cursor < old(expected).len()
            && old(expected)@[before.cursor as int] == written.last())
        &&& final(check).cursor == before.cursor + if final(check).agrees { 1int } else { 0int }
    } else {
        &&& final(writer).writes() == old(writer).writes()
        &&& final(check).cursor == old(check).cursor
        &&& if final(check).agrees {
            &&& old(check).agrees
            &&& final(expected)@.len() == old(expected)@.len() + 1
            &&& final(expected)@.drop_last() == old(expected)@
            &&& records_rectangle(final(expected)@.last(), id, rect, local)
        } else { final(expected)@ == old(expected)@ }
    },
    no_unwind
))]
fn write_checked<I: OutputIdentity, W: SlotBits, T: Writer<I, W> + ?Sized, M: FallibleVecMemory>(
    check: &mut ViewCheck, expected: &mut Vec<OutputRecord<I>>, writer: &mut T,
    id: I, rect: [[W; 2]; 2], local: [[W; 2]; 2], comparing: bool,
) {
    let record = packed_record(id, rect, local);
    if comparing {
        check.compare_record(expected.as_slice(), record);
        writer.write_rect(id, rect, local);
        #[cfg(verus_keep_ghost)]
        proof! {
            let written = writer.writes().last();
            assert(written.1 =~= record.1);
            assert(written == record);
        }
    } else {
        check.capture_record::<_, M>(expected, record);
    }
}

#[cfg(not(verus_keep_ghost))]
pub(super) struct CheckedView<'a, T: TreeAdapter + ?Sized> {
    inner: &'a mut T,
    expected: &'a mut Vec<OutputRecord<T::NodeId>>,
    comparing: bool,
    order: ViewCheck,
}

#[cfg(not(verus_keep_ghost))]
impl<'a, T: TreeAdapter + ?Sized> CheckedView<'a, T> {
    pub(super) fn capture(inner: &'a mut T, expected: &'a mut Vec<OutputRecord<T::NodeId>>) -> Self {
        Self { inner, expected, comparing: false, order: view_check::start() }
    }

    pub(super) fn compare(inner: &'a mut T, expected: &'a mut Vec<OutputRecord<T::NodeId>>) -> Self {
        Self { comparing: true, ..Self::capture(inner, expected) }
    }

    pub(super) fn agrees(&self) -> bool {
        self.order.finished(self.expected.len())
    }

    pub(super) fn captured(&self) -> bool {
        self.order.agrees
    }
}

#[cfg(not(verus_keep_ghost))]
impl<T: TreeAdapter + ?Sized> TreeAdapter for CheckedView<'_, T> {
    type NodeId = T::NodeId;

    fn root(&self) -> Self::NodeId { self.inner.root() }
    fn parent(&self, id: Self::NodeId) -> Option<Self::NodeId> { self.inner.parent(id) }
    fn first_child(&self, id: Self::NodeId) -> Option<Self::NodeId> { self.inner.first_child(id) }
    fn next_sibling(&self, id: Self::NodeId) -> Option<Self::NodeId> { self.inner.next_sibling(id) }
    fn node_layout_params(&self, id: Self::NodeId) -> &LayoutParams { self.inner.node_layout_params(id) }
    fn node_layout_data(&self, id: Self::NodeId) -> &NodeLayoutData { self.inner.node_layout_data(id) }
    fn node_layout_data_mut(&mut self, id: Self::NodeId) -> &mut NodeLayoutData { self.inner.node_layout_data_mut(id) }
    fn layout_data(&mut self) -> &mut LayoutData<Self::NodeId> { self.inner.layout_data() }
    fn measure_text_width(&mut self, id: Self::NodeId) -> f32 { self.inner.measure_text_width(id) }
    fn measure_text_height(&mut self, id: Self::NodeId, wrap: Option<f32>) -> f32 {
        self.inner.measure_text_height(id, wrap)
    }
    fn measure_content(&mut self, id: Self::NodeId, input: ContentMeasureInput) -> Xy<f32> {
        self.inner.measure_content(id, input)
    }
    fn retains_output_rects(&self) -> bool { self.inner.retains_output_rects() }
    fn layout_warning(&mut self, warning: LayoutWarning<Self::NodeId>) {
        self.inner.layout_warning(warning);
    }

    fn write_output_rect(&mut self, id: Self::NodeId, rect: XyRect, local: XyRect) {
        write_checked::<_, _, _, RustVec>(
            &mut self.order, self.expected, self.inner, id, [rect.x, rect.y], [local.x, local.y], self.comparing,
        );
    }
}
