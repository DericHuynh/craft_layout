//! Compare placement emitted by the two sizing runs without publishing twice.
use crate::*;

#[path = "../view_check.rs"]
mod view_check;
use view_check::ViewCheck;

pub(crate) type OutputRecord<I> = (I, [u32; 8]);

pub(super) struct CheckedView<'a, T: TreeAdapter + ?Sized> {
    inner: &'a mut T,
    expected: &'a mut Vec<OutputRecord<T::NodeId>>,
    comparing: bool,
    order: ViewCheck,
}

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
}

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
        let record = (id, [
            rect.x[0], rect.x[1], rect.y[0], rect.y[1],
            local.x[0], local.x[1], local.y[0], local.y[1],
        ].map(f32::to_bits));
        if self.comparing {
            self.order.compare(self.expected.get(self.order.position()) == Some(&record));
            self.inner.write_output_rect(id, rect, local);
        } else {
            self.expected.push(record);
        }
    }
}
