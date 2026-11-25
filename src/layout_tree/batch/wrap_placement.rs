//! Admit stable Wrap runs to the ordinary prepared placement sweep.

use super::{Frame, Host, Node, NodeKey};
use crate::solve::Kind;
use crate::{Arrange, Axis, ChildrenLayout, LayoutParams, NodeLayoutData, Pos, Size, TreeAdapter};

impl Frame {
    pub(super) fn prepare_wrap_placement(&mut self) {
        self.ready_wrap_placement = false;
        if !self.data.has_flow {
            return;
        }
        for &parent in &self.visible {
            let params = &self.params[parent];
            let ChildrenLayout::Wrap {
                axis,
                arrange: Arrange::Start,
                ..
            } = params.children_layout
            else {
                continue;
            };
            if !matches!(params.size[axis.other()], Size::Auto | Size::FitContent)
                || params.children_origin_flipped.x
                || params.children_origin_flipped.y
            {
                continue;
            }
            let Some(first) = self.nodes[parent].and_then(Node::first) else {
                continue;
            };
            let mut next = Some(first);
            while let Some(child) = next {
                let params = &self.params[child];
                let rise = params.size[axis.other()];
                if params.disabled
                    || params.free_placement
                    || !nonnegative_pixels(params.size[axis])
                    || !(matches!(rise, Size::Fill) || nonnegative_pixels(rise))
                    || !unbounded(params)
                    || !crate::place::placement_modes::zero_margins(params)
                    || !matches!(params.position[axis.other()], Pos::Start)
                {
                    break;
                }
                next = self.nodes[child].and_then(Node::next);
            }
            if next.is_none() {
                self.records[parent].prepared_placement |= NodeLayoutData::PREPARED_WRAP_START;
                self.ready_wrap_placement = true;
            }
        }
    }
}

impl<A: TreeAdapter<NodeId = NodeKey>> Host<'_, A> {
    #[inline(always)]
    pub(super) fn reset_wrap_output(&mut self, node: usize) {
        crate::sizing_pass::reset_wrap_items(self, node);
        if self.prepare_wrap_output {
            self.records[node].prepared_placement &= !NodeLayoutData::PREPARED_WRAP;
        }
    }

    // Placement reads only line words stamped by this completed Flow step.
    #[inline(always)]
    pub(super) fn finish_wrap_output(&mut self, node: usize, axis: Axis, kind: Kind) {
        if self.prepare_wrap_output
            && kind == Kind::Flow
            && self.records[node].prepared_placement & NodeLayoutData::PREPARED_WRAP_START != 0
            && matches!(self.params[node].children_layout,
                ChildrenLayout::Wrap { axis: main, .. } if main != axis)
        {
            self.records[node].prepared_placement |= NodeLayoutData::PREPARED_WRAP;
        }
    }
}

fn nonnegative_pixels(size: Size) -> bool {
    matches!(size, Size::Pixels(value) if value.is_finite() && !value.is_sign_negative())
}

fn unbounded(params: &LayoutParams) -> bool {
    params.min_size.x.is_none()
        && params.min_size.y.is_none()
        && params.max_size.x.is_none()
        && params.max_size.y.is_none()
}
