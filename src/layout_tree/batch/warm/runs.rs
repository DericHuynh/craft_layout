//! Group adjacent producers in the retained topological order.

use super::{Host, LayoutParams, NodeKey, TreeAdapter, WarmSlot, fill_axis, flex, ratio};

#[derive(Debug, Default)]
pub(in crate::layout_tree::batch) struct Runs {
    current: bool,
    pub(super) groups: Vec<Group>,
}

#[derive(Debug)]
pub(super) struct Group {
    pub(super) start: usize,
    pub(super) end: usize,
    operation: Operation,
}

#[derive(Debug)]
enum Operation {
    FillAxis(fill_axis::FillAxis),
    Flex(flex::FlexRun),
    Ratio(ratio::RatioRun),
}

impl Runs {
    pub(in crate::layout_tree::batch) fn invalidate(&mut self) {
        self.current = false;
    }

    pub(in crate::layout_tree::batch) fn compile(
        &mut self,
        slots: &[WarmSlot],
        params: &[LayoutParams],
    ) {
        if self.current {
            return;
        }
        self.current = true;
        self.groups.clear();
        let mut start = 0;
        while start < slots.len() {
            let Some((count, operation)) = Operation::compile(&slots[start..], params) else {
                start += 1;
                continue;
            };
            if self.groups.try_reserve(1).is_err() {
                break;
            }
            let end = start + count;
            self.groups.push(Group {
                start,
                end,
                operation,
            });
            start = end;
        }
    }
}

impl Operation {
    fn compile(slots: &[WarmSlot], params: &[LayoutParams]) -> Option<(usize, Self)> {
        if let Some((count, fill)) = fill_axis::FillAxis::compile(slots, params) {
            return Some((count, Self::FillAxis(fill)));
        }
        if let Some((count, fill)) = flex::FlexRun::compile(slots, params) {
            return Some((count, Self::Flex(fill)));
        }
        ratio::RatioRun::compile(slots, params).map(|(count, run)| (count, Self::Ratio(run)))
    }
}

impl Group {
    pub(super) fn execute<A: TreeAdapter<NodeId = NodeKey>>(&self, host: &mut Host<'_, A>) -> bool {
        match &self.operation {
            Operation::FillAxis(fill) => fill.execute(host),
            Operation::Flex(fill) => fill.execute(host),
            Operation::Ratio(run) => run.execute(host),
        }
    }
}
