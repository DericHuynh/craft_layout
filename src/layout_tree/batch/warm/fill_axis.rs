//! Consecutive unbounded Fill pairs with the same parent and sizing input.

use super::{
    Axis, DirectSize, Host, Kind, LayoutParams, NodeKey, RustFloat, TreeAdapter, WarmSlot,
    sizing_finish, slot_index,
};

const MIN_RUN: usize = 4;

#[derive(Debug)]
pub(super) struct FillAxis {
    first: usize,
    count: usize,
    parent: usize,
    axis: Axis,
    input: Input,
}

#[derive(Debug, Clone, Copy)]
enum Input {
    Parent(f32),
    Share(f32),
}

impl Input {
    fn same(self, other: Self) -> bool {
        match (self, other) {
            (Self::Parent(left), Self::Parent(right)) | (Self::Share(left), Self::Share(right)) => {
                left.to_bits() == right.to_bits()
            }
            _ => false,
        }
    }
}

impl FillAxis {
    pub(super) fn compile(slots: &[WarmSlot], params: &[LayoutParams]) -> Option<(usize, Self)> {
        let mut pairs = slots.chunks_exact(2);
        let first_pair = pairs.next()?;
        let first = first_pair[0];
        let input = pair_input(first_pair, first, 0, params)?;
        let count = 1 + pairs
            .enumerate()
            .take_while(|(offset, pair)| {
                pair_input(pair, first, 1 + offset, params).is_some_and(|next| input.same(next))
            })
            .count();
        if count < MIN_RUN {
            return None;
        }
        Some((
            count * 2,
            Self {
                first: first.row as usize,
                count,
                parent: first.parent as usize,
                axis: first.axis,
                input,
            },
        ))
    }

    pub(super) fn execute<A: TreeAdapter<NodeId = NodeKey>>(&self, host: &mut Host<'_, A>) -> bool {
        let value = match self.input {
            Input::Parent(margin) => {
                let inner = host.parent_inner(self.parent, self.axis);
                if margin == 0.0 {
                    inner
                } else {
                    sizing_finish::inner::<RustFloat>(inner, margin)
                }
            }
            Input::Share(weight) => {
                let share =
                    host.records[self.parent].values[slot_index(self.axis, Kind::EvenShare)];
                share * weight
            }
        };
        if !value.is_finite() {
            return false;
        }
        let regular = slot_index(self.axis, Kind::Regular);
        let final_size = slot_index(self.axis, Kind::Final);
        for record in &mut host.records[self.first..self.first + self.count] {
            record.publish_slot(regular, value);
            record.publish_slot(final_size, value);
        }
        true
    }
}

fn pair_input(
    pair: &[WarmSlot],
    first: WarmSlot,
    offset: usize,
    params: &[LayoutParams],
) -> Option<Input> {
    let [regular, final_size] = [pair[0], pair[1]];
    if regular.kind != Kind::Regular
        || !matches!(final_size.op, DirectSize::Final)
        || regular.axis != first.axis
        || final_size.axis != first.axis
        || regular.parent != first.parent
        || regular.row != final_size.row
        || (first.row as usize).checked_add(offset) != Some(regular.row as usize)
    {
        return None;
    }
    match regular.op {
        DirectSize::ParentFill => Some(Input::Parent(0.0)),
        DirectSize::ParentFillMargins => {
            let [before, after] = crate::flow::margins(&params[regular.row as usize], first.axis);
            Some(Input::Parent(before + after))
        }
        DirectSize::StackFill => Some(Input::Share(params[regular.row as usize].fill_weight)),
        _ => None,
    }
}
