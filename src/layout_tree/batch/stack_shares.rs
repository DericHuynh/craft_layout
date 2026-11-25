use super::{Node, ScheduledSlot};
use crate::fill_budget;
use crate::placement_geometry::RustFloat;
use crate::solve::fill_compaction::{self as fill, FillChild};
use crate::solve::sizing_finish::{inner, padding, stack_gap_total};
use crate::solve::{Kind, N_SLOTS, NodeLayoutData, slot_index};
use crate::{Axis, ChildrenLayout, LayoutParams, Size};

#[derive(Debug, Default)]
pub(super) struct StackShares {
    plans: Vec<Share>,
    owners: Vec<u32>,
    compiled: bool,
}

#[derive(Debug, Clone, Copy)]
enum Bounds {
    None,
    One(FillChild),
    Two([FillChild; 2]),
}

#[derive(Debug)]
struct Share {
    padding: f32,
    gaps: f32,
    weight: f32,
    max_unconstrained: Option<f32>,
    bounds: Bounds,
}

impl StackShares {
    pub(super) fn invalidate(&mut self) {
        self.owners.clear();
        self.plans.clear();
        self.compiled = false;
    }

    #[inline(always)]
    pub(super) fn resolve(&self, row: usize, axis: Axis, record: &NodeLayoutData) -> Option<f32> {
        let index = *self.owners.get(row)? as usize;
        let plan = self.plans.get(index)?;
        let size = record.values[slot_index(axis, Kind::Final)];
        let budget = fill_budget::after_gaps(inner::<RustFloat>(size, plan.padding), plan.gaps);
        let share = match plan.bounds {
            Bounds::None => fill_budget::share(budget, 0.0, plan.weight),
            Bounds::One(bound) => fill::resolve_fill_share_with::<fill::RustFloat>(
                &mut [bound],
                budget,
                plan.weight,
                plan.max_unconstrained,
            ),
            Bounds::Two(mut bounds) => fill::resolve_fill_share_with::<fill::RustFloat>(
                &mut bounds,
                budget,
                plan.weight,
                plan.max_unconstrained,
            ),
        };
        Some(share)
    }

    pub(super) fn compile(
        &mut self,
        execution: &[ScheduledSlot],
        nodes: &[Option<Node>],
        params: &[LayoutParams],
        records: &[NodeLayoutData],
    ) {
        if self.compiled {
            return;
        }
        self.compiled = true;
        for slot in execution {
            if slot.kind != Kind::EvenShare {
                continue;
            }
            let row = slot.vertex / N_SLOTS;
            let axis = if slot.vertical { Axis::Y } else { Axis::X };
            let Some(plan) = compile_share(nodes, params, &records[row], row, axis) else {
                continue;
            };
            if self.owners.is_empty() {
                if self.owners.try_reserve_exact(nodes.len()).is_err() {
                    break;
                }
                self.owners.resize(nodes.len(), u32::MAX);
            }
            let Ok(index) = u32::try_from(self.plans.len()) else {
                break;
            };
            if index == u32::MAX || self.plans.try_reserve(1).is_err() {
                break;
            }
            self.owners[row] = index;
            self.plans.push(plan);
        }
    }
}

/// Accept a stack whose in-flow children all take its share with static
/// constraints. Every warm evaluation reads the current parent Final size
/// and recomputes the share using the canonical bound resolver.
fn compile_share(
    nodes: &[Option<Node>],
    params: &[LayoutParams],
    record: &NodeLayoutData,
    row: usize,
    axis: Axis,
) -> Option<Share> {
    let p = &params[row];
    let ChildrenLayout::Stack {
        axis: main,
        spacing,
        ..
    } = p.children_layout
    else {
        return None;
    };
    if main != axis || p.disabled {
        return None;
    }
    let mut next = nodes[row].and_then(Node::first);
    let mut weight = 0.0;
    let mut max_unconstrained: Option<f32> = None;
    let mut bounds = Bounds::None;
    while let Some(child) = next {
        let style = &params[child];
        next = nodes[child].and_then(Node::next);
        if style.disabled || style.free_placement {
            continue;
        }
        let [start, end] = style.margin[axis];
        if start.as_px().unwrap_or(0.0) != 0.0 || end.as_px().unwrap_or(0.0) != 0.0 {
            return None;
        }
        let share_weight = style.fill_weight;
        if !share_weight.is_finite() || share_weight < 0.0 {
            return None;
        }
        let regular = style.size[axis];
        let min = style.min_size[axis];
        let max = style.max_size[axis];
        if !matches!(
            (regular, min, max),
            (Size::Fill, _, _) | (_, Some(Size::Fill), _) | (_, _, Some(Size::Fill))
        ) {
            return None;
        }
        let pixel = |size| match size {
            None | Some(Size::Fill) => Some(None),
            Some(Size::Pixels(value)) if value.is_finite() => Some(Some(value)),
            _ => None,
        };
        let content = pixel(Some(regular))?;
        let minimum = pixel(min)?;
        let maximum = pixel(max)?;
        // Keep the collector's binary32 addition in sibling order.
        weight += share_weight;
        if content.is_none() && minimum.is_none() && maximum.is_none() {
            let absolute = share_weight.abs();
            max_unconstrained = Some(max_unconstrained.map_or(absolute, |old| old.max(absolute)));
        } else {
            let capped = content.is_some() && matches!(max, Some(Size::Fill));
            let bound = FillChild::new_with::<fill::RustFloat>(
                content,
                minimum,
                maximum,
                capped,
                share_weight,
            );
            bounds = match bounds {
                Bounds::None => Bounds::One(bound),
                Bounds::One(first) => Bounds::Two([first, bound]),
                Bounds::Two(_) => return None,
            };
        }
    }
    Some(Share {
        padding: padding(p, axis),
        gaps: stack_gap_total::<RustFloat>(spacing, record.n_placed_children),
        weight,
        max_unconstrained,
        bounds,
    })
}
