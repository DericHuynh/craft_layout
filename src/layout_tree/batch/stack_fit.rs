//! Compact input lists for intrinsic sizing in settled Free and Stack graphs.

use crate::{ChildrenLayout, ContentMeasure, LayoutParams, NodeLayoutData, Size, TextContent};

use super::{
    Axis, BatchLayoutError, Frame, Kind, Node, RustFloat, push, sizing_finish, slot_index,
};

const REGULAR: u8 = 1;
const MIN: u8 = 2;
const MAX: u8 = 4;
const LITERAL: u8 = 8;

#[derive(Debug, Default)]
pub(super) struct StackFit {
    built: bool,
    by_axis: Vec<u32>,
    recipes: Vec<Recipe>,
    inputs: Vec<Input>,
}

#[derive(Debug)]
struct Recipe {
    lo: u32,
    hi: u32,
    padding: f32,
    gaps: f32,
    sum: bool,
    repeated: Option<(f32, u32)>,
}

#[derive(Debug, Clone, Copy)]
struct Input {
    operand: u32,
    margin: f32,
    words: u8,
}

impl StackFit {
    pub(super) fn invalidate(&mut self) {
        self.built = false;
        self.by_axis.clear();
    }

    #[inline(always)]
    pub(super) fn measure(
        &self,
        records: &[NodeLayoutData],
        node: usize,
        axis: Axis,
    ) -> Option<f32> {
        let index = *self.by_axis.get(2 * node + axis.index())? as usize;
        if index == 0 {
            return None;
        }
        let recipe = &self.recipes[index - 1];
        let children = if let Some((value, count)) = recipe.repeated {
            value * count as f32
        } else {
            let input = &self.inputs[recipe.lo as usize..recipe.hi as usize];
            let regular = slot_index(axis, Kind::Regular);
            let min = slot_index(axis, Kind::Min);
            let max = slot_index(axis, Kind::Max);
            let values = input
                .iter()
                .map(|input| input.extent(records, regular, min, max));
            if recipe.sum {
                values.fold(0.0, |total, child| total + child)
            } else {
                values.fold(0.0, f32::max)
            }
        };
        Some(sizing_finish::intrinsic_extent::<RustFloat>(
            children,
            0.0,
            recipe.gaps,
            recipe.padding,
        ))
    }

    fn build(&mut self, frame: &Frame) -> Result<(), BatchLayoutError> {
        self.recipes.clear();
        self.inputs.clear();
        if frame.has_block || frame.active_nodes != frame.indices.len() {
            return Ok(());
        }
        let limit = frame
            .nodes
            .len()
            .checked_mul(2)
            .ok_or(BatchLayoutError::Capacity)?;
        self.by_axis.try_reserve_exact(limit)?;
        self.by_axis.resize(limit, 0);
        for (row, node) in frame.nodes.iter().enumerate() {
            let Some(node) = node else { continue };
            let params = &frame.params[row];
            if !matches!(params.text, TextContent::None)
                || !matches!(params.content_measure, ContentMeasure::None)
                || params.image.is_some()
            {
                continue;
            }
            for axis in [Axis::X, Axis::Y] {
                if !matches!(params.size[axis], Size::FitContent) {
                    continue;
                }
                if let Some(recipe) = self.recipe(frame, row, *node, params, axis)? {
                    push(&mut self.recipes, recipe)?;
                    self.by_axis[2 * row + axis.index()] = index32(self.recipes.len())?;
                }
            }
        }
        if self.recipes.is_empty() {
            self.by_axis.clear();
        }
        Ok(())
    }

    fn recipe(
        &mut self,
        frame: &Frame,
        row: usize,
        node: Node,
        params: &LayoutParams,
        axis: Axis,
    ) -> Result<Option<Recipe>, BatchLayoutError> {
        let (sum, gaps, free) = match params.children_layout {
            ChildrenLayout::Free => (false, 0.0, true),
            ChildrenLayout::Stack {
                axis: main,
                spacing,
                ..
            } => {
                let gaps = if main == axis {
                    sizing_finish::stack_gap_total::<RustFloat>(
                        spacing,
                        frame.records[row].n_placed_children,
                    )
                } else {
                    0.0
                };
                (main == axis, gaps, false)
            }
            _ => return Ok(None),
        };
        let lo = index32(self.inputs.len())?;
        let mut next = node.first();
        while let Some(child) = next {
            let child_node = frame.nodes[child].ok_or(BatchLayoutError::InvalidGraph)?;
            let child_params = &frame.params[child];
            next = child_node.next();
            if child_params.free_placement || child_params.disabled {
                continue;
            }
            if sum && matches!(child_params.size[axis], Size::Frac(_)) {
                self.inputs.truncate(lo as usize);
                return Ok(None);
            }
            let input = Input::new(child, child_params, axis, free)?;
            // One value from a run of identical positive literals gives
            // the same binary32 maximum.
            if !sum
                && input.words == LITERAL
                && input.margin == 0.0
                && f32::from_bits(input.operand) > 0.0
                && self.inputs.len() > lo as usize
                && self.inputs.last().is_some_and(|previous| {
                    previous.words == LITERAL
                        && previous.margin == 0.0
                        && previous.operand == input.operand
                })
            {
                continue;
            }
            push(&mut self.inputs, input)?;
        }
        let repeated = if sum {
            repeat_sum(&self.inputs[lo as usize..])
        } else {
            None
        };
        if repeated.is_some() {
            self.inputs.truncate(lo as usize);
        }
        Ok(Some(Recipe {
            lo,
            hi: index32(self.inputs.len())?,
            padding: sizing_finish::padding(params, axis),
            gaps,
            sum,
            repeated,
        }))
    }
}

fn repeat_sum(input: &[Input]) -> Option<(f32, u32)> {
    let count = u32::try_from(input.len()).ok()?;
    if !(8..=(1 << 24)).contains(&count) {
        return None;
    }
    let literal = input[0].operand;
    let value = f32::from_bits(literal);
    // Binary32 represents every integer through 2^24 exactly. Scaling
    // each of those partial sums by a normal power of two stays exact
    // whenever the final product is finite.
    if !value.is_normal()
        || !value.is_sign_positive()
        || literal & 0x7f_ffff != 0
        || !(value * count as f32).is_finite()
        || !input
            .iter()
            .all(|row| row.words == LITERAL && row.margin == 0.0 && row.operand == literal)
    {
        return None;
    }
    Some((value, count))
}

impl Input {
    fn new(
        row: usize,
        params: &LayoutParams,
        axis: Axis,
        free: bool,
    ) -> Result<Self, BatchLayoutError> {
        let mut words = match params.size[axis] {
            Size::Fill | Size::Frac(_) => 0,
            _ => REGULAR,
        };
        let reads_bound =
            |bound| matches!(bound, Some(size) if !matches!(size, Size::Fill | Size::Frac(_)));
        if reads_bound(params.min_size[axis]) {
            words |= MIN;
        }
        if reads_bound(params.max_size[axis]) {
            words |= MAX;
        }
        let margin = if free {
            0.0
        } else {
            let [start, end] = crate::flow::margins(params, axis);
            start + end
        };
        let mut operand = index32(row)?;
        if words == REGULAR {
            if let Size::Pixels(value) = params.size[axis]
                && value.is_finite()
            {
                operand = value.to_bits();
                words = LITERAL;
            }
        }
        Ok(Self {
            operand,
            margin,
            words,
        })
    }

    #[inline(always)]
    fn extent(self, records: &[NodeLayoutData], regular: usize, min: usize, max: usize) -> f32 {
        let size = match self.words {
            LITERAL => f32::from_bits(self.operand),
            0 => 0.0,
            REGULAR => records[self.operand as usize].values[regular],
            words => {
                let values = &records[self.operand as usize].values;
                let size = if words & REGULAR != 0 {
                    values[regular]
                } else {
                    0.0
                };
                let min = (words & MIN != 0).then(|| values[min]);
                let max = (words & MAX != 0).then(|| values[max]);
                sizing_finish::clamp::<RustFloat>(size, min, max)
            }
        };
        if self.margin == 0.0 {
            size
        } else {
            size + self.margin
        }
    }
}

impl Frame {
    pub(super) fn prepare_stack_fit(&mut self) {
        if self.stack_fit.built {
            return;
        }
        let mut program = std::mem::take(&mut self.stack_fit);
        if program.build(self).is_err() {
            program.by_axis.clear();
        }
        program.built = true;
        self.stack_fit = program;
    }
}

fn index32(index: usize) -> Result<u32, BatchLayoutError> {
    u32::try_from(index).map_err(|_| BatchLayoutError::Capacity)
}
