//! Retain the geometry walk for unrounded, start-aligned subtrees.
//! Consume physical leaves in preorder and keep only live ancestor cursors.

use super::{
    Axis, ChildrenLayout, Edges, Frame, NodeKey, NodeLayoutData, PlacementWork, Pos, RustFloat,
    TreeAdapter, Xy, size, stable_edges,
};
use crate::flow::margins;
use crate::place::stack_line::{after_item, with_margin};
use crate::placement_geometry::inner_start;
use crate::{Arrange, WindowOverflow};

#[derive(Clone, Copy, Debug)]
enum Flow {
    Free,
    X,
    Y,
}

#[derive(Clone, Copy, Debug)]
struct Style {
    flow: Flow,
    padding: [f32; 2],
    spacing: f32,
}

#[derive(Clone, Copy, Debug)]
struct Cursor {
    flow: Flow,
    start: [f32; 2],
    origin: [f32; 2],
    spacing: f32,
}

#[derive(Clone, Copy, Debug, Default, PartialEq)]
struct StackMargins {
    leading: f32,
    trailing: f32,
    cross: f32,
}

impl StackMargins {
    fn from_params(params: &crate::LayoutParams, flow: Flow) -> Self {
        let main = match flow {
            Flow::Free => return Self::default(),
            Flow::X => Axis::X,
            Flow::Y => Axis::Y,
        };
        let [leading, trailing] = margins(params, main);
        Self {
            leading,
            trailing,
            cross: margins(params, main.other())[0],
        }
    }

    fn applies(self) -> bool {
        self.leading != 0.0 || self.trailing != 0.0 || self.cross != 0.0
    }
}

impl Cursor {
    #[inline(always)]
    fn at(style: Style, edges: Edges) -> Self {
        let origin = [edges[0][0], edges[1][0]];
        Self {
            flow: style.flow,
            start: [
                inner_start::<RustFloat>(edges[0], style.padding[0]),
                inner_start::<RustFloat>(edges[1], style.padding[1]),
            ],
            origin,
            spacing: style.spacing,
        }
    }

    #[inline(always)]
    fn next(&mut self, [width, height]: [f32; 2]) -> Edges {
        let [left, top] = self.start;
        match self.flow {
            Flow::Free => {}
            Flow::X => self.start[0] += width + self.spacing,
            Flow::Y => self.start[1] += height + self.spacing,
        }
        [[left, left + width], [top, top + height]]
    }

    #[inline(always)]
    fn next_with_margin<const X: bool>(&mut self, size: [f32; 2], margin: StackMargins) -> Edges {
        let (main, cross) = if X { (0, 1) } else { (1, 0) };
        let leading = with_margin(self.start[main], margin.leading);
        let side_start = with_margin(self.start[cross], margin.cross);
        self.start[main] = after_item(leading, size[main], margin.trailing, self.spacing);
        let along = [leading, leading + size[main]];
        let side = [side_start, side_start + size[cross]];
        if X { [along, side] } else { [side, along] }
    }

    #[inline(always)]
    fn next_with_flow_margin(&mut self, size: [f32; 2], margin: StackMargins) -> Edges {
        match self.flow {
            Flow::Free => self.next(size),
            Flow::X => self.next_with_margin::<true>(size, margin),
            Flow::Y => self.next_with_margin::<false>(size, margin),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SizeInput {
    Constant(u32),
    StackShare { parent: u32, weight: u32 },
    ParentFillMargins { parent: u32, margins: [u32; 2] },
}

#[derive(Clone, Copy, Debug)]
enum RunSize {
    Varying,
    Constant([f32; 2]),
    Shared,
}

#[derive(Clone, Copy, Debug)]
enum Step {
    Branch {
        depth: u32,
        row: u32,
        key: NodeKey,
        style: Style,
    },
    Run {
        depth: u32,
        first: u32,
        keys: u32,
        len: u32,
        size: RunSize,
        uniform_margins: bool,
    },
}

#[derive(Default, Debug)]
pub(super) struct FullPlan {
    pub(super) valid: Option<bool>,
    // A successful full walk cleared every active mark in this plan. The
    // partial driver and every change to the admitted shape reset this flag.
    pub(super) clean: bool,
    root: Option<(NodeKey, Style)>,
    steps: Vec<Step>,
    keys: Vec<NodeKey>,
    cursors: Vec<Cursor>,
    todo: Vec<(usize, u32, Flow)>,
    margins: Vec<StackMargins>,
}

fn get_style(frame: &Frame, row: usize) -> Option<Style> {
    let params = frame.params.get(row)?;
    if params.children_origin_flipped.x || params.children_origin_flipped.y {
        return None;
    }
    let (flow, spacing) = match params.children_layout {
        ChildrenLayout::Free => (Flow::Free, 0.0),
        ChildrenLayout::Stack {
            axis,
            arrange: Arrange::Start,
            spacing,
        } => (if axis == Axis::X { Flow::X } else { Flow::Y }, spacing),
        _ => return None,
    };
    Some(Style {
        flow,
        padding: [params.padding.x[0], params.padding.y[0]],
        spacing,
    })
}

// An unbounded Final copies the Regular. Identical Stack Fill inputs share
// the parent share and weight, or the parent inner extent and cross margins.
fn size_input(frame: &Frame, row: usize, axis: Axis) -> Option<SizeInput> {
    use super::super::{DirectSize, N_SLOTS};

    let base = row.checked_mul(N_SLOTS)?;
    let final_index = super::slot_index(axis, super::Kind::Final);
    let final_id = base.checked_add(final_index)?;
    if *frame.ready.get(final_id)? {
        return Some(SizeInput::Constant(
            frame.records.get(row)?.values[final_index].to_bits(),
        ));
    }
    let final_slot = frame.execution.get(*frame.execution_ranks.get(final_id)?)?;
    if final_slot.vertex != final_id || !matches!(final_slot.direct, DirectSize::Final) {
        return None;
    }
    let regular_id = base.checked_add(super::slot_index(axis, super::Kind::Regular))?;
    let regular = frame
        .execution
        .get(*frame.execution_ranks.get(regular_id)?)?;
    if regular.vertex != regular_id {
        return None;
    }
    let params = frame.params.get(row)?;
    let parent = regular.parent;
    match regular.direct {
        DirectSize::StackFill if params.fill_weight.is_finite() => Some(SizeInput::StackShare {
            parent,
            weight: params.fill_weight.to_bits(),
        }),
        DirectSize::ParentFillMargins => Some(SizeInput::ParentFillMargins {
            parent,
            margins: margins(params, axis).map(f32::to_bits),
        }),
        _ => None,
    }
}

fn size_inputs(frame: &Frame, row: usize) -> Option<[SizeInput; 2]> {
    Some([
        size_input(frame, row, Axis::X)?,
        size_input(frame, row, Axis::Y)?,
    ])
}

fn push<T>(items: &mut Vec<T>, item: T) -> Option<()> {
    items.try_reserve(1).ok()?;
    items.push(item);
    Some(())
}

impl FullPlan {
    fn prepare(&mut self, frame: &Frame) -> Option<()> {
        self.root = None;
        self.clean = false;
        self.steps.clear();
        self.keys.clear();
        self.cursors.clear();
        self.todo.clear();
        self.margins.clear();

        let root = frame.nodes.get(frame.root).copied().flatten()?;
        if frame.params[frame.root].disabled {
            return Some(());
        }
        let root_style = root
            .first()
            .map(|_| get_style(frame, frame.root))
            .unwrap_or(Some(Style {
                flow: Flow::Free,
                padding: [0.0; 2],
                spacing: 0.0,
            }))?;
        self.root = Some((root.key, root_style));
        if let Some(first) = root.first() {
            push(&mut self.todo, (first, 0, root_style.flow))?;
        }

        // Capture and validate the active preorder before writing rectangles.
        self.keys.try_reserve_exact(frame.nodes.len()).ok()?;
        let mut height = 0;
        let mut budget = frame.nodes.len();
        while let Some((row, depth, flow)) = self.todo.pop() {
            budget = budget.checked_sub(1)?;
            let node = frame.nodes.get(row).copied().flatten()?;
            if frame.params[row].disabled {
                if let Some(next) = node.next() {
                    push(&mut self.todo, (next, depth, flow))?;
                }
                continue;
            }
            self.prepare_child(frame, row, flow)?;
            if let Some(first) = node.first() {
                let style = get_style(frame, row)?;
                let inside = depth.checked_add(1)?;
                height = height.max(inside);
                let packed_row = u32::try_from(row).ok()?;
                push(
                    &mut self.steps,
                    Step::Branch {
                        depth,
                        row: packed_row,
                        key: node.key,
                        style,
                    },
                )?;
                if let Some(next) = node.next() {
                    push(&mut self.todo, (next, depth, flow))?;
                }
                push(&mut self.todo, (first, inside, style.flow))?;
                continue;
            }

            let keys = u32::try_from(self.keys.len()).ok()?;
            let first = u32::try_from(row).ok()?;
            let mut inputs = size_inputs(frame, row);
            let mut count = 1usize;
            self.keys.push(node.key);
            let mut next = node.next();
            while let Some(i) = next {
                if Some(i) != row.checked_add(count) || frame.params[i].disabled {
                    break;
                }
                let child = frame.nodes[i]?;
                if child.first().is_some() {
                    break;
                }
                self.prepare_child(frame, i, flow)?;
                if let Some(prior) = inputs {
                    inputs = size_inputs(frame, i).filter(|now| *now == prior);
                }
                budget = budget.checked_sub(1)?;
                self.keys.push(child.key);
                count += 1;
                next = child.next();
            }
            if let Some(next) = next {
                push(&mut self.todo, (next, depth, flow))?;
            }
            let len = u32::try_from(count).ok()?;
            let size = match inputs {
                Some([SizeInput::Constant(x), SizeInput::Constant(y)]) => {
                    RunSize::Constant([f32::from_bits(x), f32::from_bits(y)])
                }
                Some(_) => RunSize::Shared,
                None => RunSize::Varying,
            };
            let uniform_margins = self.margins.is_empty()
                || self.margins[row..row + count]
                    .iter()
                    .all(|margin| *margin == self.margins[row]);
            push(
                &mut self.steps,
                Step::Run {
                    depth,
                    first,
                    keys,
                    len,
                    size,
                    uniform_margins,
                },
            )?;
        }
        let count = (height as usize).checked_add(1)?;
        self.cursors.try_reserve_exact(count).ok()?;
        self.cursors
            .resize(count, Cursor::at(root_style, [[0.0; 2]; 2]));
        Some(())
    }

    #[inline]
    fn prepare_child(&mut self, frame: &Frame, row: usize, flow: Flow) -> Option<()> {
        let params = &frame.params[row];
        let usable = match flow {
            Flow::Free => {
                matches!(
                    (params.position.x, params.position.y),
                    (Pos::Start, Pos::Start)
                ) && matches!(
                    (params.window_overflow.x, params.window_overflow.y),
                    (WindowOverflow::Ignore, WindowOverflow::Ignore)
                )
            }
            Flow::X => matches!(params.position.y, Pos::Start) && !params.has_auto_margin(Axis::X),
            Flow::Y => matches!(params.position.x, Pos::Start) && !params.has_auto_margin(Axis::Y),
        };
        if params.free_placement || !usable {
            return None;
        }
        let margin = StackMargins::from_params(params, flow);
        if margin.applies() {
            if self.margins.is_empty() {
                self.margins.try_reserve_exact(frame.nodes.len()).ok()?;
                self.margins
                    .resize(frame.nodes.len(), StackMargins::default());
            }
            self.margins[row] = margin;
        }
        Some(())
    }

    fn place<A: TreeAdapter<NodeId = NodeKey>>(&mut self, frame: &mut Frame, source: &mut A) {
        if self.margins.is_empty() {
            self.place_rows::<A, false>(frame, source);
        } else {
            self.place_rows::<A, true>(frame, source);
        }
    }

    fn place_rows<A: TreeAdapter<NodeId = NodeKey>, const MARGINS: bool>(
        &mut self,
        frame: &mut Frame,
        source: &mut A,
    ) {
        let Some((key, style)) = self.root else {
            return;
        };
        let root = &mut frame.records[frame.root];
        let [width, height] = size(root);
        let edges = [[0.0, width], [0.0, height]];
        emit(source, key, root, edges, [0.0; 2]);
        self.cursors[0] = Cursor::at(style, edges);
        for &step in &self.steps {
            match step {
                Step::Branch {
                    depth,
                    row,
                    key,
                    style,
                } => {
                    let parent = &mut self.cursors[depth as usize];
                    let record = &mut frame.records[row as usize];
                    let raw = if MARGINS {
                        parent.next_with_flow_margin(size(record), self.margins[row as usize])
                    } else {
                        parent.next(size(record))
                    };
                    emit(source, key, record, raw, parent.origin);
                    self.cursors[depth as usize + 1] = Cursor::at(style, raw);
                }
                Step::Run {
                    depth,
                    first,
                    keys,
                    len,
                    size: run_size,
                    uniform_margins,
                } => {
                    let first = first as usize;
                    let limit = first + len as usize;
                    let keys = &self.keys[keys as usize..][..len as usize];
                    let records = &mut frame.records[first..limit];
                    let cursor = &mut self.cursors[depth as usize];
                    let repeated = match run_size {
                        RunSize::Constant(size) => Some(size),
                        RunSize::Shared => {
                            let resolved = size(&records[0]);
                            resolved
                                .iter()
                                .all(|value| value.is_finite())
                                .then_some(resolved)
                        }
                        RunSize::Varying => None,
                    };
                    if MARGINS && !matches!(cursor.flow, Flow::Free) {
                        let margins = &self.margins[first..limit];
                        let uniform = repeated.filter(|_| uniform_margins);
                        match (cursor.flow, self.clean) {
                            (Flow::X, true) => margin_run::<A, true, true>(
                                source, keys, records, cursor, margins, uniform,
                            ),
                            (Flow::X, false) => margin_run::<A, true, false>(
                                source, keys, records, cursor, margins, uniform,
                            ),
                            (Flow::Y, true) => margin_run::<A, false, true>(
                                source, keys, records, cursor, margins, uniform,
                            ),
                            _ => margin_run::<A, false, false>(
                                source, keys, records, cursor, margins, uniform,
                            ),
                        }
                        continue;
                    }
                    match repeated {
                        Some(size) => match cursor.flow {
                            Flow::X if self.clean => fixed_run::<A, true, true, false>(
                                source,
                                keys,
                                records,
                                cursor,
                                size,
                                StackMargins::default(),
                            ),
                            Flow::Y if self.clean => fixed_run::<A, false, true, false>(
                                source,
                                keys,
                                records,
                                cursor,
                                size,
                                StackMargins::default(),
                            ),
                            Flow::X => fixed_run::<A, true, false, false>(
                                source,
                                keys,
                                records,
                                cursor,
                                size,
                                StackMargins::default(),
                            ),
                            Flow::Y => fixed_run::<A, false, false, false>(
                                source,
                                keys,
                                records,
                                cursor,
                                size,
                                StackMargins::default(),
                            ),
                            Flow::Free => {
                                let raw = cursor.next(size);
                                for (&key, record) in keys.iter().zip(records) {
                                    emit(source, key, record, raw, cursor.origin);
                                }
                            }
                        },
                        None => {
                            for (&key, record) in keys.iter().zip(records) {
                                let raw = cursor.next(size(record));
                                emit(source, key, record, raw, cursor.origin);
                            }
                        }
                    }
                }
            }
        }
    }
}

#[inline]
fn margin_run<A: TreeAdapter<NodeId = NodeKey>, const X: bool, const CLEAN: bool>(
    source: &mut A,
    keys: &[NodeKey],
    records: &mut [NodeLayoutData],
    cursor: &mut Cursor,
    margins: &[StackMargins],
    uniform: Option<[f32; 2]>,
) {
    if let Some(size) = uniform {
        fixed_run::<A, X, CLEAN, true>(source, keys, records, cursor, size, margins[0]);
        return;
    }
    for ((&key, record), &margin) in keys.iter().zip(records).zip(margins) {
        let raw = cursor.next_with_margin::<X>(size(record), margin);
        if CLEAN {
            emit_edges(source, key, raw, cursor.origin);
        } else {
            emit(source, key, record, raw, cursor.origin);
        }
    }
}

#[inline]
fn fixed_run<
    A: TreeAdapter<NodeId = NodeKey>,
    const X: bool,
    const CLEAN: bool,
    const MARGINS: bool,
>(
    source: &mut A,
    keys: &[NodeKey],
    records: &mut [NodeLayoutData],
    cursor: &mut Cursor,
    size: [f32; 2],
    margin: StackMargins,
) {
    let (main, cross) = if X { (0, 1) } else { (1, 0) };
    let mut start = cursor.start[main];
    let side_start = if MARGINS {
        with_margin(cursor.start[cross], margin.cross)
    } else {
        cursor.start[cross]
    };
    let side = [side_start, side_start + size[cross]];
    // Keep the binary32 additions ordered as in after_item().
    let outer_extent = if MARGINS {
        with_margin(size[main], margin.trailing)
    } else {
        size[main]
    };
    let stride = outer_extent + cursor.spacing;
    for (index, &key) in keys.iter().enumerate() {
        let leading = if MARGINS {
            with_margin(start, margin.leading)
        } else {
            start
        };
        let along = [leading, leading + size[main]];
        let raw = if X { [along, side] } else { [side, along] };
        if CLEAN {
            emit_edges(source, key, raw, cursor.origin);
        } else {
            emit(source, key, &mut records[index], raw, cursor.origin);
        }
        start = leading + stride;
    }
    cursor.start[main] = start;
}

#[inline(always)]
fn emit<A: TreeAdapter<NodeId = NodeKey>>(
    source: &mut A,
    key: NodeKey,
    record: &mut NodeLayoutData,
    raw: Edges,
    origin: [f32; 2],
) {
    if record.placement != PlacementWork::Clean {
        record.placement = PlacementWork::Clean;
    }
    emit_edges(source, key, raw, origin);
}

#[inline(always)]
fn emit_edges<A: TreeAdapter<NodeId = NodeKey>>(
    source: &mut A,
    key: NodeKey,
    raw: Edges,
    [left, top]: [f32; 2],
) {
    let [x, y] = stable_edges::<RustFloat>(raw);
    let [local_x, local_y] = stable_edges::<RustFloat>([
        raw[0].map(|value| value - left),
        raw[1].map(|value| value - top),
    ]);
    source.write_output_rect(key, Xy::new(x, y), Xy::new(local_x, local_y));
}

impl Frame {
    pub(in crate::layout_tree::batch) fn place_full_plan<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
    ) -> bool {
        if self.data.pixel_scale.is_some() {
            self.stack_placement.full_plan.clean = false;
            return false;
        }
        let mut plan = std::mem::take(&mut self.stack_placement.full_plan);
        let supported = plan.valid.unwrap_or_else(|| {
            // A partially built plan will be ignored on admission failure.
            let supported = plan.prepare(self).is_some();
            plan.valid = Some(supported);
            supported
        });
        if supported {
            plan.place(self, source);
            plan.clean = true;
        }
        self.stack_placement.full_plan = plan;
        supported
    }
}
