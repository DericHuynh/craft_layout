use super::{Frame, Node, NodeKey};
use crate::place::placement_modes::{Frame as ParentFrame, StackMath, stack_item, zero_margins};
use crate::placement_adapter::{stable_edges, stack_style};
use crate::placement_geometry::{RustFloat, inner_range};
use crate::placement_work::PlacementWork;
use crate::solve::{Kind, slot_index};
use crate::{Arrange, Axis, ChildrenLayout, NodeLayoutData, Pos, TreeAdapter, Xy};

type Edges = [[f32; 2]; 2];

mod full_plan;

#[derive(Debug)]
struct Branch {
    row: usize,
    edges: Edges,
    partial: bool,
}

#[derive(Debug, Default)]
pub(super) struct StackPlacement {
    eligible: Option<bool>,
    pending: Vec<Branch>,
    snapped_eligible: Option<bool>,
    full_plan: full_plan::FullPlan,
    rows: Vec<(usize, usize)>,
    edges: Vec<[f32; 4]>,
}

impl StackPlacement {
    pub(super) fn note_dirty_marks(&mut self) {
        self.full_plan.clean = false;
    }

    pub(super) fn invalidate(&mut self) {
        self.eligible = None;
        self.full_plan.valid = None;
        self.full_plan.clean = false;
        self.snapped_eligible = None;
    }
}

impl Frame {
    /// A forward, start-aligned Stack needs only its next item and cursor.
    /// Keep just the pending branches for this common unsnapped geometry.
    pub(super) fn place_start_stacks<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        partial: bool,
    ) -> bool {
        if let Some(scale) = self.data.pixel_scale {
            return !partial && self.place_snapped_stacks(source, scale);
        }
        let placement = &mut self.stack_placement;
        let supported = *placement.eligible.get_or_insert_with(|| {
            self.nodes.iter().zip(&self.params).all(|(node, params)| {
                node.is_none_or(|node| {
                    !params.free_placement
                        && (node.first().is_none()
                            || (!params.children_origin_flipped.x
                                && !params.children_origin_flipped.y
                                && matches!(
                                    params.children_layout,
                                    ChildrenLayout::Stack {
                                        arrange: Arrange::Start,
                                        ..
                                    }
                                )))
                })
            })
        });
        if !supported {
            return false;
        }
        let pending = &mut placement.pending;
        pending.clear();
        if pending.try_reserve_exact(self.nodes.len()).is_err() {
            return false;
        }
        if self.params[self.root].disabled {
            return true;
        }
        let [width, height] = size(&self.records[self.root]);
        let root_rect = [[0.0, width], [0.0, height]];
        if let Some(branch) = publish(
            source,
            self.root,
            root_rect,
            [0.0; 2],
            partial,
            &self.nodes,
            &mut self.records,
        ) {
            pending.push(branch);
        }
        while let Some(Branch {
            row,
            edges,
            partial,
        }) = pending.pop()
        {
            let params = &self.params[row];
            let ChildrenLayout::Stack { axis, spacing, .. } = params.children_layout else {
                // Only parents enter the queue, and admission checked their mode.
                continue;
            };
            let x = axis == Axis::X;
            let main = usize::from(!x);
            let cross = usize::from(x);
            let origin = [edges[0][0], edges[1][0]];
            let padding = [params.padding.x, params.padding.y];
            let frame = ParentFrame {
                edges,
                origin,
                padding,
                flipped: [false; 2],
            };
            let [mut cursor, _] = inner_range::<RustFloat>(edges[main], padding[main]);
            let [cross_start, _] = inner_range::<RustFloat>(edges[cross], padding[cross]);
            let mut next = self.nodes[row].and_then(Node::first);
            let start = pending.len();
            while let Some(child) = next {
                let child_params = &self.params[child];
                let node = self.nodes[child];
                next = node.and_then(Node::next);
                if child_params.disabled {
                    continue;
                }
                let child_size = size(&self.records[child]);
                let cross_pos = if x {
                    child_params.position.y
                } else {
                    child_params.position.x
                };
                let rect = if matches!(cross_pos, Pos::Start) && zero_margins(child_params) {
                    RustFloat::place_start(&mut cursor, cross_start, x, child_size, spacing)
                } else {
                    stack_item::<RustFloat>(
                        &frame,
                        stack_style::<RustFloat>(child_params),
                        child_size,
                        x,
                        &mut cursor,
                        spacing,
                    )
                };
                if let Some(branch) = publish(
                    source,
                    child,
                    rect,
                    origin,
                    partial,
                    &self.nodes,
                    &mut self.records,
                ) {
                    pending.push(branch);
                }
            }
            pending[start..].reverse();
        }
        true
    }
}

#[inline(always)]
fn size(record: &NodeLayoutData) -> [f32; 2] {
    [
        record.values[slot_index(Axis::X, Kind::Final)],
        record.values[slot_index(Axis::Y, Kind::Final)],
    ]
}

#[inline(always)]
fn publish<A: TreeAdapter<NodeId = NodeKey>>(
    source: &mut A,
    row: usize,
    edges: Edges,
    origin: [f32; 2],
    partial: bool,
    nodes: &[Option<Node>],
    records: &mut [NodeLayoutData],
) -> Option<Branch> {
    let work = records[row].placement;
    if !work.visits(!partial) {
        return None;
    }
    let node = nodes[row]?;
    records[row].placement = PlacementWork::Clean;
    let write = work.writes(!partial);
    if write {
        let [x, y] = stable_edges::<RustFloat>(edges);
        let [local_x, local_y] = stable_edges::<RustFloat>([
            edges[0].map(|edge| edge - origin[0]),
            edges[1].map(|edge| edge - origin[1]),
        ]);
        source.write_output_rect(node.key, Xy::new(x, y), Xy::new(local_x, local_y));
    }
    node.first().map(|_| Branch {
        row,
        edges,
        partial: partial && !write,
    })
}
impl Frame {
    fn place_snapped_stacks<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        scale: f32,
    ) -> bool {
        let placement = &mut self.stack_placement;
        let eligible = *placement.snapped_eligible.get_or_insert_with(|| {
            self.nodes.iter().zip(&self.params).all(|(node, params)| {
                node.is_none_or(|node| {
                    !params.free_placement
                        && (node.first().is_none()
                            || (!params.children_origin_flipped.x
                                && !params.children_origin_flipped.y
                                && matches!(params.children_layout, ChildrenLayout::Stack { .. })))
                })
            })
        });
        if !eligible {
            return false;
        }
        let rows = &mut placement.rows;
        let edges = &mut placement.edges;
        rows.clear();
        edges.clear();
        if rows.try_reserve_exact(self.nodes.len()).is_err()
            || edges.try_reserve_exact(self.nodes.len()).is_err()
        {
            return false;
        }
        if self.params[self.root].disabled {
            return true;
        }
        let [width, height] = size(&self.records[self.root]);
        rows.push((self.root, usize::MAX));
        edges.push([0.0, width, 0.0, height]);
        let mut at = 0;
        while let Some(&(row, _)) = rows.get(at) {
            let parent = at;
            at += 1;
            let Some(mut child) = self.nodes[row].and_then(Node::first) else {
                continue;
            };
            let params = &self.params[row];
            let ChildrenLayout::Stack {
                axis,
                arrange: arrangement,
                spacing,
            } = params.children_layout
            else {
                return false;
            };
            let x = axis == Axis::X;
            let main = usize::from(!x);
            let cross = usize::from(x);
            let [left, right, top, bottom] = edges[parent];
            let raw = [[left, right], [top, bottom]];
            let padding = [params.padding.x, params.padding.y];
            let main_range = inner_range::<RustFloat>(raw[main], padding[main]);
            let cross_range = inner_range::<RustFloat>(raw[cross], padding[cross]);
            let (mut cursor, gap) = if matches!(arrangement, Arrange::Start) {
                (main_range[0], spacing)
            } else {
                let mut total = 0.0;
                let mut count = 0u32;
                let mut next = Some(child);
                while let Some(row) = next {
                    let style = &self.params[row];
                    next = self.nodes[row].and_then(Node::next);
                    if !style.disabled {
                        let [start, end] = crate::flow::margins(style, axis);
                        total +=
                            RustFloat::with_margin(size(&self.records[row])[main], start + end);
                        count = count.saturating_add(1);
                    }
                }
                if count > 0 {
                    total += spacing * crate::place::stack_line::between_gaps(count) as f32;
                }
                crate::placement_geometry::line_start_and_gap::<RustFloat>(
                    arrangement,
                    main_range,
                    total,
                    count,
                    spacing,
                )
            };
            let frame = ParentFrame {
                edges: raw,
                origin: [left, top],
                padding,
                flipped: [false; 2],
            };
            loop {
                let style = &self.params[child];
                if !style.disabled {
                    let child_size = size(&self.records[child]);
                    let cross_position = if x {
                        style.position.y
                    } else {
                        style.position.x
                    };
                    let rect = if zero_margins(style)
                        && matches!(cross_position, Pos::Start | Pos::Center)
                    {
                        if matches!(cross_position, Pos::Start) {
                            RustFloat::place_start(&mut cursor, cross_range[0], x, child_size, gap)
                        } else {
                            let cross_edges = crate::placement_geometry::centered_range::<RustFloat>(
                                cross_range[0],
                                cross_range[1],
                                child_size[cross],
                            );
                            let along = RustFloat::place(
                                &mut cursor,
                                false,
                                main_range,
                                child_size[main],
                                [0.0; 2],
                                gap,
                            );
                            if x {
                                [along, cross_edges]
                            } else {
                                [cross_edges, along]
                            }
                        }
                    } else {
                        stack_item::<RustFloat>(
                            &frame,
                            stack_style::<RustFloat>(style),
                            child_size,
                            x,
                            &mut cursor,
                            gap,
                        )
                    };
                    let [[left, right], [top, bottom]] = rect;
                    rows.push((child, parent));
                    edges.push([left, right, top, bottom]);
                }
                let Some(next) = self.nodes[child].and_then(Node::next) else {
                    break;
                };
                child = next;
            }
        }

        crate::place::Snapper::new(scale).snap_many(edges);
        for (index, &(row, parent)) in rows.iter().enumerate() {
            let [left, right, top, bottom] = edges[index];
            let origin = if let Some(&[left, _, top, _]) = edges.get(parent) {
                [left, top]
            } else {
                [0.0; 2]
            };
            let [abs_x, abs_y] = stable_edges::<RustFloat>([[left, right], [top, bottom]]);
            let [local_x, local_y] = stable_edges::<RustFloat>([
                [left - origin[0], right - origin[0]],
                [top - origin[1], bottom - origin[1]],
            ]);
            if let Some(node) = self.nodes[row] {
                self.records[row].placement = PlacementWork::Clean;
                source.write_output_rect(
                    node.key,
                    Xy::new(abs_x, abs_y),
                    Xy::new(local_x, local_y),
                );
            }
        }
        true
    }
}
