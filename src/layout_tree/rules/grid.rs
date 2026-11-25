//! Resolve shared tracks through descendants before positioning any grid item.
use super::driver::{Frame, FrameNode};
use super::flex::bound;
use crate::tracks::{GridAlign, GridCell, GridItem, TrackAxis, TrackContribution, TrackGrid};
use crate::{Axis, ChildrenLayout, Margin, Size, Xy};

fn in_flow(n: &FrameNode) -> bool {
    !n.base.disabled && !n.base.free_placement
}
fn item(n: &FrameNode) -> GridItem {
    let mut it = n.rule.grid_item;
    for a in [Axis::X, Axis::Y] {
        if it.span[a] == 1 {
            it.span[a] = n.base.grid_span[a].max(1);
        }
    }
    it
}
fn children(frame: &Frame<'_>, id: usize) -> (Vec<usize>, Vec<GridItem>) {
    frame.nodes[id]
        .children
        .iter()
        .copied()
        .filter(|&c| in_flow(&frame.nodes[c]))
        .map(|c| (c, item(&frame.nodes[c])))
        .unzip()
}
fn metrics(n: &FrameNode, a: Axis, inner: Xy<f32>) -> (f32, f32, f32) {
    let p = &n.base;
    let low = p.padding[a]
        .iter()
        .sum::<f32>()
        .max(p.min_size[a].map_or(0., |s| bound(s, a, inner, n.natural, super::size(n.rect))));
    let high = p.max_size[a]
        .map_or(f32::INFINITY, |s| {
            bound(s, a, inner, n.natural, super::size(n.rect))
        })
        .max(low);
    let pref = match p.size[a] {
        Size::Auto | Size::Fill | Size::FitContent => n.measured[a],
        fixed => bound(fixed, a, inner, n.natural, super::size(n.rect)),
    };
    (low, pref.min(high).max(low), high)
}
fn occupied_axis(n: &FrameNode, a: Axis) -> bool {
    n.rule
        .grid
        .as_ref()
        .is_some_and(|grid| matches!(grid.tracks[a], TrackAxis::Subgrid))
}
fn boundary(edges: &[[f32; 2]], r: &std::ops::Range<usize>) -> [f32; 2] {
    let first = edges[r.start];
    let last = edges[r.end - 1];
    [first[0].min(last[0]), first[1].max(last[1])]
}
fn item_edges(
    frame: &Frame<'_>,
    i: usize,
    parent: usize,
    grid: &TrackGrid,
    a: Axis,
    area: [f32; 2],
) -> [f32; 2] {
    let n = &frame.nodes[i];
    let total = area[1] - area[0];
    let mut room = frame.content_size(parent);
    room[a] = total;
    let (min, pref, max) = metrics(n, a, room);
    let [m0, m1] = n.base.margin[a].map(Margin::as_px);
    let m = m0.unwrap_or(0.) + m1.unwrap_or(0.);
    let align = n.rule.grid_item.align[a].unwrap_or(grid.align_items[a]);
    let share = occupied_axis(n, a);
    let stretch = align == GridAlign::Stretch
        && matches!(n.base.size[a], Size::Fill | Size::Auto)
        && m0.is_some()
        && m1.is_some();
    let size = if share {
        (total - m).max(0.)
    } else if stretch {
        (total - m).min(max).max(min)
    } else {
        pref
    };
    let spare = total - size - m;
    let flipped = frame.nodes[parent].base.children_origin_flipped[a];
    let start = if m0.is_none() || m1.is_none() {
        m0.unwrap_or(spare.max(0.) / ((u8::from(m0.is_none()) + u8::from(m1.is_none())) as f32))
    } else {
        let offset = match align {
            GridAlign::Center => spare / 2.,
            GridAlign::End => spare,
            _ => 0.,
        };
        m0.unwrap_or(0.) + if flipped { spare - offset } else { offset }
    };
    [area[0] + start, area[0] + start + size]
}
type Baselines = Vec<[Option<f32>; 2]>;
struct ResolvedAxis {
    edges: Vec<[f32; 2]>,
    baselines: Baselines,
}
struct TrackMeasurements {
    items: Vec<TrackContribution>,
    // Offset from the track's first/last logical edge.
    baselines: Baselines,
}
fn baseline_at(
    align: GridAlign,
    n: &FrameNode,
    a: Axis,
    size: f32,
    tracks: &std::ops::Range<usize>,
) -> Option<(usize, usize, f32)> {
    if n.base.margin[a].iter().any(|m| m.as_px().is_none()) || occupied_axis(n, a) {
        return None;
    }
    match align {
        GridAlign::FirstBaseline => Some((tracks.start, 0, n.rule.baselines.x.unwrap_or(size))),
        GridAlign::LastBaseline => Some((tracks.end - 1, 1, n.rule.baselines.y.unwrap_or(size))),
        _ => None,
    }
}
fn inherited_tracks(frame: &Frame<'_>, id: usize, a: Axis) -> Option<ResolvedAxis> {
    if !occupied_axis(&frame.nodes[id], a) {
        return None;
    }
    let parent = frame.nodes[id].parent?;
    let pg = frame.nodes[parent].rule.grid.as_ref()?;
    let indices = &frame.grid_cells.get(&id)?[a];
    let resolved = &frame.grid_tracks.get(&parent)?[a];
    let bounds = boundary(resolved, indices);
    let rect = item_edges(frame, id, parent, pg, a, bounds);
    let node = &frame.nodes[id];
    let origin = rect[0] + node.effective.padding[a][0];
    let extent = frame.content_size(id)[a];
    let mut edges: Vec<_> = resolved[indices.clone()]
        .iter()
        .map(|v| {
            [
                (v[0] - origin).clamp(0., extent),
                (v[1] - origin).clamp(0., extent),
            ]
        })
        .collect();
    let mut baselines = frame.grid_baselines.get(&parent)?[a][indices.clone()]
        .iter()
        .map(|pair| pair.map(|v| v.map(|value| value - origin)))
        .collect::<Vec<_>>();
    if node.base.children_origin_flipped[a] != frame.nodes[parent].base.children_origin_flipped[a] {
        edges.reverse();
        baselines.reverse();
    }
    Some(ResolvedAxis { edges, baselines })
}
fn contributions(
    frame: &Frame<'_>,
    parent: usize,
    a: Axis,
    ids: &[usize],
    cells: &[GridCell],
    count: usize,
) -> TrackMeasurements {
    let primary_flip = frame.nodes[parent].base.children_origin_flipped[a];
    let mut demands = Vec::new();
    let mut groups: Baselines = vec![[None; 2]; count];
    let mut participants = Vec::new();
    let mut todo: Vec<_> = ids
        .iter()
        .copied()
        .zip(cells.iter().cloned())
        .map(|(id, cell)| (id, cell, 0., 0.))
        .collect();
    while let Some((id, cell, extra_start, extra_end)) = todo.pop() {
        let n = &frame.nodes[id];
        let containing = n.parent.map_or(frame.window, |p| frame.content_size(p));
        let (mut min, mut pref, _) = metrics(n, a, containing);
        let shared = occupied_axis(n, a) && !n.children.is_empty();
        if matches!(n.base.size[a], Size::Frac(_)) {
            pref = min;
        }
        if !shared && matches!(n.base.size[a], Size::Pixels(_) | Size::FitContent) {
            min = pref;
        }
        let m = n.base.margin[a].map(|v| v.as_px().unwrap_or(0.));
        let extra = extra_start + extra_end + m[0] + m[1];
        let r = cell[a].clone();
        let parent_grid = frame.nodes[n.parent.unwrap()].rule.grid.as_ref().unwrap();
        let align = n.rule.grid_item.align[a].unwrap_or(parent_grid.align_items[a]);
        if let Some((track, kind, baseline)) = baseline_at(align, n, a, pref, &r) {
            let low = baseline + m[0];
            let high = pref - baseline + m[1];
            let distance = if kind == 0 {
                extra_start + if primary_flip { high } else { low }
            } else {
                extra_end + if primary_flip { low } else { high }
            };
            let max = &mut groups[track][kind];
            *max = Some(max.map_or(distance, |v| v.max(distance)));
            participants.push((demands.len(), track, kind, distance));
        }
        demands.push(TrackContribution {
            tracks: r.clone(),
            minimum: min + extra,
            preferred: if shared { min + extra } else { pref + extra },
        });
        if !shared {
            continue;
        }
        let grid = n.rule.grid.as_ref().unwrap();
        let (nested, items) = children(frame, id);
        let inherited = Xy::new(Some(cell.x.len()), Some(cell.y.len()));
        let (_, slots) = grid.place_cells(frame.content_size(id), &items, inherited);
        let reverse = n.base.children_origin_flipped[a] != primary_flip;
        let mut first = n.effective.padding[a][0] + m[0];
        let mut last = n.effective.padding[a][1] + m[1];
        if primary_flip {
            std::mem::swap(&mut first, &mut last);
        }
        for (child, mut slot) in nested.into_iter().zip(slots) {
            let local = slot[a].clone();
            let assigned = if reverse {
                r.end - local.end..r.end - local.start
            } else {
                r.start + local.start..r.start + local.end
            };
            let before = if assigned.start == r.start {
                first + extra_start
            } else {
                0.
            };
            let after = if assigned.end == r.end {
                last + extra_end
            } else {
                0.
            };
            slot[a] = assigned;
            todo.push((child, slot, before, after));
        }
    }
    for (index, track, kind, prior) in participants {
        let shift = groups[track][kind].unwrap() - prior;
        demands[index].minimum += shift;
        demands[index].preferred += shift;
    }
    TrackMeasurements {
        items: demands,
        baselines: groups,
    }
}
pub(super) fn apply(frame: &mut Frame<'_>, parent: usize, grid: &TrackGrid) {
    let inherited = Xy::new(
        inherited_tracks(frame, parent, Axis::X),
        inherited_tracks(frame, parent, Axis::Y),
    );
    let inherited_counts = Xy::new(
        inherited.x.as_ref().map(|r| r.edges.len()),
        inherited.y.as_ref().map(|r| r.edges.len()),
    );
    let (ids, items) = children(frame, parent);
    let inner = frame.content_size(parent);
    let (counts, cells) = grid.place_cells(inner, &items, inherited_counts);
    let demand = Xy::new(
        contributions(frame, parent, Axis::X, &ids, &cells, counts.x),
        contributions(frame, parent, Axis::Y, &ids, &cells, counts.y),
    );
    let mut natural = inner;
    for a in [Axis::X, Axis::Y] {
        if inherited[a].is_none() {
            natural[a] = grid.resolve_axis(a, None, counts[a], &demand[a].items).1;
        }
    }
    frame.set_intrinsic(parent, natural);
    let inner = frame.content_size(parent);
    let resolve = |a: Axis, inherited: Option<ResolvedAxis>| {
        inherited.unwrap_or_else(|| {
            let mut edges = grid
                .resolve_axis(a, Some(inner[a]), counts[a], &demand[a].items)
                .0;
            let flip = frame.nodes[parent].base.children_origin_flipped[a];
            if flip {
                for edge in &mut edges {
                    *edge = [inner[a] - edge[1], inner[a] - edge[0]];
                }
            }
            let baselines = edges
                .iter()
                .zip(&demand[a].baselines)
                .map(|(&[lo, hi], group)| {
                    [
                        group[0].map(|v| if flip { hi - v } else { lo + v }),
                        group[1].map(|v| if flip { lo + v } else { hi - v }),
                    ]
                })
                .collect();
            ResolvedAxis { edges, baselines }
        })
    };
    let x = resolve(Axis::X, inherited.x);
    let y = resolve(Axis::Y, inherited.y);
    let edges = Xy::new(x.edges, y.edges);
    let baselines = Xy::new(x.baselines, y.baselines);
    frame.nodes[parent].effective.children_layout = ChildrenLayout::Free;
    for (id, cell) in ids.into_iter().zip(cells) {
        let mut rect = Xy::new(
            item_edges(
                frame,
                id,
                parent,
                grid,
                Axis::X,
                boundary(&edges.x, &cell.x),
            ),
            item_edges(
                frame,
                id,
                parent,
                grid,
                Axis::Y,
                boundary(&edges.y, &cell.y),
            ),
        );
        let n = &frame.nodes[id];
        for a in [Axis::X, Axis::Y] {
            let align = n.rule.grid_item.align[a].unwrap_or(grid.align_items[a]);
            let size = rect[a][1] - rect[a][0];
            if let Some((track, kind, offset)) = baseline_at(align, n, a, size, &cell[a])
                && let Some(target) = baselines[a][track][kind]
            {
                let start = target - offset;
                rect[a] = [start, start + size];
            }
        }
        frame.place(id, parent, rect);
        frame.grid_cells.insert(id, cell);
    }
    frame.grid_tracks.insert(parent, edges);
    frame.grid_baselines.insert(parent, baselines);
}
