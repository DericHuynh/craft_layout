//! Resolve shared tracks through descendants before positioning any grid item.
use super::driver::{Frame, FrameNode};
use super::flex::bound;
use crate::tracks::{
    GridAlign, GridCell, GridItem, Track, TrackAxis, TrackContribution, TrackGrid, TrackMax,
    TrackMin,
};
use crate::{Axis, ChildrenLayout, Margin, Size, Xy};

fn in_flow(n: &FrameNode) -> bool {
    !n.base.disabled && !n.base.free_placement && n.rule.grid_overlay.is_none()
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
    let low = (p.padding[a].iter().sum::<f32>() - n.gutter[a])
        .max(0.)
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
// If this area has an automatic track minimum, the supplied content
// minimum can protect an item from shrinking. A definite maximum on every
// spanned track limits that protection. Unresolved percentages are intrinsic
// during measurement and become definite again for final placement.
fn content_floor(
    n: &FrameNode,
    a: Axis,
    context: &TrackGrid,
    tracks: &std::ops::Range<usize>,
    extent: Option<f32>,
    inner: Xy<f32>,
) -> (f32, bool) {
    let Some(measure) = n.rule.grid_content_minimum[a] else {
        return (0., false);
    };
    let template = &context.tracks[a];
    let gap = context.gap[a].max(0.);
    let explicit = template.count(inner[a], gap, None);
    let mut qualifies = false;
    let mut cap = gap * tracks.len().saturating_sub(1) as f32;
    let mut relative = false;
    for i in tracks.clone() {
        let track = context.track_at(a, i, explicit);
        let (min, max) = track.bounds();
        if tracks.len() > 1 && matches!(max, TrackMax::Fr(_)) {
            return (0., false);
        }
        qualifies |= matches!(min, TrackMin::Content) || min.is_relative() && extent.is_none();
        let fixed_min = min.resolve(extent).unwrap_or(0.) as f32;
        // fit-content() limits preferred growth. Its argument is not a
        // fixed maximum for the automatic minimum of its occupants.
        let fixed_max = match (track, max) {
            (Track::FitContent(_) | Track::FitContentPercent(_), _) => f32::INFINITY,
            (_, TrackMax::Pixels(v)) => v.max(0.),
            (_, TrackMax::Percent(p)) => {
                relative = true;
                extent.map_or(f32::INFINITY, |w| p.max(0.) * w)
            }
            _ => f32::INFINITY,
        };
        relative |= min.is_relative();
        cap += fixed_max.max(fixed_min);
    }
    if !qualifies {
        return (0., false);
    }
    let m = n.base.margin[a]
        .iter()
        .filter_map(|v| v.as_px())
        .sum::<f32>();
    let hard_max = n.base.max_size[a].map_or(f32::INFINITY, |s| {
        bound(s, a, inner, n.natural, super::size(n.rect))
    });
    (
        n.grid_minimum[a]
            .unwrap_or_else(|| bound(measure, a, inner, n.natural, super::size(n.rect)))
            .min(cap - m)
            .min(hard_max),
        relative,
    )
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
    tracks: &std::ops::Range<usize>,
) -> [f32; 2] {
    let n = &frame.nodes[i];
    let total = area[1] - area[0];
    let mut room = frame.content_size(parent);
    let (floor, _) = content_floor(n, a, grid, tracks, Some(room[a]), room);
    room[a] = total;
    let (hard_min, pref, max) = metrics(n, a, room);
    let min = hard_min.max(floor.min(max));
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
    } else if n.base.size[a] == Size::Auto
        && let Some(s) = n.rule.grid_content_minimum[a]
    {
        let content =
            n.grid_minimum[a].unwrap_or_else(|| bound(s, a, room, n.natural, super::size(n.rect)));
        pref.min((total - m).max(content)).max(min).min(max)
    } else {
        pref.max(min)
    };
    let spare = total - size - m;
    let flipped = frame.nodes[parent].base.children_origin_flipped[a];
    let start = if m0.is_none() || m1.is_none() {
        m0.unwrap_or(spare.max(0.) / ((u8::from(m0.is_none()) + u8::from(m1.is_none())) as f32))
    } else {
        let offset = match align {
            GridAlign::SafeCenter => spare.max(0.) / 2.,
            GridAlign::SafeEnd => spare.max(0.),
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
    relative_floor: bool,
    items: Vec<TrackContribution>,
    min_content: Vec<f32>,
    // Offset from the track's first/last logical edge.
    baselines: Baselines,
}
fn baseline_at(
    align: GridAlign,
    frame: &Frame<'_>,
    id: usize,
    a: Axis,
    size: f32,
    tracks: &std::ops::Range<usize>,
) -> Option<(usize, usize, f32)> {
    let n = &frame.nodes[id];
    if n.base.margin[a].iter().any(|m| m.as_px().is_none()) || occupied_axis(n, a) {
        return None;
    }
    match align {
        GridAlign::FirstBaseline => Some((
            tracks.start,
            0,
            super::flex::exported_baseline(frame, id, a, false).unwrap_or(size),
        )),
        GridAlign::LastBaseline => Some((
            tracks.end - 1,
            1,
            super::flex::exported_baseline(frame, id, a, true).unwrap_or(size),
        )),
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
    let resolved = &frame.grid_tracks.get(&frame.nodes[parent].id.key())?[a];
    let bounds = boundary(resolved, indices);
    let rect = item_edges(frame, id, parent, pg, a, bounds, indices);
    let node = &frame.nodes[id];
    let origin = crate::placement_geometry::inner_start::<crate::placement_geometry::RustFloat>(
        rect,
        node.effective.padding[a][0],
    );
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
    root_grid: &TrackGrid,
    a: Axis,
    ids: &[usize],
    cells: &[GridCell],
    count: usize,
    extent: Option<f32>,
) -> TrackMeasurements {
    let primary_flip = frame.nodes[parent].base.children_origin_flipped[a];
    let grid_space = frame.content_size(parent);
    let mut demands = Vec::new();
    let mut min_content = Vec::new();
    let mut relative_floor = false;
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
        let (floor, relative) = content_floor(n, a, root_grid, &cell[a], extent, grid_space);
        min = min.max(floor);
        pref = pref.max(min);
        relative_floor |= relative;
        let shared = occupied_axis(n, a) && !n.children.is_empty();
        if n.relative_size(a) {
            pref = min;
        } else if !shared && matches!(n.base.size[a], Size::Pixels(_) | Size::FitContent) {
            min = pref;
        }
        let m = n.base.margin[a].map(|v| v.as_px().unwrap_or(0.));
        // Percentage margins resolve against the allocated area after track sizing.
        let inline = frame.nodes[n.parent.unwrap()]
            .context
            .axis(crate::LogicalAxis::Inline);
        let basis = if a == inline {
            n.grid_reference.map_or(0., |area| area[inline])
        } else {
            0.
        };
        let relative_margin = n.rule.box_model.margin_fraction[a].iter().sum::<f32>() * basis;
        let extra = extra_start + extra_end + m[0] + m[1] - relative_margin;
        let r = cell[a].clone();
        let parent_grid = frame.nodes[n.parent.unwrap()].rule.grid.as_ref().unwrap();
        let align = n.rule.grid_item.align[a].unwrap_or(parent_grid.align_items[a]);
        if let Some((track, kind, baseline)) = baseline_at(align, frame, id, a, pref, &r) {
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
        let measured = match n.rule.grid_intrinsic_minimum[a] {
            Some(Size::FitContent) => n.measured[a],
            Some(s) => bound(s, a, containing, n.natural, super::size(n.rect)),
            None => min,
        };
        min_content.push(n.grid_minimum[a].unwrap_or(measured).clamp(min, pref) + extra);
        demands.push(TrackContribution {
            tracks: r.clone(),
            minimum: min + extra,
            preferred: if shared { min + extra } else { pref + extra },
        });
        if !shared {
            continue;
        }
        let grid = n.rule.grid.as_ref().unwrap();
        let inherited = Xy::new(Some(cell.x.len()), Some(cell.y.len()));
        let Placement {
            ids: nested,
            cells: slots,
            ..
        } = place(frame, id, grid, inherited);
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
        min_content[index] += shift;
        demands[index].minimum += shift;
        demands[index].preferred += shift;
    }
    TrackMeasurements {
        relative_floor,
        items: demands,
        min_content,
        baselines: groups,
    }
}
// Resolve signed line coordinates relative to the explicit template before
// assigning any auto cells. Adding leading tracks translates every item by
// the same amount; a late definite item therefore preserves all line names.
struct Placement<'g> {
    grid: std::borrow::Cow<'g, TrackGrid>,
    ids: Vec<usize>,
    counts: Xy<usize>,
    cells: Vec<GridCell>,
    explicit: Xy<usize>,
    shift: Xy<usize>,
}
fn place<'g>(
    frame: &Frame<'_>,
    parent: usize,
    grid: &'g TrackGrid,
    inherited: Xy<Option<usize>>,
) -> Placement<'g> {
    let (ids, mut items) = children(frame, parent);
    let inner = frame.content_size(parent);
    let mut explicit = Xy::new_symm(0);
    let mut shift = Xy::new_symm(0);
    let mut grid = std::borrow::Cow::Borrowed(grid);
    for a in [Axis::X, Axis::Y] {
        explicit[a] = grid.explicit_count(a, inner[a], inherited[a]);
        if grid.tracks[a] == TrackAxis::Subgrid
            && let Some(ancestor) = frame.nodes[parent].parent
            && let Some(cell) = frame.grid_cells.get(&parent)
            && let Some(names) = frame.grid_line_names.get(&frame.nodes[ancestor].id.key())
        {
            let reverse = frame.nodes[ancestor].base.children_origin_flipped[a]
                != frame.nodes[parent].base.children_origin_flipped[a];
            let r = &cell[a];
            let mut local = grid.line_names[a].clone();
            for (&i, ns) in names[a].range(r.start..=r.end) {
                let at = if reverse { r.end - i } else { i - r.start };
                local.entry(at).or_default().extend(ns.iter().cloned());
            }
            grid.to_mut().line_names[a] = local;
        }
        if let TrackAxis::AutoRepeat {
            before,
            pattern,
            after,
            ..
        } = &grid.tracks[a]
        {
            let repeat_names = &grid.repeat_line_names[a];
            if !repeat_names.group.is_empty() || !repeat_names.suffix.is_empty() {
                let mut names = grid.line_names[a].clone();
                let end = explicit[a].saturating_sub(after.len());
                for offset in (before.len()..end).step_by(pattern.len().max(1)) {
                    crate::tracks::lines::append(&mut names, offset, &repeat_names.group, end);
                }
                crate::tracks::lines::append(&mut names, end, &repeat_names.suffix, explicit[a]);
                grid.to_mut().line_names[a] = names;
            }
        }
        if !ids
            .iter()
            .any(|&id| frame.nodes[id].rule.grid_lines[a].is_some())
        {
            continue;
        }
        let count = explicit[a];
        let names = grid.placement_names(a);
        let positions: Vec<_> = ids
            .iter()
            .zip(&items)
            .map(|(&id, it)| {
                frame.nodes[id].rule.grid_lines[a]
                    .as_ref()
                    .map_or((it.start[a].map(i64::from), it.span[a]), |pair| {
                        crate::tracks::lines::slot(pair, count, &names)
                    })
            })
            .collect();
        let leading = positions
            .iter()
            .filter_map(|&(start, _)| start)
            .min()
            .unwrap_or(0)
            .min(0)
            .unsigned_abs()
            .min(u64::from(u16::MAX)) as usize;
        let leading = if grid.tracks[a] == TrackAxis::Subgrid {
            0
        } else {
            leading
        };
        shift[a] = leading;
        for (it, (start, span)) in items.iter_mut().zip(positions) {
            it.start[a] = start.map(|v| (v + leading as i64).clamp(0, i64::from(u16::MAX)) as u16);
            it.span[a] = span;
        }
        if leading > 0 {
            let pattern = &grid.implicit_pattern[a];
            let prefix = (0..leading)
                .map(|i| {
                    if pattern.is_empty() {
                        grid.implicit[a]
                    } else {
                        pattern
                            [(i as i64 - leading as i64).rem_euclid(pattern.len() as i64) as usize]
                    }
                })
                .collect();
            let template = std::mem::take(&mut grid.to_mut().tracks[a]);
            grid.to_mut().tracks[a] = TrackAxis::Prefixed {
                implicit: prefix,
                explicit: Box::new(template),
            };
        }
    }
    let (counts, cells) = grid.place_cells(inner, &items, inherited);
    Placement {
        grid,
        ids,
        counts,
        cells,
        explicit,
        shift,
    }
}

// A CSS grid line falls on different sides of its gutter for starts and
// ends. Empty tracks in an auto-fit run share the surrounding gutter.
fn line_edge(
    edges: &[[f32; 2]],
    i: usize,
    edge: usize,
    flip: bool,
    inner: f32,
    collapse: std::ops::Range<usize>,
) -> f32 {
    if edges.is_empty() {
        return if flip { inner } else { 0. };
    }
    if i == 0 {
        return edges[0][usize::from(flip)];
    }
    if i == edges.len() {
        return edges[i - 1][usize::from(!flip)];
    }
    let side = edge ^ usize::from(flip);
    if edge == 1 {
        return edges[i - 1][side];
    }
    let mut start = i;
    while start + 1 < edges.len() && collapse.contains(&start) && edges[start][0] == edges[start][1]
    {
        start += 1;
    }
    edges[start][side]
}
fn area_for(
    frame: &Frame<'_>,
    parent: usize,
    id: usize,
    grid: &TrackGrid,
    edges: &Xy<Vec<[f32; 2]>>,
    explicit: Xy<usize>,
    shift: Xy<usize>,
) -> crate::XyRect {
    let p = &frame.nodes[parent];
    let outer = frame.outer_size(parent);
    let inner = p.inner_size(outer);
    let offset = p.content_offset(outer);
    // An unspecified grid line uses the padding box. Convert that box to
    // content coordinates once, even when both insets exhaust the grid.
    let port = super::viewport::port_in(p, Xy::new([0., outer.x], [0., outer.y]));
    let mut rect = Xy::new_symm([0.; 2]);
    for a in [Axis::X, Axis::Y] {
        let flip = p.base.children_origin_flipped[a];
        let mut area = port[a].map(|edge| edge - offset[a]);
        if let Some(pair) = &frame.nodes[id].rule.grid_lines[a] {
            let lines =
                crate::tracks::lines::endpoints(pair, explicit[a], &grid.placement_names(a), true);
            let collapse = grid.tracks[a].collapsed_range(explicit[a] + shift[a]);
            for (edge, line) in lines.into_iter().enumerate() {
                if let Some(i) = line
                    .and_then(|l| usize::try_from(l + shift[a] as i64).ok())
                    .filter(|&i| i <= edges[a].len())
                {
                    area[edge ^ usize::from(flip)] =
                        line_edge(&edges[a], i, edge, flip, inner[a], collapse.clone());
                }
            }
        }
        if area[0] > area[1] {
            let start = area[usize::from(flip)];
            area = [start, start];
        }
        rect[a] = area;
    }
    rect
}
/// The ancestor's grid area replaces its padding box for a positioned
/// descendant, including when a static wrapper lies between them.
pub(super) fn ancestor_area(frame: &Frame<'_>, parent: usize, id: usize) -> Option<crate::XyRect> {
    let p = &frame.nodes[parent];
    if frame.nodes[id].rule.grid_lines == Xy::default() {
        return None;
    }
    let grid = p.rule.grid.as_ref()?;
    let edges = frame.grid_tracks.get(&p.id.key())?;
    let origin = p.grid_origin;
    let mut declaration = std::borrow::Cow::Borrowed(grid);
    if let Some(published) = frame.grid_line_names.get(&p.id.key()) {
        for a in [Axis::X, Axis::Y] {
            declaration.to_mut().line_names[a] = published[a]
                .iter()
                .filter_map(|(&i, ns)| i.checked_sub(origin[a].1).map(|i| (i, ns.clone())))
                .collect();
        }
    }
    let mut rect = area_for(
        frame,
        parent,
        id,
        &declaration,
        edges,
        Xy::new(origin.x.0, origin.y.0),
        Xy::new(origin.x.1, origin.y.1),
    );
    let offset = frame.content_offset(parent);
    for a in [Axis::X, Axis::Y] {
        let before = p.rect[a][0] + offset[a];
        rect[a] = rect[a].map(|x| x + before);
    }
    Some(rect)
}
fn place_overlays(
    frame: &mut Frame<'_>,
    parent: usize,
    grid: &TrackGrid,
    edges: &Xy<Vec<[f32; 2]>>,
    explicit: Xy<usize>,
    shift: Xy<usize>,
) {
    for pos in 0..frame.nodes[parent].children.len() {
        let id = frame.nodes[parent].children[pos];
        let n = &frame.nodes[id];
        let Some(insets) = n.rule.grid_overlay else {
            continue;
        };
        if n.base.disabled {
            continue;
        }
        let mut rect = area_for(frame, parent, id, grid, edges, explicit, shift);
        let room = super::size(rect);
        for a in [Axis::X, Axis::Y] {
            let area = rect[a];
            let flip = frame.nodes[parent].base.children_origin_flipped[a];
            let [s, e] = insets[a].map(|v| v.map(|l| l.resolve(room[a])));
            let [m0, m1] = n.base.margin[a].map(Margin::as_px);
            let margins = m0.unwrap_or(0.) + m1.unwrap_or(0.);
            let (min, pref, max) = metrics(n, a, room);
            let align = n.rule.grid_item.align[a].unwrap_or(grid.align_items[a]);
            let size = if s.is_some()
                && e.is_some()
                && matches!(n.base.size[a], Size::Auto | Size::Fill)
            {
                (room[a] - s.unwrap() - e.unwrap() - margins).clamp(min, max)
            } else {
                pref
            };
            let spare = room[a] - s.unwrap_or(0.) - e.unwrap_or(0.) - size - margins;
            let auto = if s.is_some() && e.is_some() {
                spare.max(0.) / (u8::from(m0.is_none()) + u8::from(m1.is_none())).max(1) as f32
            } else {
                0.
            };
            let start = if s.is_some() && (e.is_none() || !flip) {
                s.unwrap() + m0.unwrap_or(auto)
            } else if let Some(e) = e {
                room[a] - e - size - m1.unwrap_or(auto)
            } else {
                let logical = match align {
                    GridAlign::End | GridAlign::LastBaseline => spare,
                    GridAlign::Center => spare / 2.,
                    GridAlign::SafeEnd => spare.max(0.),
                    GridAlign::SafeCenter => spare.max(0.) / 2.,
                    _ => 0.,
                };
                m0.unwrap_or(0.) + if flip { spare - logical } else { logical }
            };
            rect[a] = [area[0] + start, area[0] + start + size];
        }
        frame.place(id, parent, rect);
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
    let Placement {
        grid: prepared,
        ids,
        counts,
        cells,
        explicit,
        shift,
    } = place(frame, parent, grid, inherited_counts);
    let grid = prepared.as_ref();
    let inner = frame.content_size(parent);
    frame.nodes[parent].grid_origin = Xy::new((explicit.x, shift.x), (explicit.y, shift.y));
    frame.nodes[parent].grid_baseline_items = ids.first().map(|&first| {
        let mut source = Xy::new_symm([first; 2]);
        for a in [Axis::X, Axis::Y] {
            for side in [0, 1] {
                let last = side == 1;
                let pick = ids
                    .iter()
                    .zip(&cells)
                    .min_by_key(|(id, cell)| {
                        let n = &frame.nodes[**id];
                        let align = n.rule.grid_item.align[a].unwrap_or(grid.align_items[a]);
                        let participant = align
                            == if last {
                                GridAlign::LastBaseline
                            } else {
                                GridAlign::FirstBaseline
                            }
                            && n.base.margin[a].iter().all(|m| m.as_px().is_some());
                        let at = if last {
                            counts[a] - cell[a].end
                        } else {
                            cell[a].start
                        };
                        let cross = if last {
                            counts[a.other()] - cell[a.other()].end
                        } else {
                            cell[a.other()].start
                        };
                        (
                            at,
                            !participant,
                            cross,
                            if last { usize::MAX - **id } else { **id },
                        )
                    })
                    .unwrap()
                    .0;
                source[a][side] = *pick;
            }
        }
        source
    });
    if !grid.line_names.x.is_empty() || !grid.line_names.y.is_empty() {
        let mut names: Xy<crate::tracks::LineNames> = Xy::default();
        for a in [Axis::X, Axis::Y] {
            crate::tracks::lines::append(&mut names[a], shift[a], &grid.line_names[a], counts[a]);
        }
        frame
            .grid_line_names
            .insert(frame.nodes[parent].id.key(), names);
    }
    let mut demand = Xy::new(
        contributions(frame, parent, grid, Axis::X, &ids, &cells, counts.x, None),
        contributions(frame, parent, grid, Axis::Y, &ids, &cells, counts.y, None),
    );
    // Percentage gutters need an allocated extent. A grid's own intrinsic
    // measure uses only the fixed part, including for spanning contributions.
    let mut intrinsic_grid = std::borrow::Cow::Borrowed(grid);
    let gap_fraction = frame.nodes[parent].rule.box_model.gap_fraction;
    if gap_fraction != Xy::new_symm(0.) {
        intrinsic_grid.to_mut().gap = frame.nodes[parent].rule.grid.as_ref().unwrap().gap;
    }
    let mut natural = inner;
    for a in [Axis::X, Axis::Y] {
        if inherited[a].is_none() {
            let (minimum, preferred) = intrinsic_grid.intrinsic_measurements(
                a,
                counts[a],
                &demand[a].items,
                &demand[a].min_content,
            );
            let node = &mut frame.nodes[parent];
            let min_outer = if a == node.context.axis(crate::LogicalAxis::Block) {
                preferred
            } else {
                minimum
            };
            node.grid_minimum[a] = Some(min_outer + node.base.padding[a].iter().sum::<f32>());
            natural[a] = match node.rule.grid_fit_limit[a] {
                Some(limit) => preferred.min(limit).max(minimum),
                None => preferred,
            };
        }
    }
    frame.set_intrinsic(parent, natural);
    let inner = frame.content_size(parent);
    for a in [Axis::X, Axis::Y] {
        if demand[a].relative_floor && inherited[a].is_none() {
            demand[a] = contributions(
                frame,
                parent,
                grid,
                a,
                &ids,
                &cells,
                counts[a],
                Some(inner[a]),
            );
        }
    }
    let resolve = |a: Axis, inherited: Option<ResolvedAxis>| {
        inherited.unwrap_or_else(|| {
            let mut edges = grid
                .resolve_measurements(
                    a,
                    Some(inner[a]),
                    counts[a],
                    &demand[a].items,
                    &demand[a].min_content,
                )
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
        let area = Xy::new(boundary(&edges.x, &cell.x), boundary(&edges.y, &cell.y));
        frame.nodes[id].grid_reference = Some(super::size(area));
        if matches!(
            frame.nodes[id].rule.placement,
            super::Placement::StickyInGridArea(_)
        ) {
            // Cache the same parent-local coordinates used by positioned grid descendants.
            // Scroll-only updates translate these edges without sizing the tracks again.
            let local = super::viewport::shifted(area, frame.content_offset(parent));
            frame
                .grid_positioned_areas
                .insert(frame.nodes[id].id.key(), (parent, local));
        }
        let mut rect = Xy::new(
            item_edges(frame, id, parent, grid, Axis::X, area.x, &cell.x),
            item_edges(frame, id, parent, grid, Axis::Y, area.y, &cell.y),
        );
        let n = &frame.nodes[id];
        for a in [Axis::X, Axis::Y] {
            let align = n.rule.grid_item.align[a].unwrap_or(grid.align_items[a]);
            let size = rect[a][1] - rect[a][0];
            if let Some((track, kind, offset)) = baseline_at(align, frame, id, a, size, &cell[a])
                && let Some(target) = baselines[a][track][kind]
            {
                let start = target - offset;
                rect[a] = [start, start + size];
            }
        }
        frame.place(id, parent, rect);
        frame.grid_cells.insert(id, cell);
    }
    place_overlays(frame, parent, grid, &edges, explicit, shift);
    frame
        .grid_tracks
        .insert(frame.nodes[parent].id.key(), edges);
    frame.grid_baselines.insert(parent, baselines);
}
