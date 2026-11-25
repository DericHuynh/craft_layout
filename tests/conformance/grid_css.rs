//! Lower the fixture generator's Grid longhands. Track numbering remains in
//! source order even when the writing context reverses a physical axis.
use super::{Result, box_css, unsupported};
use crate::css::Style;
use keru_layout::tracks::{
    GridAlign, GridItem, GridLine, LineNames, RepeatLineNames, Track, TrackAxis, TrackGrid,
    TrackMax, TrackMin,
};
use keru_layout::{Arrange, Axis, LogicalAxis, WritingContext, Xy};

#[derive(Debug, Clone, Copy)]
pub struct GridContext {
    inline: Axis,
    pub origins: Xy<bool>,

    items: Xy<Alignment>,
}

#[derive(Debug, Clone, Copy)]
enum Alignment {
    Value(GridAlign),
    SelfStart,
    SelfEnd,
}

fn alignment(raw: &str) -> Result<Alignment> {
    // Native positional alignment permits overflow, matching explicit unsafe alignment.
    let raw = raw.strip_prefix("unsafe ").unwrap_or(raw);
    let a = match raw {
        "normal" | "stretch" => GridAlign::Stretch,
        "start" | "flex-start" => GridAlign::Start,
        "end" | "flex-end" => GridAlign::End,
        "center" => GridAlign::Center,
        "safe center" => GridAlign::SafeCenter,
        "safe end" | "safe flex-end" => GridAlign::SafeEnd,
        "safe start" | "safe flex-start" => GridAlign::Start,
        "baseline" | "first baseline" => GridAlign::FirstBaseline,
        "last baseline" => GridAlign::LastBaseline,
        "self-start" => return Ok(Alignment::SelfStart),
        "self-end" => return Ok(Alignment::SelfEnd),
        other => return unsupported(format!("grid item alignment={other}")),
    };
    Ok(Alignment::Value(a))
}

impl Alignment {
    fn resolve(self, opposed: bool) -> GridAlign {
        match self {
            Self::Value(a) => a,
            Self::SelfStart if !opposed => GridAlign::Start,
            Self::SelfEnd if opposed => GridAlign::Start,
            _ => GridAlign::End,
        }
    }
}

fn arrangement(raw: &str) -> Result<(Arrange, bool)> {
    let raw = raw
        .strip_prefix("unsafe ")
        .or_else(|| raw.strip_prefix("safe "))
        .unwrap_or(raw);
    let a = match raw {
        "normal" | "stretch" => return Ok((Arrange::Start, true)),
        "start" | "flex-start" => Arrange::Start,
        "end" | "flex-end" => Arrange::End,
        "center" => Arrange::Center,
        "space-between" => Arrange::SpaceBetween,
        "space-around" => Arrange::SpaceAround,
        "space-evenly" => Arrange::SpaceEvenly,
        other => return unsupported(format!("grid track alignment={other}")),
    };
    Ok((a, false))
}

fn breadth(raw: &str, unit: &str) -> Option<f32> {
    let n = raw.strip_suffix(unit)?.trim().parse::<f32>().ok()?;
    (n.is_finite() && n >= 0.).then_some(n)
}

fn pixels(raw: &str) -> Option<f32> {
    if raw == "0" {
        Some(0.)
    } else {
        breadth(raw, "px")
    }
}

// CSS min() in the lower bound of a grid track, with one percentage and one pixel length.
fn capped_percentage(raw: &str) -> Option<TrackMin> {
    let (a, b) = raw
        .strip_prefix("min(")?
        .strip_suffix(')')?
        .split_once(',')?;
    let (percent, pixels) = if a.trim_end().ends_with('%') {
        (a, b)
    } else {
        (b, a)
    };
    Some(TrackMin::CappedPercent {
        fraction: breadth(percent.trim(), "%")? / 100.,
        pixels: breadth(pixels.trim(), "px")?,
    })
}

fn track(raw: &str, stretch: bool) -> Result<Track> {
    if let Some(px) = pixels(raw) {
        return Ok(Track::Pixels(px));
    }
    if let Some(p) = breadth(raw, "%") {
        return Ok(Track::Percent(p / 100.));
    }
    if let Some(f) = breadth(raw, "fr") {
        // CSS's standalone fraction has an automatic minimum.
        return Ok(Track::MinMax(TrackMin::Content, TrackMax::Fr(f)));
    }
    if raw == "min-content" {
        return Ok(Track::MinMax(TrackMin::MinContent, TrackMax::MinContent));
    }
    if raw == "max-content" {
        return Ok(Track::MinMax(TrackMin::MaxContent, TrackMax::Content));
    }
    if raw == "auto" {
        return Ok(if stretch { Track::Auto } else { Track::Content });
    }
    if let Some(args) = raw
        .strip_prefix("fit-content(")
        .and_then(|s| s.strip_suffix(')'))
        && let Some(limit) = breadth(args.trim(), "px")
    {
        return Ok(Track::FitContent(limit));
    }
    if let Some(limit) = raw
        .strip_prefix("fit-content(")
        .and_then(|s| s.strip_suffix(')'))
        .and_then(|s| breadth(s, "%"))
    {
        return Ok(Track::FitContentPercent(limit / 100.));
    }
    if let Some(args) = raw
        .strip_prefix("minmax(")
        .and_then(|s| s.strip_suffix(')'))
        && let Some((min, max)) = args.rsplit_once(',')
    {
        let (min, max) = (min.trim(), max.trim());
        let min = if let Some(v) = pixels(min) {
            TrackMin::Pixels(v)
        } else if let Some(v) = breadth(min, "%") {
            TrackMin::Percent(v / 100.)
        } else if let Some(limit) = capped_percentage(min) {
            limit
        } else if min == "min-content" {
            TrackMin::MinContent
        } else if min == "max-content" {
            TrackMin::MaxContent
        } else if min == "auto" {
            TrackMin::Content
        } else {
            return unsupported(format!("grid track minimum={min}"));
        };
        let max = if let Some(v) = pixels(max) {
            TrackMax::Pixels(v)
        } else if let Some(v) = breadth(max, "%") {
            TrackMax::Percent(v / 100.)
        } else if let Some(v) = breadth(max, "fr") {
            TrackMax::Fr(v)
        } else if max == "min-content" {
            TrackMax::MinContent
        } else if max == "auto" {
            if stretch {
                TrackMax::Auto
            } else {
                TrackMax::Content
            }
        } else if max == "max-content" {
            TrackMax::Content
        } else {
            return unsupported(format!("grid track maximum={max}"));
        };
        return Ok(Track::MinMax(min, max));
    }
    unsupported(format!("grid track breadth={raw}"))
}

// Split at whitespace outside functions. Commas and whitespace inside minmax
// or repeat belong to the value of a single track.
fn components(raw: &str) -> Result<Vec<&str>> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (i, ch) in raw.char_indices() {
        match ch {
            '(' | '[' => depth += 1,
            ')' | ']' => {
                depth = depth
                    .checked_sub(1)
                    .ok_or("unbalanced grid track function")?
            }
            c if c.is_whitespace() && depth == 0 => {
                if i > start {
                    parts.push(&raw[start..i]);
                }
                start = i + c.len_utf8();
            }
            _ => {}
        }
    }
    if depth != 0 {
        return unsupported("unbalanced grid track function");
    }
    if start < raw.len() {
        parts.push(&raw[start..]);
    }
    Ok(parts)
}

fn labels(raw: &str) -> Option<Vec<String>> {
    raw.strip_prefix('[')?
        .strip_suffix(']')
        .map(|names| names.split_whitespace().map(str::to_owned).collect())
}
fn template(
    raw: &str,
    stretch: bool,
    names: &mut LineNames,
    repeat_names: &mut RepeatLineNames,
) -> Result<TrackAxis> {
    if raw == "none" {
        return Ok(TrackAxis::default());
    }
    if raw == "subgrid" || raw.starts_with("subgrid ") {
        for (i, token) in components(raw)?.into_iter().skip(1).enumerate() {
            names.insert(i, labels(token).ok_or("invalid subgrid line names")?);
        }
        return Ok(TrackAxis::Subgrid);
    }
    let mut tracks = Vec::new();
    let mut repeated = None;
    for part in components(raw)? {
        let local_names = if repeated.is_some() {
            &mut repeat_names.suffix
        } else {
            &mut *names
        };
        if let Some(labels) = labels(part) {
            local_names.entry(tracks.len()).or_default().extend(labels);
        } else if let Some(args) = part
            .strip_prefix("repeat(")
            .and_then(|s| s.strip_suffix(')'))
        {
            let (n, args) = args.split_once(',').ok_or("invalid grid repeat")?;
            let mut group = Vec::new();
            let mut group_names = LineNames::new();
            for token in components(args.trim())? {
                if let Some(labels) = labels(token) {
                    group_names.entry(group.len()).or_default().extend(labels);
                } else {
                    group.push(track(token, stretch)?);
                }
            }
            if group.is_empty() {
                return unsupported("empty grid repeat");
            }
            if matches!(n.trim(), "auto-fill" | "auto-fit") {
                if repeated.is_some() {
                    return unsupported("multiple automatic repeats");
                }
                repeat_names.group = group_names;
                repeated = Some((std::mem::take(&mut tracks), group, n.trim() == "auto-fit"));
            } else {
                let count = n
                    .trim()
                    .parse::<usize>()
                    .map_err(|_| "invalid repeat count")?;
                for _ in 0..count {
                    let start = tracks.len();
                    if start == 65_536 {
                        break;
                    }
                    for (i, ns) in &group_names {
                        if start + i <= 65_536 {
                            local_names
                                .entry(start + i)
                                .or_default()
                                .extend(ns.iter().cloned());
                        }
                    }
                    tracks.extend(group.iter().take(65_536 - start));
                }
            }
        } else {
            let t = track(part, stretch)?;
            if tracks.len() < 65_536 {
                tracks.push(t);
            }
        }
    }
    if let Some((before, pattern, fit)) = repeated {
        return Ok(TrackAxis::AutoRepeat {
            before,
            pattern,
            after: tracks,
            fit,
        });
    }
    Ok(TrackAxis::Tracks(tracks))
}

// Template areas form a rectangle. They also establish explicit tracks when
// the template has fewer declarations than the area map.
fn areas(raw: &str, grid: &mut TrackGrid, inline: Axis) -> Result<()> {
    if raw == "none" {
        return Ok(());
    }
    let mut rest = raw.trim();
    let mut cols = None;
    let mut rows = 0;
    let mut counts = std::collections::BTreeMap::<String, usize>::new();
    while !rest.is_empty() {
        let quote = rest.chars().next().unwrap();
        if !matches!(quote, '\'' | '"') {
            return unsupported("unquoted grid-template-areas row");
        }
        let (row, tail) = rest[quote.len_utf8()..]
            .split_once(quote)
            .ok_or("unterminated grid-template-areas row")?;
        let row = row.split_whitespace().collect::<Vec<_>>();
        if row.is_empty() || cols.replace(row.len()).is_some_and(|n| n != row.len()) {
            return unsupported("uneven grid-template-areas rows");
        }
        for (col, name) in row.into_iter().enumerate() {
            if name.chars().all(|c| c == '.') {
                continue;
            }
            let cell = grid.areas.entry(name.to_owned()).or_insert_with(|| {
                let mut cell = Xy::default();
                cell[inline] = col..col + 1;
                cell[inline.other()] = rows..rows + 1;
                cell
            });
            cell[inline].start = cell[inline].start.min(col);
            cell[inline].end = cell[inline].end.max(col + 1);
            cell[inline.other()].end = rows + 1;
            *counts.entry(name.to_owned()).or_default() += 1;
        }
        rows += 1;
        rest = tail.trim_start();
    }
    for (name, area) in &grid.areas {
        if area.x.len().saturating_mul(area.y.len()) != counts[name] {
            return unsupported("nonrectangular grid-template-areas");
        }
    }
    for (a, count) in [(inline, cols.unwrap_or(0)), (inline.other(), rows)] {
        if let TrackAxis::Tracks(tracks) = &mut grid.tracks[a] {
            let start = tracks.len();
            let pattern = &grid.implicit_pattern[a];
            tracks.extend((start..count).map(|i| {
                if pattern.is_empty() {
                    grid.implicit[a]
                } else {
                    pattern[(i - start) % pattern.len()]
                }
            }));
        }
    }
    Ok(())
}
pub fn container(style: &Style, writing: WritingContext) -> Result<(TrackGrid, GridContext)> {
    let inline = writing.axis(LogicalAxis::Inline);
    let mut grid = TrackGrid::default();
    let mut context = GridContext {
        inline,
        origins: writing.origins(),

        items: Xy::new_symm(Alignment::Value(GridAlign::Stretch)),
    };
    let (flow, dense) = match style.keyword("grid-auto-flow", "row") {
        "row" => (inline, false),
        "column" => (inline.other(), false),
        "row dense" | "dense row" | "dense" => (inline, true),
        "column dense" | "dense column" => (inline.other(), true),
        raw => return unsupported(format!("grid-auto-flow={raw}")),
    };
    grid.flow = flow;
    grid.dense = dense;
    for (axis, explicit, implicit, gap, items, content) in [
        (
            inline,
            "grid-template-columns",
            "grid-auto-columns",
            "column-gap",
            "justify-items",
            "justify-content",
        ),
        (
            inline.other(),
            "grid-template-rows",
            "grid-auto-rows",
            "row-gap",
            "align-items",
            "align-content",
        ),
    ] {
        let raw = style.keyword(content, "normal");
        let (justify, stretch) = arrangement(raw)?;
        grid.safe_justify[axis] = raw.starts_with("safe ");
        grid.justify[axis] = justify;
        context.items[axis] = alignment(style.keyword(items, "normal"))?;
        grid.align_items[axis] = context.items[axis].resolve(false);
        grid.gap[axis] = box_css::gap(style, gap)?.0;
        grid.tracks[axis] = template(
            style.keyword(explicit, "none"),
            stretch,
            &mut grid.line_names[axis],
            &mut grid.repeat_line_names[axis],
        )?;
        let ts = components(style.keyword(implicit, "auto"))?
            .into_iter()
            .map(|s| track(s, stretch))
            .collect::<Result<Vec<_>>>()?;
        grid.implicit[axis] = *ts.first().ok_or("empty implicit grid track list")?;
        if ts.len() > 1 {
            grid.implicit_pattern[axis] = ts;
        }
    }
    areas(
        style.keyword("grid-template-areas", "none"),
        &mut grid,
        inline,
    )?;
    Ok((grid, context))
}

fn line(raw: &str) -> Result<GridLine> {
    if raw == "auto" {
        return Ok(GridLine::Auto);
    }
    let mut span = false;
    let mut n = None;
    let mut name = None;
    for token in raw.split_whitespace() {
        if token == "span" && !span {
            span = true;
        } else if let Ok(index) = token.parse::<i32>() {
            if index == 0 || n.replace(index).is_some() {
                return unsupported("invalid grid line index");
            }
        } else if name.replace(token.to_owned()).is_some() {
            return unsupported("invalid grid line name");
        }
    }
    if span {
        Ok(GridLine::Span {
            count: u16::try_from(n.unwrap_or(1)).map_err(|_| "invalid span count")?,
            name,
        })
    } else if let Some(name) = name {
        Ok(GridLine::Named {
            name,
            occurrence: n.unwrap_or(1),
            area_edge: n.is_none(),
        })
    } else {
        Ok(GridLine::Index(n.ok_or("empty grid line")?))
    }
}
fn declared_lines(style: &Style) -> Result<[[GridLine; 2]; 2]> {
    let mut row = [GridLine::Auto, GridLine::Auto];
    let mut col = row.clone();
    if let Some(area) = style.get("grid-area") {
        let spec = area
            .split('/')
            .map(|v| line(v.trim()))
            .collect::<Result<Vec<_>>>()?;
        let implicit = |l: &GridLine| match l {
            GridLine::Named {
                area_edge: true, ..
            } => l.clone(),
            _ => GridLine::Auto,
        };
        if spec.is_empty() || spec.len() > 4 {
            return unsupported("invalid grid-area");
        }
        row[0] = spec[0].clone();
        col[0] = spec.get(1).cloned().unwrap_or_else(|| implicit(&row[0]));
        row[1] = spec.get(2).cloned().unwrap_or_else(|| implicit(&row[0]));
        col[1] = spec.get(3).cloned().unwrap_or_else(|| implicit(&col[0]));
    }
    for (axis, pair, start, end) in [
        (
            "grid-column",
            &mut col,
            "grid-column-start",
            "grid-column-end",
        ),
        ("grid-row", &mut row, "grid-row-start", "grid-row-end"),
    ] {
        if let Some(raw) = style.get(axis) {
            let (a, b) = raw
                .split_once('/')
                .map_or((raw, None), |(a, b)| (a, Some(b)));
            pair[0] = line(a.trim())?;
            pair[1] = if let Some(b) = b {
                line(b.trim())?
            } else if matches!(
                pair[0],
                GridLine::Named {
                    area_edge: true,
                    ..
                }
            ) {
                pair[0].clone()
            } else {
                GridLine::Auto
            };
        }
        if let Some(raw) = style.get(start) {
            pair[0] = line(raw)?;
        }
        if let Some(raw) = style.get(end) {
            pair[1] = line(raw)?;
        }
    }
    Ok([col, row])
}
pub(super) fn placement(
    style: &Style,
    writing: WritingContext,
) -> Result<Xy<Option<[GridLine; 2]>>> {
    physical_lines(style, writing.axis(LogicalAxis::Inline))
}
fn physical_lines(style: &Style, inline: Axis) -> Result<Xy<Option<[GridLine; 2]>>> {
    let mut lines = Xy::default();
    for (a, pair) in [inline, inline.other()]
        .into_iter()
        .zip(declared_lines(style)?)
    {
        if pair != [GridLine::Auto, GridLine::Auto] {
            lines[a] = Some(pair);
        }
    }
    Ok(lines)
}
pub fn item(
    style: &Style,
    context: GridContext,
    writing: WritingContext,
) -> Result<(GridItem, Xy<Option<[GridLine; 2]>>)> {
    let mut item = GridItem::default();
    for (axis, key) in [
        (context.inline, "justify-self"),
        (context.inline.other(), "align-self"),
    ] {
        let a = match style.keyword(key, "auto") {
            "auto" => context.items[axis],
            raw => alignment(raw)?,
        };
        item.align[axis] = Some(a.resolve(writing.origins()[axis] != context.origins[axis]));
    }
    Ok((item, physical_lines(style, context.inline)?))
}
