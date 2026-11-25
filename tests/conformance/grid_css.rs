//! Lower the fixture generator's Grid longhands. Track numbering remains in
//! source order even when the writing context reverses a physical axis.
use super::{Result, px, unsupported};
use crate::css::Style;
use keru_layout::tracks::{GridAlign, GridItem, Track, TrackAxis, TrackGrid, TrackMax, TrackMin};
use keru_layout::{Arrange, Axis, LogicalAxis, WritingContext, Xy};

#[derive(Debug, Clone, Copy)]
pub struct GridContext {
    inline: Axis,
    pub origins: Xy<bool>,
    explicit: Xy<Option<usize>>,
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
    let raw = raw.strip_prefix("unsafe ").unwrap_or(raw);
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

fn track(raw: &str, stretch: bool) -> Result<Track> {
    if raw == "0" {
        return Ok(Track::Pixels(0.));
    }
    if let Some(px) = breadth(raw, "px") {
        return Ok(Track::Pixels(px));
    }
    if let Some(p) = breadth(raw, "%") {
        return Ok(Track::Percent(p / 100.));
    }
    if let Some(f) = breadth(raw, "fr") {
        // CSS's standalone fraction has an automatic minimum.
        return Ok(Track::MinMax(TrackMin::Content, TrackMax::Fr(f)));
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
    if let Some(args) = raw
        .strip_prefix("minmax(")
        .and_then(|s| s.strip_suffix(')'))
        && let Some((min, max)) = args.split_once(',')
    {
        let (min, max) = (min.trim(), max.trim());
        let min = if let Some(v) = breadth(min, "px") {
            TrackMin::Pixels(v)
        } else if let Some(v) = breadth(min, "%") {
            TrackMin::Percent(v / 100.)
        } else if min == "auto" {
            TrackMin::Content
        } else {
            return unsupported(format!("grid track minimum={min}"));
        };
        let max = if let Some(v) = breadth(max, "px") {
            TrackMax::Pixels(v)
        } else if let Some(v) = breadth(max, "%") {
            TrackMax::Percent(v / 100.)
        } else if let Some(v) = breadth(max, "fr") {
            TrackMax::Fr(v)
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
    if raw.contains(['[', ']']) {
        return unsupported("named grid lines");
    }
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0usize;
    for (i, ch) in raw.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
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

fn template(raw: &str, stretch: bool) -> Result<TrackAxis> {
    if raw == "none" {
        return Ok(TrackAxis::default());
    }
    let parts = components(raw)?;
    let mut tracks = Vec::new();
    for part in &parts {
        if let Some(args) = part
            .strip_prefix("repeat(")
            .and_then(|s| s.strip_suffix(')'))
        {
            let (count, pattern) = args.split_once(',').ok_or("invalid grid repetition")?;
            let pattern = components(pattern.trim())?
                .into_iter()
                .map(|s| track(s, stretch))
                .collect::<Result<Vec<_>>>()?;
            if pattern.is_empty() {
                return unsupported("empty grid repetition");
            }
            if matches!(count.trim(), "auto-fit" | "auto-fill") {
                if parts.len() != 1 || pattern.len() != 1 {
                    return unsupported("mixed or multi-track automatic repetition");
                }
                let t = pattern[0];
                return Ok(if count.trim() == "auto-fill" {
                    TrackAxis::AutoFill {
                        minimum: 0.,
                        track: t,
                    }
                } else {
                    TrackAxis::AutoFit {
                        minimum: 0.,
                        track: t,
                    }
                });
            }
            let count = count
                .trim()
                .parse::<usize>()
                .map_err(|_| "invalid grid repeat count")?;
            if count == 0 {
                return unsupported("zero grid repeat count");
            }
            // The native axis addresses 65,536 tracks. A pattern longer
            // than that only needs its addressable prefix materialized.
            let remaining = (usize::from(u16::MAX) + 1).saturating_sub(tracks.len());
            let length = count.saturating_mul(pattern.len()).min(remaining);
            tracks.extend(pattern.iter().copied().cycle().take(length));
        } else {
            let t = track(part, stretch)?;
            if tracks.len() <= usize::from(u16::MAX) {
                tracks.push(t);
            }
        }
    }
    Ok(TrackAxis::Tracks(tracks))
}

pub fn container(style: &Style, writing: WritingContext) -> Result<(TrackGrid, GridContext)> {
    let inline = writing.axis(LogicalAxis::Inline);
    let mut grid = TrackGrid::default();
    let mut context = GridContext {
        inline,
        origins: writing.origins(),
        explicit: Xy::new_symm(None),
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
        let (justify, stretch) = arrangement(style.keyword(content, "normal"))?;
        grid.justify[axis] = justify;
        context.items[axis] = alignment(style.keyword(items, "normal"))?;
        grid.align_items[axis] = context.items[axis].resolve(false);
        grid.gap[axis] = px(style, gap)?;
        grid.tracks[axis] = template(style.keyword(explicit, "none"), stretch)?;
        if let TrackAxis::Tracks(ts) = &grid.tracks[axis] {
            context.explicit[axis] = Some(ts.len());
        }
        grid.implicit[axis] = track(style.keyword(implicit, "auto"), stretch)?;
    }
    Ok((grid, context))
}

#[derive(Clone, Copy)]
enum Line {
    Auto,
    Number(i32),
    Span(u16),
}

fn line(raw: &str) -> Result<Line> {
    if raw == "auto" {
        return Ok(Line::Auto);
    }
    if let Some(raw_span) = raw.strip_prefix("span ") {
        let value = raw_span
            .trim()
            .parse::<u64>()
            .map_err(|_| format!("unsupported grid span={raw_span}"))?;
        if value == 0 {
            return unsupported("zero grid span");
        }
        return u16::try_from(value)
            .map(Line::Span)
            .map_err(|_| "grid span exceeds native representation".into());
    }
    if let Ok(n) = raw.parse::<i32>() {
        if n != 0 {
            return Ok(Line::Number(n));
        }
        return unsupported("zero grid line number");
    }
    unsupported(format!("named or unsupported grid line={raw}"))
}

fn placement(start: Line, end: Line, count: Option<usize>) -> Result<(Option<u16>, u16)> {
    let number = |n: i32| -> Result<i64> {
        let n = i64::from(n);
        Ok(if n > 0 {
            n - 1
        } else {
            count.ok_or("negative grid line against auto-repeat")? as i64 + 1 + n
        })
    };
    let (start, span) = match (start, end) {
        (Line::Number(a), Line::Number(b)) => {
            let (a, b) = (number(a)?, number(b)?);
            (Some(a.min(b)), a.abs_diff(b).max(1))
        }
        (Line::Number(a), Line::Span(n)) => (Some(number(a)?), u64::from(n)),
        (Line::Span(n), Line::Number(b)) => (Some(number(b)? - i64::from(n)), u64::from(n)),
        (Line::Number(a), _) => (Some(number(a)?), 1),
        (_, Line::Number(b)) => (Some(number(b)? - 1), 1),
        (Line::Span(n), _) | (_, Line::Span(n)) => (None, u64::from(n)),
        _ => (None, 1),
    };
    if start.is_some_and(|n| n < 0) {
        return unsupported("grid tracks preceding the explicit grid");
    }
    let span = u16::try_from(span).map_err(|_| "grid span exceeds native representation")?;
    let start = start.map(|n| u16::try_from(n).unwrap_or(u16::MAX));
    Ok((start, span))
}

pub fn item(style: &Style, context: GridContext, writing: WritingContext) -> Result<GridItem> {
    let mut item = GridItem::default();
    for (axis, start, end, align) in [
        (
            context.inline,
            "grid-column-start",
            "grid-column-end",
            "justify-self",
        ),
        (
            context.inline.other(),
            "grid-row-start",
            "grid-row-end",
            "align-self",
        ),
    ] {
        (item.start[axis], item.span[axis]) = placement(
            line(style.keyword(start, "auto"))?,
            line(style.keyword(end, "auto"))?,
            context.explicit[axis],
        )?;
        let a = match style.keyword(align, "auto") {
            "auto" => context.items[axis],
            raw => alignment(raw)?,
        };
        item.align[axis] = Some(a.resolve(writing.origins()[axis] != context.origins[axis]));
    }
    Ok(item)
}
