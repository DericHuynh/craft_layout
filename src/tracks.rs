//! Heterogeneous grid tracks, explicit and automatic cell placement, and shared
//! tracks for nested grids. Track starts are zero-based; spans count tracks.
use crate::placement_geometry::{RustFloat, line_start_and_gap};
use crate::solve::grid_sparse::{Occupied, find_cell};
use crate::{Arrange, Axis, Xy};
use std::ops::Range;
pub(crate) mod lines;
pub use lines::{GridLine, LineNames, RepeatLineNames};

// Bounded independently on each axis; a tall span never allocates a dense
// two-dimensional matrix. Items beyond an axis boundary share the last area.
const MAX_TRACKS: usize = 65_536;

/// Lower limit of a track.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TrackMin {
    /// Fixed logical pixels.
    Pixels(f32),
    /// Fraction of the container's content size.
    Percent(f32),
    /// Protect the full preferred contribution, even under a tight budget.
    MaxContent,
    /// Protect the minimum unbreakable content contribution.
    MinContent,
    /// Minimum contribution of items occupying this track.
    Content,
}
/// Upper limit of a track.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum TrackMax {
    /// Grow into available space up to this size.
    Pixels(f32),
    /// Grow into available space up to this fraction of the container.
    Percent(f32),
    /// Stop at the minimum unbreakable contribution of the occupants.
    MinContent,
    /// Grow to the preferred contributions of its items.
    Content,
    /// Grow to preferred contributions, then share any unclaimed space equally
    /// with other Auto maxima on this axis.
    Auto,
    /// A weighted share of the remaining space.
    Fr(f32),
}
/// A single track. A bare fraction has a zero minimum, allowing the author
/// to choose explicitly which content may force a grid to overflow.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub enum Track {
    /// Fixed logical pixels.
    Pixels(f32),
    /// Fraction of the full inner size, before gaps.
    Percent(f32),
    /// Size to the preferred contributions of occupants, within available space.
    #[default]
    Content,
    /// Size to content, then share any space left over after fractional tracks.
    /// Use Content when this track should stop growing at its preferred size.
    Auto,
    /// Weighted share of the remaining space.
    Fr(f32),
    /// Content sizing capped at this many pixels, subject to the minimum contribution.
    FitContent(f32),
    /// Content sizing capped at a fraction of the definite content extent.
    FitContentPercent(f32),
    /// Independent minimum and maximum sizing policies.
    MinMax(TrackMin, TrackMax),
}
impl Track {
    pub(crate) fn bounds(self) -> (TrackMin, TrackMax) {
        match self {
            Track::Pixels(p) => (TrackMin::Pixels(p), TrackMax::Pixels(p)),
            Track::Percent(f) => (TrackMin::Percent(f), TrackMax::Percent(f)),
            Track::Content => (TrackMin::Content, TrackMax::Content),
            Track::Auto => (TrackMin::Content, TrackMax::Auto),
            Track::Fr(f) => (TrackMin::Pixels(0.), TrackMax::Fr(f)),
            Track::MinMax(min, max) => (min, max),
            Track::FitContent(cap) => (TrackMin::Content, TrackMax::Pixels(cap)),
            Track::FitContentPercent(cap) => (TrackMin::Content, TrackMax::Percent(cap)),
        }
    }
}
/// Template for one axis. Auto-repeat reserves up to 65,536 tracks, uses a
/// positive repetition pitch (at least one pixel), and accounts for gaps.
#[derive(Debug, Clone, PartialEq)]
pub enum TrackAxis {
    /// Explicit tracks followed by any needed implicit tracks.
    Tracks(Vec<Track>),
    /// Repeat as often as fits and retain empty tracks.
    AutoFill {
        /// Minimum space needed for one repetition, excluding gaps.
        minimum: f32,
        /// Track declaration used for each repetition.
        track: Track,
    },
    /// Repeat as often as fits, collapsing empty tracks and adjacent gaps.
    AutoFit {
        /// Minimum space needed for one repetition, excluding gaps.
        minimum: f32,
        /// Track declaration used for each repetition.
        track: Track,
    },
    /// Prefix an explicit template by implicit tracks before its first line.
    Prefixed {
        /// Implicit tracks in final logical order.
        implicit: Vec<Track>,
        /// Original template retaining its line numbering.
        explicit: Box<TrackAxis>,
    },
    /// Repeat a sequence between fixed leading and trailing declarations.
    AutoRepeat {
        /// Fixed leading tracks.
        before: Vec<Track>,
        /// The repeated sequence.
        pattern: Vec<Track>,
        /// Fixed trailing tracks.
        after: Vec<Track>,
        /// Collapse unoccupied tracks inside the repeated sequence.
        fit: bool,
    },
    /// Use the parent track boundaries spanned by this grid item.
    Subgrid,
}
impl Default for TrackAxis {
    fn default() -> Self {
        Self::Tracks(Vec::new())
    }
}
impl TrackAxis {
    /// Create an explicit template with a fixed repetition count.
    pub fn repeat(count: u16, track: Track) -> Self {
        Self::Tracks(vec![track; usize::from(count)])
    }
    pub(crate) fn count(&self, extent: f32, gap: f32, inherited: Option<usize>) -> usize {
        match self {
            Self::Tracks(v) => v.len().min(MAX_TRACKS),
            Self::Prefixed { implicit, explicit } => {
                (implicit.len() + explicit.count(extent, gap, inherited)).min(MAX_TRACKS)
            }
            Self::Subgrid => inherited.unwrap_or(1).clamp(1, MAX_TRACKS),
            Self::AutoRepeat {
                before,
                pattern,
                after,
                ..
            } => {
                let breadth = |t: &Track| {
                    let state = sizing(*t, Some(extent));
                    if state.cap.is_finite() {
                        state.cap
                    } else {
                        state.base
                    }
                };
                let gap = f64::from(gap);
                let fixed: f64 = before.iter().chain(after).map(|t| breadth(t) + gap).sum();
                let pitch: f64 = pattern.iter().map(|t| breadth(t).max(1.) + gap).sum();
                let repeats = if pitch > 0. {
                    ((f64::from(extent) + gap - fixed) / pitch).floor().max(1.) as usize
                } else {
                    0
                };
                (before.len() + after.len())
                    .saturating_add(repeats.saturating_mul(pattern.len()))
                    .min(MAX_TRACKS)
            }
            Self::AutoFit { minimum, track } | Self::AutoFill { minimum, track } => {
                let state = sizing(*track, Some(extent));
                let reference = if state.cap.is_finite() {
                    state.cap
                } else {
                    state.base
                };
                let pitch = reference.max(f64::from(minimum.max(1.)));
                ((f64::from(extent.max(0.) + gap) / (pitch + f64::from(gap))).floor() as usize)
                    .clamp(1, MAX_TRACKS)
            }
        }
    }
    pub(crate) fn collapsed_range(&self, explicit: usize) -> Range<usize> {
        match self {
            Self::AutoFit { .. } => 0..explicit,
            Self::AutoRepeat {
                before,
                after,
                fit: true,
                ..
            } => {
                before.len().min(explicit)
                    ..explicit
                        .saturating_sub(after.len())
                        .max(before.len().min(explicit))
            }
            Self::Prefixed {
                implicit,
                explicit: inner,
            } => {
                let r = inner.collapsed_range(explicit.saturating_sub(implicit.len()));
                implicit.len() + r.start..implicit.len() + r.end
            }
            _ => 0..0,
        }
    }
    pub(crate) fn at(&self, index: usize, explicit: usize, implicit: Track) -> Track {
        match self {
            Self::Tracks(v) => v.get(index).copied().unwrap_or(implicit),
            Self::Prefixed {
                implicit: before,
                explicit: inner,
            } => before.get(index).copied().unwrap_or_else(|| {
                inner.at(
                    index.saturating_sub(before.len()),
                    explicit.saturating_sub(before.len()),
                    implicit,
                )
            }),
            Self::AutoRepeat {
                before,
                pattern,
                after,
                ..
            } if index < explicit => {
                if index < before.len() {
                    before[index]
                } else if index >= explicit.saturating_sub(after.len()) {
                    after[index - explicit.saturating_sub(after.len())]
                } else if pattern.is_empty() {
                    implicit
                } else {
                    pattern[(index - before.len()) % pattern.len()]
                }
            }
            Self::AutoFit { track, .. } | Self::AutoFill { track, .. } if index < explicit => {
                *track
            }
            _ => implicit,
        }
    }
}
/// Alignment inside a grid area.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum GridAlign {
    /// Align to the logical start.
    Start,
    /// Align to the logical end.
    End,
    /// Center within the area.
    Center,
    /// Center if the item fits, otherwise preserve its logical start.
    SafeCenter,
    /// Align to the end if the item fits, otherwise preserve its logical start.
    SafeEnd,
    /// Align first baselines against the first spanned track's start edge.
    FirstBaseline,
    /// Align last baselines against the last spanned track's end edge.
    LastBaseline,
    /// Stretch an Auto or Fill dimension within its bounds.
    #[default]
    Stretch,
}
/// Grid placement and alignment of a child.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct GridItem {
    /// Zero-based starting column and row. None requests auto-placement.
    pub start: Xy<Option<u16>>,
    /// Column and row spans. On an owned tree, a span of one defers to the
    /// corresponding native `LayoutParams::grid_span`. Set that declaration
    /// back to one when migrating to a smaller managed span. Zero also occupies one track.
    pub span: Xy<u16>,
    /// Alignment overrides on either axis.
    pub align: Xy<Option<GridAlign>>,
}
impl Default for GridItem {
    fn default() -> Self {
        Self {
            start: Xy::new_symm(None),
            span: Xy::new_symm(1),
            align: Xy::new_symm(None),
        }
    }
}
/// Two-dimensional track layout for a managed container.
#[derive(Debug, Clone, PartialEq)]
pub struct TrackGrid {
    /// Explicit, repeated or shared tracks on each physical axis.
    pub tracks: Xy<TrackAxis>,
    /// Tracks introduced by placement outside an explicit template.
    pub implicit: Xy<Track>,
    /// A cyclic pattern for implicit tracks, extending in both directions.
    pub implicit_pattern: Xy<Vec<Track>>,
    /// Named rectangular areas. Each range uses zero-based explicit tracks.
    /// A name supplies its start and end lines for placement on both axes.
    pub areas: std::collections::BTreeMap<String, GridCell>,
    /// Named lines keyed by zero-based explicit grid line.
    pub line_names: Xy<LineNames>,
    /// Line names that expand with an automatic track repetition.
    pub repeat_line_names: Xy<RepeatLineNames>,
    /// Keep the logical start visible when positional alignment overflows.
    pub safe_justify: Xy<bool>,
    /// Gaps between noncollapsed tracks on each axis.
    pub gap: Xy<f32>,
    /// Advance along X for row-major placement, Y for column-major placement.
    pub flow: Axis,
    /// Search earlier holes for each automatically placed item.
    pub dense: bool,
    /// Distribution of leftover space around the tracks.
    pub justify: Xy<Arrange>,
    /// Default alignment inside a grid area.
    pub align_items: Xy<GridAlign>,
}
impl Default for TrackGrid {
    fn default() -> Self {
        Self {
            tracks: Xy::default(),
            implicit: Xy::new_symm(Track::Content),
            implicit_pattern: Xy::default(),
            areas: Default::default(),
            line_names: Xy::default(),
            repeat_line_names: Xy::default(),
            safe_justify: Xy::new_symm(false),
            gap: Xy::new_symm(0.),
            flow: Axis::X,
            dense: false,
            justify: Xy::new_symm(Arrange::Start),
            align_items: Xy::new_symm(GridAlign::Stretch),
        }
    }
}
/// Occupied track ranges on X and Y.
pub type GridCell = Xy<Range<usize>>;

fn cell(axis: Axis, x: usize, y: usize, w: usize, h: usize) -> GridCell {
    if axis == Axis::X {
        Xy::new(x..x + w, y..y + h)
    } else {
        Xy::new(y..y + h, x..x + w)
    }
}
fn bounded_start(start: usize, span: usize, limit: usize) -> usize {
    start.min(limit.saturating_sub(span))
}
impl TrackGrid {
    pub(crate) fn explicit_count(&self, a: Axis, extent: f32, inherited: Option<usize>) -> usize {
        let template = &self.tracks[a];
        let tracks = template.count(extent, self.gap[a].max(0.), inherited);
        if matches!(template, TrackAxis::Subgrid) || self.areas.is_empty() {
            return tracks;
        }
        let preceding = match template {
            TrackAxis::Prefixed { implicit, .. } => implicit.len(),
            _ => 0,
        };
        self.areas
            .values()
            .map(|area| area[a].end.saturating_add(preceding))
            .fold(tracks, usize::max)
            .min(MAX_TRACKS)
    }
    #[cfg(feature = "incremental")]
    pub(crate) fn placement_names(&self, axis: Axis) -> std::borrow::Cow<'_, LineNames> {
        let mut names = std::borrow::Cow::Borrowed(&self.line_names[axis]);
        for (name, area) in &self.areas {
            for (i, side) in [(area[axis].start, "start"), (area[axis].end, "end")] {
                names
                    .to_mut()
                    .entry(i)
                    .or_default()
                    .push(format!("{name}-{side}"));
            }
        }
        names
    }
    pub(crate) fn track_at(&self, a: Axis, index: usize, explicit: usize) -> Track {
        let pattern = &self.implicit_pattern[a];
        let implicit = if pattern.is_empty() || index < explicit {
            self.implicit[a]
        } else {
            pattern[(index - explicit) % pattern.len()]
        };
        self.tracks[a].at(index, explicit, implicit)
    }

    /// Assign cells in tree order. A subgridded axis can occupy only its inherited
    /// span. Fully explicit overlapping assignments are respected. Each axis
    /// supports 65,536 tracks. Items past its boundary occupy the last possible area.
    pub fn place_cells(
        &self,
        inner: Xy<f32>,
        items: &[GridItem],
        inherited: Xy<Option<usize>>,
    ) -> (Xy<usize>, Vec<GridCell>) {
        let mut counts = Xy::new_symm(0);
        for a in [Axis::X, Axis::Y] {
            counts[a] = self.explicit_count(a, inner[a], inherited[a]);
        }
        let main = self.flow;
        let cross = main.other();
        let shared = |a: Axis| {
            if self.tracks[a] == TrackAxis::Subgrid {
                counts[a].max(1)
            } else {
                MAX_TRACKS
            }
        };
        let limits = Xy::new(shared(Axis::X), shared(Axis::Y));
        let spans = |item: &GridItem, a: Axis| usize::from(item.span[a].max(1)).min(limits[a]);
        for item in items {
            for a in [main, cross] {
                let span = spans(item, a);
                let start = bounded_start(usize::from(item.start[a].unwrap_or(0)), span, limits[a]);
                counts[a] = counts[a].max(start + span);
            }
        }
        let mut result = vec![GridCell::default(); items.len()];
        if items
            .iter()
            .all(|it| it.start == Xy::new_symm(None) && it.span.x <= 1 && it.span.y <= 1)
        {
            let columns = counts[main].max(1);
            for (i, output) in result.iter_mut().enumerate() {
                let row = bounded_start(i / columns, 1, limits[cross]);
                *output = cell(main, i % columns, row, 1, 1);
                counts[cross] = counts[cross].max(row + 1);
            }
            return (counts, result);
        }
        let mut occupied = Vec::<Occupied>::new();
        let mut row_cursors = std::collections::HashMap::new();
        let mut cursor = (0, 0);
        // Reserve both-axis placements first, then items locked to a line, then
        // the remaining stream. A later explicit control may reserve the first cell.
        for phase in 0..3 {
            for (i, item) in items.iter().enumerate() {
                let w = spans(item, main);
                let h = spans(item, cross);
                let fixed_x =
                    item.start[main].map(|s| bounded_start(usize::from(s), w, limits[main]));
                let fixed_y =
                    item.start[cross].map(|s| bounded_start(usize::from(s), h, limits[cross]));
                let group = if fixed_y.is_some() {
                    if fixed_x.is_some() { 0 } else { 1 }
                } else {
                    2
                };
                if group != phase {
                    continue;
                }
                let (mut x, mut y) = if self.dense || phase < 2 {
                    (0, 0)
                } else {
                    cursor
                };
                if let Some(locked) = fixed_y {
                    y = locked;
                    if phase == 1 && !self.dense {
                        x = row_cursors.get(&y).copied().unwrap_or(0);
                    }
                }
                if let Some(locked) = fixed_x {
                    if phase == 2 && x > locked {
                        y += 1;
                    }
                    x = locked;
                }
                if fixed_x.is_none() && fixed_y.is_none() {
                    let (row, column) = find_cell(
                        &occupied,
                        counts[main],
                        (y as u128, x),
                        counts[cross] as u128,
                        h as u128,
                        w,
                    );
                    x = column;
                    y = bounded_start(row as usize, h, limits[cross]);
                } else if phase != 0 {
                    // Search along the unlocked axis, jumping directly beyond a
                    // blocking rectangle. A fixed row may grow implicit columns.
                    y = bounded_start(y, h, limits[cross]);
                    loop {
                        if x + w > limits[main] {
                            x = limits[main] - w;
                            break;
                        }
                        let blocked = occupied.iter().filter(|c| {
                            x < c.cols.1
                                && c.cols.0 < x + w
                                && (y as u128) < c.rows.1
                                && c.rows.0 < ((y + h) as u128)
                        });
                        let Some(next) = blocked
                            .map(|c| {
                                if fixed_x.is_some() {
                                    c.rows.1 as usize
                                } else {
                                    c.cols.1
                                }
                            })
                            .max()
                        else {
                            break;
                        };
                        if fixed_x.is_some() {
                            if next + h > limits[cross] {
                                y = limits[cross] - h;
                                break;
                            }
                            y = next;
                        } else {
                            x = next;
                        }
                    }
                }
                counts[main] = counts[main].max(x + w);
                counts[cross] = counts[cross].max(y + h);
                result[i] = cell(main, x, y, w, h);
                occupied.push(Occupied {
                    rows: (y as u128, (y + h) as u128),
                    cols: (x, x + w),
                });
                if phase == 1 && !self.dense {
                    row_cursors.insert(y, x + w);
                }
                if phase == 2 {
                    cursor = (x + w, y);
                }
            }
        }
        (counts, result)
    }
}

/// Measured contribution of a grid item (or descendant sharing tracks), including margins.
#[derive(Debug, Clone, PartialEq)]
pub struct TrackContribution {
    /// Track indices spanned by the item.
    pub tracks: Range<usize>,
    /// Minimum outer contribution. If a span crosses flexible tracks, the
    /// flexible tracks with content floors share the remaining demand by weight.
    /// Positive weights preserve their ratio even when their sum is below one.
    /// All-zero eligible weights share a required floor equally.
    pub minimum: f32,
    /// Preferred outer contribution.
    pub preferred: f32,
}
#[derive(Clone, Copy)]
struct Sizing {
    base: f64,
    cap: f64,
    min_content: bool,
    measured_floor: bool,
    max_floor: bool,
    min_ceiling: bool,
    ideal_content: bool,
    fr: f64,
    flexible: bool,
    fit_content: bool,
    grow_to_cap: bool,
    stretch: bool,
}
fn sizing(track: Track, extent: Option<f32>) -> Sizing {
    let percent = |f: f32| extent.map(|e| f64::from(e) * f64::from(f.max(0.)));
    let (min, max) = track.bounds();
    let lower = match min {
        TrackMin::Pixels(p) => Some(f64::from(p.max(0.))),
        TrackMin::Percent(f) => percent(f),
        TrackMin::Content | TrackMin::MinContent | TrackMin::MaxContent => None,
    };
    let upper = match max {
        TrackMax::Pixels(p) => Some(f64::from(p.max(0.))),
        TrackMax::Percent(f) => percent(f),
        _ => None,
    };
    let base = lower.unwrap_or(0.);
    let fr = if let TrackMax::Fr(v) = max {
        if v.is_finite() {
            f64::from(v.max(0.))
        } else {
            0.
        }
    } else {
        0.
    };
    Sizing {
        base,
        cap: upper.unwrap_or(f64::INFINITY).max(base),
        min_content: lower.is_none(),
        measured_floor: matches!(min, TrackMin::MinContent | TrackMin::MaxContent),
        max_floor: min == TrackMin::MaxContent,
        min_ceiling: max == TrackMax::MinContent,
        ideal_content: matches!(
            max,
            TrackMax::Content | TrackMax::Auto | TrackMax::MinContent
        ) || matches!(track, Track::FitContent(_) | Track::FitContentPercent(_))
            || matches!(max, TrackMax::Percent(_)) && extent.is_none(),
        fr,
        flexible: matches!(max, TrackMax::Fr(_)),
        fit_content: matches!(track, Track::FitContent(_) | Track::FitContentPercent(_)),
        stretch: matches!(max, TrackMax::Auto),
        grow_to_cap: matches!(
            track,
            Track::MinMax(_, TrackMax::Pixels(_) | TrackMax::Percent(_))
        ) && upper.is_some(),
    }
}
// Distribute a positive deficit equally, freezing tracks at their individual caps.
fn grow_toward(values: &mut [f64], caps: &[f64], mut deficit: f64) {
    while deficit > 0. {
        let active = values.iter().zip(caps).filter(|(v, c)| **v < **c).count();
        if active == 0 {
            break;
        }
        let share = deficit / active as f64;
        let mut applied = 0.;
        let mut capped = false;
        for (v, cap) in values.iter_mut().zip(caps) {
            let growth = (cap - *v).max(0.).min(share);
            if *v < *cap && growth < share {
                capped = true;
            }
            *v += growth;
            applied += growth;
        }
        if !capped || applied <= 0. {
            break;
        }
        deficit -= applied;
    }
}
#[derive(Clone, Copy)]
struct Demand<'a> {
    item: &'a TrackContribution,
    min_content: f32,
}
impl std::ops::Deref for Demand<'_> {
    type Target = TrackContribution;
    fn deref(&self) -> &Self::Target {
        self.item
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum ContributionPhase {
    Minimum,
    MeasuredFloor,
    PreferredFloor,
    MeasuredLimit,
    PreferredLimit,
}
impl ContributionPhase {
    fn target(self, item: &Demand<'_>) -> f64 {
        f64::from(match self {
            Self::Minimum => item.minimum,
            Self::MeasuredFloor | Self::MeasuredLimit => item.min_content,
            Self::PreferredFloor | Self::PreferredLimit => item.preferred,
        })
    }
    fn eligible(self, s: &Sizing) -> bool {
        match self {
            Self::Minimum => s.min_content,
            Self::MeasuredFloor => s.measured_floor,
            Self::PreferredFloor => s.max_floor,
            Self::MeasuredLimit => s.ideal_content,
            Self::PreferredLimit => s.ideal_content && !s.min_ceiling,
        }
    }
}
// Compute demands at each span length from a common snapshot, so equally
// spanning items produce the same track sizes in either source order.
fn contributions(
    sizes: &mut [f64],
    states: &[Sizing],
    items: &[Demand<'_>],
    gap: f64,
    phase: ContributionPhase,
) {
    // Single-span contributions constrain just one track. Folding their maxima
    // directly is equivalent to planning each increase from a shared snapshot.
    let minimum = matches!(
        phase,
        ContributionPhase::Minimum
            | ContributionPhase::MeasuredFloor
            | ContributionPhase::PreferredFloor
    );
    let eligible_cap = |s: &Sizing, value: f64| {
        if !phase.eligible(s) {
            value
        } else if minimum {
            f64::INFINITY
        } else {
            s.cap.max(value)
        }
    };
    let single = items.partition_point(|item| item.tracks.len() == 1);
    for item in &items[..single] {
        let i = item.tracks.start;
        let demand = phase.target(item);
        // With mixed spans, all flexible floors are planned below together.
        if !(minimum && single < items.len() && states[i].flexible) {
            sizes[i] = sizes[i].max(demand.min(eligible_cap(&states[i], sizes[i])));
        }
    }
    if single == items.len() {
        return;
    }
    let mut planned = vec![0.; sizes.len()];
    let mut local = Vec::new();
    let mut caps = Vec::new();
    // An intrinsic track occupied by a single item has a known growth
    // limit. Give tracks with unclaimed capacity the first opportunity to
    // absorb a spanning floor. A fit-content track also uses that limit
    // when sharing preferred space. Hard minima can still exceed it.
    let mut single_preferred = vec![0.0f64; sizes.len()];
    for item in &items[..single] {
        let i = item.tracks.start;
        single_preferred[i] = single_preferred[i].max(f64::from(item.preferred));
    }
    for group in items[single..].chunk_by(|a, b| a.tracks.len() == b.tracks.len()) {
        planned.copy_from_slice(sizes);
        for item in group {
            let r = item.tracks.clone();
            if states[r.clone()].iter().any(|s| s.flexible) {
                continue;
            }
            let demand = phase.target(item);
            let missing =
                demand - sizes[r.clone()].iter().sum::<f64>() - gap * (r.len() - 1) as f64;
            if missing <= 0. {
                continue;
            }
            local.clear();
            local.extend_from_slice(&sizes[r.clone()]);
            caps.clear();
            caps.extend(
                states[r.clone()]
                    .iter()
                    .zip(&local)
                    .map(|(s, &v)| eligible_cap(s, v)),
            );
            for (cap, i) in caps.iter_mut().zip(r.clone()) {
                if phase == ContributionPhase::PreferredFloor {
                    *cap = cap.min(states[i].cap.max(sizes[i]));
                } else if (minimum || states[i].fit_content)
                    && states[i].ideal_content
                    && single_preferred[i] > 0.
                {
                    *cap = cap.min(single_preferred[i].max(sizes[i]));
                }
            }
            grow_toward(&mut local, &caps, missing);
            let remaining = demand - local.iter().sum::<f64>() - gap * (r.len() - 1) as f64;
            if remaining > 0. {
                let prefer_intrinsic = phase == ContributionPhase::PreferredFloor
                    && states[r.clone()]
                        .iter()
                        .any(|s| s.max_floor && s.ideal_content);
                for (cap, i) in caps.iter_mut().zip(r.clone()) {
                    *cap = if prefer_intrinsic && !states[i].ideal_content {
                        local[i - r.start]
                    } else {
                        eligible_cap(&states[i], sizes[i])
                    };
                }
                grow_toward(&mut local, &caps, remaining);
            }
            for (target, &v) in planned[r].iter_mut().zip(&local) {
                *target = target.max(v);
            }
        }
        sizes.copy_from_slice(&planned);
    }
    // A spanning minimum crossing a fractional track is carried by the
    // fractional tracks with intrinsic floors. All span lengths share one
    // snapshot, so an overlapping short item cannot bias a longer one.
    if phase == ContributionPhase::Minimum && states.iter().any(|s| s.flexible && s.min_content) {
        planned.copy_from_slice(sizes);
        for item in items {
            let r = item.tracks.clone();
            let eligible = |s: &Sizing| s.flexible && s.min_content;
            let deficit = f64::from(item.minimum)
                - sizes[r.clone()].iter().sum::<f64>()
                - gap * (r.len() - 1) as f64;
            if deficit <= 0. {
                continue;
            }
            let mut weight = 0.;
            let mut count = 0;
            for state in states[r.clone()].iter().filter(|s| eligible(s)) {
                count += 1;
                weight += state.fr;
            }
            for i in r.filter(|&i| eligible(&states[i])) {
                let share = if weight > 0. {
                    states[i].fr / weight
                } else {
                    1. / f64::from(count)
                };
                planned[i] = planned[i].max(sizes[i] + deficit * share);
            }
        }
        sizes.copy_from_slice(&planned);
    }
}

// Solve one common fraction. Freeze a track whose minimum exceeds its share
// and recalculate the denominator from the remaining factors. The caller
// reuses the temporary indices across intrinsic contributions.
fn fraction_unit(states: &[Sizing], sizes: &[f64], mut space: f64, active: &mut Vec<usize>) -> f64 {
    active.clear();
    for (i, state) in states.iter().enumerate() {
        if state.fr > 0. {
            active.push(i);
        } else {
            space -= sizes[i];
        }
    }
    while !active.is_empty() {
        let weight = active.iter().map(|&i| states[i].fr).sum::<f64>().max(1.);
        let unit = space / weight;
        let count = active.len();
        active.retain(|&i| {
            if sizes[i] > unit * states[i].fr {
                space -= sizes[i];
                false
            } else {
                true
            }
        });
        if active.len() == count {
            return unit.max(0.);
        }
    }
    0.
}
struct SizedAxis {
    sizes: Vec<f64>,
    used: Vec<bool>,
    visible: usize,
    minimum: f32,
    total: f32,
}

impl TrackGrid {
    /// Minimum and preferred content extents before parent space is known.
    /// Percentage tracks contribute intrinsically. Both extents include gaps.
    pub fn intrinsic_extents(
        &self,
        axis: Axis,
        count: usize,
        items: &[TrackContribution],
    ) -> (f32, f32) {
        self.intrinsic_measurements(axis, count, items, &[])
    }
    pub(crate) fn intrinsic_measurements(
        &self,
        axis: Axis,
        count: usize,
        items: &[TrackContribution],
        minimum: &[f32],
    ) -> (f32, f32) {
        let sized = self.size_axis(axis, None, count, items, minimum);
        (sized.minimum, sized.total)
    }

    fn size_axis(
        &self,
        axis: Axis,
        extent: Option<f32>,
        count: usize,
        contributions_in: &[TrackContribution],
        minimum_content: &[f32],
    ) -> SizedAxis {
        let count = count.min(MAX_TRACKS);
        let gap = self.gap[axis].max(0.);
        let template = &self.tracks[axis];
        let explicit = template.count(extent.unwrap_or(0.), gap, None);
        let mut items: Vec<_> = contributions_in
            .iter()
            .enumerate()
            .map(|(i, item)| Demand {
                item,
                min_content: minimum_content.get(i).copied().unwrap_or(item.minimum),
            })
            .filter(|c| c.tracks.start < c.tracks.end && c.tracks.end <= count)
            .collect();
        // Equal-span plans use a common snapshot. Their relative order is
        // immaterial, and the usual all-single-span grid is already ordered.
        if !items.is_sorted_by_key(|c| c.tracks.len()) {
            items.sort_unstable_by_key(|c| c.tracks.len());
        }
        let mut used = vec![true; count];
        let range = template.collapsed_range(explicit);
        let collapsible = range.start.min(count)..range.end.min(count);
        if !collapsible.is_empty() {
            used[collapsible].fill(false);
            for item in &items {
                used[item.tracks.clone()].fill(true);
            }
        }
        let visible = used.iter().filter(|&&v| v).count();
        let gaps = gap * visible.saturating_sub(1) as f32;
        let states: Vec<_> = (0..count)
            .map(|i| {
                if used[i] {
                    let mut state = sizing(self.track_at(axis, i, explicit), extent);
                    if i < explicit
                        && let TrackAxis::AutoFit { minimum, .. }
                        | TrackAxis::AutoFill { minimum, .. } = template
                    {
                        state.base = state.base.max(f64::from(*minimum));
                        state.cap = state.cap.max(state.base);
                    }
                    state
                } else {
                    sizing(Track::Pixels(0.), extent)
                }
            })
            .collect();
        let mut sizes: Vec<_> = states.iter().map(|s| s.base).collect();
        let apply = |sizes: &mut [f64], phase: ContributionPhase| {
            if states.iter().any(|s| phase.eligible(s)) {
                contributions(sizes, &states, &items, f64::from(gap), phase);
            }
        };
        apply(&mut sizes, ContributionPhase::Minimum);
        apply(&mut sizes, ContributionPhase::MeasuredFloor);
        apply(&mut sizes, ContributionPhase::PreferredFloor);
        let minimum = sizes.iter().sum::<f64>() as f32 + gaps;
        let mut ideal = sizes.clone();
        if states.iter().any(|s| s.min_ceiling) {
            apply(&mut ideal, ContributionPhase::MeasuredLimit);
        }
        apply(&mut ideal, ContributionPhase::PreferredLimit);
        if let Some(extent) = extent {
            let budget = f64::from(extent.max(0.) - gaps);
            let spare = budget - sizes.iter().sum::<f64>();
            grow_toward(&mut sizes, &ideal, spare);
            let caps: Vec<_> = states
                .iter()
                .zip(&sizes)
                .map(|(s, &v)| if s.grow_to_cap { s.cap.max(v) } else { v })
                .collect();
            let spare = budget - sizes.iter().sum::<f64>();
            grow_toward(&mut sizes, &caps, spare);
            // Solve a common fr unit. Floors above their proposed shares freeze,
            // returning the unclaimed budget to the remaining fractional tracks.
            let unit = fraction_unit(&states, &sizes, budget, &mut Vec::new());
            for (state, size) in states.iter().zip(&mut sizes) {
                *size = size.max(unit * state.fr);
            }
            let stretch_count = states.iter().filter(|state| state.stretch).count();
            if stretch_count > 0 {
                let share = (budget - sizes.iter().sum::<f64>()).max(0.) / stretch_count as f64;
                for (size, state) in sizes.iter_mut().zip(&states) {
                    if state.stretch {
                        *size += share;
                    }
                }
            }
        } else {
            sizes = ideal;
            for (state, size) in states.iter().zip(&mut sizes) {
                if state.grow_to_cap {
                    *size = size.max(state.cap);
                }
            }
            if states.iter().any(|state| state.fr > 0.) {
                let mut active = Vec::new();
                let mut unit = states
                    .iter()
                    .zip(&sizes)
                    .filter(|(s, _)| s.flexible)
                    .map(|(s, v)| v / s.fr.max(1.))
                    .fold(0., f64::max);
                for item in &items {
                    let r = item.tracks.clone();
                    let tracks = &states[r.clone()];
                    if tracks.iter().any(|s| s.fr > 0.) {
                        let space =
                            f64::from(item.preferred) - f64::from(gap) * (r.len() - 1) as f64;
                        unit = unit.max(fraction_unit(tracks, &sizes[r], space, &mut active));
                    }
                }
                for (s, v) in states.iter().zip(&mut sizes) {
                    *v = v.max(unit * s.fr);
                }
            }
        }
        let total = sizes.iter().sum::<f64>() as f32 + gaps;
        SizedAxis {
            sizes,
            used,
            visible,
            minimum,
            total,
        }
    }

    /// Resolve one standalone axis. An absent extent requests the natural size
    /// before the container size is known. Returned edges are local to its content box.
    pub fn resolve_axis(
        &self,
        axis: Axis,
        extent: Option<f32>,
        count: usize,
        contributions_in: &[TrackContribution],
    ) -> (Vec<[f32; 2]>, f32) {
        self.resolve_measurements(axis, extent, count, contributions_in, &[])
    }
    pub(crate) fn resolve_measurements(
        &self,
        axis: Axis,
        extent: Option<f32>,
        count: usize,
        contributions_in: &[TrackContribution],
        minimum_content: &[f32],
    ) -> (Vec<[f32; 2]>, f32) {
        let SizedAxis {
            sizes,
            used,
            visible,
            total,
            ..
        } = self.size_axis(axis, extent, count, contributions_in, minimum_content);
        let gap = self.gap[axis].max(0.);
        let (mut cursor, step) = if visible > 0 {
            line_start_and_gap::<RustFloat>(
                if self.safe_justify[axis] && extent.is_some_and(|e| e < total) {
                    Arrange::Start
                } else {
                    self.justify[axis]
                },
                [0., extent.unwrap_or(total)],
                total,
                visible as u32,
                gap,
            )
        } else {
            (0., 0.)
        };
        let mut seen = false;
        let edges = sizes
            .iter()
            .zip(used)
            .map(|(&size, present)| {
                if present && seen {
                    cursor += step;
                }
                let start = cursor;
                cursor += size as f32;
                seen |= present;
                [start, cursor]
            })
            .collect();
        (edges, total)
    }
}
