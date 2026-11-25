//! Heterogeneous grid tracks, explicit and automatic cell placement, and shared
//! tracks for nested grids. Track starts are zero-based; spans count tracks.
use crate::placement_geometry::{RustFloat, line_start_and_gap};
use crate::solve::grid_sparse::{Occupied, find_cell};
use crate::{Arrange, Axis, Xy};
use std::ops::Range;

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
    /// Grow to the preferred contributions of its items.
    Content,
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
    /// Weighted share of the remaining space.
    Fr(f32),
    /// Content sizing capped at this many pixels, subject to the minimum contribution.
    FitContent(f32),
    /// Independent minimum and maximum sizing policies.
    MinMax(TrackMin, TrackMax),
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
            Self::Subgrid => inherited.unwrap_or(1).clamp(1, MAX_TRACKS),
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
    fn at(&self, index: usize, explicit: usize, implicit: Track) -> Track {
        match self {
            Self::Tracks(v) => v.get(index).copied().unwrap_or(implicit),
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
            counts[a] = self.tracks[a].count(inner[a], self.gap[a].max(0.), inherited[a]);
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
    /// Minimum outer contribution.
    pub minimum: f32,
    /// Preferred outer contribution.
    pub preferred: f32,
}
#[derive(Clone, Copy)]
struct Sizing {
    base: f64,
    cap: f64,
    min_content: bool,
    ideal_content: bool,
    fr: f64,
    grow_to_cap: bool,
}
fn sizing(track: Track, extent: Option<f32>) -> Sizing {
    let percent = |f: f32| extent.map(|e| f64::from(e) * f64::from(f.max(0.)));
    let (min, max) = match track {
        Track::Pixels(p) => (TrackMin::Pixels(p), TrackMax::Pixels(p)),
        Track::Percent(f) => (TrackMin::Percent(f), TrackMax::Percent(f)),
        Track::Content => (TrackMin::Content, TrackMax::Content),
        Track::Fr(f) => (TrackMin::Pixels(0.), TrackMax::Fr(f)),
        Track::MinMax(min, max) => (min, max),
        Track::FitContent(cap) => (TrackMin::Content, TrackMax::Pixels(cap)),
    };
    let lower = match min {
        TrackMin::Pixels(p) => Some(f64::from(p.max(0.))),
        TrackMin::Percent(f) => percent(f),
        TrackMin::Content => None,
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
        ideal_content: matches!(max, TrackMax::Content)
            || matches!(track, Track::FitContent(_))
            || matches!(max, TrackMax::Percent(_)) && extent.is_none(),
        fr,
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
// Compute demands at each span length from a common snapshot, so equally
// spanning items produce the same track sizes in either source order.
fn contributions(
    sizes: &mut [f64],
    states: &[Sizing],
    items: &[&TrackContribution],
    gap: f64,
    minimum: bool,
    intrinsic: bool,
) {
    let mut planned = vec![0.; sizes.len()];
    for group in items.chunk_by(|a, b| a.tracks.len() == b.tracks.len()) {
        planned.copy_from_slice(sizes);
        for item in group {
            let r = item.tracks.clone();
            let demand = f64::from(if minimum {
                item.minimum
            } else {
                item.preferred
            });
            let missing =
                demand - sizes[r.clone()].iter().sum::<f64>() - gap * (r.len() - 1) as f64;
            if missing <= 0. {
                continue;
            }
            let mut local = sizes[r.clone()].to_vec();
            let caps: Vec<_> = states[r.clone()]
                .iter()
                .zip(&local)
                .map(|(s, &v)| {
                    if minimum && s.min_content {
                        f64::INFINITY
                    } else if !minimum && (s.ideal_content || intrinsic && s.fr > 0.) {
                        s.cap.max(v)
                    } else {
                        v
                    }
                })
                .collect();
            grow_toward(&mut local, &caps, missing);
            for (target, &v) in planned[r].iter_mut().zip(&local) {
                *target = target.max(v);
            }
        }
        sizes.copy_from_slice(&planned);
    }
}
impl TrackGrid {
    /// Resolve one standalone axis. An absent extent requests the natural size
    /// before the container size is known. Returned edges are local to its content box.
    pub fn resolve_axis(
        &self,
        axis: Axis,
        extent: Option<f32>,
        count: usize,
        contributions_in: &[TrackContribution],
    ) -> (Vec<[f32; 2]>, f32) {
        let count = count.min(MAX_TRACKS);
        let gap = self.gap[axis].max(0.);
        let template = &self.tracks[axis];
        let explicit = template.count(extent.unwrap_or(0.), gap, None);
        let mut items: Vec<_> = contributions_in
            .iter()
            .filter(|c| c.tracks.start < c.tracks.end && c.tracks.end <= count)
            .collect();
        items.sort_by_key(|c| c.tracks.len());
        let mut used = vec![true; count];
        if matches!(template, TrackAxis::AutoFit { .. }) {
            used[..explicit.min(count)].fill(false);
            for item in &items {
                used[item.tracks.clone()].fill(true);
            }
        }
        let visible = used.iter().filter(|&&v| v).count();
        let gaps = gap * visible.saturating_sub(1) as f32;
        let states: Vec<_> = (0..count)
            .map(|i| {
                if used[i] {
                    let mut state = sizing(template.at(i, explicit, self.implicit[axis]), extent);
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
        contributions(
            &mut sizes,
            &states,
            &items,
            f64::from(gap),
            true,
            extent.is_none(),
        );
        let mut ideal = sizes.clone();
        contributions(
            &mut ideal,
            &states,
            &items,
            f64::from(gap),
            false,
            extent.is_none(),
        );
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
            let mut available = budget;
            let mut flexible: Vec<_> = states
                .iter()
                .enumerate()
                .filter_map(|(i, s)| {
                    if s.fr > 0. {
                        Some(i)
                    } else {
                        available -= sizes[i];
                        None
                    }
                })
                .collect();
            while !flexible.is_empty() {
                let factor = flexible.iter().map(|&i| states[i].fr).sum::<f64>().max(1.);
                let unit = available / factor;
                let old = flexible.len();
                flexible.retain(|&i| {
                    if sizes[i] > unit * states[i].fr {
                        available -= sizes[i];
                        false
                    } else {
                        true
                    }
                });
                if old == flexible.len() {
                    for i in flexible {
                        sizes[i] = unit * states[i].fr;
                    }
                    break;
                }
            }
        } else {
            sizes = ideal;
            let unit = states
                .iter()
                .zip(&sizes)
                .filter(|(s, _)| s.fr > 0.)
                .map(|(s, v)| v / s.fr)
                .fold(0., f64::max);
            for (s, v) in states.iter().zip(&mut sizes) {
                if s.fr > 0. {
                    *v = unit * s.fr;
                }
            }
        }
        let total = sizes.iter().sum::<f64>() as f32 + gaps;
        let (mut cursor, step) = if visible > 0 {
            line_start_and_gap::<RustFloat>(
                self.justify[axis],
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
