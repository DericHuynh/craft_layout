//! Grid lines address the explicit template. Implicit tracks may extend
//! before its first line without changing the meaning of any explicit line.
use std::collections::BTreeMap;

/// Names attached to explicit grid lines in declaration order.
pub type LineNames = BTreeMap<usize, Vec<String>>;

/// A line or span in the logical track ordering.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum GridLine {
    /// Leave this edge open.
    #[default]
    Auto,
    /// CSS-style one-based line. Negative numbers count back from the end.
    Index(i32),
    /// A named occurrence. A bare name can resolve the matching area edge.
    Named {
        /// Line or area name.
        name: String,
        /// Signed, one-based occurrence.
        occurrence: i32,
        /// A bare name first looks for the corresponding area edge.
        area_edge: bool,
    },
    /// Count that many tracks, optionally counting only lines with a given name.
    Span {
        /// Number of matching lines to cross.
        count: u16,
        /// Restrict the count to lines with this name.
        name: Option<String>,
    },
}

#[cfg(feature = "incremental")]
fn find_named(names: &LineNames, name: &str, count: usize, from: i64, n: i64, step: i64) -> i64 {
    // Skip implicit prefixes/suffixes in one step. Within the explicit
    // template, visit only stored labels even on very large sparse grids.
    let end = count as i64;
    let mut at = from;
    let mut remaining = n.max(1);
    if step > 0 {
        if at < -1 {
            let skip = (-1 - at).min(remaining);
            at += skip;
            remaining -= skip;
        }
        if remaining == 0 || at >= end {
            return at + remaining;
        }
        for (&i, labels) in names.range((at + 1) as usize..=count) {
            if labels.iter().any(|label| label == name) {
                remaining -= 1;
                if remaining == 0 {
                    return i as i64;
                }
            }
        }
        end + remaining
    } else {
        if at > end + 1 {
            let skip = (at - end - 1).min(remaining);
            at -= skip;
            remaining -= skip;
        }
        if remaining == 0 || at <= 0 {
            return at - remaining;
        }
        for (&i, labels) in names.range(..=(at - 1) as usize).rev() {
            if labels.iter().any(|label| label == name) {
                remaining -= 1;
                if remaining == 0 {
                    return i as i64;
                }
            }
        }
        -remaining
    }
}
#[cfg(feature = "incremental")]
impl GridLine {
    fn index(&self, end: bool, count: usize, names: &LineNames) -> Option<i64> {
        match self {
            Self::Index(n) if *n < 0 => Some(count as i64 + 1 + i64::from(*n)),
            Self::Index(n) => Some(i64::from(*n) - 1),
            Self::Named {
                name,
                occurrence,
                area_edge,
            } => {
                if *area_edge {
                    let edge = format!("{name}-{}", if end { "end" } else { "start" });
                    if let Some((i, _)) = names.iter().find(|(_, ns)| ns.contains(&edge)) {
                        return Some(*i as i64);
                    }
                }
                let n = i64::from(*occurrence);
                Some(find_named(
                    names,
                    name,
                    count,
                    if n < 0 { count as i64 + 1 } else { -1 },
                    n.abs(),
                    if n < 0 { -1 } else { 1 },
                ))
            }
            _ => None,
        }
    }
}
/// Return explicit line offsets. Absolute items preserve open edges and
/// never allocate implicit tracks. A line pair with both ends auto has no range.
#[cfg(feature = "incremental")]
pub(crate) fn endpoints(
    pair: &[GridLine; 2],
    count: usize,
    names: &LineNames,
    absolute: bool,
) -> [Option<i64>; 2] {
    let [start, end] = pair;
    let mut a = start.index(false, count, names);
    let mut b = end.index(true, count, names);
    let span_edge = |line: &GridLine, anchor: i64, dir: i64| match line {
        GridLine::Span {
            count: n,
            name: Some(name),
        } => Some(find_named(names, name, count, anchor, i64::from(*n), dir)),
        GridLine::Span {
            count: n,
            name: None,
        } => Some(anchor + dir * i64::from(*n)),
        _ if !absolute => Some(anchor + dir),
        _ => None,
    };
    match (a, b) {
        (Some(lo), Some(hi)) if lo > hi => {
            a = Some(hi);
            b = Some(lo);
        }
        (Some(lo), Some(hi)) if lo == hi => {
            b = if absolute { None } else { Some(lo + 1) };
        }
        (Some(lo), None) => b = span_edge(end, lo, 1),
        (None, Some(hi)) => a = span_edge(start, hi, -1),
        _ => {}
    }
    [a, b]
}
#[cfg(feature = "incremental")]
pub(crate) fn slot(pair: &[GridLine; 2], count: usize, names: &LineNames) -> (Option<i64>, u16) {
    match endpoints(pair, count, names, false) {
        [Some(lo), Some(hi)] => (Some(lo), (hi - lo).clamp(1, i64::from(u16::MAX)) as u16),
        _ => (
            None,
            pair.iter()
                .find_map(|l| match l {
                    GridLine::Span { count, name } => Some(if name.is_some() { 1 } else { *count }),
                    _ => None,
                })
                .unwrap_or(1),
        ),
    }
}

/// Names inside an automatic repetition and in the fixed suffix after it.
/// Prefix names remain in the grid's ordinary line name map.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RepeatLineNames {
    /// Lines relative to the beginning of one repeated group.
    pub group: LineNames,
    /// Lines relative to the first track after the repetition.
    pub suffix: LineNames,
}
#[cfg(feature = "incremental")]
pub(crate) fn append(names: &mut LineNames, offset: usize, addition: &LineNames, limit: usize) {
    for (&i, labels) in addition {
        let index = i.saturating_add(offset);
        if index > limit {
            continue;
        }
        names
            .entry(index)
            .or_default()
            .extend(labels.iter().cloned());
    }
}
