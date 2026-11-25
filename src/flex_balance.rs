//! Balanced breaks keep the greedy number of rows, then minimize the sum of squared
//! occupied widths at that line count. Source order breaks equal-cost ties.
use std::ops::Range;

struct Candidates<'a> {
    row: usize,
    band: usize,
    widths: &'a [f64],
    prefix: &'a [f64],
    gap: f64,
    fit: &'a [usize],
    next: &'a [f64],
}

impl Candidates<'_> {
    fn cost(&self, start: usize, end: usize) -> f64 {
        let length = self.prefix[end] - self.prefix[start] - self.gap;
        length * length + self.next[end - self.row - 1]
    }

    // Squared widths are convex: as the start advances, the best break
    // before a positive-width item never moves back. The glue rule for
    // zero-width items is evaluated separately from those monotone breaks.
    fn solve(
        &self,
        starts: Range<usize>,
        low: usize,
        high: usize,
        costs: &mut [f64],
        ends: &mut [usize],
    ) {
        if starts.is_empty() {
            return;
        }
        let mid = starts.start + starts.len() / 2;
        let start = self.row + mid;
        let limit = self.fit[start].min(self.row + self.band);
        let mut best = f64::INFINITY;
        let mut best_end = None;
        for end in (start + 1).max(low)..=limit.min(high) {
            if self.widths[end] <= 0. {
                continue;
            }
            let cost = self.cost(start, end);
            if cost.is_finite() && cost <= best {
                best = cost;
                best_end = Some(end);
            }
        }
        let monotone_end = best_end;
        if self.widths[limit] <= 0. {
            let cost = self.cost(start, limit);
            if cost <= best {
                best = cost;
                best_end = Some(limit);
            }
        }
        costs[mid] = best;
        ends[mid] = best_end.unwrap_or(limit);
        self.solve(
            starts.start..mid,
            low,
            monotone_end.unwrap_or(high),
            costs,
            ends,
        );
        self.solve(
            mid + 1..starts.end,
            monotone_end.unwrap_or(low),
            high,
            costs,
            ends,
        );
    }
}

pub(super) fn ranges(widths: &[f64], gap: f64, limit: f64, minimum: u16) -> Vec<Range<usize>> {
    let n = widths.len();
    if n == 0 {
        return Vec::new();
    }
    let mut prefix = Vec::with_capacity(n + 1);
    prefix.push(0.);
    for &w in widths {
        prefix.push(prefix.last().unwrap() + w.max(0.) + gap);
    }
    let size = |start: usize, end: usize| prefix[end] - prefix[start] - gap;
    let mut fit = Vec::with_capacity(n);
    let mut end = 0;
    for start in 0..n {
        end = end.max(start + 1);
        while end < n && size(start, end + 1) <= limit {
            end += 1;
        }
        fit.push(end);
    }
    let mut greedy = Vec::new();
    let mut start = 0;
    while start < n {
        let end = fit[start];
        greedy.push(start..end);
        start = end;
    }
    let lines = greedy.len().max(usize::from(minimum).min(n));
    if lines == 1 || greedy.len() == n {
        return greedy;
    }
    if lines == n {
        return (0..n).map(|i| i..i + 1).collect();
    }

    if widths[0] > 0. && widths.iter().all(|w| *w == widths[0]) {
        let mut start = 0;
        return (0..lines)
            .map(|line| {
                let end = start + n / lines + usize::from(line < n % lines);
                let range = start..end;
                start = end;
                range
            })
            .collect();
    }
    let mut suffix_minimum = vec![0; n + 1];
    for i in (0..n).rev() {
        suffix_minimum[i] = 1 + suffix_minimum[fit[i]];
    }

    // Each row considers only the diagonal band of starts reachable after the
    // preceding nonempty lines. In a narrow container the fit limits bound
    // the search; when the requested count is near n the band is short.
    let band = n - lines + 1;
    let mut ends = vec![0; (lines - 1) * band];
    let mut next = vec![f64::INFINITY; band + 1];
    let mut current = next.clone();
    for (k, cost) in next[..band].iter_mut().enumerate() {
        let start = lines - 1 + k;
        if fit[start] == n {
            *cost = size(start, n).powi(2);
        }
    }
    for row in (0..lines - 1).rev() {
        // Infeasible suffixes form a prefix of this row. The first row
        // needs only start zero because readback always begins at zero.
        current.fill(f64::INFINITY);
        let first = suffix_minimum[row..row + band].partition_point(|&count| count > lines - row);
        let reachable = if row == 0 { 1 } else { band };
        if first < reachable {
            let candidates = Candidates {
                row,
                band,
                widths,
                prefix: &prefix,
                gap,
                fit: &fit,
                next: &next,
            };
            candidates.solve(
                first..reachable,
                row + 1,
                row + band,
                &mut current,
                &mut ends[row * band..(row + 1) * band],
            );
        }
        std::mem::swap(&mut current, &mut next);
    }
    let mut breaks = Vec::with_capacity(lines);
    let mut start = 0;
    for row in 0..lines - 1 {
        let end = ends[row * band + start - row];
        breaks.push(start..end);
        start = end;
    }
    breaks.push(start..n);
    breaks
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Enumerate every cut for small rows, independently checking feasibility,
    /// zero-size adhesion, the squared-error objective and the source-order tie.
    fn exhaustive(widths: &[f64], gap: f64, limit: f64, minimum: usize) -> Vec<usize> {
        let n = widths.len();
        let size = |a: usize, b: usize| {
            widths[a..b].iter().map(|v| v.max(0.)).sum::<f64>() + gap * (b - a - 1) as f64
        };
        let mut winner: Option<(usize, f64, Vec<usize>)> = None;
        for mask in 0..1 << (n - 1) {
            let mut ends: Vec<usize> = (1..n).filter(|&i| mask & (1 << (i - 1)) != 0).collect();
            ends.push(n);
            if ends.len() < minimum.min(n) {
                continue;
            }
            let mut start = 0;
            let mut score = 0.;
            let mut valid = true;
            for (row, &end) in ends.iter().enumerate() {
                let used = size(start, end);
                let remaining = ends.len() - row - 1;
                if end - start > 1 && used > limit
                    || end < n
                        && widths[end] <= 0.
                        && n - end > remaining
                        && size(start, end + 1) <= limit
                {
                    valid = false;
                    break;
                }
                score += used * used;
                start = end;
            }
            if valid
                && winner.as_ref().is_none_or(|(count, best, best_ends)| {
                    ends.len() < *count
                        || ends.len() == *count
                            && (score < *best || score == *best && ends > *best_ends)
                })
            {
                winner = Some((ends.len(), score, ends));
            }
        }
        winner.unwrap().2
    }

    #[test]
    fn optimized_breaks_match_exhaustive_partitions() {
        let mut seed = 53u32;
        for n in 1..=9 {
            for _ in 0..80 {
                let mut next = || {
                    seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
                    seed >> 16
                };
                let widths: Vec<f64> = (0..n).map(|_| f64::from((next() % 7) as i32 - 2)).collect();
                let gap = f64::from(next() % 4);
                let limit = f64::from(next() % 14);
                let minimum = (next() % (n as u32 + 2)) as u16;
                let chosen: Vec<_> = ranges(&widths, gap, limit, minimum)
                    .into_iter()
                    .map(|r| r.end)
                    .collect();
                assert_eq!(
                    chosen,
                    exhaustive(&widths, gap, limit, usize::from(minimum)),
                    "widths {widths:?}, gap {gap}, limit {limit}, minimum {minimum}"
                );
            }
        }
    }
}
