use std::hint::black_box;
use std::time::Instant;

pub(super) type Sample = u128;
pub(super) const COLUMNS: &str = "cold_ns\tp50_ns\tp95_ns";

pub(super) fn solve(run: impl FnOnce() -> bool) -> (Sample, bool) {
    let start = Instant::now();
    let rebuilt = black_box(run());
    (start.elapsed().as_nanos(), rebuilt)
}

pub(super) fn print(cold: Sample, samples: &mut [Sample]) {
    samples.sort_unstable();
    let count = samples.len();
    let median = (samples[(count - 1) / 2] + samples[count / 2]) as f64 * 0.5;
    let p95 = samples[(count * 95).div_ceil(100) - 1];
    print!("{cold}\t{median}\t{p95}");
}
