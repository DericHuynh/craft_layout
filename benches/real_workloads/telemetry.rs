use super::{Case, WARMUP_FRAMES, cases, percentiles, verify};
use keru_layout::{BatchLayoutStats, IncrementalRelayoutOutcome};
use std::hint::black_box;
use std::time::{Duration, Instant};

const MODE_NAMES: [&str; 3] = ["default", "batch", "full"];

struct Sample {
    duration: Duration,
    computed: Option<usize>,
    fallback: bool,
    batch: Option<BatchLayoutStats>,
}

fn solve(case: &mut Case, mode: usize) -> Sample {
    if mode == 1 {
        let start = Instant::now();
        let result = black_box(case.layout_batch());
        let duration = start.elapsed();
        return Sample {
            duration,
            computed: Some(result.computed),
            fallback: false,
            batch: Some(result),
        };
    }
    let start = Instant::now();
    let result = black_box(case.layout(false));
    let duration = start.elapsed();
    let computed = match result {
        IncrementalRelayoutOutcome::Success { computed } => Some(computed as usize),
        _ => None,
    };
    Sample {
        duration,
        computed,
        fallback: computed.is_none(),
        batch: None,
    }
}

pub(super) fn run(filter: &str, frames: usize, runs: usize) -> Result<(), String> {
    let mut selected = false;
    println!(
        "workload\trun\tmode\tphase\tframes\tp50_us\tp95_us\tfallback_frames\tgraph_rebuild_frames\trepaired_intervals\tcomputed_min\tcomputed_max"
    );
    for run in 0..runs {
        for ((default, batch), full) in cases().zip(cases()).zip(cases()) {
            if default.name.contains(filter) {
                run_case([default, batch, full], frames, run);
                selected = true;
            }
        }
    }
    if selected {
        Ok(())
    } else {
        Err(format!("no workloads matched {filter:?}"))
    }
}

fn run_case(mut cases: [Case; 3], frames: usize, run: usize) {
    let name = cases[0].name;
    let period = cases[0].period;
    assert!(
        cases
            .iter()
            .all(|case| case.name == name && case.period == period)
    );

    for (mode, case) in cases.iter_mut().enumerate() {
        solve(case, mode);
    }
    verify(&cases[0], &cases[2], "initial default");
    verify(&cases[1], &cases[2], "initial batch");
    let mut samples = std::array::from_fn::<_, 3, _>(|_| Vec::with_capacity(frames));
    for frame in 0..WARMUP_FRAMES + frames {
        for case in &mut cases {
            case.apply_frame(frame);
        }
        cases[2].tree.invalidate();
        for offset in 0..cases.len() {
            let mode = (offset + frame + run) % cases.len();
            let sample = solve(&mut cases[mode], mode);
            if frame >= WARMUP_FRAMES {
                samples[mode].push((frame % period, sample));
            }
        }
        if frame < WARMUP_FRAMES || frame + 1 == WARMUP_FRAMES + frames {
            verify(&cases[0], &cases[2], &format!("frame {frame} default"));
            verify(&cases[1], &cases[2], &format!("frame {frame} batch"));
        }
    }

    for (mode, samples) in MODE_NAMES.into_iter().zip(&samples) {
        report(
            name,
            run,
            mode,
            "all",
            samples.iter().map(|(_, sample)| sample),
        );
        for phase in 0..period {
            report(
                name,
                run,
                mode,
                &phase.to_string(),
                samples
                    .iter()
                    .filter(|(index, _)| *index == phase)
                    .map(|(_, sample)| sample),
            );
        }
    }
}

fn report<'a>(
    name: &str,
    run: usize,
    mode: &str,
    phase: &str,
    samples: impl Iterator<Item = &'a Sample>,
) {
    let mut times = Vec::new();
    let mut fallbacks = 0;
    let mut rebuilds = 0;
    let mut repairs = 0;
    let mut computed_min: Option<usize> = None;
    let mut computed_max: Option<usize> = None;
    for sample in samples {
        times.push(sample.duration);
        fallbacks += usize::from(sample.fallback);
        if let Some(stats) = sample.batch {
            rebuilds += usize::from(stats.rebuilt_graph);
            repairs += stats.repaired_intervals;
        }
        if let Some(computed) = sample.computed {
            computed_min = Some(computed_min.map_or(computed, |min| min.min(computed)));
            computed_max = Some(computed_max.map_or(computed, |max| max.max(computed)));
        }
    }
    if times.is_empty() {
        return;
    }
    let frames = times.len();
    let (p50, p95) = percentiles(times);
    let count = |value: Option<usize>| value.map_or_else(|| "-".to_owned(), |n| n.to_string());
    println!(
        "{name}\t{run}\t{mode}\t{phase}\t{frames}\t{p50:.3}\t{p95:.3}\t{fallbacks}\t{rebuilds}\t{repairs}\t{}\t{}",
        count(computed_min),
        count(computed_max)
    );
}
