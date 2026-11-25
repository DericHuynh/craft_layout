extern crate self as keru_layout;
mod bridge;
#[cfg(feature = "allocations")]
#[path = "allocations.rs"]
mod measurement;
#[cfg(not(feature = "allocations"))]
#[path = "timing.rs"]
mod measurement;
pub use bridge::*;
mod browser {
    include!("../../../../benches/real_workloads/browser.rs");
}
mod cad {
    include!("../../../../benches/real_workloads/cad.rs");
}
mod compositor {
    include!("../../../../benches/real_workloads/compositor.rs");
}

use std::process::ExitCode;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode {
    Upstream,
    UpstreamFull,
    Tuned,
    TunedFull,
    Batch,
}

const MODES: [Mode; 5] = [
    Mode::Upstream,
    Mode::UpstreamFull,
    Mode::Tuned,
    Mode::TunedFull,
    Mode::Batch,
];

impl Mode {
    fn original(self) -> bool {
        matches!(self, Self::Upstream | Self::UpstreamFull)
    }
    fn name(self) -> &'static str {
        match self {
            Self::Upstream => "upstream",
            Self::UpstreamFull => "upstream_full",
            Self::Tuned => "tuned",
            Self::TunedFull => "tuned_full",
            Self::Batch => "batch",
        }
    }
}

type Edit = dyn FnMut(&mut LayoutTree<String>, usize) -> Xy<f32>;

struct Case {
    name: &'static str,
    period: usize,
    tree: LayoutTree<String>,
    viewport: Xy<f32>,
    edit: Box<Edit>,
}

impl Case {
    fn edit(&mut self, frame: usize) {
        self.viewport = (self.edit)(&mut self.tree, frame);
    }

    fn solve(&mut self) -> (measurement::Sample, bool) {
        self.tree.invalidate_if_forced();
        measurement::solve(|| self.tree.solve(self.viewport))
    }

    fn snapshot(&self) -> Vec<(usize, Option<[f32; 4]>)> {
        let mut output = Vec::new();
        let mut pending = vec![self.tree.root()];
        while let Some(node) = pending.pop() {
            let first = pending.len();
            self.tree.children(&node, &mut pending);
            pending[first..].reverse();
            let edges = self
                .tree
                .layout(&node)
                .map(|rect| [rect.x[0], rect.x[1], rect.y[0], rect.y[1]]);
            output.push((pending.len() - first, edges));
        }
        output
    }
}

#[derive(Debug, Default)]
struct Check {
    mismatches: usize,
    warning_frames: usize,
    max_abs: f32,
}

impl Check {
    fn compare(
        &mut self,
        actual: &Case,
        reference: &[(usize, Option<[f32; 4]>)],
        frame: usize,
        mode: Mode,
    ) {
        let view = actual.snapshot();
        let mut mismatch = view.len() != reference.len();
        for (index, (&(actual_children, actual_edges), &(expected_children, expected_edges))) in
            view.iter().zip(reference).enumerate()
        {
            let before = mismatch;
            mismatch |= actual_children != expected_children;
            match (actual_edges, expected_edges) {
                (Some(actual), Some(expected)) => {
                    for (a, e) in actual.into_iter().zip(expected) {
                        let error = (a - e).abs();
                        self.max_abs = self.max_abs.max(error);
                        mismatch |= !a.is_finite() || a.to_bits() != e.to_bits();
                    }
                }
                (None, None) => {}
                _ => mismatch = true,
            }
            if !before && mismatch && self.mismatches == 0 {
                eprintln!(
                    "{} {} frame={frame} node={index} actual={:?} reference={:?}",
                    actual.name,
                    mode.name(),
                    view[index],
                    reference[index]
                );
            }
        }
        self.warning_frames += usize::from(actual.tree.has_warnings());
        self.mismatches += usize::from(mismatch);
    }
}

fn main() -> ExitCode {
    let mut args = std::env::args().skip(1);
    let frames: usize = args.next().map_or(120, |value| value.parse().unwrap());
    let runs: usize = args.next().map_or(5, |value| value.parse().unwrap());
    let filter = args.next();
    assert!(frames > 0 && runs > 0, "frames and runs must be positive");
    const WARMUP: usize = 24;
    let mut verified = true;
    let mut selected = false;
    println!(
        "workload\trun\tmode\tnodes\t{}\trebuild_or_fallback\tgeometry_mismatch\twarnings\tmax_abs_error",
        measurement::COLUMNS,
    );
    for run in 0..runs {
        let mut all = MODES.map(|mode| bridge::build_cases(mode).into_iter());
        while let Some(first) = all[0].next() {
            let mut cases = [
                first,
                all[1].next().unwrap(),
                all[2].next().unwrap(),
                all[3].next().unwrap(),
                all[4].next().unwrap(),
            ];
            if filter
                .as_ref()
                .is_some_and(|filter| !cases[0].name.contains(filter))
            {
                continue;
            }
            selected = true;
            assert!(
                cases
                    .iter()
                    .all(|case| case.name == cases[0].name && case.period == cases[0].period)
            );
            let mut samples = MODES.map(|_| Vec::with_capacity(frames));
            let mut cold = [measurement::Sample::default(); MODES.len()];
            let mut rebuilt = [0; MODES.len()];
            let mut checks = MODES.map(|_| Check::default());
            let mut nodes = 0;
            for frame in 0..=WARMUP + frames {
                if frame > 0 {
                    for case in &mut cases {
                        case.edit(frame - 1);
                    }
                }
                assert!(cases.iter().all(|case| case.viewport == cases[0].viewport));
                for offset in 0..MODES.len() {
                    let engine = (offset + frame + run) % MODES.len();
                    let (sample, full) = cases[engine].solve();
                    if frame == 0 {
                        cold[engine] = sample;
                    } else if frame > WARMUP {
                        samples[engine].push(sample);
                        rebuilt[engine] += usize::from(full);
                    }
                }
                let reference = cases[3].snapshot();
                if frame == 0 {
                    nodes = reference.len();
                }
                for (engine, case) in cases.iter().enumerate() {
                    checks[engine].compare(case, &reference, frame, MODES[engine]);
                }
            }
            for (engine, samples) in samples.iter_mut().enumerate() {
                let check = &checks[engine];
                verified &= check.mismatches == 0 && check.warning_frames == 0;
                print!(
                    "{}\t{run}\t{}\t{nodes}\t",
                    cases[engine].name,
                    MODES[engine].name()
                );
                measurement::print(cold[engine], samples);
                println!(
                    "\t{}\t{}\t{}\t{}",
                    rebuilt[engine], check.mismatches, check.warning_frames, check.max_abs
                );
            }
        }
    }
    if !selected {
        eprintln!("no workload matched {filter:?}");
    }
    if selected && verified {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
