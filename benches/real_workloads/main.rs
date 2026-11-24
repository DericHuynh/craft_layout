mod browser;
mod cad;
mod compositor;

use keru_layout::{
    IncrementalRelayoutOutcome, LayoutTree, NodeId, TreeError, Xy, measure_monospace_text,
};
use std::hint::black_box;
use std::num::NonZeroUsize;
use std::process::ExitCode;
use std::time::{Duration, Instant};

const DEFAULT_FRAMES: usize = 120;
const WARMUP_FRAMES: usize = 24;
const USAGE: &str =
    "Usage: cargo bench --bench real_workloads -- [--frames N] [--filter NAME] [--verify-only]";

type Edit = dyn FnMut(&mut LayoutTree<String>, usize) -> Xy<f32>;

struct Case {
    name: &'static str,
    tree: LayoutTree<String>,
    viewport: Xy<f32>,
    edit: Box<Edit>,
}

impl Case {
    fn apply_frame(&mut self, frame: usize) {
        self.viewport = (self.edit)(&mut self.tree, frame);
    }

    fn layout(&mut self) -> IncrementalRelayoutOutcome {
        self.tree
            .solve_layout_with_measure(self.viewport, measure_monospace_text)
    }
}

#[derive(Debug, PartialEq, Eq)]
struct NodeOutput {
    children: usize,
    edges: Option<[u32; 4]>,
}

fn snapshot(tree: &LayoutTree<String>) -> Vec<NodeOutput> {
    let mut output = Vec::new();
    let mut pending = vec![tree.root()];
    while let Some(id) = pending.pop() {
        let edges = match tree.layout(&id) {
            Ok(rect) => {
                let edges = [rect.x[0], rect.x[1], rect.y[0], rect.y[1]];
                assert!(edges.iter().all(|edge| edge.is_finite()), "{id:?} {rect:?}");
                Some(edges.map(f32::to_bits))
            }
            Err(TreeError::LayoutUnavailable) => None,
            Err(error) => panic!("could not inspect {id:?}: {error}"),
        };
        let first_child = pending.len();
        pending.extend(tree.children(&id).unwrap().map(NodeId::from));
        pending[first_child..].reverse();
        output.push(NodeOutput {
            children: pending.len() - first_child,
            edges,
        });
    }
    output
}

fn verify(incremental: &Case, full: &Case, frame: &str) -> Vec<NodeOutput> {
    let name = incremental.name;
    assert_eq!(incremental.viewport, full.viewport, "{name} {frame}");
    assert!(
        incremental.tree.warnings().is_empty() && full.tree.warnings().is_empty(),
        "{name} {frame} layout warnings: {:?} / {:?}",
        incremental.tree.warnings(),
        full.tree.warnings(),
    );
    let actual = snapshot(&incremental.tree);
    let expected = snapshot(&full.tree);
    assert_eq!(actual.len(), expected.len(), "{name} {frame} node count");
    for (index, (actual, expected)) in actual.iter().zip(&expected).enumerate() {
        assert_eq!(actual, expected, "{name} {frame} preorder node {index}");
    }
    actual
}

fn time_layout(case: &mut Case) -> (Duration, IncrementalRelayoutOutcome) {
    let start = Instant::now();
    let outcome = black_box(case.layout());
    (start.elapsed(), outcome)
}

fn percentiles(mut times: Vec<Duration>) -> (f64, f64) {
    times.sort_unstable();
    let mid = times.len() / 2;
    let micros = |duration: Duration| duration.as_secs_f64() * 1e6;
    let median = if times.len() % 2 == 0 {
        (micros(times[mid - 1]) + micros(times[mid])) / 2.0
    } else {
        micros(times[mid])
    };
    let p95 = times.len() - times.len() / 20 - 1;
    (median, micros(times[p95]))
}

fn run(mut incremental: Case, mut full: Case, frames: Option<NonZeroUsize>) {
    assert_eq!(incremental.name, full.name);
    incremental.layout();
    full.layout();
    let mut previous = verify(&incremental, &full, "initial");
    let initial_nodes = previous.len();
    let mut changed = false;
    for frame in 0..WARMUP_FRAMES {
        incremental.apply_frame(frame);
        full.apply_frame(frame);
        full.tree.invalidate();
        incremental.layout();
        full.layout();
        let current = verify(&incremental, &full, &format!("warmup frame {frame}"));
        changed |= previous != current;
        previous = current;
    }
    assert!(changed, "{} did not change geometry", incremental.name);

    let Some(frames) = frames else {
        println!("{}\t{initial_nodes}\tverified", incremental.name);
        return;
    };
    let frames = frames.get();
    let mut incremental_times = Vec::with_capacity(frames);
    let mut full_times = Vec::with_capacity(frames);
    let mut fallback_frames = 0;
    for (index, frame) in (WARMUP_FRAMES..).take(frames).enumerate() {
        incremental.apply_frame(frame);
        full.apply_frame(frame);
        full.tree.invalidate();
        let (incremental_sample, full_sample) = if index % 2 == 0 {
            (time_layout(&mut incremental), time_layout(&mut full))
        } else {
            let full_sample = time_layout(&mut full);
            (time_layout(&mut incremental), full_sample)
        };
        assert_eq!(
            full_sample.1,
            IncrementalRelayoutOutcome::FallbackInvalidated
        );
        fallback_frames += usize::from(!matches!(
            incremental_sample.1,
            IncrementalRelayoutOutcome::Success { .. }
        ));
        incremental_times.push(incremental_sample.0);
        full_times.push(full_sample.0);
    }
    verify(&incremental, &full, "final measured frame");
    let (full_p50, full_p95) = percentiles(full_times);
    let (incremental_p50, incremental_p95) = percentiles(incremental_times);
    println!(
        "{}\t{initial_nodes}\t{frames}\t{full_p50:.3}\t{full_p95:.3}\t{incremental_p50:.3}\t{incremental_p95:.3}\t{fallback_frames}",
        incremental.name,
    );
}

fn cases() -> impl Iterator<Item = Case> {
    browser::cases()
        .into_iter()
        .chain(compositor::cases())
        .chain(cad::cases())
}

fn execute() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let mut frames = NonZeroUsize::new(DEFAULT_FRAMES).unwrap();
    let mut filter = String::new();
    let mut verify_only = false;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            // Cargo appends this argument to custom benchmark executables.
            "--bench" => {}
            "--frames" => {
                frames = args
                    .next()
                    .and_then(|value| value.parse().ok())
                    .ok_or("--frames expects a positive integer")?;
            }
            "--filter" => filter = args.next().ok_or("--filter expects a workload name")?,
            "--verify-only" => verify_only = true,
            "-h" | "--help" => {
                println!("{USAGE}");
                return Ok(());
            }
            _ => return Err(format!("unknown argument {arg}")),
        }
    }

    let mut selected = cases()
        .zip(cases())
        .filter(|(incremental, _)| incremental.name.contains(&filter))
        .peekable();
    if selected.peek().is_none() {
        return Err(format!("no workloads matched {filter:?}"));
    }
    if verify_only {
        println!("workload\tinitial_nodes\tstatus");
    } else {
        println!(
            "workload\tinitial_nodes\tframes\tfull_p50_us\tfull_p95_us\tincremental_p50_us\tincremental_p95_us\tfallback_frames"
        );
    }
    for (incremental, full) in selected {
        run(incremental, full, (!verify_only).then_some(frames));
    }
    Ok(())
}

fn main() -> ExitCode {
    match execute() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}\n{USAGE}");
            ExitCode::FAILURE
        }
    }
}
