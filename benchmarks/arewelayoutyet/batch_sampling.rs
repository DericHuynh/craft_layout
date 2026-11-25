//! Paired full-solve timings for the pinned PanGUI peer adapters.

use keru_layout::BatchLayoutStats;
use std::hint::black_box;
use std::time::{Duration, Instant};

use crate::keru_layout_helpers::KeruLayoutTree;
use crate::owned_adapter::OwnedKeruLayoutTree;
use crate::pangui_template::LayoutNode;
use crate::root_size;

const SAMPLES: usize = 21;
const SAMPLE_NS: u128 = 4_000_000;

pub(super) struct BenchmarkId<'a> {
    workload: &'a str,
    engine: &'a str,
}

impl<'a> BenchmarkId<'a> {
    pub(super) fn new(workload: &'a str, engine: &'a str) -> Self {
        Self { workload, engine }
    }
}

struct References {
    dense: KeruLayoutTree,
    default: OwnedKeruLayoutTree,
    batch: OwnedKeruLayoutTree,
}

impl References {
    fn new(workload: &str, root: &LayoutNode) -> Self {
        let width = root_size(&root.width);
        let height = root_size(&root.height);
        let mut dense = KeruLayoutTree::new(root, width, height).expect("build dense Keru tree");
        let mut default = OwnedKeruLayoutTree::new(root, width, height).expect("build owned tree");
        let mut batch = OwnedKeruLayoutTree::new(root, width, height).expect("build batch tree");

        let dense_ns = timed(|| dense.compute_layout()).as_nanos();
        let default_ns = timed(|| default.compute_default()).as_nanos();
        let (first, stats) = timed_batch(&mut batch, workload, "first");
        assert_eq!(
            stats,
            BatchLayoutStats::default(),
            "{workload} first solve ran Batch work",
        );
        let mut references = Self {
            dense,
            default,
            batch,
        };
        references.verify();

        references.batch.mark_all_dirty();
        let (handoff, stats) = timed_batch(&mut references.batch, workload, "handoff");
        assert!(stats.rebuilt_graph, "{workload} handoff reused a graph");
        references.verify();
        eprintln!(
            "{workload}\t{}\t{dense_ns}\t{default_ns}\t{}\t{}\t{:016x}\t{}\t{}\t{}",
            references.dense.node_count(),
            first.as_nanos(),
            handoff.as_nanos(),
            references.dense.geometry_hash(),
            stats.slots,
            stats.edges,
            stats.repaired_intervals,
        );

        references.dense_sample();
        references.default_sample();
        references.batch_sample(workload);
        references.verify();
        references
    }

    fn verify(&self) {
        self.default.assert_matches_dense(&self.dense);
        self.batch.assert_matches_dense(&self.dense);
    }

    fn dense_sample(&mut self) -> Duration {
        self.dense.mark_all_dirty();
        timed(|| self.dense.compute_layout())
    }

    fn default_sample(&mut self) -> Duration {
        self.default.mark_all_dirty();
        timed(|| self.default.compute_default())
    }

    fn batch_sample(&mut self, workload: &str) -> Duration {
        batch_sample(&mut self.batch, workload)
    }
}

pub(super) struct PairGroup<'a> {
    references: &'a mut References,
}

impl PairGroup<'_> {
    pub(super) fn bench_function(
        &mut self,
        id: BenchmarkId<'_>,
        run: impl FnOnce(&mut PairBencher<'_>),
    ) {
        run(&mut PairBencher {
            id,
            references: self.references,
        });
    }
}

pub(super) struct PairBencher<'a> {
    id: BenchmarkId<'a>,
    references: &'a mut References,
}

fn timed<T>(run: impl FnOnce() -> T) -> Duration {
    let start = Instant::now();
    black_box(run());
    start.elapsed()
}

fn timed_batch(
    tree: &mut OwnedKeruLayoutTree,
    workload: &str,
    phase: &str,
) -> (Duration, BatchLayoutStats) {
    let start = Instant::now();
    let result = black_box(tree.compute_batch());
    let elapsed = start.elapsed();
    let stats = result.unwrap_or_else(|error| panic!("{workload} {phase} batch: {error:?}"));
    (elapsed, stats)
}

fn batch_sample(tree: &mut OwnedKeruLayoutTree, workload: &str) -> Duration {
    tree.mark_all_dirty();
    let (elapsed, stats) = timed_batch(tree, workload, "warm");
    assert!(!stats.rebuilt_graph, "{workload} recaptured a stable graph");
    elapsed
}

fn iterations(run: &mut dyn FnMut() -> Duration) -> usize {
    let mut warm = std::array::from_fn::<_, 5, _>(|_| run().as_nanos().max(1));
    warm.sort_unstable();
    (SAMPLE_NS / warm[2]).clamp(1, 20_000) as usize
}

fn sample(run: &mut dyn FnMut() -> Duration, iterations: usize) -> f64 {
    run();
    let elapsed: Duration = (0..iterations).map(|_| run()).sum();
    elapsed.as_nanos() as f64 / iterations as f64
}

pub(super) fn iter_timed(bencher: &mut PairBencher<'_>, mut peer: impl FnMut() -> Duration) {
    let BenchmarkId { workload, engine } = bencher.id;
    let References {
        dense,
        default,
        batch,
    } = &mut *bencher.references;
    let mut modes: [&mut dyn FnMut() -> Duration; 4] = [
        &mut || {
            dense.mark_all_dirty();
            timed(|| dense.compute_layout())
        },
        &mut || {
            default.mark_all_dirty();
            timed(|| default.compute_default())
        },
        &mut || batch_sample(batch, workload),
        &mut peer,
    ];
    let iterations = std::array::from_fn::<_, 4, _>(|index| iterations(modes[index]));
    for round in 0..SAMPLES {
        let mut elapsed = [0.0; 4];
        for offset in 0..modes.len() {
            let mode = (round + offset) % modes.len();
            elapsed[mode] = sample(modes[mode], iterations[mode]);
        }
        let [dense, default, batch, peer] = elapsed;
        println!("{workload}\t{engine}\t{round}\t{dense:.3}\t{default:.3}\t{batch:.3}\t{peer:.3}");
    }
}

pub(super) fn bench_layout<T>(
    bencher: &mut PairBencher<'_>,
    tree: &mut Option<T>,
    build: impl FnOnce() -> T,
    mut invalidate: impl FnMut(&mut T),
    mut layout: impl FnMut(&mut T),
) {
    let tree = tree.get_or_insert_with(build);
    iter_timed(bencher, || {
        invalidate(tree);
        timed(|| layout(tree))
    });
}

pub(super) fn run(
    templates: Vec<(String, LayoutNode)>,
    run_peers: impl Fn(&mut PairGroup<'_>, &str, &LayoutNode),
) {
    let filter = std::env::var("PANGUI_FILTER").unwrap_or_default();
    let verify_only = std::env::var_os("PANGUI_VERIFY_ONLY").is_some();
    if !verify_only {
        println!("workload\tengine\tsample\tdense_ns\tdefault_ns\tbatch_ns\tpeer_ns");
    }
    eprintln!(
        "workload\tnodes\tdense_ns\tdefault_ns\tbatch_ns\thandoff_ns\tgeometry_hash\tslots\tedges\trepaired_intervals"
    );
    let mut matched = false;
    for (name, root) in templates {
        if !name.contains(&filter) {
            continue;
        }
        matched = true;
        let mut references = References::new(&name, &root);
        if !verify_only {
            let mut group = PairGroup {
                references: &mut references,
            };
            run_peers(&mut group, &name, &root);
            references.verify();
        }
    }
    assert!(matched, "no PanGUI templates matched {filter:?}");
}
