use batch_topological_order::{RepairScratch, TopologicalOrder};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::hint::black_box;
use std::path::Path;
use std::time::Instant;

type Edge = (usize, usize);

#[derive(Default)]
struct RawFrame {
    vertices: BTreeSet<u64>,
    edges: BTreeSet<(u64, u64)>,
}

struct Frame {
    vertices: BTreeSet<usize>,
    edges: BTreeSet<Edge>,
    outgoing: Vec<Vec<usize>>,
}

fn trace(path: &Path) -> Vec<Frame> {
    let input = fs::read_to_string(path).unwrap();
    let mut raw = Vec::<RawFrame>::new();
    for line in input.lines() {
        let fields: Vec<_> = line.split_whitespace().collect();
        match fields.as_slice() {
            [] => {}
            [comment, ..] if comment.starts_with('#') => {}
            ["frame", _] => raw.push(RawFrame::default()),
            ["v", id] => {
                raw.last_mut().unwrap().vertices.insert(id.parse().unwrap());
            }
            ["e", producer, reader] => {
                raw.last_mut()
                    .unwrap()
                    .edges
                    .insert((producer.parse().unwrap(), reader.parse().unwrap()));
            }
            _ => panic!("invalid trace row {line}"),
        }
    }
    let all = raw
        .iter()
        .flat_map(|frame| frame.vertices.iter().copied())
        .collect::<BTreeSet<_>>();
    let ids: BTreeMap<_, _> = all
        .into_iter()
        .enumerate()
        .map(|(index, id)| (id, index))
        .collect();
    raw.into_iter()
        .map(|frame| {
            let vertices = frame
                .vertices
                .into_iter()
                .map(|id| ids[&id])
                .collect::<BTreeSet<_>>();
            let edges = frame
                .edges
                .into_iter()
                .map(|(u, v)| (ids[&u], ids[&v]))
                .collect::<BTreeSet<_>>();
            let mut outgoing = vec![Vec::new(); ids.len()];
            for &(u, v) in &edges {
                assert!(
                    vertices.contains(&u) && vertices.contains(&v),
                    "{path:?}: edge references an inactive slot"
                );
                outgoing[u].push(v);
            }
            Frame {
                vertices,
                edges,
                outgoing,
            }
        })
        .collect()
}

#[derive(Default)]
struct Kahn {
    indegree: Vec<usize>,
    ready: Vec<usize>,
    sorted: Vec<usize>,
}

impl Kahn {
    fn sort(
        &mut self,
        outgoing: &[Vec<usize>],
        order: &[usize],
        positions: Option<&[usize]>,
        first: usize,
        last: usize,
    ) -> bool {
        let in_scope =
            |v: usize| positions.is_none_or(|positions| (first..last).contains(&positions[v]));
        self.indegree.resize(outgoing.len(), 0);
        for &node in &order[first..last] {
            self.indegree[node] = 0;
        }
        for &node in &order[first..last] {
            for &reader in &outgoing[node] {
                if in_scope(reader) {
                    self.indegree[reader] += 1;
                }
            }
        }
        self.ready.clear();
        self.ready.extend(
            order[first..last]
                .iter()
                .copied()
                .filter(|&node| self.indegree[node] == 0),
        );
        self.sorted.clear();
        let mut head = 0;
        while let Some(&node) = self.ready.get(head) {
            self.sorted.push(node);
            head += 1;
            for &reader in &outgoing[node] {
                if in_scope(reader) {
                    self.indegree[reader] -= 1;
                    if self.indegree[reader] == 0 {
                        self.ready.push(reader);
                    }
                }
            }
        }
        self.sorted.len() == last - first
    }
}

#[derive(Default)]
struct IntervalKahn {
    kahn: Kahn,
    ranges: Vec<(usize, usize)>,
    pending: Vec<(usize, usize)>,
}

impl IntervalKahn {
    fn repair(
        &mut self,
        order: &mut [usize],
        positions: &mut [usize],
        graph: &[Vec<usize>],
        additions: &[Edge],
    ) -> bool {
        self.ranges.clear();
        self.ranges.extend(additions.iter().filter_map(|&(u, v)| {
            (positions[u] >= positions[v]).then_some((positions[v], positions[u] + 1))
        }));
        self.ranges.sort_unstable();
        self.pending.clear();
        let mut at = 0;
        while let Some(&(first, mut last)) = self.ranges.get(at) {
            at += 1;
            while let Some(&(other_first, other_last)) = self.ranges.get(at) {
                if other_first >= last {
                    break;
                }
                last = last.max(other_last);
                at += 1;
            }
            if !self.kahn.sort(graph, order, Some(positions), first, last) {
                return false;
            }
            self.pending.extend(
                self.kahn
                    .sorted
                    .iter()
                    .enumerate()
                    .map(|(i, &node)| (first + i, node)),
            );
        }
        for &(i, node) in &self.pending {
            order[i] = node;
            positions[node] = i;
        }
        true
    }
}

fn positions(order: &[usize]) -> Vec<usize> {
    let mut positions = vec![0; order.len()];
    for (i, &node) in order.iter().enumerate() {
        positions[node] = i;
    }
    positions
}

fn validate(order: &[usize], edges: &BTreeSet<Edge>) {
    assert_eq!(
        order.iter().copied().collect::<BTreeSet<_>>().len(),
        order.len()
    );
    let positions = positions(order);
    assert!(edges.iter().all(|&(u, v)| positions[u] < positions[v]));
}

#[derive(Default)]
struct Timings {
    full: Vec<u128>,
    interval: Vec<u128>,
    batch: Vec<u128>,
}

impl Timings {
    fn record(&mut self, full: u128, interval: u128, batch: u128) {
        self.full.push(full);
        self.interval.push(interval);
        self.batch.push(batch);
    }
}

fn summarize(times: &mut [u128]) -> String {
    if times.is_empty() {
        return "-".to_owned();
    }
    times.sort_unstable();
    let percentile =
        |percent: usize| times[(times.len() * percent).div_ceil(100) - 1] as f64 / 1_000.0;
    format!("{:.3}/{:.3}", percentile(50), percentile(95))
}

fn evaluate(path: &Path, repetitions: usize) {
    let frames = trace(path);
    let count = frames[0].outgoing.len();
    let identity = (0..count).collect::<Vec<_>>();
    let additions = frames
        .windows(2)
        .map(|pair| {
            pair[1]
                .edges
                .difference(&pair[0].edges)
                .copied()
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let changed = frames
        .windows(2)
        .filter(|pair| pair[0].edges != pair[1].edges)
        .count();
    let vertex_changed = frames
        .windows(2)
        .filter(|pair| pair[0].vertices != pair[1].vertices)
        .count();
    let retained_edge_changes = frames
        .windows(2)
        .flat_map(|pair| {
            let before = &pair[0];
            let after = &pair[1];
            before
                .edges
                .symmetric_difference(&after.edges)
                .filter(|&&(u, v)| {
                    before.vertices.contains(&u)
                        && before.vertices.contains(&v)
                        && after.vertices.contains(&u)
                        && after.vertices.contains(&v)
                })
        })
        .count();
    let removed: usize = frames
        .windows(2)
        .map(|pair| pair[0].edges.difference(&pair[1].edges).count())
        .sum();
    let mut changed_times = Timings::default();
    let mut repair_times = Timings::default();
    let mut cycles = 0;
    let mut repair_batches = 0;
    let mut backward_edges = 0;
    let mut moved = 0;

    for repetition in 0..repetitions {
        let mut kahn = Kahn::default();
        let mut interval = IntervalKahn::default();
        let mut pk_scratch = RepairScratch::default();
        let mut pk = None::<TopologicalOrder>;
        let mut interval_order = Vec::new();
        let mut interval_positions = Vec::new();
        for (i, frame) in frames.iter().enumerate() {
            let mut compare_full = || {
                let t = Instant::now();
                let dag =
                    black_box(kahn.sort(black_box(&frame.outgoing), &identity, None, 0, count));
                (dag, t.elapsed().as_nanos())
            };
            if let (Some(batch), Some(order)) = (i.checked_sub(1), pk.as_mut()) {
                let old = order.order().to_vec();
                let old_positions = positions(&old);
                let backward = additions[batch]
                    .iter()
                    .filter(|&&(u, v)| old_positions[u] >= old_positions[v])
                    .count();
                let mut compare_pk = || {
                    let t = Instant::now();
                    let outcome = black_box(order.repair(
                        black_box(&frame.outgoing),
                        black_box(&additions[batch]),
                        &mut pk_scratch,
                    ));
                    (outcome, t.elapsed().as_nanos())
                };
                let mut compare_interval = || {
                    let t = Instant::now();
                    let ok = black_box(interval.repair(
                        &mut interval_order,
                        &mut interval_positions,
                        black_box(&frame.outgoing),
                        black_box(&additions[batch]),
                    ));
                    (ok, t.elapsed().as_nanos())
                };
                let ((dag, full_ns), (repaired, pk_ns), (interval_ok, interval_ns)) =
                    match (repetition + i) % 3 {
                        0 => (compare_full(), compare_pk(), compare_interval()),
                        1 => {
                            let pk = compare_pk();
                            let interval = compare_interval();
                            (compare_full(), pk, interval)
                        }
                        _ => {
                            let interval = compare_interval();
                            (compare_full(), compare_pk(), interval)
                        }
                    };
                assert_eq!(repaired.is_ok(), dag, "{path:?} frame {i}: {repaired:?}");
                assert_eq!(interval_ok, dag, "{path:?} frame {i}");
                if dag {
                    validate(order.order(), &frame.edges);
                    validate(&interval_order, &frame.edges);
                    if frame.edges != frames[batch].edges {
                        changed_times.record(full_ns, interval_ns, pk_ns);
                    }
                    if backward != 0 {
                        repair_times.record(full_ns, interval_ns, pk_ns);
                        if repetition == 0 {
                            repair_batches += 1;
                            backward_edges += backward;
                            moved += old
                                .iter()
                                .zip(order.order())
                                .filter(|(a, b)| a != b)
                                .count();
                        }
                    }
                } else {
                    assert_eq!(order.order(), old);
                    pk = None;
                }
                if !dag && repetition == 0 {
                    cycles += 1;
                }
            } else {
                let (dag, _) = compare_full();
                if dag {
                    interval_order = kahn.sorted.clone();
                    interval_positions = positions(&interval_order);
                    pk = Some(TopologicalOrder::new(kahn.sorted.clone()).unwrap());
                } else if repetition == 0 {
                    cycles += 1;
                }
            }
        }
    }

    println!(
        "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
        path.file_stem().unwrap().to_string_lossy(),
        frames.len() - 1,
        count,
        vertex_changed,
        changed,
        cycles,
        additions.iter().map(Vec::len).sum::<usize>(),
        removed,
        retained_edge_changes,
        repair_batches,
        backward_edges,
        moved,
        summarize(&mut changed_times.full),
        summarize(&mut changed_times.interval),
        summarize(&mut changed_times.batch),
        summarize(&mut repair_times.full),
        summarize(&mut repair_times.interval),
        summarize(&mut repair_times.batch)
    );
}

fn main() {
    println!(
        "fixture\tedits\tunion_slots\tslot_delta_frames\tedge_delta_frames\tcyclic_frames\tadded_edges\tremoved_edges\tretained_edge_changes\tpk_repair_frames\tbackward_edges\tmoved_positions\tchanged_full_p50/p95_us\tchanged_interval_p50/p95_us\tchanged_pk2_p50/p95_us\trepair_full_p50/p95_us\trepair_interval_p50/p95_us\trepair_pk2_p50/p95_us"
    );
    for input in std::env::args_os().skip(1) {
        evaluate(Path::new(&input), 32);
    }
}
