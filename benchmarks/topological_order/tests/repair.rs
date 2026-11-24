use std::collections::VecDeque;

use batch_topological_order::{RepairError, RepairScratch, RepairStats, TopologicalOrder};

fn static_kahn(graph: &[Vec<usize>]) -> Option<Vec<usize>> {
    let mut remaining = vec![0; graph.len()];
    for row in graph {
        for &to in row {
            remaining[to] += 1;
        }
    }
    let mut ready: VecDeque<usize> = (0..graph.len()).filter(|&id| remaining[id] == 0).collect();
    let mut ordered = Vec::new();
    while let Some(vertex) = ready.pop_front() {
        ordered.push(vertex);
        for &to in &graph[vertex] {
            remaining[to] -= 1;
            if remaining[to] == 0 {
                ready.push_back(to);
            }
        }
    }
    (ordered.len() == graph.len()).then_some(ordered)
}

fn assert_repair_matches_kahn(
    initial: &[usize],
    graph: &[Vec<usize>],
    additions: &[(usize, usize)],
    scratch: &mut RepairScratch,
) {
    let before = TopologicalOrder::new(initial.to_vec()).unwrap();
    let mut order = before.clone();
    let result = order.repair(graph, additions, scratch);
    if static_kahn(graph).is_none() {
        assert_eq!(
            result,
            Err(RepairError::Cycle),
            "{initial:?} {graph:?} {additions:?}"
        );
        assert_eq!(order, before);
        return;
    }

    let stats =
        result.unwrap_or_else(|error| panic!("{error:?}: {initial:?} {graph:?} {additions:?}"));
    let mut occupied = vec![false; graph.len()];
    for (position, &vertex) in order.order().iter().enumerate() {
        assert!(vertex < graph.len() && !occupied[vertex]);
        occupied[vertex] = true;
        assert_eq!(order.positions()[vertex], position);
    }
    assert!(occupied.iter().all(|&present| present));
    for (from, row) in graph.iter().enumerate() {
        for &to in row {
            assert!(
                order.positions()[from] < order.positions()[to],
                "{initial:?} {graph:?} {additions:?} {order:?}",
            );
        }
    }

    let mut affected = vec![false; graph.len()];
    for &(from, to) in additions {
        let left = before.positions()[to];
        let right = before.positions()[from];
        if left < right {
            affected[left..=right].fill(true);
        }
    }
    assert_eq!(
        stats.interval_vertices,
        affected.iter().filter(|&&present| present).count()
    );
    for (position, &inside) in affected.iter().enumerate() {
        if !inside {
            assert_eq!(order.order()[position], initial[position]);
        }
    }
}

#[test]
fn every_old_forward_graph_and_insertion_batch_for_four_vertices() {
    // Each old-order forward edge can be absent, retained, or added. An
    // old-order backward edge can only be absent or added. Vertex renaming
    // gives the same graph family for any old order.
    let orientations = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
    let mut scratch = RepairScratch::default();
    for forward in 0..3usize.pow(6) {
        for backward in 0..1 << 6 {
            let mut remaining = forward;
            let mut graph = vec![Vec::new(); 4];
            let mut additions = Vec::new();
            for (bit, &(a, b)) in orientations.iter().enumerate() {
                match remaining % 3 {
                    1 => graph[a].push(b),
                    2 => {
                        graph[a].push(b);
                        additions.push((a, b));
                    }
                    _ => {}
                }
                remaining /= 3;
                if backward & (1 << bit) != 0 {
                    graph[b].push(a);
                    additions.push((b, a));
                }
            }
            assert_repair_matches_kahn(&[0, 1, 2, 3], &graph, &additions, &mut scratch);
        }
    }
}

#[test]
fn independently_permuted_orders_and_inserted_edges() {
    let mut state = 0x843b_794a_b16f_1b57u64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut scratch = RepairScratch::default();
    for _ in 0..5_000 {
        let count = 5 + (next() % 16) as usize;
        let mut initial: Vec<_> = (0..count).collect();
        for at in (1..count).rev() {
            initial.swap(at, (next() % (at as u64 + 1)) as usize);
        }
        let mut graph = vec![Vec::new(); count];
        let mut additions = Vec::new();
        for (rank, &from) in initial.iter().enumerate() {
            for (other, &to) in initial.iter().enumerate() {
                if rank == other {
                    continue;
                }
                let flags = next() % 100;
                if rank < other && flags < 12 {
                    graph[from].push(to);
                } else if flags < 16 && (rank < other || flags < 4) {
                    graph[from].push(to);
                    additions.push((from, to));
                }
            }
        }
        for row in &mut graph {
            for at in (1..row.len()).rev() {
                row.swap(at, (next() % (at as u64 + 1)) as usize);
            }
        }
        assert_repair_matches_kahn(&initial, &graph, &additions, &mut scratch);
        if !additions.is_empty() {
            let mut first = TopologicalOrder::new(initial.clone()).unwrap();
            let mut second = TopologicalOrder::new(initial).unwrap();
            let expected = first.repair(&graph, &additions, &mut scratch);
            let duplicate = additions[0];
            additions.reverse();
            additions.push(duplicate);
            let actual = second.repair(&graph, &additions, &mut scratch);
            assert_eq!(actual.is_ok(), expected.is_ok());
            assert_eq!(first, second);
        }
    }
}

#[test]
fn forward_only_checks_seed_endpoints_and_keeps_the_unchanged_order() {
    let initial = vec![2, 0, 3, 1];
    let graph = vec![vec![3], vec![], vec![0, 1], vec![1]];
    let mut order = TopologicalOrder::new(initial.clone()).unwrap();
    let mut scratch = RepairScratch::default();
    assert_eq!(
        order.repair(&graph, &[(2, 1), (3, 1)], &mut scratch),
        Ok(RepairStats::default())
    );
    assert_eq!(order.order(), initial);
    assert_eq!(order.validate_graph(&graph), Ok(()));
}

#[test]
fn merges_overlapping_intervals_and_keeps_disjoint_intervals_separate() {
    let initial: Vec<_> = (0..12).collect();
    let mut graph = vec![Vec::new(); initial.len()];
    graph[2].extend([3, 10]);
    graph[3].push(10);
    graph[6].push(2);
    graph[8].push(4);
    graph[11].push(10);
    let additions = [(6, 2), (11, 10), (8, 4)];
    let mut order = TopologicalOrder::new(initial.clone()).unwrap();
    let mut scratch = RepairScratch::default();
    assert_repair_matches_kahn(&initial, &graph, &additions, &mut scratch);
    let stats = order.repair(&graph, &additions, &mut scratch).unwrap();
    assert_eq!(stats.regions, 2);
    assert_eq!(stats.interval_vertices, 9);
    for position in [0, 1, 9] {
        assert_eq!(order.order()[position], position);
    }
}

#[test]
fn detects_cycle_created_only_by_combining_two_insertions() {
    let before = vec![vec![1], vec![], vec![3], vec![]];
    let mut graph = before.clone();
    graph[1].push(2);
    assert!(static_kahn(&graph).is_some());
    graph = before;
    graph[3].push(0);
    assert!(static_kahn(&graph).is_some());
    graph[1].push(2);
    assert_repair_matches_kahn(
        &[0, 1, 2, 3],
        &graph,
        &[(1, 2), (3, 0)],
        &mut RepairScratch::default(),
    );
}

#[test]
fn a_late_cycle_or_invalid_edge_leaves_earlier_regions_uncommitted() {
    let before = TopologicalOrder::new((0..8).collect()).unwrap();
    let mut order = before.clone();
    let mut scratch = RepairScratch::default();
    let mut graph = vec![Vec::new(); 8];
    graph[0].push(1);
    graph[1].push(0);
    graph[7].push(5);
    let additions = [(1, 0), (7, 5)];
    assert_eq!(
        order.repair(&graph, &additions, &mut scratch),
        Err(RepairError::Cycle)
    );
    assert_eq!(order, before);
    graph[0][0] = 8;
    assert_eq!(
        order.repair(&graph, &additions, &mut scratch),
        Err(RepairError::UnknownVertex(8))
    );
    assert_eq!(order, before);
    graph[0].clear();
    assert_eq!(
        order
            .repair(&graph, &additions, &mut scratch)
            .unwrap()
            .regions,
        2
    );
    assert_eq!(order.validate_graph(&graph), Ok(()));
}

#[test]
fn rejects_invalid_permutations_and_reported_endpoints() {
    assert_eq!(
        TopologicalOrder::new(vec![0, 0]),
        Err(RepairError::InvalidOrder {
            vertex: 0,
            position: 1
        })
    );
    assert_eq!(
        TopologicalOrder::new(vec![0, 2]),
        Err(RepairError::InvalidOrder {
            vertex: 2,
            position: 1
        })
    );
    let original = TopologicalOrder::new(vec![0, 1]).unwrap();
    let mut order = original.clone();
    let mut scratch = RepairScratch::default();
    let graph = vec![vec![1], vec![]];
    assert_eq!(
        order.repair(&graph, &[(2, 0)], &mut scratch),
        Err(RepairError::UnknownVertex(2))
    );
    assert_eq!(
        order.repair(&graph, &[(0, 2)], &mut scratch),
        Err(RepairError::UnknownVertex(2))
    );
    assert_eq!(
        order.repair(&graph, &[(1, 1)], &mut scratch),
        Err(RepairError::Cycle)
    );
    assert_eq!(
        order.repair(&graph[..1], &[], &mut scratch),
        Err(RepairError::WrongVertexCount {
            expected: 2,
            actual: 1
        })
    );
    assert_eq!(order, original);
    assert_eq!(
        TopologicalOrder::new(vec![1, 0])
            .unwrap()
            .validate_graph(&graph),
        Err(RepairError::OrderViolation { from: 0, to: 1 })
    );
}

#[test]
fn deep_repair_uses_a_reusable_explicit_stack() {
    let count = 25_000;
    let mut graph = vec![Vec::new(); count];
    for (from, row) in graph[..count - 2].iter_mut().enumerate() {
        row.push(from + 1);
    }
    graph[count - 1].push(0);
    let initial: Vec<_> = (0..count).collect();
    let thread = std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            assert_repair_matches_kahn(
                &initial,
                &graph,
                &[(count - 1, 0)],
                &mut RepairScratch::default(),
            );
        })
        .unwrap();
    thread.join().unwrap();
}

#[test]
fn repeated_random_batches_after_deletion_preserve_the_last_valid_order() {
    const COUNT: usize = 18;
    let mut graph = vec![Vec::new(); COUNT];
    let mut order = TopologicalOrder::new((0..COUNT).collect()).unwrap();
    let mut scratch = RepairScratch::default();
    let mut state = 0x136b_4c95_78c3_1c9bu64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..2_000 {
        let mut candidate = graph.clone();
        let before = order.clone();
        for _ in 0..3 {
            let from = (next() as usize) % COUNT;
            if !candidate[from].is_empty() {
                let slot = (next() as usize) % candidate[from].len();
                candidate[from].swap_remove(slot);
            }
        }

        let mut additions = Vec::new();
        for _ in 0..(1 + next() % 5) {
            let from = (next() as usize) % COUNT;
            let to = (next() as usize) % COUNT;
            if from != to && !candidate[from].contains(&to) {
                candidate[from].push(to);
                additions.push((from, to));
            }
        }
        let result = order.repair(&candidate, &additions, &mut scratch);
        if static_kahn(&candidate).is_some() {
            assert!(result.is_ok());
            order.validate_graph(&candidate).unwrap();
            graph = candidate;
        } else {
            assert_eq!(result, Err(RepairError::Cycle));
            assert_eq!(order, before);
        }
    }
}
