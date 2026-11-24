# Batch topological order experiment

The layout solver builds dependency levels during ordered DFS, uses a ranked queue for dirty slots, and replays cached resize tapes. Keep that schedule for a stable graph. For structural changes, first try keeping the existing levels and assigning levels to arriving slots from their predecessors. A backwards insertion into a retained order is the case for batch Pearce–Kelly repair. A new acyclic graph admits a linear-time DFS or Kahn sort. The layout solver's ordered DFS also defines which provisional words cycles read. [Batch Pearce–Kelly paper](https://whileydave.com/publications/PK10_ACSC_preprint.pdf)

The trace sampled the first 24 edits from each of six browser, compositor, and CAD fixtures. Each layout matched an independently invalidated solve bit for bit. All recorded dependency edges ran strictly forward in the packed levels. No edge changed between two slots that stayed active, and no retained or returning slot changed its packed level. The rank check placed every arriving slot while pinning the retained levels.

| Fixture | Edits that changed edges | Edits with a backward insertion in the retained total order |
| --- | ---: | ---: |
| Browser article | 0 | 0 |
| Browser catalog | 16 | 0 |
| Compositor tiled split | 0 | 0 |
| Compositor floating windows | 6 | 0 |
| CAD dock | 0 | 0 |
| CAD assembly inspector | 24 | 7 |

The total-order experiment starts with a Kahn order of the initial graph. Slots that appear later start isolated, and deactivation removes edges while keeping positions available for reuse. On the seven CAD edits that needed repair in this model, batch Pearce–Kelly took **1.79 µs median and 3.48 µs p95**. Kahn restricted to the affected intervals took 3.38 and 7.15 µs. A full Kahn sort took 5.48 and 6.68 µs. The harness repeats the captured sequence 32 times, rotates algorithm order, and independently validates each resulting order. Timings cover ordering alone. Graph extraction, delta calculation, and layout run outside the timer.

The prototype accepts dense vertex IDs and the complete post-edit adjacency. It sorts the reported backwards edges by old tail position, discovers vertices inside overlapping affected intervals, and stages each shift. Only after all intervals succeed does it publish the order and its inverse. The tests check exhaustive four-vertex batches against Kahn, sequential mixed edits, cycles across a batch, rollback, and a deep bounded-stack traversal. Graph extraction, slot lifetime management, and the connection between a repaired order and bitwise layout equivalence belong to any future solver integration.

## Reproduce

Run from the repository root. The tracer applies to the checkpoint in a temporary checkout and exports dependencies from the production sizing request dispatcher after each solve. Set the rank option to include the packed levels.

```sh
cargo test --locked --manifest-path benchmarks/topological_order/Cargo.toml

experiment_path="$PWD/benchmarks/topological_order"
trace_root=$(mktemp -d)
git worktree add --detach "$trace_root/checkout" 1512601050acee1b8e614cd6c4e647c419664d56
git -C "$trace_root/checkout" apply "$experiment_path/trace.patch"
mkdir "$trace_root/traces"
LAYOUT_TRACE_DIRECTORY="$trace_root/traces" LAYOUT_TRACE_EDITS=24 LAYOUT_TRACE_RANKS=1 \
    cargo bench --locked --manifest-path "$trace_root/checkout/Cargo.toml" --bench real_workloads
python3 "$experiment_path/rank_admission.py" "$trace_root/traces"
cargo run --locked --release --manifest-path "$experiment_path/Cargo.toml" -- "$trace_root"/traces/*.tsv
```
