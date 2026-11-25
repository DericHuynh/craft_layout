# Batch topological order experiment

The default layout solver builds dependency levels during ordered DFS, uses a ranked queue for dirty slots, and replays cached resize tapes. The trace experiment asks how often a structural edit needs to move a slot in an existing order. The layout pilot below uses the published batch algorithm to build and maintain its own schedule. [Batch Pearce–Kelly paper](https://whileydave.com/publications/PK10_ACSC_preprint.pdf)

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

The shared ordering implementation accepts dense vertex IDs and the complete post-edit adjacency. It sorts backwards edges by decreasing old tail position, runs the published bounded DFS inside overlapping affected intervals, and stages each shift. It publishes the order and inverse after every interval succeeds. The kernel tests check exhaustive four-vertex batches against Kahn, sequential mixed edits, cycles across a batch, rollback, and a deep bounded-stack traversal. [Ordering implementation](../../src/batch_order.rs)

## Layout pilot

Enable the opt-in `batch-pilot` feature and call `LayoutTree::solve_layout_batch`, `solve_layout_batch_with_measure`, or `solve_layout_batch_with_measurers`. Both owned entry points share full sizing and placement and select preparation according to whether previous sizing records are available. On a first Batch solve, the sizing pass can call measurers while detecting a cycle. A cycle rejects placement and preserves published rectangles and warnings. The first successful solve reports zero Batch work. Idle calls reuse its output, and the Batch workspace is allocated at handoff. [Shared owned solve](../../src/full_layout.rs) · [Owned entry point](../../src/layout_tree.rs)

The first later solve that needs work captures the current sizing requests, uses batch Pearce–Kelly from an edgeless order, and evaluates the captured graph. Later structural edits recapture the graph using retained buffers and repair the previous order. The graph stores only nonempty rows when there are at least 256 slots and at most 32 captured edges. Both adjacency representations preserve reader order within each producer row and emit the same backward seeds for repair.

When repair is required, the kernel merges overlapping affected intervals and consumes seeds in decreasing old tail rank. Its bounded DFS assigns a vertex to the highest tail that reaches it. The shift places each group after that tail in reverse DFS postorder while preserving the relative order of untouched vertices. A bounded search checks an edge back to the seed's tail before applying the exclusive rank bound, so a two-edge cycle is detected. Both rank maps are published after all intervals succeed. [Ordering kernel](../../src/batch_order.rs)

Eligible same-parent Free and Stack reorders keep the sizing graph. Appending an independent tail subtree repairs its new slots against the resident order, and removal isolates those slots for reuse. Appending the same shape at the same boundary can reuse the order and still measures the new nodes. Visibility changes use the existing schedule when it covers the affected subtrees. A cold Stack or Free tree can include hidden requests in that schedule and retry with visible requests if the larger graph is cyclic. A cycle among the live requests returns `BatchLayoutError::Cycle` before replacing the order or publishing rectangles.

Viewport, content, and declaration edits mark affected slots in a bitset indexed by execution rank. The pilot evaluates dirty producers in order and stops propagation at unchanged scalar results. Ordinary Block resizes compile width and height sweeps from the repaired order and keep collapsed margins in stable entries. Eligible viewport states and independent Width-grid subgraphs reuse bounded snapshots when the relevant inputs match bit for bit and measurement data is still current. Stable edits can place only affected branches. Dense Stack placement uses native cursor arithmetic and can batch pixel snapping.

For a forced warm solve, the pilot runs a compact copy of the retained order that omits prepared pixel slots. Consecutive Fill and percentage/aspect-ratio producers can share current inputs across siblings. Compiled intrinsic size and Fill reductions preserve sibling order. Eligible Wrap groups recompute line breaks and cross extents for the current solve, then place from those line metrics. The unrounded Stack placement plan streams leaves in document order and supports margins.

The workload tests and layout regression tests check exact rectangle bits against an independently invalidated full solve. Verus checks the finite percentage/aspect-ratio arithmetic and the four sizing words written by the admitted ratio run. The pilot's graph capture, repair, and end-to-end equivalence remain open. [Solver implementation](../../src/layout_tree/batch.rs) · [Ratio run proof](../../src/layout_tree/batch/warm/ratio.rs) · [Layout regression tests](../../tests/batch_layout.rs) · [Workload commands](../real_workloads/README.md#batch-pearcekelly-pilot)

## Reproduce

Run from the repository root. The tracer applies to the checkpoint in a temporary checkout and exports dependencies from the production sizing request dispatcher after each solve. Set the rank option to include the packed levels.

```sh
cargo test --locked --manifest-path benchmarks/topological_order/Cargo.toml
cargo test --locked --release --manifest-path benchmarks/topological_order/Cargo.toml \
    --test repair every_five_vertex_graph_on_the_initial_append_path -- --ignored

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
