# Application layout benchmarks

These fixtures model browser pages, Linux compositor workspaces, and CAD editor panels. Each workload replays a deterministic sequence of UI events through the public `LayoutTree` API. Text uses the library's monospace measurer.

```sh
cargo bench --locked --bench real_workloads
cargo bench --locked --bench real_workloads -- --filter browser/ --frames 240
cargo bench --locked --bench real_workloads -- --verify-only
```

| Workload | Layout and edits |
| --- | --- |
| `browser/article_reflow` | Long article with Block flow, wrapping paragraphs, captions, and auto margins. Replays paragraph edits and desktop-to-mobile viewport changes. |
| `browser/product_catalog` | Responsive product grid and wrapping filter bar. Changes the viewport and filters out-of-stock cards. |
| `compositor/tiled_split_resize` | Panels and nested splits contain 24 decorated clients. Drags a split and resizes the output at fractional pixel scale. |
| `compositor/floating_drag_and_raise` | Eighteen floating clients have fixed geometry and decorations. Drags and raises windows and toggles a popup at fractional pixel scale. |
| `cad/docked_viewport` | A wrapping command ribbon, weighted drawing views, and model and property panels. Resizes a dock and the window and changes the active projection label. |
| `cad/assembly_inspector` | Assembly tree and grouped property inspector. Expands and collapses subassemblies, reorders a component, and adds and removes inspection details. |

The runner builds two equivalent trees per workload. Both receive the same edits. One uses normal incremental layout, and the other is explicitly invalidated before each solve. The benchmark alternates solve order and measures 120 frames by default. Construction, edits, invalidation, and geometry inspection are outside the timer.

The TSV reports the initial node count including the root and disabled nodes, median and 95th-percentile solve latency in microseconds, and the number of incremental frames that fell back to a full solve. The median averages the two middle samples for even sample counts. The 95th percentile uses nearest rank. The initial solve, 24 warmup frames, and the final measured frame compare tree order, rectangle availability, and exact rectangle bits with the forced-full reference. `--verify-only` runs the initial and warmup checks.

## Batch Pearce–Kelly pilot

Use the same fixtures to compare the opt-in batch scheduler with both the default incremental solver and a forced-full solve. In a pilot run the `incremental_p50_us` and `incremental_p95_us` columns measure the batch scheduler. A graph rebuild is part of the batch path.

```sh
cargo bench --locked --features batch-pilot --bench real_workloads
cargo bench --locked --features batch-pilot --bench real_workloads -- --batch-pilot
cargo bench --locked --features batch-pilot --bench real_workloads -- --batch-pilot --verify-only
```

Pilot verification compares the initial solve, 24 warmup frames, and another 120 frames per workload by default. Use `--frames` to change the number of additional checks. A difference in tree order, rectangle availability, or rectangle bits fails the run. [Pilot design](../topological_order/README.md#layout-pilot)

The table records the pilot before the tail latency optimizations. It reports the median p50 from five 480-frame runs on one x86-64 logical CPU. These runs use the full-feature fixtures from the application benchmarks. Values are solve times in microseconds.

| Workload | Default incremental p50 | Batch pilot p50 | Forced full p50 |
| --- | ---: | ---: | ---: |
| `browser/article_reflow` | 6.27 | 14.57 | 36.44 |
| `browser/product_catalog` | 29.28 | 40.94 | 119.60 |
| `compositor/tiled_split_resize` | 5.18 | 4.26 | 44.32 |
| `compositor/floating_drag_and_raise` | 1.97 | 1.12 | 29.36 |
| `cad/docked_viewport` | 9.85 | 10.09 | 38.91 |
| `cad/assembly_inspector` | 9.88 | 12.32 | 39.36 |

The geometric mean of the pilot-to-default latency ratios is 1.12×, down from 4.55× in the first pilot. General structural edits recapture the graph, and stable edits can retain both the sizing order and unaffected rectangles.

### Profile latency by event

Use the full-feature fixtures to compare the tuned default solver, batch solver, and forced-full solver on each step of the edit cycle. The three modes run in rotating order in the same process. The `all` rows summarize each run. Numbered phases are the zero-based edit cycle indices from the fixture source. Each row reports p50 and p95, default fallback counts, batch graph rebuild and repair counts, and the range of computed sizing producers.

```sh
taskset -c 4 cargo bench --locked --features batch-pilot --bench real_workloads -- \
  --phase-timings --frames 2400 --runs 9 > phase-timings.tsv
python3 benchmarks/real_workloads/summarize_phases.py phase-timings.tsv
cargo bench --locked --features batch-pilot --bench real_workloads -- \
  --batch-pilot --verify-only --frames 1440
```

Use `--filter` to restrict the run to a workload or application family. The summary reports batch p95 divided by default p50 and by batch p50 using median paired ratios. Its `--phases` option includes individual edit phases. The runner checks rectangle bits and tree shape on setup, warmup, and the last measured frame. Run the separate `--batch-pilot --verify-only` mode to compare every frame.

The results below use nine paired runs of 2,400 measured frames pinned to one x86-64 logical CPU. Latencies are medians of per-run percentiles in microseconds. The 1.20× bound holds on all six workloads against default p50 and on three workloads against the batch solver's own p50.

| Workload | Default p50 | Batch p50 | Batch p95 | p95 / default p50 | p95 / batch p50 |
| --- | ---: | ---: | ---: | ---: | ---: |
| `browser/article_reflow` | 6.343 | 5.693 | 6.668 | 1.045× | 1.180× |
| `browser/product_catalog` | 29.537 | 9.378 | 16.124 | 0.545× | 1.722× |
| `compositor/tiled_split_resize` | 5.276 | 4.457 | 5.058 | 0.963× | 1.142× |
| `compositor/floating_drag_and_raise` | 2.476 | 1.228 | 1.588 | 0.633× | 1.295× |
| `cad/docked_viewport` | 10.015 | 10.146 | 11.747 | 1.174× | 1.161× |
| `cad/assembly_inspector` | 10.105 | 7.014 | 10.586 | 1.046× | 1.502× |

The slowest remaining edit phases in the three workloads above the batch p50 bound involve revealing product cards, changing the floating window and popup layout, and attaching the transient CAD inspection subtree.

## Compare against original Keru

The paired runner uses upstream Keru at `56b2769b54fcf203d77ffe8c0874fa20a4ccfe12`. It loads the same six fixture builders for both checkouts. Both use vertical Stack in place of Block, Stack in place of Wrap, zero margins, and unsnapped coordinates. The Block fixture's Auto dimensions become Fill width and FitContent height. Text wrapping still uses the same allocation-free monospace measurer in every mode. [Upstream commit](https://github.com/kekelp/keru_layout/commit/56b2769b54fcf203d77ffe8c0874fa20a4ccfe12)

One binary runs upstream incremental, upstream forced full, tuned incremental, tuned forced full, and the batch pilot. It rotates solve order each frame. Construction, edits, invalidation, and rectangle checks run outside the measurements. Every mode must match the tuned forced-full rectangle bits and tree shape on the initial frame, warmup, and measured frames. The report counts graph rebuilds for the batch solver and full solve fallbacks for the other modes.

The table records the comparison before the tail latency optimizations. It reports the median of per-run medians from 11 runs of 480 measured frames on one x86-64 logical CPU. Latencies are in microseconds. The batch p50 was lower than upstream in all 11 runs for each workload, with a 2.33× geometric mean speedup.

| Workload | Upstream p50 | Tuned p50 | Batch p50 | Upstream p95 | Batch p95 |
| --- | ---: | ---: | ---: | ---: | ---: |
| `browser/article_reflow` | 3.51 | 8.28 | 3.25 | 49.72 | 14.78 |
| `browser/product_catalog` | 74.47 | 68.79 | 43.34 | 111.34 | 77.15 |
| `compositor/tiled_split_resize` | 4.65 | 4.51 | 3.44 | 29.19 | 15.85 |
| `compositor/floating_drag_and_raise` | 16.74 | 2.38 | 0.93 | 18.12 | 53.56 |
| `cad/docked_viewport` | 22.76 | 9.04 | 9.99 | 26.88 | 10.80 |
| `cad/assembly_inspector` | 21.60 | 11.35 | 13.93 | 30.51 | 120.98 |

The allocation build made zero allocation and reallocation calls across all 2,880 measured batch solves. Cold batch solves made 58–74 calls and took longer than upstream. At this stage, graph recapture accounted for the high tail latency on floating compositor and CAD assembly edits.

```sh
manifest=benchmarks/real_workloads/compare_upstream/Cargo.toml
output_dir=target/compare-upstream
cargo build --release --locked --manifest-path "$manifest" --target-dir "$output_dir"
taskset -c 4 "$output_dir/release/keru-upstream-workloads" 480 11
```

The arguments set the measured frames per run and the number of runs. An optional third argument filters by workload name. Use a CPU available on the host or omit `taskset`.

The `allocations` feature runs the same checks and reports allocation calls and cumulative requested bytes for the cold solve and measured frames. It counts alloc, zeroed alloc, and realloc requests. This build does allocation counting without latency timing.

```sh
cargo build --release --locked --features allocations --manifest-path "$manifest" --target-dir "$output_dir"
taskset -c 4 "$output_dir/release/keru-upstream-workloads" 480 1
```
