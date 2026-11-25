# Kahn initialization and Pearce–Kelly repair, 24 November 2026

The hybrid starts with Kahn’s algorithm and uses batch Pearce–Kelly for graph edits after a successful first solve. On PanGUI, its first solves took **2.3% longer** by geometric mean across 13 workloads than the earlier generic Batch build. It was faster on five workloads by paired median. The row-group queue preserves locality across sizing slots that are ready on the same node. [Earlier generic Batch comparison](../pangui-2026-11-24-batch-cold/report.md) · [Scheduling implementation](../../benchmarks/topological_order/README.md#layout-pilot)

## First solve

Times are medians in milliseconds. The two ratio columns use the median of individual paired ratios. Values above 1× favor the hybrid.

| Workload | Previous Batch | Hybrid Batch | Dense default | Previous ÷ hybrid | Dense ÷ hybrid | Hybrid wins |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 3.592 | 3.354 | 0.230 | 1.050× | 0.073× | 6/11 |
| `expand_with_min_constraint` | 2.518 | 1.976 | 0.122 | 1.274× | 0.058× | 9/11 |
| `fit_nesting` | 121.308 | 110.421 | 9.574 | 1.096× | 0.084× | 6/11 |
| `flex_expand_equal_weights` | 9.893 | 11.656 | 1.187 | 0.822× | 0.104× | 1/11 |
| `flex_expand_weights` | 5.938 | 7.444 | 0.555 | 0.814× | 0.081× | 2/11 |
| `nested_vertical_stack` | 4.070 | 4.290 | 0.265 | 0.961× | 0.064× | 3/11 |
| `padding_and_margin` | 0.051 | 0.051 | 0.005 | 0.977× | 0.102× | 3/11 |
| `percentage_and_ratio` | 4.852 | 4.898 | 0.267 | 0.991× | 0.058× | 5/11 |
| `perpendicular_expand_with_wrap` | 6.900 | 5.078 | 0.489 | 1.217× | 0.096× | 10/11 |
| `pixels_with_min_expand_constraint` | 32.177 | 27.822 | 1.205 | 1.090× | 0.044× | 9/11 |
| `wide_no_wrap_simple_few` | 0.194 | 0.232 | 0.020 | 0.836× | 0.090× | 2/11 |
| `wide_no_wrap_simple_many` | 50.725 | 65.298 | 5.182 | 0.800× | 0.078× | 0/11 |
| `wide_wrapping` | 4.792 | 4.897 | 0.631 | 0.912× | 0.127× | 4/11 |

The pinned PanGUI release runner measured 11 pairs of fresh processes. Process order alternated on logical CPU 4 of an Intel Xeon Platinum 8573C. The baseline used Pearce–Kelly for the initial capture and for later graph repair. The timer covered the first solve and its schedule construction. Parsing, tree construction, invalidation, and rectangle comparisons ran outside the timer. Absolute rectangle bits, logical slot counts, and edge counts agreed across both builds. Dense default led on all first solves in this run. [Reproduction commands](../../benchmarks/arewelayoutyet/README.md#compare-batch-pearcekelly-with-the-upstream-engines) · [First-solve samples](first-solve-pairs.tsv)

## Warm solve

The hybrid led dense default on **13 of 13** warmed workloads by paired median, with a **1.284×** geometric mean speedup. The runner measured 21 rounds across 126 peer and workload pairs. The slot-by-slot FIFO trial led on 6 workloads and had a 0.932× geometric mean dense-to-Batch ratio in a separate run. Grouping changes which ready slot runs next while preserving the Kahn indegree rule. [Warm samples](paired-samples.tsv)

Times are medians in microseconds. The last column uses paired ratios.

| Workload | Dense default | Owned default | Hybrid Batch | Dense ÷ hybrid |
| --- | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 76.348 | 95.256 | 63.583 | 1.1728× |
| `expand_with_min_constraint` | 75.639 | 94.631 | 63.050 | 1.1896× |
| `fit_nesting` | 4,463.888 | 4,847.850 | 4,390.517 | 1.0314× |
| `flex_expand_equal_weights` | 288.137 | 426.328 | 263.644 | 1.0960× |
| `flex_expand_weights` | 420.860 | 500.339 | 376.764 | 1.0997× |
| `nested_vertical_stack` | 179.157 | 261.024 | 164.722 | 1.1093× |
| `padding_and_margin` | 1.408 | 1.667 | 0.802 | 1.7768× |
| `percentage_and_ratio` | 182.555 | 286.605 | 134.869 | 1.3331× |
| `perpendicular_expand_with_wrap` | 281.972 | 840.398 | 252.594 | 1.1131× |
| `pixels_with_min_expand_constraint` | 1,217.373 | 1,482.316 | 1,063.143 | 1.1474× |
| `wide_no_wrap_simple_few` | 9.486 | 12.413 | 4.557 | 2.0991× |
| `wide_no_wrap_simple_many` | 3,686.573 | 5,049.557 | 2,054.160 | 1.8691× |
| `wide_wrapping` | 213.571 | 665.467 | 189.454 | 1.1271× |

## Verification

An independent reachability oracle tested the grouped kernel on all 1,048,576 directed graphs without self-loops on five vertices. It accepted all 29,281 DAGs with valid orders and inverse ranks and rejected all 1,019,295 cyclic graphs. A native layout test forces a backward dependency after Kahn initialization and checks that Pearce–Kelly repairs it. The cycle tests also verify that rejected graphs preserve published rectangles and that the solver recovers after the cycle is removed. Formal verification of graph capture, ordering, and end-to-end equivalence remains open. [Ordering tests](../../src/batch_order/kahn.rs) · [Layout tests](../../tests/batch_layout.rs)

All 223 crate tests and 17 standalone order tests passed. Six browser, compositor, and CAD fixtures matched forced-full layout on the initial solve, 24 warmup edits, and 1,440 additional edits each. [Application verification](../../benchmarks/real_workloads/README.md#batch-pearcekelly-pilot)
