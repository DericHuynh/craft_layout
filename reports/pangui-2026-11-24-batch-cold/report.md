# Batch Pearce–Kelly first solves, 24 November 2026

Batch first solves improved on all 13 PanGUI fixtures by paired median. The geometric mean speedup over the previous Batch implementation was **1.348×**, with a range of **1.104× to 1.554×**. The dense default still led on all 13 fixtures by a geometric mean of **12.628×**. [Previous Batch comparison](../pangui-2026-11-24-batch-dense/report.md)

## First solve

Times are medians in milliseconds. The two ratio columns show medians of individual paired ratios. Wins count the pairs in which the new Batch solve was faster than the previous one.

| Workload | Previous Batch | New Batch | Dense default | Batch speedup | New Batch ÷ dense | Wins |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 3.268 | 2.888 | 0.201 | 1.104× | 14.61× | 10/11 |
| `expand_with_min_constraint` | 2.618 | 2.280 | 0.088 | 1.167× | 26.09× | 9/11 |
| `fit_nesting` | 154.051 | 123.077 | 8.561 | 1.213× | 12.30× | 8/11 |
| `flex_expand_equal_weights` | 13.029 | 8.594 | 1.269 | 1.529× | 6.69× | 11/11 |
| `flex_expand_weights` | 7.631 | 5.572 | 0.492 | 1.343× | 11.25× | 11/11 |
| `nested_vertical_stack` | 5.007 | 3.823 | 0.279 | 1.334× | 13.22× | 11/11 |
| `padding_and_margin` | 0.067 | 0.050 | 0.005 | 1.335× | 9.23× | 11/11 |
| `percentage_and_ratio` | 5.665 | 4.190 | 0.250 | 1.358× | 15.75× | 11/11 |
| `perpendicular_expand_with_wrap` | 8.061 | 5.098 | 0.384 | 1.554× | 13.30× | 11/11 |
| `pixels_with_min_expand_constraint` | 35.624 | 28.765 | 1.095 | 1.215× | 26.15× | 10/11 |
| `wide_no_wrap_simple_few` | 0.266 | 0.165 | 0.018 | 1.539× | 8.85× | 9/11 |
| `wide_no_wrap_simple_many` | 70.846 | 47.199 | 3.734 | 1.443× | 12.58× | 11/11 |
| `wide_wrapping` | 7.055 | 4.607 | 0.607 | 1.494× | 7.91× | 11/11 |

The same upstream runner measured each release binary in 11 pairs of fresh processes. Run order alternated on logical CPU 4 of an Intel Xeon Platinum 8573C. Dense, owned default, and Batch solved equivalent inputs in each process. Timing included the initial Batch graph capture and repair. Template parsing, tree construction, invalidation, and rectangle comparisons ran outside the timer. The geometry hashes and graph sizes agreed across both builds and all repeats. [First-solve samples](first-solve-pairs.tsv) · [Runner and setup](../../benchmarks/arewelayoutyet/README.md#compare-batch-pearcekelly-with-the-upstream-engines)

## Warm solve

Batch still beat dense default on all 13 fixtures by paired median. The geometric mean speedup was **1.246×**, with a range of **1.015× to 1.987×**. The runner measured 21 rounds across 126 supported peer and workload pairs on the same logical CPU. Batch compiles its warm-only instructions on the first eligible retained-graph solve. This table measures subsequent solves once that program is available. [Warm samples](paired-samples.tsv)

Times are medians in microseconds. The last column uses paired ratios.

| Workload | Dense default | Owned default | Batch | Dense ÷ batch |
| --- | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 70.813 | 93.377 | 69.856 | 1.0150× |
| `expand_with_min_constraint` | 69.789 | 92.127 | 67.278 | 1.0339× |
| `fit_nesting` | 4,190.882 | 4,632.244 | 4,001.020 | 1.0575× |
| `flex_expand_equal_weights` | 277.902 | 410.516 | 257.716 | 1.0795× |
| `flex_expand_weights` | 392.926 | 488.147 | 368.997 | 1.0585× |
| `nested_vertical_stack` | 169.899 | 241.672 | 150.910 | 1.1215× |
| `padding_and_margin` | 1.330 | 1.592 | 0.733 | 1.8073× |
| `percentage_and_ratio` | 171.029 | 272.078 | 125.743 | 1.3491× |
| `perpendicular_expand_with_wrap` | 269.004 | 787.319 | 238.069 | 1.1321× |
| `pixels_with_min_expand_constraint` | 1,093.978 | 1,441.405 | 976.547 | 1.1293× |
| `wide_no_wrap_simple_few` | 9.275 | 12.010 | 4.614 | 1.9873× |
| `wide_no_wrap_simple_many` | 3,249.963 | 4,329.511 | 1,876.086 | 1.7493× |
| `wide_wrapping` | 209.497 | 656.575 | 181.249 | 1.1277× |

## Algorithm checks

The first capture uses identity ranks and skips materializing the rank maps when every edge already runs forward. Sparse adjacency and packed capture preserve producer and reader order. Batch Pearce–Kelly repair processes backward edges in descending old tail rank, searches inside each affected interval with bounded DFS, and stages the paper's shift before publishing either rank map. The search explicitly checks edges returning to an insertion's tail at the rank bound.

An independent Kahn oracle checked all 1,048,576 directed graphs without self-loops on five vertices against the initial append and repair path. Repair accepted 29,281 DAGs with valid inverse maps and rejected 1,019,295 cyclic graphs while restoring the prior order. The order suite also exercises all four-vertex graph and batch combinations, self-loops, mixed edits, and rollback. Sparse adjacency matched CSR successor rows and seed order across 6,760 captures, including overlapping base and tail rows. [Implementation and paper](../../benchmarks/topological_order/README.md#layout-pilot) · [Order tests](../../benchmarks/topological_order/tests/repair.rs)

All 217 crate tests and 12 order tests passed. All 13 PanGUI fixtures matched exact rectangle bits before and after invalidation. The six browser, compositor, and CAD fixtures matched the forced-full solver through 1,440 additional checked edits each, after the initial solve and 24 warmup edits per fixture. The focused Verus run verified four ratio arithmetic and record publication obligations. Formal verification of the Batch graph capture, repair, and end-to-end equivalence remains open. [Application workload commands](../../benchmarks/real_workloads/README.md#batch-pearcekelly-pilot)
