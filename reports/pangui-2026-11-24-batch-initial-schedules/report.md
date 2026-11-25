# Compact initial Batch schedules, 24 November 2026

Batch first solves were **2.017× faster** by geometric mean across 13 PanGUI fixtures, with eight wins by paired median over the previous Batch build. `fit_nesting` and `wide_no_wrap_simple_few` also beat dense default on the first solve. Dense default still led by **6.44×** on geometric mean across the whole suite. [Previous first-solve comparison](../pangui-2026-11-24-batch-cold/report.md)

## First solve

Times are medians in milliseconds. Ratio columns use the median of individual paired ratios. A value above 1× favors the current Batch solver in both columns.

| Workload | Previous Batch | Current Batch | Dense default | Previous ÷ current | Dense ÷ current | Batch wins |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 2.826 | 2.938 | 0.183 | 0.851× | 0.054× | 2/11 |
| `expand_with_min_constraint` | 2.375 | 2.347 | 0.093 | 1.016× | 0.039× | 7/11 |
| `fit_nesting` | 119.185 | 8.841 | 10.818 | 12.957× | 1.190× | 11/11 |
| `flex_expand_equal_weights` | 9.113 | 8.439 | 1.137 | 1.113× | 0.144× | 9/11 |
| `flex_expand_weights` | 5.779 | 5.783 | 0.611 | 0.990× | 0.104× | 4/11 |
| `nested_vertical_stack` | 3.991 | 0.359 | 0.272 | 11.818× | 0.736× | 11/11 |
| `padding_and_margin` | 0.051 | 0.052 | 0.005 | 0.953× | 0.097× | 3/11 |
| `percentage_and_ratio` | 4.382 | 4.572 | 0.314 | 0.930× | 0.066× | 4/11 |
| `perpendicular_expand_with_wrap` | 5.650 | 5.613 | 0.427 | 1.062× | 0.070× | 7/11 |
| `pixels_with_min_expand_constraint` | 31.431 | 31.066 | 1.328 | 1.001× | 0.043× | 6/11 |
| `wide_no_wrap_simple_few` | 0.197 | 0.018 | 0.021 | 10.440× | 1.140× | 11/11 |
| `wide_no_wrap_simple_many` | 52.096 | 7.681 | 4.512 | 6.872× | 0.578× | 11/11 |
| `wide_wrapping` | 4.827 | 6.163 | 0.510 | 0.927× | 0.087× | 4/11 |

The same release runner measured the two Batch builds in 11 pairs of fresh processes. Process order alternated on logical CPU 4 of an Intel Xeon Platinum 8573C. Each process also measured the dense and owned default solvers. The timer covered the first solve, including schedule construction. Template parsing, tree construction, invalidation, and rectangle checks took place outside the timer. Geometry hashes, logical slot counts, and edge counts agreed across both builds and all repeats. [Reproduction commands](../../benchmarks/arewelayoutyet/README.md#compare-batch-pearcekelly-with-the-upstream-engines) · [First-solve samples](first-solve-pairs.tsv)

Four of the slower generic fixtures were rerun in isolation. The paired cold speedups were 1.009× for `expand_with_max_constraint`, 1.049× for `percentage_and_ratio`, 1.003× for `padding_and_margin`, and 0.887× for `wide_wrapping`. [Isolated samples](focused-first-solve-pairs.tsv)

## Warm solve

Current Batch beat dense default on **12 of 13** warmed fixtures by paired median. The geometric mean speedup was **1.388×** in 21 rounds across 126 supported peer and workload pairs. The `expand_with_max_constraint` ratio was 0.978× in the full run and 0.989× by median across three isolated warm runs. [Warm samples](paired-samples.tsv)

Times are medians in microseconds. The last column uses paired ratios.

| Workload | Dense default | Owned default | Batch | Dense ÷ Batch |
| --- | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 73.986 | 96.827 | 74.639 | 0.9775× |
| `expand_with_min_constraint` | 75.786 | 98.995 | 74.752 | 1.0306× |
| `fit_nesting` | 4,550.936 | 5,114.554 | 2,546.551 | 1.8269× |
| `flex_expand_equal_weights` | 301.600 | 442.905 | 276.184 | 1.0895× |
| `flex_expand_weights` | 425.560 | 546.124 | 397.101 | 1.1031× |
| `nested_vertical_stack` | 189.375 | 264.358 | 86.141 | 2.1777× |
| `padding_and_margin` | 1.406 | 1.763 | 0.820 | 1.7343× |
| `percentage_and_ratio` | 193.781 | 300.653 | 147.046 | 1.3123× |
| `perpendicular_expand_with_wrap` | 290.996 | 881.383 | 261.769 | 1.1374× |
| `pixels_with_min_expand_constraint` | 1,272.813 | 1,579.302 | 1,056.478 | 1.1817× |
| `wide_no_wrap_simple_few` | 9.625 | 12.891 | 4.611 | 2.1415× |
| `wide_no_wrap_simple_many` | 3,910.421 | 5,747.391 | 2,182.883 | 1.9616× |
| `wide_wrapping` | 220.172 | 684.399 | 196.698 | 1.1465× |

## Algorithms and verification

An eligible flat Free or Start Stack tree retains constant pixel finals and the two viewport dependencies. An eligible nested Start Stack tree uses independent sizing sweeps. Heights are computed leaf to root with the original sibling reduction order. Widths are computed root to leaf from the existing Fill arithmetic. Both plans publish in document order. General captures and retained graph repairs use Batch Pearce–Kelly. The prototypes that replaced initial repair with a generic DFS or compacted the general graph order stayed in scratch after measuring first and retained solves. [Algorithm and code](../../benchmarks/topological_order/README.md#layout-pilot)

All 220 crate tests and 12 order tests passed. New tests cover fixed and nested schedules under visibility, sizing, rounding, and measurement edits, plus preserving published rectangles on a rejected cycle. All 13 PanGUI templates matched dense rectangle bits on the first solve and after invalidation. Six browser, compositor, and CAD workloads matched forced-full output on the initial solve, 24 warmup edits, and 1,440 additional edits each. The end-to-end Verus proof remains open. [Layout tests](../../tests/batch_layout.rs) · [Application verification](../../benchmarks/real_workloads/README.md#batch-pearcekelly-pilot)
