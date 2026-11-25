# Batch Pearce–Kelly vs dense default, 24 November 2026

Batch was faster on all 13 PanGUI fixtures by paired median. The geometric mean speedup was 1.264× and the range was 1.034× to 2.000×. Each warm solve recomputed sizing and placement using the retained graph and compiled declarations.

## Warm solve times

Times are microseconds. The last column uses paired ratios, so it can differ from dividing the displayed medians.

| Workload | Dense default | Owned default | Batch | Dense ÷ batch |
| --- | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 73.293 | 94.980 | 71.720 | 1.0376× |
| `expand_with_min_constraint` | 69.743 | 92.220 | 67.222 | 1.0399× |
| `fit_nesting` | 4,092.605 | 4,653.122 | 4,088.361 | 1.0343× |
| `flex_expand_equal_weights` | 283.083 | 415.248 | 259.750 | 1.0924× |
| `flex_expand_weights` | 397.508 | 496.420 | 383.406 | 1.0527× |
| `nested_vertical_stack` | 174.851 | 253.416 | 158.242 | 1.1155× |
| `padding_and_margin` | 1.448 | 1.635 | 0.754 | 1.9289× |
| `percentage_and_ratio` | 175.595 | 280.672 | 132.407 | 1.3640× |
| `perpendicular_expand_with_wrap` | 264.666 | 774.356 | 240.407 | 1.1231× |
| `pixels_with_min_expand_constraint` | 1,098.634 | 1,484.647 | 1,005.577 | 1.1174× |
| `wide_no_wrap_simple_few` | 9.381 | 12.532 | 4.880 | 1.9309× |
| `wide_no_wrap_simple_many` | 3,743.135 | 5,293.686 | 2,041.015 | 1.9999× |
| `wide_wrapping` | 214.323 | 661.305 | 185.142 | 1.1549× |

## First solve

Medians from seven fresh processes, in milliseconds. Batch includes graph capture and ordering.

| Workload | Dense default | Owned default | Batch |
| --- | ---: | ---: | ---: |
| `expand_with_max_constraint` | 0.254 | 0.242 | 3.806 |
| `expand_with_min_constraint` | 0.100 | 0.123 | 2.854 |
| `fit_nesting` | 9.662 | 13.406 | 125.875 |
| `flex_expand_equal_weights` | 1.279 | 1.578 | 13.678 |
| `flex_expand_weights` | 0.501 | 0.637 | 7.891 |
| `nested_vertical_stack` | 0.257 | 0.244 | 5.549 |
| `padding_and_margin` | 0.005 | 0.006 | 0.060 |
| `percentage_and_ratio` | 0.263 | 0.316 | 5.943 |
| `perpendicular_expand_with_wrap` | 0.391 | 0.923 | 8.142 |
| `pixels_with_min_expand_constraint` | 1.218 | 1.416 | 36.737 |
| `wide_no_wrap_simple_few` | 0.018 | 0.031 | 0.328 |
| `wide_no_wrap_simple_many` | 4.074 | 6.910 | 75.048 |
| `wide_wrapping` | 0.599 | 1.110 | 7.487 |

## Method and checks

The release runner uses the same PanGUI templates, engines, and timing boundaries as the previous comparison. It samples all 126 supported peer and workload pairs in 21 rotating rounds pinned to logical CPU 4 of an Intel Xeon Platinum 8573C. Warm samples are means of individually timed solves. Reported Keru medians and dense-to-batch speedups fold across peers within each round and then across rounds. Construction, invalidation, and rectangle inspection take place outside the timed calls. [Reproduction commands](../../benchmarks/arewelayoutyet/README.md#compare-batch-pearcekelly-with-the-upstream-engines) · [Previous run](../pangui-2026-11-24-batch/report.md) · [Warm samples](paired-samples.tsv) · [First-solve samples](first-solve-samples.tsv)

All 13 PanGUI fixtures matched dense rectangle bits before and after invalidation. All 215 crate tests and 10 independent order repair tests passed. The six application fixtures matched forced-full rectangle bits through 1,440 checked edits each. The focused Verus run verified four obligations for ratio arithmetic and record publication. [Batch design](../../benchmarks/topological_order/README.md#layout-pilot)
