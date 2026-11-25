# Are We Layout Yet Batch Pearce–Kelly comparison, 24 November 2026

Batch Pearce–Kelly took 1.98× as long as the tuned default solver by geometric mean on identical owned trees. Its paired median was faster than the quickest external peer on all 13 PanGUI fixtures, with a 1.62× geometric mean and a 1.02× minimum speedup. The dense full-layout Keru adapter was 4.84× faster by geometric mean and 3.51× at minimum against the fastest peer per fixture. The owned default was 3.22× faster by geometric mean and 1.58× at minimum.

## Warm full recomputation

Times are microseconds. The fastest peer is selected by median solve time on each fixture. Ratios are medians of paired observations, so they can differ from a division of the displayed time columns.

| Workload | Dense Keru | Owned default | Owned batch | Fastest peer | Peer time | Batch ÷ owned default | Peer ÷ batch | Batch wins vs fastest peer |
| --- | ---: | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 69.21 | 91.47 | 282.29 | Torin | 295.10 | 3.066× | 1.021× | 17/21 |
| `expand_with_min_constraint` | 69.36 | 92.12 | 278.55 | Torin | 297.26 | 3.034× | 1.048× | 18/21 |
| `fit_nesting` | 3,859.76 | 4,500.53 | 7,149.28 | Cephal | 13,829.29 | 1.622× | 2.140× | 21/21 |
| `flex_expand_equal_weights` | 275.76 | 409.07 | 857.50 | Cephal | 1,752.64 | 2.095× | 2.033× | 21/21 |
| `flex_expand_weights` | 387.55 | 487.01 | 1,156.43 | Torin | 1,729.81 | 2.356× | 1.494× | 21/21 |
| `nested_vertical_stack` | 170.75 | 242.24 | 481.70 | Torin | 839.08 | 1.973× | 1.761× | 21/21 |
| `padding_and_margin` | 1.42 | 1.58 | 4.44 | Torin | 5.16 | 2.827× | 1.155× | 21/21 |
| `percentage_and_ratio` | 170.50 | 270.47 | 847.87 | Morphorm | 1,182.93 | 3.116× | 1.405× | 21/21 |
| `perpendicular_expand_with_wrap` | 261.85 | 780.22 | 959.05 | Torin | 1,500.09 | 1.226× | 1.569× | 21/21 |
| `pixels_with_min_expand_constraint` | 1,113.78 | 1,248.33 | 3,631.32 | Torin | 3,870.48 | 2.900× | 1.085× | 19/21 |
| `wide_no_wrap_simple_few` | 9.23 | 12.17 | 17.11 | Torin | 50.41 | 1.417× | 2.952× | 21/21 |
| `wide_no_wrap_simple_many` | 2,836.07 | 3,613.54 | 4,540.65 | Torin | 10,197.21 | 1.065× | 3.283× | 21/21 |
| `wide_wrapping` | 200.95 | 633.68 | 631.78 | Morphorm | 1,045.11 | 1.006× | 1.637× | 21/21 |

### All peer engines

Each speedup is the geometric mean of that peer's paired ratios on its supported fixtures. Values above 1 mean the Keru mode was faster.

| Peer | Coverage | Peer ÷ dense | Peer ÷ owned default | Peer ÷ owned batch |
| --- | ---: | ---: | ---: | ---: |
| Backer | 7/13 | 8.52× | 6.44× | 3.27× |
| Cephal | 13/13 | 8.72× | 5.78× | 2.85× |
| Clay | 8/13 | 13.83× | 10.40× | 4.94× |
| Morphorm | 12/13 | 8.92× | 5.79× | 2.98× |
| Ply | 10/13 | 14.04× | 8.93× | 4.48× |
| Taffy 0.3 | 13/13 | 17.28× | 11.48× | 5.83× |
| Taffy main | 13/13 | 19.27× | 12.81× | 6.52× |
| Torin | 12/13 | 5.02× | 3.36× | 1.77× |
| Yoga | 13/13 | 64.55× | 42.37× | 21.37× |
| hooke | 13/13 | 9.13× | 6.19× | 3.09× |
| ui_layout | 12/13 | 30.94× | 20.32× | 10.69× |

## First solve

These medians use seven fresh processes. Trees are built before timing. Batch first solve includes dependency capture and topological ordering. Times are milliseconds.

| Workload | Dense Keru | Owned default | Owned batch |
| --- | ---: | ---: | ---: |
| `expand_with_max_constraint` | 0.152 | 0.165 | 3.161 |
| `expand_with_min_constraint` | 0.079 | 0.106 | 2.553 |
| `fit_nesting` | 8.370 | 10.600 | 104.961 |
| `flex_expand_equal_weights` | 1.220 | 1.352 | 12.395 |
| `flex_expand_weights` | 0.527 | 0.652 | 6.928 |
| `nested_vertical_stack` | 0.229 | 0.247 | 4.462 |
| `padding_and_margin` | 0.005 | 0.006 | 0.054 |
| `percentage_and_ratio` | 0.240 | 0.308 | 5.232 |
| `perpendicular_expand_with_wrap` | 0.338 | 0.874 | 7.103 |
| `pixels_with_min_expand_constraint` | 1.048 | 1.244 | 32.629 |
| `wide_no_wrap_simple_few` | 0.018 | 0.030 | 0.258 |
| `wide_no_wrap_simple_many` | 2.996 | 5.452 | 63.457 |
| `wide_wrapping` | 0.550 | 0.993 | 7.437 |

## Method

The runner uses the 13 PanGUI templates and 11 external engines in arewelayoutyet revision `b1f5ff86eae840705950ae037f8d397e0f20a0a2`. Each of 126 supported peer and workload pairs has 21 rotating measurement rounds. Each mode is timed individually and reported as a mean within each round. Workload medians for Keru modes are folded across peers within each round and then across rounds. The release binary ran on logical CPU 4 of an Intel Xeon Platinum 8573C with Rust 1.99.1. [Upstream benchmark](https://github.com/DericHuynh/arewelayoutyet/tree/b1f5ff86eae840705950ae037f8d397e0f20a0a2/benchmarks) · [Raw warm samples](paired-samples.tsv) · [Raw first solves](first-solve-samples.tsv)

Each warm solve recomputes sizing and placement. Batch retains the graph. Tree construction, invalidation and geometry validation are outside the timer. All three Keru modes reproduced the same absolute rectangle bits, including signed zero, on every template before and after invalidation. Peer adapters retain upstream rounding and timing policies, including declaration and render-command work for Clay and Ply. [Reproduction commands](../../benchmarks/arewelayoutyet/README.md#compare-batch-pearcekelly-with-the-upstream-engines) · [Peer timing boundaries](../pangui-2026-11-23-optimized/report.md#method)
