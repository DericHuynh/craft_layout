# PanGUI layout benchmarks, 22 November 2026

Keru took **36.8% less time** than the saved pre-structural solver across the 13 warm workloads by geometric mean of the paired time ratios. The build entering this recovery had taken **32.2% more time**. Twelve workloads improved. Wide no-wrap with 100,000 siblings was 4.1% slower warm and 7.1% slower cold in the paired run. The four-process Criterion comparison measured it 2.0% faster.

Keru had the lowest mean layout time among the supported peer engines on all 13 workloads. The full Criterion matrix has 162 measured cells across 14 configurations. Its geometric mean was 30.6% below pre-structural Keru on all 13 workloads and 64.5% below published Keru 0.1.0 on the ten shared workloads. Both targeted full solves allocated zero bytes on fresh and reused trees.

The tables use milliseconds unless marked in microseconds. Negative changes mean less elapsed time. The data files include per-case 95% confidence intervals and raw samples. [Timing data](timings.tsv) · [Raw measurements and verification](measurements.zip)

## Measurement conditions

The harness used the original 13 PanGUI templates on logical CPU 6 of an AMD Ryzen 7 5800H, with Rust 1.97.0 release builds and default x86-64 code generation. Tree construction and template parsing took place outside the timed full solves. Clay and Ply include declaration and render-command generation in their timed adapters. The historical Keru source is the optimized working tree immediately preceding incremental structural edits. The incoming build is the checkout at the start of this recovery.

The full matrix used ten flat samples per supported case, with 300 ms of warm-up and a one-second measurement target. The final candidate ran on all 13 workloads after the wrapping optimization. The 149 unchanged peer, published, and pre-structural entries come from the preceding pass on the same core. The target and paired comparisons below timed the historical source again alongside the recovered solver.

## Target workloads

Each version ran in four processes per workload, alternating versions and reversing order. Each process used 12 Criterion samples, a 300 ms warm-up and a one-second measurement target. The table shows the median of the four process point estimates. The two historical reruns show how absolute timings varied on this host.

| Workload | Historical as previously reported | Historical alongside incoming | Incoming | Historical alongside recovery | Recovered | Recovered vs matched historical |
|---|---:|---:|---:|---:|---:|---:|
| wide_no_wrap_simple_many | 2.2238 | 2.2829 | 5.3547 | 2.7088 | 2.6551 | -2.0% |
| fit_nesting | 5.7764 | 6.4079 | 9.3551 | 6.9763 | 6.2706 | -10.1% |

## Paired full solves

The original paired native harness alternated adjacent batches within each process. Two runs reversed engine allocation order and retained 30 pairs each. Times are independent medians in milliseconds. Changes are medians of the 60 within-pair ratios. A cold measurement times the first solve on a freshly constructed tree.

| Workload | State | Historical vs incoming (ms) | Incoming (ms) | Incoming paired change | Historical vs recovery (ms) | Recovered (ms) | Recovered paired change |
|---|---|---:|---:|---:|---:|---:|---:|
| wide_no_wrap_simple_many | warm | 2.7064 | 5.2013 | +91.5% | 2.5175 | 2.6451 | +4.1% |
| fit_nesting | warm | 6.8608 | 9.8000 | +42.2% | 6.4049 | 5.7383 | -10.4% |
| expand_with_max_constraint | warm | 0.2123 | 0.1946 | -8.6% | 0.2135 | 0.1391 | -35.0% |
| expand_with_min_constraint | warm | 0.2113 | 0.1928 | -8.5% | 0.2137 | 0.1387 | -34.8% |
| flex_expand_equal_weights | warm | 1.1546 | 1.0290 | -11.1% | 1.1235 | 0.4098 | -64.3% |
| flex_expand_weights | warm | 1.0046 | 1.0041 | -0.5% | 0.9546 | 0.4465 | -53.9% |
| nested_vertical_stack | warm | 0.5346 | 0.7845 | +47.0% | 0.4971 | 0.1929 | -61.4% |
| padding_and_margin | warm | 0.0052 | 0.0076 | +46.4% | 0.0051 | 0.0023 | -55.5% |
| percentage_and_ratio | warm | 0.6793 | 0.9064 | +32.8% | 0.6635 | 0.2030 | -69.4% |
| perpendicular_expand_with_wrap | warm | 0.8505 | 1.1146 | +30.5% | 0.8286 | 0.7413 | -12.1% |
| pixels_with_min_expand_constraint | warm | 3.5254 | 4.7733 | +33.8% | 2.4682 | 2.4266 | -2.6% |
| wide_no_wrap_simple_few | warm | 0.0092 | 0.0262 | +185.2% | 0.0096 | 0.0086 | -11.5% |
| wide_wrapping | warm | 0.5453 | 0.7202 | +31.6% | 0.5639 | 0.5498 | -1.8% |
| wide_no_wrap_simple_many | cold | 3.1202 | 5.7146 | +82.3% | 3.0552 | 3.2497 | +7.1% |
| fit_nesting | cold | 6.2385 | 8.9326 | +45.2% | 6.2569 | 5.3044 | -16.7% |

The equal-workload geometric mean of the 13 warm paired time ratios was +32.2% for incoming versus historical and -36.8% for recovered versus historical.

## Full comparison across engines

The following tables give the Criterion arithmetic mean for every supported engine and workload. A dash marks an input the adapter could not represent. The rank compares current Keru with the 11 peer configurations supporting each case. Both historical Keru configurations are shown separately.

| Workload | Current ms | Pre-structural ms | Published ms | Fastest peer | Peer ms | Rank |
|---|---:|---:|---:|---|---:|---:|
| expand_with_max_constraint | 0.1568 | 0.2276 | 0.3062 | Torin | 0.2642 | 1/12 |
| expand_with_min_constraint | 0.1498 | 0.2244 | 0.3064 | Torin | 0.2862 | 1/12 |
| fit_nesting | 5.5722 | 8.0504 | 14.4656 | Cephal | 13.2275 | 1/12 |
| flex_expand_equal_weights | 0.4398 | 1.3814 | 1.4620 | Torin | 1.3551 | 1/12 |
| flex_expand_weights | 0.4569 | 0.9646 | 1.3059 | Torin | 1.5465 | 1/10 |
| nested_vertical_stack | 0.2054 | 0.5067 | 0.8840 | Torin | 0.5672 | 1/12 |
| padding_and_margin | 0.0044 | 0.0066 | — | Torin | 0.0064 | 1/8 |
| percentage_and_ratio | 0.2437 | 0.6700 | 0.8858 | Morphorm | 0.9876 | 1/9 |
| perpendicular_expand_with_wrap | 0.8206 | 0.8120 | — | Torin | 1.1496 | 1/10 |
| pixels_with_min_expand_constraint | 2.7610 | 2.3012 | 3.4273 | Torin | 4.3821 | 1/9 |
| wide_no_wrap_simple_few | 0.0132 | 0.0114 | 0.0656 | Torin | 0.0479 | 1/12 |
| wide_no_wrap_simple_many | 2.8180 | 2.3555 | 9.2967 | Morphorm | 9.1283 | 1/11 |
| wide_wrapping | 0.6234 | 0.5710 | — | Morphorm | 0.8139 | 1/10 |

## Sizing and constraints

Arithmetic mean times in milliseconds. A dash marks an unsupported case.

| Engine | expand with max constraint | expand with min constraint | flex expand equal weights | flex expand weights | percentage and ratio | pixels with min expand constraint |
|---|---:|---:|---:|---:|---:|---:|
| Keru current | 0.1568 | 0.1498 | 0.4398 | 0.4569 | 0.2437 | 2.7610 |
| Keru pre-structural | 0.2276 | 0.2244 | 1.3814 | 0.9646 | 0.6700 | 2.3012 |
| Keru published 0.1.0 | 0.3062 | 0.3064 | 1.4620 | 1.3059 | 0.8858 | 3.4273 |
| Backer | 0.5210 | 0.4729 | 1.9570 | — | — | — |
| Cephal | 1.0459 | 0.9688 | 1.4189 | 3.8559 | 1.7697 | 11.2425 |
| Clay | 0.5867 | 0.8967 | 3.2479 | — | 2.9922 | — |
| hooke | 1.0998 | 1.1630 | 1.7171 | 3.1218 | 1.2457 | 15.9831 |
| Morphorm | 0.8816 | 0.8315 | 1.5852 | 1.7994 | 0.9876 | 6.2846 |
| Ply | 0.6271 | 0.7570 | 6.0141 | 6.3968 | 3.6168 | — |
| Taffy 0.3 | 1.4113 | 1.5491 | 5.3939 | 9.9994 | 2.6882 | 26.4067 |
| Taffy main | 1.7268 | 2.2276 | 5.4927 | 11.3473 | 3.5654 | 33.6344 |
| Torin | 0.2642 | 0.2862 | 1.3551 | 1.5465 | — | 4.3821 |
| ui_layout | 1.8798 | 1.7139 | 9.6632 | 13.1801 | — | 36.9335 |
| Yoga | 2.3226 | 2.1592 | 11.4582 | 14.2074 | 7.5411 | 27.4942 |

## Stacks, nesting and wrapping

Arithmetic mean times in milliseconds. A dash marks an unsupported case.

| Engine | fit nesting | nested vertical stack | padding and margin | perpendicular expand with wrap | wide no wrap simple few | wide no wrap simple many | wide wrapping |
|---|---:|---:|---:|---:|---:|---:|---:|
| Keru current | 5.5722 | 0.2054 | 0.0044 | 0.8206 | 0.0132 | 2.8180 | 0.6234 |
| Keru pre-structural | 8.0504 | 0.5067 | 0.0066 | 0.8120 | 0.0114 | 2.3555 | 0.5710 |
| Keru published 0.1.0 | 14.4656 | 0.8840 | — | — | 0.0656 | 9.2967 | — |
| Backer | 16.3907 | 1.2881 | — | — | 0.1319 | 18.8029 | — |
| Cephal | 13.2275 | 1.0102 | 0.0123 | 1.3901 | 0.1004 | 15.4216 | 1.0758 |
| Clay | 26.8767 | 2.0067 | — | — | 0.1692 | 21.0014 | — |
| hooke | 23.0464 | 1.1361 | 0.0130 | 2.1157 | 0.1267 | 18.4120 | 1.2836 |
| Morphorm | 74.3019 | 0.8600 | — | 2.1752 | 0.0841 | 9.1283 | 0.8139 |
| Ply | 44.4869 | 2.3847 | — | 6.3031 | 0.1827 | — | 4.5811 |
| Taffy 0.3 | 165.7700 | 3.5894 | 0.0219 | 4.9505 | 0.1582 | 34.7379 | 3.1108 |
| Taffy main | 42.4459 | 3.3179 | 0.0237 | 5.6438 | 0.2518 | 44.5502 | 3.1627 |
| Torin | 28.3758 | 0.5672 | 0.0064 | 1.1496 | 0.0479 | 14.3328 | 0.8362 |
| ui_layout | 103.1541 | 6.3415 | 0.0463 | 9.2142 | 0.3586 | 59.2094 | 8.0754 |
| Yoga | 127.8753 | 7.1585 | 0.0710 | 87.1836 | 0.4719 | 52.5074 | 25.2783 |

The published Keru adapter supports ten workloads. It omits in-flow margins and wrapping. The two workspace builds share the same native adapter. Both Taffy versions use their pinned adapters, including the earlier compatibility adjustments for Taffy 0.3.

## Target workload engine comparison

The 12-sample PanGUI Criterion measurements compared the current checkout, the saved pre-structural Keru source, and all 11 registered peer configurations, including Taffy 0.3. The unchanged peer and pre-structural rows come from the preceding run. The current Keru row was refreshed after the wrapping optimization. Both templates and each adapter’s native layout semantics were preserved. Clay and Ply include declaration and render-command generation. Ply cannot represent the wide workload with 100,000 siblings. Values are arithmetic mean milliseconds per full solve.

| Implementation | fit_nesting | wide_no_wrap_simple_many |
|---|---:|---:|
| keru_layout | 5.8989 | 2.6901 |
| Keru baseline | 7.5273 | 2.9085 |
| Cephal | 13.1610 | 14.4746 |
| Backer | 16.2120 | 17.7233 |
| hooke | 23.8767 | 16.1536 |
| Torin | 28.6531 | 17.0716 |
| Clay | 29.0360 | 20.7980 |
| Taffy main | 45.8043 | 51.2855 |
| Ply | 46.1609 | Unsupported |
| Morphorm | 78.4727 | 10.0512 |
| ui_layout | 102.9894 | 65.9110 |
| Yoga | 127.8167 | 58.5591 |
| Taffy 0.3 | 180.2040 | 35.2814 |

## Allocation and placement controls

Times in this independent counting-allocator harness are medians of four process medians, with nine batches per process. Allocation counts include reallocations. Historical and recovered timings shown here were collected together. Cold allocation columns compare historical, incoming and recovered builds.

| Workload | Historical µs | Recovered µs | Time change | Cold allocations, historical / incoming / recovered | Cold requested bytes, historical / incoming / recovered | Recovered warm allocations / bytes |
|---|---:|---:|---:|---:|---:|---:|
| wide_no_wrap_simple_many | 2505.002 | 2584.735 | +3.2% | 0 / 2 / 0 | 0 / 3200736 / 0 | 0 / 0 |
| fit_nesting | 6314.870 | 5342.179 | -15.4% | 0 / 12 / 0 | 0 / 4611168 / 0 | 0 / 0 |
| grid 12 columns backfill=true | 56.600 | 39.866 | -29.6% | 5 / 5 / 5 | 4216 / 4216 / 4216 | 0 / 0 |
| grid 12 columns backfill=false | 24.897 | 9.706 | -61.0% | 3 / 3 / 3 | 224 / 224 / 224 | 0 / 0 |
| grid 97 columns backfill=true | 210.453 | 153.694 | -27.0% | 5 / 5 / 5 | 3472 / 3472 / 3472 | 0 / 0 |
| grid 97 columns backfill=false | 78.367 | 29.994 | -61.7% | 4 / 4 / 4 | 480 / 480 / 480 | 0 / 0 |
| grid 257 columns backfill=true | 194.923 | 128.872 | -33.9% | 5 / 5 / 5 | 3720 / 3720 / 3720 | 0 / 0 |
| grid 257 columns backfill=false | 77.851 | 30.336 | -61.0% | 5 / 5 / 5 | 1240 / 1240 / 1240 | 0 / 0 |
| free center | 118.844 | 116.249 | -2.2% | 0 / 0 / 0 | 0 / 0 / 0 | 0 / 0 |
| free start | 121.613 | 119.374 | -1.8% | 0 / 0 / 0 | 0 / 0 / 0 | 0 / 0 |

## Paired grid and free-placement confirmation

A second control run used both builds in the same process and alternated their order within each pair. Two processes reversed tree allocation order. Each retained 30 pairs of 20 invalidated full solves, for 60 time ratios per workload. The inputs match the allocation controls.

| Workload | Historical µs | Recovered µs | Median paired change |
|---|---:|---:|---:|
| grid 12 columns backfill=true | 55.072 | 40.697 | -26.4% |
| grid 12 columns backfill=false | 24.878 | 9.493 | -61.9% |
| grid 97 columns backfill=true | 212.360 | 157.693 | -25.9% |
| grid 97 columns backfill=false | 77.199 | 30.014 | -60.9% |
| grid 257 columns backfill=true | 196.488 | 131.721 | -33.1% |
| grid 257 columns backfill=false | 78.500 | 30.096 | -61.6% |
| free center | 110.019 | 106.426 | -3.9% |
| free start | 116.525 | 114.734 | +0.1% |

## Incremental append and removal

These independent measurements alternate the incoming structural solver and the recovered solver on a 12,288-child workload. Each reported operation time is the median of eight runs per build on logical CPU 2. The harness also compared geometry and measured work after each edit against a full solve. All eight controls recorded zero warmed allocations.

| Workload | Append incoming µs | Append recovered µs | Remove incoming µs | Remove recovered µs |
|---|---:|---:|---:|---:|
| flat-zero | 1.76 | 1.47 | 1.47 | 1.47 |
| flat-weighted | 197.56 | 206.33 | 193.04 | 205.82 |
| flat-bounded | 206.97 | 211.78 | 212.14 | 210.26 |
| flat-bounded-edit-dense | 1232.98 | 1119.71 | 1248.47 | 1161.95 |
| flat-positive-crossfill | 195.15 | 214.45 | 195.35 | 206.82 |
| panels-positive | 79.51 | 79.32 | 79.03 | 78.69 |
| flat-independent | 197.63 | 198.56 | 196.45 | 198.59 |
| full-control | 1335.63 | 870.90 | 1340.71 | 871.43 |

## Implementation and correctness

Ordinary full solves now avoid copying topology and declarations until the adapter needs that history. Stack preparation measures eligible Fit dimensions in the existing sibling pass. Four contiguous cached pixel values can be compared with one SSE2 packed comparison. Count grids reuse the same track calculation across unbounded Fill leaves, and wrapped Fill leaves reuse the cross-axis extent of their line. Width-defined grids with a zero track step use one track.

Debug and release runs each passed 67 tests. The build without default features passed eight tests, and both feature configurations passed strict Clippy. Historical output checks matched on all 13 templates, 10,000 randomized weighted layouts, 2,000 mixed-flow trees, 2,400 floating-point placement cases and 6,208 Fill solves. Another 30,000 randomized grid frames matched the historical full solver, and 86,400 randomized batches with unknown structural edit locations matched full recomputation.

On 12,000 deliberately extreme three-frame trees, every finite coordinate bit pattern, logical slot value, dependency level and warning sequence matched. On 31 trees, an already-NaN rectangle coordinate changed sign. The raw archive includes the validation logs and final source hashes.
