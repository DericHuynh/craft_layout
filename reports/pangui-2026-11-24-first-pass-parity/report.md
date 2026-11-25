# First-pass parity for owned layout, 24 November 2026

The first Batch call shares the ordinary owned full-layout routine. Both modes use the existing unregistered preparation on fresh trees and the registered path when sizing records are available. The Batch call checks for cycles between sizing and placement. It allocates its workspace on the first later call that needs Batch graph capture. The first call and idle reuse both leave the Batch workspace at zero capacity. [Owned entry and regression test](../../src/layout_tree.rs) · [Shared full solve](../../src/full_layout.rs)

## Comparison with ordinary owned first solves

The paired probe used 48 fresh tree pairs per fixture on logical CPU 1. Each block varied both construction order and solve order. Every pair compared absolute rectangle bits to the ordinary owned and dense results. The first Batch-to-owned ratio was **0.9981× for thread CPU time** and **1.0003× for elapsed time** by geometric mean. Ratios above 1× indicate greater time for Batch. Intervals are paired block-bootstrap estimates. [Owned first samples](owned-first-pairs.tsv)

| Workload | CPU Batch ÷ owned | CPU 95% interval | Elapsed Batch ÷ owned | Elapsed 95% interval |
| --- | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 0.9918× | 0.9696–1.0118 | 0.9911× | 0.9796–1.0115 |
| `expand_with_min_constraint` | 0.9949× | 0.9692–1.0247 | 0.9953× | 0.9771–1.0300 |
| `fit_nesting` | 0.9957× | 0.9201–1.0547 | 1.0010× | 0.9378–1.0548 |
| `flex_expand_equal_weights` | 1.0707× | 1.0270–1.0938 | 1.0701× | 1.0267–1.0954 |
| `flex_expand_weights` | 1.0147× | 0.9725–1.0938 | 1.0158× | 0.9730–1.0956 |
| `nested_vertical_stack` | 0.9991× | 0.8947–1.0214 | 0.9989× | 0.9094–1.0228 |
| `padding_and_margin` | 0.9825× | 0.9778–0.9915 | 0.9888× | 0.9790–0.9961 |
| `percentage_and_ratio` | 0.9737× | 0.9196–1.0017 | 0.9727× | 0.9270–0.9974 |
| `perpendicular_expand_with_wrap` | 1.0261× | 0.9874–1.0722 | 1.0245× | 0.9858–1.0757 |
| `pixels_with_min_expand_constraint` | 0.9874× | 0.9755–1.0186 | 0.9872× | 0.9755–1.0175 |
| `wide_no_wrap_simple_few` | 0.9510× | 0.9467–0.9854 | 0.9513× | 0.9463–1.0080 |
| `wide_no_wrap_simple_many` | 0.9780× | 0.9550–1.0723 | 0.9943× | 0.9531–1.0725 |
| `wide_wrapping` | 1.0143× | 0.9710–1.0668 | 1.0181× | 0.9726–1.0677 |

The equal-weight flex result was sensitive to object position. A 96-pair rerun alternated both APIs between the same two object positions and measured 0.995× CPU and 0.996× elapsed. In the same controlled rerun, the small fixed-pixel wide fixture measured 1.007× CPU and 1.009× elapsed. [Equal-weight flex rerun](owned-equal-flex-pairs.tsv) · [Small wide rerun](owned-wide-few-pairs.tsv)

## Comparison with the previous Batch build

The PanGUI release runner alternated the previous and current binaries in 11 pairs of fresh processes on logical CPU 4 of an Intel Xeon Platinum 8573C. Values are medians in microseconds. The speedup column is the median of paired previous-to-current ratios. First calls include sizing and publication. [Raw samples](release-first-pairs.tsv) · [Benchmark setup](../../benchmarks/arewelayoutyet/README.md#compare-batch-pearcekelly-with-the-upstream-engines)

| Workload | Previous Batch | Current Batch | Current owned default | Dense default | Batch speedup | Wins |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 236.80 | 149.52 | 276.47 | 206.75 | 1.6491× | 10/11 |
| `expand_with_min_constraint` | 128.31 | 125.81 | 121.22 | 96.96 | 1.0144× | 6/11 |
| `fit_nesting` | 14,002.22 | 13,829.10 | 13,063.62 | 10,079.52 | 0.9256× | 4/11 |
| `flex_expand_equal_weights` | 1,056.74 | 1,141.12 | 1,637.65 | 1,396.38 | 1.0411× | 6/11 |
| `flex_expand_weights` | 665.76 | 866.69 | 788.56 | 651.16 | 1.0070× | 7/11 |
| `nested_vertical_stack` | 328.87 | 267.76 | 278.95 | 285.38 | 1.0174× | 7/11 |
| `padding_and_margin` | 5.31 | 3.02 | 7.25 | 5.81 | 1.7419× | 10/11 |
| `percentage_and_ratio` | 311.76 | 306.49 | 391.04 | 361.60 | 1.0906× | 7/11 |
| `perpendicular_expand_with_wrap` | 478.09 | 451.96 | 470.89 | 382.74 | 1.1758× | 6/11 |
| `pixels_with_min_expand_constraint` | 1,889.02 | 1,983.27 | 1,785.92 | 1,427.80 | 0.9661× | 5/11 |
| `wide_no_wrap_simple_few` | 20.56 | 22.75 | 27.17 | 18.72 | 0.8800× | 2/11 |
| `wide_no_wrap_simple_many` | 9,292.70 | 10,709.58 | 8,244.79 | 5,584.52 | 0.8332× | 4/11 |
| `wide_wrapping` | 650.02 | 531.50 | 681.45 | 672.84 | 1.2259× | 7/11 |

The 13-workload geometric mean improved by **1.094×** over the previous Batch build. The small fixed-pixel wide fixture varied across protocols. In the dedicated Cargo release rerun it went from 60.46 µs to 26.56 µs, with wins in 19 of 21 pairs. [Isolated wide samples](wide-few-release-first-pairs.tsv)

An additional 17-pair release rerun favored the current first pass on `fit_nesting`, `pixels_with_min_expand_constraint`, and equal-weight flex. The large fixed-pixel wide fixture measured 8.96 ms against 8.27 ms for the previous Batch build, with 7 of 17 pairs favoring the current build. A separate direct-Rust probe favored the previous build on the small fixed-pixel wide fixture, so its prior-build comparison depends on the benchmark build and protocol. [Focused release samples](focused-release-first-pairs.tsv)

## Retained solves

After handoff, Batch led dense default on 12 of 13 workloads with a **1.269×** geometric mean speedup. The closest result was `expand_with_min_constraint` at 0.995×. [Warm samples](paired-samples.tsv)

## Verification

All 219 crate tests and 12 order tests passed. The 13 PanGUI fixtures matched dense rectangle bits on the first solve, on the first invalidated solve that builds the Batch graph, and on a retained solve. Browser, compositor, and CAD fixtures matched forced-full layout through 1,440 checked edits each. Focused Verus verified four full-layout obligations, including the cycle rejection path. [Application verification](../../benchmarks/real_workloads/README.md#batch-pearcekelly-pilot)
