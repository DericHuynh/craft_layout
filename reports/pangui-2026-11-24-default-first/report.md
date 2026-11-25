# Default first solve and Pearce–Kelly handoff, 24 November 2026

The first Batch API call uses the default owned solver. The first call was **12.276× faster** by geometric mean than the prior Kahn-first Batch build, with all 13 fixtures improving in all 11 pairs. The first subsequent call that needs work builds and evaluates the Batch graph. The benchmark measures that handoff separately. [Kahn-first baseline](../pangui-2026-11-24-kahn-pearce-kelly/report.md) · [Scheduling design](../../benchmarks/topological_order/README.md#layout-pilot)

## First solve and handoff

Times are medians in milliseconds. Speedups are medians of the paired ratios between first calls. The handoff column measures the first invalidated Batch solve at the same viewport and declarations.

| Workload | Kahn-first Batch | Default-first Batch | Owned default | Dense default | Batch handoff | First-solve speedup | Wins |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 2.993 | 0.197 | 0.209 | 0.183 | 2.911 | 14.704× | 11/11 |
| `expand_with_min_constraint` | 2.044 | 0.121 | 0.117 | 0.089 | 2.533 | 17.356× | 11/11 |
| `fit_nesting` | 128.301 | 14.203 | 13.443 | 11.650 | 130.764 | 8.946× | 11/11 |
| `flex_expand_equal_weights` | 12.512 | 1.121 | 1.403 | 1.140 | 8.816 | 11.956× | 11/11 |
| `flex_expand_weights` | 6.959 | 0.667 | 0.785 | 0.555 | 6.061 | 10.748× | 11/11 |
| `nested_vertical_stack` | 4.355 | 0.286 | 0.244 | 0.268 | 3.993 | 16.149× | 11/11 |
| `padding_and_margin` | 0.049 | 0.006 | 0.006 | 0.005 | 0.050 | 8.963× | 11/11 |
| `percentage_and_ratio` | 4.472 | 0.274 | 0.335 | 0.260 | 4.335 | 16.121× | 11/11 |
| `perpendicular_expand_with_wrap` | 5.410 | 0.453 | 0.825 | 0.395 | 5.606 | 12.448× | 11/11 |
| `pixels_with_min_expand_constraint` | 31.230 | 1.942 | 1.600 | 1.293 | 32.885 | 15.773× | 11/11 |
| `wide_no_wrap_simple_few` | 0.233 | 0.022 | 0.031 | 0.019 | 0.178 | 10.552× | 11/11 |
| `wide_no_wrap_simple_many` | 83.037 | 8.564 | 7.972 | 5.068 | 61.754 | 10.052× | 11/11 |
| `wide_wrapping` | 5.480 | 0.544 | 1.093 | 0.609 | 5.089 | 10.082× | 11/11 |

The release runner measured 11 pairs of fresh processes and alternated process order on logical CPU 4 of an Intel Xeon Platinum 8573C. The timer includes sizing and publication. Template parsing, tree construction, invalidation, and rectangle inspection run outside the timer. The first call reports zero Batch work. Slot and edge counts in the current samples come from the handoff. They match the counts from the prior Kahn build. Both builds matched exact dense rectangle bits, and the current build also checked the handoff and the first retained solve. [Reproduction commands](../../benchmarks/arewelayoutyet/README.md#compare-batch-pearcekelly-with-the-upstream-engines) · [First-solve and handoff samples](first-solve-pairs.tsv)

## Warm solve

After handoff, Batch led dense default on **13 of 13** warmed workloads by paired median. The geometric mean speedup was **1.268×**. The runner measured 21 rounds across 126 supported peer and workload pairs. [Warm samples](paired-samples.tsv)

Times are medians in microseconds. The last column uses paired ratios.

| Workload | Dense default | Owned default | Batch | Dense ÷ Batch |
| --- | ---: | ---: | ---: | ---: |
| `expand_with_max_constraint` | 72.863 | 97.830 | 73.503 | 1.0020× |
| `expand_with_min_constraint` | 74.451 | 97.322 | 72.026 | 1.0287× |
| `fit_nesting` | 4,434.248 | 4,866.451 | 4,284.413 | 1.1158× |
| `flex_expand_equal_weights` | 288.196 | 421.645 | 264.311 | 1.0861× |
| `flex_expand_weights` | 413.136 | 505.664 | 380.105 | 1.0891× |
| `nested_vertical_stack` | 175.691 | 252.614 | 162.561 | 1.0909× |
| `padding_and_margin` | 1.445 | 1.664 | 0.795 | 1.8088× |
| `percentage_and_ratio` | 176.937 | 284.584 | 131.879 | 1.3369× |
| `perpendicular_expand_with_wrap` | 284.416 | 857.553 | 242.223 | 1.1654× |
| `pixels_with_min_expand_constraint` | 1,200.851 | 1,351.799 | 1,005.432 | 1.1878× |
| `wide_no_wrap_simple_few` | 9.690 | 12.730 | 4.744 | 2.0617× |
| `wide_no_wrap_simple_many` | 3,576.043 | 4,816.444 | 1,973.393 | 1.8665× |
| `wide_wrapping` | 217.094 | 678.465 | 186.472 | 1.1471× |

## Verification

The first default sizing pass checks for cycles before placing rectangles. The Batch entry restores the previous warnings if sizing rejects. The measurers can run before the default sizing pass encounters a cycle. Native regressions cover rejection, recovery, idle reuse, handoff after parameter, content, and viewport edits, and subsequent backward-edge repair. [Default cycle gate](../../src/full_layout.rs) · [Layout tests](../../tests/batch_layout.rs)

All 218 crate tests and 12 standalone order tests passed. The six browser, compositor, and CAD fixtures matched forced-full rectangle bits on the initial solve, 24 warmup edits, and 1,440 additional edits each. Focused Verus checked four obligations in the shared full-layout module, including closing packed capture when the new first-solve path rejects. The end-to-end Batch equivalence proof remains open. [Application verification](../../benchmarks/real_workloads/README.md#batch-pearcekelly-pilot)
