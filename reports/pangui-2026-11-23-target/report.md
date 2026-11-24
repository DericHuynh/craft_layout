# PanGUI results with dense adapter storage, 23 November 2026

In 126 peer comparisons across 13 workloads, the lowest speedup was **3.3462×**. The fastest-peer geometric mean was **5.0436×**, and the geometric mean across all peer comparisons was **15.4267×**. [Paired estimates](paired-timings.tsv) · [Raw samples](paired-samples.tsv)

## Fastest peer per workload

Each speedup is the median of 21 paired peer-to-Keru time ratios. The two time columns show the median observed time for each engine in those pairs. The fastest peer is the one with the lowest median paired speedup against Keru.

| Workload | Keru | Fastest peer | Peer time | Speedup |
| --- | ---: | --- | ---: | ---: |
| `expand_with_max_constraint` | 64.760 µs | Torin | 295.674 µs | 4.6471× |
| `expand_with_min_constraint` | 64.357 µs | Torin | 332.265 µs | 4.8952× |
| `fit_nesting` | 4,095.641 µs | Backer | 18,892.562 µs | 4.6565× |
| `flex_expand_equal_weights` | 289.345 µs | Torin | 2,038.739 µs | 6.9516× |
| `flex_expand_weights` | 321.415 µs | Torin | 1,856.452 µs | 5.9151× |
| `nested_vertical_stack` | 165.999 µs | Torin | 897.299 µs | 5.4398× |
| `padding_and_margin` | 1.563 µs | Torin | 5.332 µs | 3.3462× |
| `percentage_and_ratio` | 197.244 µs | Morphorm | 1,215.996 µs | 6.2086× |
| `perpendicular_expand_with_wrap` | 245.738 µs | Torin | 1,684.188 µs | 6.5285× |
| `pixels_with_min_expand_constraint` | 925.518 µs | Torin | 3,989.167 µs | 4.2437× |
| `wide_no_wrap_simple_few` | 12.781 µs | Torin | 54.129 µs | 4.3061× |
| `wide_no_wrap_simple_many` | 2,490.974 µs | Torin | 11,683.327 µs | 4.5823× |
| `wide_wrapping` | 222.504 µs | Morphorm | 1,120.378 µs | 5.0781× |

## Engine comparisons

| Engine | Shared workloads | Geometric mean paired speedup |
| --- | ---: | ---: |
| Torin | 12 | 5.38× |
| Backer | 7 | 8.56× |
| Morphorm | 12 | 9.07× |
| Cephal | 13 | 9.56× |
| hooke | 13 | 9.82× |
| Clay | 8 | 14.29× |
| Ply | 10 | 15.57× |
| Taffy 0.3 | 13 | 19.21× |
| Taffy main | 13 | 21.67× |
| ui_layout | 12 | 33.79× |
| Yoga | 13 | 66.93× |

## Method

The paired runner uses the pinned PanGUI templates and upstream engine adapters. It alternates the order of Keru and one peer on logical CPU 4 of an Intel Xeon Platinum 8573C. Each batch consists of full solves timed with the same per-iteration wall clock as the upstream runner. It constructs the trees and invalidates their caches outside the timer. Pairing reduces the effect of timing swings observed during sequential Criterion runs. The speedup geometric means give equal weight to each included workload or peer comparison. [Sampling patch](paired-sampling.patch) · [Pinned versions, compatibility patch and build options](../pangui-2026-11-23-optimized/report.md)

Keru's adapter stores links, parent IDs, declarations, sizing records, and output rectangles in separate arrays. The storage change added setup arrays and reduced the per-node footprint from 296 to 276 bytes on this host. The first and warmed solves allocated zero bytes in the instrumented PanGUI probe. The adapter publishes rectangle geometry on every full solve. [Dense storage patch](dense-storage.patch) · [Adapter and probe](../../benchmarks/arewelayoutyet/README.md)

## Reproduce the paired run

Use the pinned upstream checkout and Taffy 0.3 compatibility patch described in the earlier report. Apply the dense storage patch to a copy of the local Keru adapter before installing it in the upstream benchmark checkout. Apply the paired-sampling patch from the upstream `benchmarks` directory. Run the same Cargo benchmark command with the features shown in the earlier report and without the Criterion arguments after `--`. The runner prints the per-sample TSV to standard output. [Earlier build instructions](../pangui-2026-11-23-optimized/report.md) · [Paired sampling patch](paired-sampling.patch)

## Verification

All 13 workloads matched their baseline rectangle hashes and allocation counts in paired probes. A separate adapter audit compared the order of output callbacks and every absolute and local edge word across two full solves of every template. Verus passed 1,717 obligations with zero errors in each of the debug and optimized configurations under the documented host assumptions. Native tests and release builds with panic abort and overflow checking passed with and without default features. [Verification scope and commands](../../proofs/README.md) · [Sequential Criterion checkpoint](criterion-checkpoint.md)
