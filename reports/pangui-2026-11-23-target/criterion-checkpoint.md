# PanGUI optimization checkpoint, 23 November 2026

Keru led all 13 workloads across 139 supported engine and workload combinations. The smallest lead measured **2.4995×** and the geometric mean against the fastest peer per workload reached **3.3812×**. The geometric mean over all 126 peer comparisons reached **10.1145×**. This checkpoint keeps 2.5× and 5× as the targets for the fastest-peer metrics. [Timings and confidence intervals](timings.tsv)

## Fastest peer per workload

The speedup divides the fastest supported peer's Criterion mean by Keru's mean. Each workload has equal weight in the fastest-peer geometric mean.

| Workload | Keru | Fastest peer | Peer time | Speedup |
| --- | ---: | --- | ---: | ---: |
| `expand_with_max_constraint` | 133.935 µs | Torin | 334.776 µs | 2.4995× |
| `expand_with_min_constraint` | 139.357 µs | Torin | 367.016 µs | 2.6336× |
| `fit_nesting` | 3,787.165 µs | Cephal | 14,963.127 µs | 3.9510× |
| `flex_expand_equal_weights` | 630.889 µs | Cephal | 2,174.424 µs | 3.4466× |
| `flex_expand_weights` | 705.186 µs | Torin | 2,028.312 µs | 2.8763× |
| `nested_vertical_stack` | 287.177 µs | Torin | 1,059.682 µs | 3.6900× |
| `padding_and_margin` | 2.559 µs | Torin | 9.479 µs | 3.7042× |
| `percentage_and_ratio` | 303.867 µs | Morphorm | 1,401.071 µs | 4.6108× |
| `perpendicular_expand_with_wrap` | 702.110 µs | Cephal | 1,894.359 µs | 2.6981× |
| `pixels_with_min_expand_constraint` | 1,750.639 µs | Torin | 4,766.507 µs | 2.7227× |
| `wide_no_wrap_simple_few` | 14.434 µs | Torin | 67.122 µs | 4.6503× |
| `wide_no_wrap_simple_many` | 3,613.465 µs | Morphorm | 13,041.920 µs | 3.6093× |
| `wide_wrapping` | 341.825 µs | Morphorm | 1,288.216 µs | 3.7686× |

## Engine comparisons

| Engine | Shared workloads | Geometric mean peer time ÷ Keru |
| --- | ---: | ---: |
| Torin | 12 | 3.69× |
| Morphorm | 12 | 5.66× |
| Cephal | 13 | 5.89× |
| Backer | 7 | 5.94× |
| hooke | 13 | 6.18× |
| Clay | 8 | 9.41× |
| Ply | 10 | 9.44× |
| Taffy 0.3 | 13 | 12.91× |
| Taffy main | 13 | 14.52× |
| ui_layout | 12 | 23.98× |
| Yoga | 13 | 44.54× |

## Method

The checkpoint used the array-of-structures version of the local full-layout adapter and the same coverage and upstream revision as the earlier report. The Rust 1.99.1 release executable ran on logical CPU 4 of an Intel Xeon Platinum 8573C, after the other benchmark workers had paused. Criterion used ten samples, a 300 ms warm-up, a one-second measurement target and 10,000 bootstrap resamples. Running times are arithmetic means. Adapter rounding, coverage and timing boundaries follow the pinned harness. [Earlier run and reproduction commands](../pangui-2026-11-23-optimized/report.md) · [Upstream benchmarks](https://github.com/DericHuynh/arewelayoutyet/tree/b1f5ff86eae840705950ae037f8d397e0f20a0a2/benchmarks) · [Current adapter](../../benchmarks/arewelayoutyet/adapter.rs)
