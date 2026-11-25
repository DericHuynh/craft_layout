# PanGUI cross-engine results with the original adapter

Across 13 workloads and 11 supported peer engines, Keru’s minimum speedup against the fastest peer was **3.8190×** and the geometric mean was **5.4095×**. Taking the smallest median paired ratio for each workload gave a **3.8480×** minimum and a **5.4387×** geometric mean. [All 126 comparisons](paired-timings.tsv) · [Raw samples](paired-samples.tsv)

## Fastest engine per workload

The fastest peer is the engine with the lowest median time for that workload. The speedup is its median time divided by the median Keru time measured in those same pairs.

| Workload | Keru | Fastest peer | Peer | Speedup |
| --- | ---: | --- | ---: | ---: |
| `expand_with_max_constraint` | 79.542 µs | Torin | 379.528 µs | 4.7714× |
| `expand_with_min_constraint` | 78.967 µs | Torin | 377.839 µs | 4.7848× |
| `fit_nesting` | 2,868.435 µs | Cephal | 16,258.470 µs | 5.6681× |
| `flex_expand_equal_weights` | 314.630 µs | Cephal | 2,281.167 µs | 7.2503× |
| `flex_expand_weights` | 488.590 µs | Torin | 2,093.192 µs | 4.2841× |
| `nested_vertical_stack` | 202.691 µs | Torin | 1,196.931 µs | 5.9052× |
| `padding_and_margin` | 1.473 µs | Torin | 6.826 µs | 4.6342× |
| `percentage_and_ratio` | 200.540 µs | Morphorm | 1,363.193 µs | 6.7976× |
| `perpendicular_expand_with_wrap` | 315.948 µs | Torin | 1,911.354 µs | 6.0496× |
| `pixels_with_min_expand_constraint` | 1,220.784 µs | Torin | 4,662.121 µs | 3.8190× |
| `wide_no_wrap_simple_few` | 9.705 µs | Torin | 65.620 µs | 6.7616× |
| `wide_no_wrap_simple_many` | 2,184.518 µs | Morphorm | 13,209.609 µs | 6.0469× |
| `wide_wrapping` | 238.663 µs | Morphorm | 1,147.868 µs | 4.8096× |

## Per-engine summary

| Peer | Shared workloads | Geometric mean paired speedup |
| --- | ---: | ---: |
| Torin | 12 | 5.83× |
| Morphorm | 12 | 8.83× |
| Cephal | 13 | 9.01× |
| Backer | 7 | 9.16× |
| hooke | 13 | 9.82× |
| Clay | 8 | 14.48× |
| Ply | 10 | 15.03× |
| Taffy 0.3 | 13 | 19.71× |
| Taffy main | 13 | 21.57× |
| ui_layout | 12 | 34.68× |
| Yoga | 13 | 69.37× |

## Method

The run used the original array-of-structs Keru adapter, the pinned PanGUI fixtures, and the upstream peer adapters on logical CPU 4 of an Intel Xeon Platinum 8573C. It alternated the order of the two engines across 21 paired samples. Each sample warmed each tree once before measuring its batch of full solves. The timer starts after cache invalidation and ends when the full layout call returns, matching the upstream boundaries. It excludes template parsing and tree construction. The geometric mean weights the 13 workloads equally. [Sampling patch](paired-sampling.patch) · [Build instructions and peer versions](../pangui-2026-11-23-optimized/report.md)

The run used Rust 1.99.1 and the standard release profile. Native adapters retain the upstream work inside their timed calls, including the declarations and render-command generation in Clay and Ply. The source manifest identifies the measured production code and original adapter. [Source checksums](source-files.sha256) · [Engine and adapter details](../pangui-2026-11-23-optimized/report.md)

## Reproduce the paired run

Use the pinned upstream checkout and Taffy 0.3 compatibility patch from the earlier report. Install the original local adapter at `benchmarks/src/keru_layout_helpers.rs`. From the upstream `benchmarks` directory, copy `benches/pangui.rs` to `benches/pangui_pairs.rs` and apply the sampling patch to that copy. Use a logical CPU available on the host. [Original adapter](../../benchmarks/arewelayoutyet/adapter.rs) · [Sampling patch](paired-sampling.patch) · [Dependency setup](../pangui-2026-11-23-optimized/report.md)

```sh
PANGUI_WARM_BATCHES=1 BINDGEN_EXTRA_CLANG_ARGS="-idirafter $(gcc -print-file-name=include)" \
  taskset -c 4 cargo --config 'patch.crates-io.keru_layout.path="/path/to/craft_layout"' \
  bench --bench pangui_pairs --features cephal,clay,backer,ply,yoga,taffy03,morphorm,torin,keru_layout,hooke,ui-layout
```

## Output, allocations, and verification

Three solves of each template matched the pre-change adapter trace byte for byte. The trace covers 930,708 callbacks in order and 7,445,664 absolute and parent-local edge words, including signed zeros.

All 13 first solves and all repeated batches after the second solve allocated zero bytes. Nine workloads reserved reusable placement buffers on the second solve. The largest reservation was 2,438,820 bytes across two allocations for `fit_nesting`. The two wide fixed-pixel stacks reserved 4,000 and 400,000 bytes, respectively. [Per-workload allocation counts and geometry hashes](allocations.tsv)

Verus passed 1,766 obligations with zero errors in each `--no-cheating` profile. Native tests passed with default features (157) and without them (34). Both release builds passed with `panic=abort` and integer overflow checks enabled. The no-abort proof uses the documented host, resource, and reference-count assumptions. [Proof scope and commands](../../proofs/README.md)
