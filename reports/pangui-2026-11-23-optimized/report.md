# PanGUI cross-engine benchmarks, 23 November 2026

The optimized `craft_layout` checkout was fastest on **12 of 13** workloads. The geometric mean of the fastest peer time divided by Keru time was **2.10×**. This run measured 139 supported engine and workload combinations. [All timings and 95% confidence intervals](timings.tsv)

## Engine comparisons

Each ratio is the geometric mean of peer time divided by Keru time over that peer’s shared workloads. Each workload has equal weight.

| Peer | Shared workloads | Keru wins | Time ÷ Keru |
| --- | ---: | ---: | ---: |
| Torin | 12/13 | 11 | 2.24× |
| Morphorm | 12/13 | 12 | 3.40× |
| Cephal | 13/13 | 13 | 3.55× |
| hooke | 13/13 | 13 | 3.85× |
| Backer | 7/13 | 7 | 4.90× |
| Ply | 10/13 | 10 | 6.00× |
| Clay | 8/13 | 8 | 7.51× |
| Taffy 0.3 | 13/13 | 13 | 7.73× |
| Taffy main | 13/13 | 13 | 8.64× |
| ui_layout | 12/13 | 12 | 13.68× |
| Yoga | 13/13 | 13 | 27.19× |

## Per workload

Times are Criterion arithmetic means in milliseconds. Rank includes every supported configuration for that workload.

| Workload | Keru ms | Fastest peer | Peer ms | Keru rank | Peer ÷ Keru |
| --- | ---: | --- | ---: | ---: | ---: |
| `expand_with_max_constraint` | 0.3005 | Torin | 0.3479 | 1/12 | 1.16× |
| `expand_with_min_constraint` | 0.2572 | Torin | 0.3662 | 1/12 | 1.42× |
| `fit_nesting` | 6.2199 | Cephal | 15.4510 | 1/12 | 2.48× |
| `flex_expand_equal_weights` | 0.9568 | Cephal | 2.1121 | 1/12 | 2.21× |
| `flex_expand_weights` | 1.0391 | Torin | 2.1295 | 1/10 | 2.05× |
| `nested_vertical_stack` | 0.3018 | Torin | 1.0377 | 1/12 | 3.44× |
| `padding_and_margin` | 0.0032 | Torin | 0.0062 | 1/8 | 1.94× |
| `percentage_and_ratio` | 0.3495 | Morphorm | 1.2376 | 1/9 | 3.54× |
| `perpendicular_expand_with_wrap` | 1.2050 | Cephal | 1.9409 | 1/10 | 1.61× |
| `pixels_with_min_expand_constraint` | 4.9135 | Torin | 4.4395 | 2/9 | 0.90× |
| `wide_no_wrap_simple_few` | 0.0143 | Torin | 0.0681 | 1/12 | 4.76× |
| `wide_no_wrap_simple_many` | 3.2567 | Morphorm | 13.0432 | 1/11 | 4.01× |
| `wide_wrapping` | 0.9081 | Morphorm | 1.1233 | 1/10 | 1.24× |

## Method

The run used the Rust 1.99.1 release profile pinned to logical CPU 4 on an Intel Xeon Platinum 8573C host. Criterion used ten flat samples, 300 ms of warm-up, a one-second measurement target, and 10,000 bootstrap resamples. The accompanying TSV reports all available estimates. The suite skipped configurations according to its adapter coverage.

All configurations ran the same 13 text-free PanGUI templates from arewelayoutyet revision `b1f5ff86eae840705950ae037f8d397e0f20a0a2`. The local Keru adapter runs full unrounded layout and writes absolute rectangles. The two Taffy versions, Yoga, and Cephal round by default. Taffy 0.3 uses its default cross-line alignment. Clay and Ply include native element declarations and render-command generation in the timer. Other adapters run solver work with construction and cache invalidation outside the timer. Adapter policies and resulting layout geometry can differ across engines. [Upstream suite and adapter notes](https://github.com/DericHuynh/arewelayoutyet/tree/b1f5ff86eae840705950ae037f8d397e0f20a0a2/benchmarks) · [Local adapter](../../benchmarks/arewelayoutyet/adapter.rs)

The Taffy 0.3 adapter uses a small compatibility patch for the pinned main-branch Taffy API. Yoga’s binding generator used the host GCC include directory. The scratch build applied Yoga’s existing `YGUndefined` type correction to unformatted bindgen output because `rustfmt` was unavailable. [Taffy 0.3 compatibility patch](taffy03-compat.patch)

## Reproduce

Check out the pinned upstream revision. Replace `benchmarks/src/keru_layout_helpers.rs` with the local adapter and apply the compatibility patch in the upstream checkout. Run from the upstream `benchmarks` directory with `rustfmt` and the host C/C++ headers available.

```sh
BINDGEN_EXTRA_CLANG_ARGS="-idirafter $(gcc -print-file-name=include)" \
  taskset -c 4 cargo --config 'patch.crates-io.keru_layout.path="/path/to/craft_layout"' \
  bench --bench pangui --features cephal,clay,backer,ply,yoga,taffy03,morphorm,torin,keru_layout,hooke,ui-layout \
  -- --noplot --sample-size 10 --warm-up-time 0.3 --measurement-time 1 --nresamples 10000
```

## Resolved engines

| Configuration | Version | Source |
| --- | --- | --- |
| Backer | 0.12.0 | crates.io |
| Cephal | 0.2.0 | Git `9e77f9100ab3b2f55ade85dd5f24bb987fd28982` |
| Clay | 0.4.0 | crates.io |
| hooke | 0.1.0 | crates.io |
| Keru optimized | 0.1.0 | Optimized local checkout |
| Morphorm | 0.9.0 | crates.io |
| Ply | 1.1.1 | crates.io |
| Taffy 0.3 | 0.3.19 | crates.io |
| Taffy main | 0.15.0 | Git `4e59968eda29ceeb0bbaeb3993c8cd38baa3d0a6` |
| Torin | 0.5.0 | crates.io |
| ui_layout | 0.12.1 | Git `cffdbc4bc0e4f54b9a4466847528fbfa2127648a` |
| Yoga | 0.5.0 | crates.io |
