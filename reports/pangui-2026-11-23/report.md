# PanGUI layout benchmarks, 23 November 2026

Current Keru ranked first on **13 of 13 workloads** against the supported peer adapters. The geometric mean of the fastest peer time divided by current Keru time was **2.54×**. The equal-workload geometric mean changes were **-54.7%** against the saved Keru snapshot (13 shared workloads) and **-64.6%** against the published crate (10 shared workloads).

The run includes 162 freshly measured engine and workload combinations across 14 configurations and 13 templates. An em dash marks an unsupported combination. [Timing data with 95% intervals](timings.tsv) · [Website history](../../arewelayoutyet/site/data/history.json)

## Keru by workload

Times are Criterion arithmetic means in milliseconds. Rank includes current Keru and the supported peers for that workload. Historical Keru configurations are shown separately. The ratio divides fastest peer time by current Keru time, so values above 1 favor Keru.

| Workload | Current ms | Saved snapshot ms | Published ms | Fastest peer | Peer ms | Rank | Peer ÷ current |
|---|---:|---:|---:|---|---:|---:|---:|
| expand_with_max_constraint | 0.1409 | 0.2797 | 0.2774 | Torin | 0.2752 | 1/12 | 1.95× |
| expand_with_min_constraint | 0.1397 | 0.2783 | 0.2810 | Torin | 0.2765 | 1/12 | 1.98× |
| fit_nesting | 4.8960 | 8.5143 | 11.9777 | Cephal | 12.0149 | 1/12 | 2.45× |
| flex_expand_equal_weights | 0.4404 | 1.4398 | 1.2781 | Cephal | 1.2144 | 1/12 | 2.76× |
| flex_expand_weights | 0.4297 | 1.3023 | 1.1999 | Torin | 1.3854 | 1/10 | 3.22× |
| nested_vertical_stack | 0.1946 | 0.7110 | 0.8096 | Torin | 0.6343 | 1/12 | 3.26× |
| padding_and_margin | 0.0037 | 0.0086 | — | Torin | 0.0068 | 1/8 | 1.83× |
| percentage_and_ratio | 0.1955 | 0.8453 | 0.7648 | Morphorm | 0.9057 | 1/9 | 4.63× |
| perpendicular_expand_with_wrap | 0.6559 | 0.9812 | — | Cephal | 1.2388 | 1/10 | 1.89× |
| pixels_with_min_expand_constraint | 2.3598 | 2.8629 | 2.8778 | Torin | 3.5935 | 1/9 | 1.52× |
| wide_no_wrap_simple_few | 0.0106 | 0.0253 | 0.0619 | Torin | 0.0549 | 1/12 | 5.18× |
| wide_no_wrap_simple_many | 2.3811 | 4.6759 | 8.4202 | Morphorm | 8.2804 | 1/11 | 3.48× |
| wide_wrapping | 0.4915 | 0.6815 | — | Morphorm | 0.7544 | 1/10 | 1.53× |

## Sizing and constraints

Arithmetic mean milliseconds per solve.

| Engine | expand with max constraint | expand with min constraint | flex expand equal weights | flex expand weights | percentage and ratio | pixels with min expand constraint |
|---|---:|---:|---:|---:|---:|---:|
| Keru current | 0.1409 | 0.1397 | 0.4404 | 0.4297 | 0.1955 | 2.3598 |
| Saved Keru snapshot | 0.2797 | 0.2783 | 1.4398 | 1.3023 | 0.8453 | 2.8629 |
| Keru published 0.1.0 | 0.2774 | 0.2810 | 1.2781 | 1.1999 | 0.7648 | 2.8778 |
| Backer | 0.4343 | 0.4346 | 1.7801 | — | — | — |
| Cephal | 0.9760 | 0.9666 | 1.2144 | 3.4549 | 1.6559 | 10.2924 |
| Clay | 0.5581 | 0.8335 | 3.0996 | — | 2.7763 | — |
| hooke | 1.0312 | 1.0404 | 1.7708 | 2.5705 | 1.1601 | 12.4431 |
| Morphorm | 0.8356 | 0.8197 | 1.4094 | 1.5912 | 0.9057 | 5.5545 |
| Ply | 0.5543 | 0.6697 | 3.7211 | 5.4980 | 2.1575 | — |
| Taffy 0.3 | 1.3299 | 1.3114 | 4.5669 | 7.5004 | 2.0029 | 22.0988 |
| Taffy main | 1.7057 | 1.6858 | 3.5626 | 9.2089 | 2.6823 | 29.1961 |
| Torin | 0.2752 | 0.2765 | 1.4697 | 1.3854 | — | 3.5935 |
| ui_layout | 1.4763 | 1.5865 | 8.0852 | 10.6793 | — | 25.8233 |
| Yoga | 2.0819 | 2.0471 | 10.3446 | 11.5710 | 6.4698 | 23.0849 |

## Stacks, nesting and wrapping

Arithmetic mean milliseconds per solve.

| Engine | fit nesting | nested vertical stack | padding and margin | perpendicular expand with wrap | wide no wrap simple few | wide no wrap simple many | wide wrapping |
|---|---:|---:|---:|---:|---:|---:|---:|
| Keru current | 4.8960 | 0.1946 | 0.0037 | 0.6559 | 0.0106 | 2.3811 | 0.4915 |
| Saved Keru snapshot | 8.5143 | 0.7110 | 0.0086 | 0.9812 | 0.0253 | 4.6759 | 0.6815 |
| Keru published 0.1.0 | 11.9777 | 0.8096 | — | — | 0.0619 | 8.4202 | — |
| Backer | 14.5758 | 1.2014 | — | — | 0.1264 | 15.4144 | — |
| Cephal | 12.0149 | 0.9374 | 0.0115 | 1.2388 | 0.0899 | 12.8043 | 0.9147 |
| Clay | 24.9390 | 1.8766 | — | — | 0.1586 | 16.6208 | — |
| hooke | 21.5625 | 1.0647 | 0.0117 | 1.8948 | 0.1183 | 15.2150 | 1.1133 |
| Morphorm | 69.6898 | 0.8171 | — | 1.8056 | 0.0768 | 8.2804 | 0.7544 |
| Ply | 39.8278 | 1.8237 | — | 2.6962 | 0.1646 | — | 2.1154 |
| Taffy 0.3 | 147.1599 | 2.2136 | 0.0176 | 3.3151 | 0.1481 | 30.3292 | 2.0135 |
| Taffy main | 39.6516 | 2.6524 | 0.0228 | 4.1720 | 0.2301 | 47.6971 | 2.7963 |
| Torin | 28.1805 | 0.6343 | 0.0068 | 1.3210 | 0.0549 | 13.4363 | 0.9526 |
| ui_layout | 95.3213 | 5.2260 | 0.0418 | 7.4047 | 0.3624 | 58.6016 | 5.3712 |
| Yoga | 118.4085 | 6.1880 | 0.0625 | 79.1868 | 0.4358 | 51.7535 | 23.9423 |

## Method

The Criterion run pinned all configurations to logical CPU 6 of an AMD Ryzen 7 5800H. The Rust 1.97.0 release build used ten flat samples per supported combination, a 300 ms warm-up, and a one-second measurement target. The TSV includes bootstrap 95% confidence intervals for each mean.

All configurations use the same 13 PanGUI templates and their existing adapters. Retained-tree engines run full layout after invalidation, with tree construction and invalidation outside timing. Clay and Ply time element declarations and render-command generation as part of their native passes. Backer and ui_layout rebuild their native inputs outside timing to clear private state. Adapters can differ in layout semantics and pixel rounding. The templates exercise text-free full layout. [Adapter methodology](../../arewelayoutyet/benchmarks/UPSTREAM.md)

Current Keru is the local workspace build, including uncommitted changes. The saved Keru snapshot is the local comparison source in the harness. Both use the extended Keru adapter. The published crate uses its original adapter. The Taffy 0.3 adapter includes the existing compatibility adjustments for the pinned templates.

## Resolved engines

| Configuration | Version | Source |
|---|---|---|
| Keru current | 0.1.0 | Local workspace |
| Saved Keru snapshot | 0.1.0 | Saved local source |
| Keru published 0.1.0 | 0.1.0 | crates.io |
| Backer | 0.12.0 | crates.io |
| Cephal | 0.2.0 | Pinned Git revision `9e77f9100ab3b2f55ade85dd5f24bb987fd28982` |
| Clay | 0.4.0 | crates.io |
| hooke | 0.1.0 | crates.io |
| Morphorm | 0.9.0 | crates.io |
| Ply | 1.1.1 | crates.io |
| Taffy 0.3 | 0.3.19 | crates.io |
| Taffy main | 0.15.0 | Pinned Git revision `4e59968eda29ceeb0bbaeb3993c8cd38baa3d0a6` |
| Torin | 0.5.0 | crates.io |
| ui_layout | 0.12.1 | Pinned Git revision `cffdbc4bc0e4f54b9a4466847528fbfa2127648a` |
| Yoga | 0.5.0 | crates.io |
