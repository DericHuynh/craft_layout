# Application layout benchmarks

These fixtures model browser pages, Linux compositor workspaces, and CAD editor panels. Each workload replays a deterministic sequence of UI events through the public `LayoutTree` API. Text uses the library's monospace measurer.

```sh
cargo bench --locked --bench real_workloads
cargo bench --locked --bench real_workloads -- --filter browser/ --frames 240
cargo bench --locked --bench real_workloads -- --verify-only
```

| Workload | Layout and edits |
| --- | --- |
| `browser/article_reflow` | Long article with Block flow, wrapping paragraphs, captions, and auto margins. Replays paragraph edits and desktop-to-mobile viewport changes. |
| `browser/product_catalog` | Responsive product grid and wrapping filter bar. Changes the viewport and filters out-of-stock cards. |
| `compositor/tiled_split_resize` | Panels and nested splits contain 24 decorated clients. Drags a split and resizes the output at fractional pixel scale. |
| `compositor/floating_drag_and_raise` | Eighteen floating clients have fixed geometry and decorations. Drags and raises windows and toggles a popup at fractional pixel scale. |
| `cad/docked_viewport` | A wrapping command ribbon, weighted drawing views, and model and property panels. Resizes a dock and the window and changes the active projection label. |
| `cad/assembly_inspector` | Assembly tree and grouped property inspector. Expands and collapses subassemblies, reorders a component, and adds and removes inspection details. |

The runner builds two equivalent trees per workload. Both receive the same edits. One uses normal incremental layout, and the other is explicitly invalidated before each solve. The benchmark alternates solve order and measures 120 frames by default. Construction, edits, invalidation, and geometry inspection are outside the timer.

The TSV reports the initial node count including the root and disabled nodes, median and 95th-percentile solve latency in microseconds, and the number of incremental frames that fell back to a full solve. The median averages the two middle samples for even sample counts. The 95th percentile uses nearest rank. The initial solve, 24 warmup frames, and the final measured frame compare tree order, rectangle availability, and exact rectangle bits with the forced-full reference. `--verify-only` runs the initial and warmup checks.
