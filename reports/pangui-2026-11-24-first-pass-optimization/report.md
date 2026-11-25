# First-solve optimization

The first call uses the owned full solver and defers the Pearce–Kelly workspace until a changed solve. An allocation-range hint opens the existing Stack leaf shortcuts on fresh inputs. The shortcuts validate live siblings before committing their result. Rectangle publication places the output next to the incarnation bit. Wrap preparation specializes its child walks by axis. The native sizing continuation borrows the active solver, and sizing skips dispatch for settled nodes with no remaining flow or descendants. [Owned entry](../../src/layout_tree.rs) · [Stack preparation](../../src/prepare_fill_stack.rs) · [Native sizing](../../src/sizing_stack/native.rs)

The release runner compared separately compiled implementations in one process on logical CPU 4. It timed the first solve of two fresh trees per pair, balanced construction and solve order across eight blocks, and compared every published rectangle bit. The suite included 13 PanGUI templates and six browser, compositor, and CAD workloads. Each reference has 608 pairs, with 32 per fixture. Ratios divide candidate time by reference time. The suite ratio is the geometric mean of fixture-level paired medians. [Runner and archived revisions](../../benchmarks/first_solve/README.md)

Against the frozen ordinary owned solver, the CPU ratio was **0.861×** and the elapsed ratio was **0.860×**. The candidate won 16 of 19 CPU medians and 410 of 608 CPU pairs. The small fixed-pixel stack won all 32 CPU pairs. [Owned samples](owned-pairs.tsv) · [Owned summary](owned-summary.tsv)

Against the earlier Batch build, the CPU ratio was **0.808×** and the elapsed ratio was **0.808×**. The candidate won 13 of 19 CPU medians and 390 of 608 CPU pairs. [Prior Batch samples](prior-batch-pairs.tsv) · [Prior Batch summary](prior-batch-summary.tsv)

| Fixture | CPU ratio vs owned | Elapsed ratio vs owned | CPU wins vs owned | CPU ratio vs prior Batch |
| --- | ---: | ---: | ---: | ---: |
| `browser/article_reflow` | 1.036× | 1.032× | 11/32 | 1.027× |
| `browser/product_catalog` | 0.993× | 0.995× | 18/32 | 1.088× |
| `cad/assembly_inspector` | 0.995× | 0.994× | 22/32 | 1.034× |
| `cad/docked_viewport` | 1.024× | 1.022× | 14/32 | 1.011× |
| `compositor/floating_drag_and_raise` | 0.989× | 0.989× | 20/32 | 1.011× |
| `compositor/tiled_split_resize` | 0.989× | 0.988× | 22/32 | 1.011× |
| `expand_with_max_constraint` | 0.924× | 0.927× | 19/32 | 0.984× |
| `expand_with_min_constraint` | 0.977× | 0.983× | 17/32 | 0.970× |
| `fit_nesting` | 0.621× | 0.619× | 30/32 | 0.634× |
| `flex_expand_equal_weights` | 0.531× | 0.524× | 32/32 | 0.503× |
| `flex_expand_weights` | 0.827× | 0.836× | 22/32 | 0.922× |
| `nested_vertical_stack` | 0.936× | 0.934× | 17/32 | 0.863× |
| `padding_and_margin` | 0.734× | 0.723× | 32/32 | 0.742× |
| `percentage_and_ratio` | 0.955× | 0.965× | 19/32 | 0.915× |
| `perpendicular_expand_with_wrap` | 0.932× | 0.934× | 19/32 | 0.501× |
| `pixels_with_min_expand_constraint` | 0.990× | 0.990× | 19/32 | 1.000× |
| `wide_no_wrap_simple_few` | 0.501× | 0.494× | 32/32 | 0.441× |
| `wide_no_wrap_simple_many` | 0.751× | 0.751× | 29/32 | 0.746× |
| `wide_wrapping` | 1.002× | 1.007× | 16/32 | 0.540× |
