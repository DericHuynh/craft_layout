# `keru_layout`

`keru_layout` is a UI layout library that uses a new algorithm. It's used in the [Keru GUI library](https://github.com/kekelp/keru/), but it's available here as a self-contained crate.

## The Idea

Most layout algorithms will do one or more traversals of the tree of UI elements and calculate the size and position of each element as they go.

However, the kind of dependencies that layout libraries usually expose can go along the direction of the tree (`Frac`, `Fill`), but also in the opposite direction (`FitContent`), or "laterally" (`AspectRatio`, wrapping text).

In short, the idea of this library is to consider the resulting graph of dependencies and to solve it directly. The algorithm traverses the abstract dependency graph rather than the real UI tree.

## Advantages

- Performance: this library is very fast. [See this page for benchmarks](https://kekelp.github.io/arewelayoutyet/). Forked from [this repo](https://github.com/marc2332/arewelayoutyet) from the Torin author.

    `keru_layout` is the fastest or close to the fastest in all the categories that it supports. While other libraries have their strengths and their weaknesses, `keru_layout` is consistently fast in all cases. 
    
    It's likely that the other libraries are going faster when their top-down or bottom-up traversals of the UI tree happen to line up with the real structure of the dependency graph, and slower when the shapes don't match as well. By traversing the dependency graph directly, the new algorithm has more consistent performance regardless of the layout.

- Correctness: in some rare cases, such as layouts with many `AspectRatio` dependencies, a traditional tree-based algorithm would have to perform many traversals of the UI tree in order to finally compute the correct results. To avoid spending too much time on layout, many libraries will cut corners and silently produce an inconsistent layout.

    I wrote about one of these cases in this older [blog post](https://kekelp.github.io/keru/blog/layout/).

- Developer Experience: while it's usually not a problem to work around the correctness issues of traditional layout algorithms, it can still be confusing to run into them during development. Using a more consistent algorithm leads to fewer surprises and less confusion.

- Debuggability: almost all layout systems can express cyclic dependencies between elements, but in a traditional tree-based algorithm, this will result in a silently "broken" or inconsistent layout. With this algorithm, we can give the user a clear warning and an accurate list of the nodes that were stuck in cycles.

## Benchmarks

Run `cargo bench --bench real_workloads` for browser, Linux compositor, and CAD layout scenarios. The suite measures full and incremental layout over the same edit sequences. [Workloads and measurement method](benchmarks/real_workloads/README.md)

The benchmark handoff covers first solves, peer engines, application edits, and topological-order experiments. [Benchmark runners and adapters](benchmarks/README.md)

## Application layouts

Each sample runs a sequence of edits, checks expected geometry, and compares the retained tree with a fresh build. The authors recorded their first layout declarations before running the samples. The paired runs replay the same inputs with an alternative declaration.

| Project | Geometry under test |
| --- | --- |
| [Editor workbench](examples/editor_workbench) | Weighted panes, measured tabs, wrapped source lines and a draggable terminal. |
| [Check-in kiosk](examples/checkin_kiosk) | Translated booking text, validation, a compact summary and the one-pixel threshold at which appointment controls wrap. |
| [Command palette](examples/command_palette) | Fitted, variable-width menus, a nested coordinate frame and the choice of edge when a popup cannot fit on either side of the pointer. |
| [Mixing studio](examples/mixing_studio) | Track insertion, a removable send rack, selection overlays and two meters per channel. |
| [Dispatch board](examples/dispatch_board) | Twenty-four localized ticket rows, independently shrinkable fields, a protected action and embedded LTR content. |
| [Maintenance console](examples/maintenance_console) | Shared label and field columns, a panel-local breakpoint, a sticky heading and help anchored to a scrolling control. |

For a free-positioned popup that should remain eight pixels inside the far edge as its parent resizes, use `Pos::Offset { fraction: 1.0, pixels: -8.0 }` with `Anchor::End` on that axis. Downstream code that exhaustively matches `Pos` must handle the new variant.

## Native layout rules

Use `LayoutTree::set_rules` for an application that needs inherited writing direction, flexible lines, heterogeneous grid tracks, scrollports, or size queries. Rules attach to stable node handles. Edit the original `LayoutParams` or rules and solve again after an edit. Reading `params` returns the authored physical declarations. Passing `NodeRules::default()` to `set_rules` removes the optional declarations on that node.

```rust
# #[cfg(feature = "incremental")]
# fn main() -> Result<(), keru_layout::TreeError> {
use keru_layout::{LayoutParams, LayoutTree, Size, Xy};
use keru_layout::flex::{FlexItem, FlexLayout};
use keru_layout::layout_rules::NodeRules;

let mut tree = LayoutTree::<()>::new();
let row = tree.root();
tree.set_rules(&row, NodeRules {
    flex: Some(FlexLayout { gap: 10.0, ..Default::default() }),
    ..Default::default()
})?;
let mut fields = Vec::new();
for width in [160.0, 120.0] {
    let field = tree.add_node(&row, LayoutParams {
        size: Xy::new(Size::Pixels(width), Size::Pixels(24.0)),
        ..LayoutParams::DEFAULT
    })?;
    tree.set_rules(&field, NodeRules {
        flex_item: FlexItem { shrink: 1.0, ..Default::default() },
        ..Default::default()
    })?;
    fields.push(field);
}
tree.solve_layout(Xy::new(220.0, 40.0));
assert_eq!(tree.layout(&fields[0])?.x, [0.0, 120.0]);
assert_eq!(tree.layout(&fields[1])?.x, [130.0, 220.0]);
# Ok(())
# }
# #[cfg(not(feature = "incremental"))]
# fn main() {}
```

| When authoring | Contract |
| --- | --- |
| Localized UI | `LogicalStyle` inherits direction and writing mode independently. Logical start/end padding and margins map to physical edges. Set the direction of an embedded editor on the editor itself. |
| Text and controls | Implement `InlineMeasurer` for horizontal line metrics, then use `solve_layout_with_typography`. A bounded fit-content width stays between the measured minimum and maximum. The host supplies line breaking, shaping, and the baseline offsets. |
| Flexible rows and columns | Fixed preferred sizes keep their size by default. Set `grow` or `shrink` on the items permitted to change. A binding lower or upper bound redistributes the rest among eligible items. Native `Fill` retains its weighted share when an item has no explicit flexibility. |
| Track grids | Use `TrackGrid` and `GridItem` for explicit and implicit tracks. Track indices are zero-based. In a nested form row, `TrackAxis::Subgrid` inherits the tracks spanned by that row, including their gaps. Descendant labels can contribute to the parent’s content track. |
| Scrolling and overlays | Read `layout` for unscrolled flow geometry. Read `view_geometry` for window-space drawing, clip, scrollport, and applied offset. `set_scroll_offset` accepts a request, which the next solve clamps. Anchor fallback checks the authored sides in order. |
| Responsive components | Put size containment on the ancestor axis used for a breakpoint. A child query reads the nearest eligible ancestor’s content-box size, optionally by name. A fitted contained axis uses its intrinsic placeholder and padding. |
| Diagnostics | Read `warnings` for the underlying solver and `rule_issues` for missing dependencies, incompatible declarations, and unresolved geometry. |

The owned tree integrates these rules with its existing measurement, placement, invalidation, and publication paths. Trees authored entirely with native `LayoutParams` go directly to the existing solver. Custom `TreeAdapter` implementations can use the public logical projection, flexible-line, and grid-track functions when integrating their own node store. The [implementation goal and acceptance checks](reports/constraint-semantics/implementation-goal.md) describe the tested scope.

## Usage

`keru_layout` has a trait-based API similar to Taffy's low-level API.
There's also an alternative API similar to Taffy's high-level API where the library provides a ready-to-use `LayoutTree`, but it's only meant for quick experiments, examples and testing.

The trait-based API assumes that you already have a tree of UI elements, and that every UI element roughly corresponds to one layout element. Then, using the library looks like this:

1) Add a `LayoutParams` to each UI node. This is the struct that defines the node's layout role (size, position, stack, grid, etc).
2) Add a `NodeLayoutData` to each UI node. This is a small opaque struct that the solver uses to store per-node intermediate results and flags.

    >The layout solver could store all the `NodeLayoutData`s internally, but then it would have to maintain a mapping between your `NodeId`s and its own internal `NodeLayoutData` ids. If you help the solver out by storing the `NodeLayoutData`s in your own tree, it can go much faster.

    >If your UI nodes already have a lot of data in them, it may be good for performance to store the `LayoutParams` and `NodeLayoutData` separately: for example, in a `SecondaryMap` if the tree is a `SlotMap`, or in a parallel `Vec` if the tree is a `Slab`.

3) Add a single centralized `LayoutData` to your top level struct, or anywhere.

4) Implement the `TreeAdapter` trait for the whole UI tree:

    - Set the `NodeId` type to the Id that can be used to refer to nodes in the UI tree, such as a slotmap key or a slab index.
    - Fill in the `node_layout_params()`, `node_layout_data()`, `node_layout_data_mut()` and `layout_data()` to simply access the data corresponding to that `NodeId`.

    - Implement the `root()`, `parent()`, `first_child()`, `next_sibling()` methods so that the layout solver can read the preexisting tree links of your UI nodes.

    - Implement `measure_text_width()` and `measure_text_height()` for text, or `measure_content()` for other intrinsic content. These methods default to zero.

    - Finally, implement the `write_output_rect()` callback, and make it write provided output rects where you need them to go, such as a `rect` field in the UI node.

    - Optionally, implement the `layout_warning()` callback to notify the user about any cycles or other issues in their layout.

Then, you can call the trait's `solve_layout()` method to calculate the layout and write all the output sizes.

### `LayoutTree` API

Create a `LayoutTree`, then insert nodes into the layout tree to match the structure of your UI tree, run `tree.solve_layout()`, then use `tree.layout()` on each node to extract the results and use them to update the corresponding UI node.

`tree.root()` returns a `NodeId`, and insertion returns a `ChildId`. Borrow either handle for lookups and parent arguments. Moves and removals take a `ChildId`. Choose `Destination::LastChildOf` to append under a parent or `Destination::Before` to insert before a child under that child's current parent. Node operations report stale or foreign handles. `tree.layout()` returns the last published rectangle and reports `TreeError::LayoutUnavailable` for new or disabled nodes. Cloned trees have their own handles, accessible through the clone's root and children. The clone's first solve refreshes its measurements. `LayoutTree::with_capacity` returns a capacity error if the requested reservation fails.

Use `to_svg()` to draw the resulting layout. To reuse an output buffer across frames, clear a `String` and pass it to `write_svg()` or `write_svg_with_text()`.

```rust,no_run
use keru_layout::*;

# fn main() -> Result<(), Box<dyn std::error::Error>> {
# #[cfg(feature = "incremental")]
# {
let mut tree: LayoutTree = LayoutTree::new();
let row = tree.add_node(&tree.root(), LayoutParams { size: Xy::new(Size::FitContent, Size::FitContent), ..LayoutParams::DEFAULT })?;
let item = tree.add_node(&row, LayoutParams { size: Xy::new(Size::Pixels(100.0), Size::Pixels(20.0)), ..LayoutParams::DEFAULT })?;
tree.solve_layout(Xy::new(800.0, 600.0));
// Read the output rect for the "item" node
let rect = tree.layout(&item)?;
// Draw the layout rectangles as SVG to inspect the layout
std::fs::write("example.svg", tree.to_svg())?;
# }
# Ok(())
# }
```

### Choosing which dimension drives layout

Declare the dimension you know and put `Size::AspectRatio(width / height)` on the dimension you want derived. In a 100 × 100 row, a child with `size: Xy::new(Size::Pixels(40.0), Size::AspectRatio(2.0))` is 40 × 20. To make height drive width, use `Xy::new(Size::AspectRatio(2.0), Size::Fill)`. The solver resolves the height before computing the width. The [giraffe layout test](tests/article_layout.rs) uses this ordering to size an image from a neighboring column of wrapped text.

A stack also preserves explicit pixel and fractional sizes when its children overflow. For children that should share the available space, use `Size::Fill` and `fill_weight`. A `FitContent` stack can derive its own size from fractional children. For example, in a row with no gaps, margins, or padding, a 1 px child beside a child requesting `Size::Frac(1023.0 / 1024.0)` gives a 1,024 px row. The fractional child occupies the remaining 1,023 px.

A maximum can make a row fit even when the requested fractions add up to more than one. Put a 1 px item beside two 75% items and cap the first 75% item at 12 px. The row is 52 px wide, with children occupying 1, 12, and 39 px. Removing the cap makes the same declarations impossible to satisfy and produces an `ImpossibleFracChildren` warning on the row.

### Wrapping, margins, and block flow

- `ChildrenLayout::Wrap` lays out successive rows or columns. Choose an axis, per-line arrangement, item spacing, and line spacing. Line breaks use item sizes before distributing the remaining main-axis space to weighted `Fill` children. The tallest or widest intrinsic item sets the cross-axis extent of its line. Cross-axis `Fill` children stretch inside that extent.
- `LayoutParams::margin` takes pairs of physical left/right and top/bottom edges. `Margin::px` accepts finite pixel values, including negative margins. Margins affect the space a child occupies in a stack, wrap, grid, or block, and the output rectangle is the child's box inside those margins.
- `ChildrenLayout::Block` implements CSS normal flow for block boxes. `Size::Auto` fills the containing width for an in-flow block and fits the content on the height axis. `Margin::AUTO` distributes spare inline space, so two auto inline margins center a fixed-width block. Adjoining vertical margins collapse between siblings, through empty blocks, and across eligible parent-child edges. Box dimensions include padding. This mode lays out block boxes in a UI tree. Floats, clearance, and inline CSS formatting are outside its scope.

### Grid tracks and intrinsic sizes

Use `Track::Content` for a column that stops at its preferred content width and `Track::Auto` for one that can also take leftover room. In a 300 px grid with two such auto columns, content preferences of 70 and 30 px and a 10 px gutter leave 190 px. Each column gets another 95 px, producing 165 and 125 px. A fractional track takes its share before this stretching step.

`Track::Fr(weight)` starts with a zero floor. Use `Track::MinMax(TrackMin::Content, TrackMax::Fr(weight))` when content should establish the floor. A 100 px spanning minimum shared by two such tracks with weights 1 and 3 gives them 25 and 75 px. On an owned tree the item supplies its content floor through `NodeRules::grid_content_minimum`. For example, the [scoreboard](examples/scoreboard/README.md) supplies `Some(Size::FitContent)` for each single-line club name. Its club column can then protect the longest visible name, while the score column can yield space. `intrinsic_extents` returns both the minimum and preferred extent of an axis, including its gaps. On an owned tree, `resolved_grid_tracks` returns the published, unsnapped edges in template order, including zero-width collapsed slots. [Grid example](examples/asset_browser/README.md) · [CSS layout feature inventory](reports/constraint-semantics/css-layout-scope.md) · [Fixture results](reports/constraint-semantics/README.md)

### Custom content and pixel rounding

Set `LayoutParams::content_measure` to `ContentMeasure::Independent`, `HeightForWidth`, or `WidthForHeight` for intrinsic content such as a chart or embedded view. Use `TreeAdapter::measure_content` or `LayoutTree::solve_layout_with_content_measure` to supply the content-box dimensions. The callback receives the requested axis, any resolved orthogonal content-box dimension required by the mode, and any explicit pixel maximums. Keru adds padding and applies size constraints after measurement. When both text and custom callbacks are needed, use `LayoutTree::solve_layout_with_measurers`. Register changes with `register_content_change` or `mark_content_changed` when content changes independently of layout parameters.

Call `set_pixel_scale(Some(PixelScale::ONE))` on `LayoutData` or `LayoutTree` for whole-pixel output. Use `PixelScale::try_from(device_scale)` to validate a device scale for a higher-density grid. Keru snaps absolute edges and derives local rectangles from those same edges, so shared boundaries stay aligned. Measurements and positioning use unrounded dimensions. Pass `None` to disable rounding.

Pixel snapping uses the CPU features reported usable by Rust. On x86-64, the scale-1.0 path rounds all four edges in binary32. Builds with SSE4.1 enabled use packed floating-point truncation. Portable x86-64 builds reuse the packed kernel for powers of two with normal binary32 reciprocals and can use AVX-512, AVX2, or SSE2 at other scales. When AVX2 is enabled for the whole build, the scaled AVX kernels can inline. Enabling both AVX2 and FMA selects the fused kernel when both features are usable. Other architectures use the scalar implementation. Rust 1.89 or newer is required to compile the AVX-512 kernel. [Dispatch and arithmetic proofs](proofs/README.md)

Stack placement groups in-flow leaf rectangles when a runtime-dispatched AVX kernel can round them together. Each batch fits on the stack, shares the scale constants, and publishes rectangles in sibling order. AVX-512 rounds two complete rectangles per vector.

## Incremental Relayout

The `LayoutTree` API tracks edits automatically. In a cycle-free tree, changing a size or content queues its dependent sizes. Inserting, removing, moving, or reordering children rebuilds the affected sizing dependencies. For example, moving a label between two fixed-size panels can reuse the measurements in other panels. Reordering independently sized siblings can reuse every measurement while updating their positions.

With a custom `TreeAdapter`, call `register_child_attached(child)?` after insertion. It reads the new parent from the updated links and returns an error for a root or detached child. Report a removal or same-parent reorder with `register_children_change(parent)`. For a move, call `register_children_change(old_parent)` and `register_child_attached(child)?` after updating both parents’ links. Use `register_node_change` for parameter changes and `register_content_change` for intrinsic content changes. If the location of a structural edit is unknown, call `register_structural_change()`. Custom adapters start saving node order and parameters when they use incremental solving, retain output rectangles, or call a host measurement function. Full solves on other adapters skip this bookkeeping. If the first unlocalized edit follows such a full solve, the solver seeds independent pixel sizes from the live tree and rebuilds the remaining dependencies. Later unlocalized edits can compare directly with the saved tree, including when the root changes. `LayoutTree` records edits as they happen and skips the topology snapshot.

Measurement results must be repeatable for the same node, constraints, and content. Report content changes so the solver can invalidate reused measurements. Callbacks can update private caches or logs while keeping the current solve's layout inputs stable.

Adapters that use Verus can implement `measurement::Measurer` to prove that their executable measurement code returns the same bits for the same inputs. The contract supports mutable caches and runs without a verifier dependency in ordinary Rust builds. [Downstream measurement verification](proofs/README.md#verify-a-downstream-measurer)

When `LayoutTree` appends or removes unbounded `Fill` leaves at the end of a stack, it can update the shared dimension while retaining independent cross-axis measurements. If gaps or fixed-size siblings already consume all available space, repeated tail edits can also preserve all earlier rectangles in a start-aligned stack.

Structural edits can be batched with a resize, a content change, or a change to a sizing cycle. For general edits, the solver walks the live tree to locate affected regions. Shared fill sizes, grid cells, wrap lines, and collapsed block margins can carry the work up to the root. Within those regions, it reuses independent leaf sizes, measurements with matching constraints, and unchanged subtrees behind fixed-size boundaries.

`LayoutTree` can retain the last layout on idle frames with the same viewport and scale. Position, anchor, origin flip, and overflow edits can go directly to placement. Numeric sizing changes mark the affected branch and any in-flow siblings whose positions depend on it. Placement retains the output of unaffected branches. Resizing the viewport or changing the pixel scale refreshes output across the tree. Custom adapters receive all output rectangles by default and can opt into partial writes with `retains_output_rects()`. `solve_layout_incremental_checked` compares the sizing words and the complete ordered absolute and local view when a candidate is available. It always publishes the engine’s canonical full result.

Numeric edits budget ranked sizing work by distinct affected nodes, with a separate hard limit on slot computations. Repeated viewport edits can reuse a bounded dependency schedule when the edit inputs and dependency shape match. A numeric Width-grid edit can reuse its cell assignments when the ordered items and normalized column count agree. Placement uses the current grid rectangle.

The proof suite compares the ordered absolute and local rectangles of a retained view with a fresh full build across successive edits. It also checks the production grid search, Fill compaction, sibling traversal and pixel snapping. The verification guide describes which paths share verified Rust code and which still depend on a model of the adapter or solver. [Layout proofs](proofs/README.md)

Placement-only changes in wrapping and block layouts reuse measured sizes. Flow replay rebuilds line and margin data and retains clean measurements when their inputs still match. Eligible Block trees compute widths from parent to child and fold heights and margins in sibling order. When a Width grid's track size can be resolved early, preparation uses that size to resolve its children and reuse independent branches. Re-enabling a child can reuse its saved sizing when its declarations, visible descendants, and track width still agree.

Large batches can use root replay if edit intake reaches its limit before sizing starts. Full solves handle the initial frame, explicit invalidation, and work that cannot safely reuse prior sizing. `LayoutTree` keeps a bounded cache of wrapped text heights for matching width bits. Report content edits or call `invalidate()` when the measurer changes. Disable the `incremental` feature to omit change tracking and use full solves through `TreeAdapter`.

The opt-in `batch-pilot` feature uses the default solver for the first layout. When a later solve needs work, it builds a retained sizing graph and uses batch Pearce–Kelly for its ordering and graph edits. [Pilot API and benchmarks](benchmarks/topological_order/README.md#layout-pilot)

## FAQ

- **Is this the same as the Cassowary constraint solving algorithm?**

    No, it's different. This algorithm doesn't model all dependencies as constraints, doesn't use the simplex method, or anything like that.


## Screenshots

![Layout example](https://raw.githubusercontent.com/kekelp/keru_layout/main/examples/example.svg "Svg output for the layout in `example.rs`")

*SVG output of the `example.rs` example*
