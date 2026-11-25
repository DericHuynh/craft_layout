# Maintenance console

The technician edits five machine settings in one scrolling panel. Each row keeps its own children and inherits the form's columns. The longest measured label sets the first column, the field takes the remaining width, and each action occupies 56 pixels. The header grows from 24 to 32 pixels when the named panel is at most 300 pixels wide. The help popover follows the third row's action. Its preferred side is below, followed by above.

## Predictions recorded before the first run

The window stays at 520 × 170. The floating panel starts at (16, 12), is 140 pixels tall, and changes width from 430 to 280. The scrollbar is an overlay. A deterministic text measurer assigns eight pixels per character. “Pump speed” contributes 80 pixels. Two eight-pixel gaps leave field widths of 278 and 128. Subgrid rows should inherit the gaps and the content contribution should travel up to the form.

| Geometry in window coordinates | Wide, top | Narrow, top | Narrow, scrolled 56 | Wide, scrolled 56 |
| --- | --- | --- | --- | --- |
| Scrollport (x, y, w, h) | 16, 12, 430, 140 | 16, 12, 280, 140 | 16, 12, 280, 140 | 16, 12, 430, 140 |
| Sticky header (x, y, w, h) | 16, 12, 430, 24 | 16, 12, 280, 32 | 16, 12, 280, 32 | 16, 12, 430, 24 |
| Form (x, y, w, h) | 16, 36, 430, 176 | 16, 44, 280, 176 | 16, −12, 280, 176 | 16, −20, 430, 176 |
| Third field (x, y, w, h) | 104, 108, 278, 32 | 104, 116, 128, 32 | 104, 60, 128, 32 | 104, 52, 278, 32 |
| Third action (x, y, w, h) | 390, 108, 56, 32 | 240, 116, 56, 32 | 240, 60, 56, 32 | 390, 52, 56, 32 |
| Help (x, y, w, h) | 390, 60, 66, 44 | 240, 68, 66, 44 | 240, 96, 66, 44 | 390, 88, 66, 44 |
| Vertical scroll range | 0..60 | 0..68 | 0..68 | 0..60 |

The form has five 32-pixel rows and four 4-pixel gaps. The third action is 72 pixels below the top of the form. At the top, a 44-pixel popover cannot fit below that action with a four-pixel gap, so the popover should move above. After scrolling 56 pixels it should fit below. A fresh tree configured directly for each state and a retained tree passing through all four states should publish the same rectangles and clips.

The direct declaration lets the grid place each label, field and action in tree order. A paired version gives each control an explicit column and row index. Both should produce the same published geometry on every node.

## Editing a label in place

At the narrow, scrolled state, renaming “Zone” to “Emergency cutoff” should grow the shared label column to 128 pixels. All five fields should then start at x = 152, with actions still starting at x = 240. Reverting to “Zone” should move every field back to x = 104. The test compares the edited retained tree with a fresh tree that receives each new label before its first solve.

## Results and use

Run the four-state console with `cargo run --example maintenance_console`. Run the component regression tests with `cargo test --example maintenance_console`.

The first run matched the table on all four states. The retained, freshly constructed, and explicitly positioned versions agreed on every published geometry field for all 24 application nodes through a complete shrink, scroll, expand and reset. Updating the label through its node context grew and shrank every row’s field as predicted. The direct example therefore keeps automatic placement and names the shared columns once.

One API choice needed a second look. The crate exposes both `LayoutParams::grid_span` and `NodeRules::grid_item`. For a `TrackGrid`, this example uses `GridItem::span` to put each row across three tracks, then `TrackAxis::Subgrid` on the row so its controls inherit the boundaries. The two declarations serve different purposes. For drawing, it reads `view_geometry` for both the final rectangle and its inherited clip, including when the anchor target moves with scrolling.

## Changing the row's formatting context

A further test gives the “Valve ID” row three overlapping named queries, while the surrounding rows continue using shared tracks. The window stays at 520 × 170. The predictions for the field and action's left edges follow directly from the selected layout.

| Panel width | Last matching layout | Field left | Action left |
| ---: | --- | ---: | ---: |
| 430 | Authored subgrid | 104 | 390 |
| 340 | Flex, 8-pixel gaps, equal flexible controls | 88 | 226 |
| 300 | Local grid, 100-pixel label, 32-pixel action, 4-pixel gaps | 120 | 284 |
| 240 | Horizontal stack, 2-pixel gaps, equal fill controls | 82 | 170 |

Expanding the panel revisited the predicted geometries in reverse and restored the unmodified subgrid. All eight retained states matched freshly built trees. In the flex and stack states, the row’s own 64-pixel label determines its width independently of the longest sibling label.

## Follow-up fixed-control regression

The original five-state run, including the reset, covers a sticky header and an anchored popover. A separate probe put a fixed control in a 100-pixel-wide panel, with a query selecting width 80 over its authored width 40. At scroll offset zero it published x = 0..80. On the first scroll-only change to offset 30, it unexpectedly published x = 0..40. The query still matched. The scroll publication path had discarded its result when rebuilding the control’s visual box.

The repair retains the resolved style for fixed and absolutely positioned controls across scrolling. The regression checks the direct scroll API and compares its entire published geometry with an explicitly invalidated full solve. Run it with `cargo test --test managed_layout scroll_only_publication_keeps_query_width_of_fixed_control`.


## Follow-up sibling resize

Another probe kept the window at 480 pixels and changed a sidebar from 180 to 320 pixels. Flex shrank the adjacent panel from its authored 300 pixels to 160. The panel’s 200-pixel breakpoint should reduce the control’s width from 50 to 32. Its first run revealed a second mismatch: the control stayed 50 pixels wide because query evaluation consulted the authored panel width before allocation.

The query now reads the unrounded content box allocated by the solver, including its effective padding and scrollbar gutter. The regression exercises the direct sibling resize and restoration. Run it with `cargo test --test managed_layout width_query_uses_flex_allocation_when_a_sibling_resizes`.
