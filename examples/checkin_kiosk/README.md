# Appointment check-in kiosk

## Recorded before the first solve

A walk-up visitor confirms the booking details, sees which appointment they are checking in for, and chooses an arrival slot. The three example bookings are fictitious. The translation and validation message must be able to expand the form without moving the kiosk's Back and Check in controls offscreen.

At 1024 × 768 the screen has a 20 px outer inset, 14 px vertical gaps, a 48 px header and a 52 px footer. A 240 px booking summary sits beside the form, with a 16 px gutter. At 480 × 960 the summary becomes a short horizontal strip above the form. The footer remains at the bottom. Both viewports must show every active control, including the last slot. This scope has no scroll container.

- The form heading, instructions, optional validation notice, three booking rows, and available arrival slots appear in reading order. The error message takes up space only when present. Longer copy wraps without covering another control. The booking rows must be at least 48 px high, maintain a 12 px gap between their description and their fixed 64 px room badge, and grow vertically when the description needs extra lines.
- The summary changes from a vertical list of booking facts to a compact strip when the width goes below 760 px. The form should take all remaining space with `Fill`. A kiosk this small cannot support the original rail and still keep the form legible. We'll compare both policies on the same compact screen.
- Four 100 px arrival choices should fit on a single row whenever they have 424 px (three 8 px gaps). When only three fit, the fourth starts a second line 8 px below the first. Picking another appointment must update its booking summary and its drill-down note without shifting the outer shell.
- First-pass instinct: a very long translated description next to a fixed room badge might need a hand-calculated label width. Try ordinary `Fill` + wrapped text first, then change only that width to the hand-calculated value. Check actual badge and label rectangles; agreement between retained and fresh trees is a separate check.

## What happened on the first run

The first draft was saved before execution at SHA-256 `b840a7ed7b7ecd8d1386cb2c071430e1e9554034a05b58da59ff1892962fe6be`. The source for the library under test was commit `146f57e55e39295d8b51bec3abf07b91c56767f7`. The application was written from the public API descriptions. The first run passed the regular screen and stopped at the compact screen’s vertical gap. The 8 px gap assertion reconstructed one edge as 189.2 and read 189.20001 from the next box. The wrapped text introduced fractional heights. I had compared independently computed floating-point coordinates with exact equality.

```rust
// First pass
assert_eq!(k.rect(pair[0]).y[1] + 8.0, k.rect(pair[1]).y[0]);
// Repaired product assertion, with a tolerance of 0.002 logical pixels
near(k.rect(pair[0]).y[1] + 8.0, k.rect(pair[1]).y[0]);
```

The layout declarations required no correction. Published edges from equivalent trees are still compared bit-for-bit. The program also checks that hidden nodes have unavailable rectangles, every active descendant fits its parent, rows protect the badge, the selected room appears in the summary, and the selected booking has the only visible detail note. The French text is an expansion test for the instructions and service descriptions. The rest of the interface retains its English labels.

## Two decisions checked independently

**Should the app budget the description width by hand?** One version lets the time and badge keep their declared widths and gives the description `Fill` with `TextContent::Wrapping`. The alternative subtracts the insets, side rail when present, gutter, time, badge, and row gaps from the window width. Both give the description 540 px on the regular screen and 252 px on the compact screen. All 44 node entries match, including hidden nodes, in all nine states. I kept the arithmetic only in the executable comparison. The form uses the ordinary declaration by default.

**Should a narrow kiosk keep a side rail?** This deliberately changes only the responsive choice, retaining the same data, measurements, alert and window. On the 480 × 960 validation screen a side rail leaves a 184 px form. Its time, badge, gaps and insets exhaust the row, leaving zero width for the description. The last slot ends at y = 1010.8, below both the footer’s top at 888 and the display’s bottom at 960. Moving the same summary above the form makes the form 440 px wide. The translated description receives 252 px, wraps across three lines, and the final slot ends at 601.2. The 760 px breakpoint is an explicit choice for these two kiosk configurations. This exercise did not find a solver defect.

| State | Form width | Instruction height | Arrival area y range | Result |
| --- | ---: | ---: | --- | --- |
| 1024 × 768, regular | 728 | 14.4 | 351.6–395.6 | Four slots in one row |
| 480 × 960, compact | 440 | 14.4 | 420.4–516.4 | Fourth slot on a new row |
| Compact, expanded copy | 440 | 43.2 | 456.4–552.4 | Second appointment row grows to 55.2 px |
| Compact, error visible | 440 | 43.2 | 505.2–601.2 | 40.8 px notice plus 8 px gap |
| Compact, another booking and slot picked | 440 | 43.2 | 456.4–552.4 | Desk changes from A12 to B04 |
| Rotated back to regular, expanded copy | 728 | 28.8 | 366.0–410.0 | Four slots in one row |
| Restored regular | 728 | 14.4 | 351.6–395.6 | Original geometry restored |
| 495 × 960 | 455 | 14.4 | 420.4–516.4 | 423 px for slots, two rows |
| 496 × 960 | 456 | 14.4 | 420.4–464.4 | Exactly 424 px for slots, one row |

At each step the program updates a retained tree through the public edit methods, constructs a fresh tree directly in the target state, and compares every available absolute rectangle and each hidden state. Both use the library’s sample monospace text measurement. All comparisons passed and these layouts produced no warnings. The 495 → 496 resize returned `FallbackTooMuchWork` on the baseline, and published the same geometry as the fresh tree. The table reports geometry, not a guarantee that every transition used incremental sizing.

## Run

From the repository root:

```sh
cargo run --manifest-path examples/checkin_kiosk/Cargo.toml
cargo run --manifest-path examples/checkin_kiosk/Cargo.toml -- --svg /tmp/checkin-layouts
```

The second invocation writes a labeled geometry SVG for each state plus the cramped side-rail comparison. Both commands run all assertions. The program models kiosk state and layout. Its time-selection example uses four fixed arrival windows, and its geometry checks cover the viewports listed above.
