# Festival program

The schedule groups stage cards in reading order. Each group should have similar occupied width so that a sparsely populated last row does not distract from the program. The stage detail row uses an automatic leading margin on its ticket action. A rehearsal marker has zero width and belongs with the preceding performance.

## Expectations recorded before executing

At 130 px six cards 52, 26, 26, 26, 26 and 26 px wide should balance as 52+26+26 and 26+26+26. Ordinary greedy wrapping fits four cards on the first row. At 110 px the same balanced grouping should still fit. Hiding the 52 px opening performance leaves five equal cards. Requesting two lines should give three entries to the first and two to the second. A zero-width marker inserted after the third visible card should remain there on the first line. At 100 px a four-row request for five equal cards should put two on the first line, then one on each other line. A box with independently supplied baselines 18 and 10 px should move the shorter ascent down 8 px. With a fixed 20 px ticket action, a 50 px label and 120 px available, the right action should start at x = 100 without a spacer node.

Explicit row numbering and host-computed breaks will be checked against the direct declaration. No fixture output was used to choose these values.

The first execution matched every prediction, including the tied break, attached marker, resize, and baseline offsets. No card needed a hard-coded break or a spacer. The explicit leading margin on the ticket action expresses the intended separation. Both placement decisions survived filtering and rebuilding the list. Run the assertions with `cargo run --example festival_program`.

A second trial uses a venue panel with automatic height and a minimum of 192 px. A growing booking fills that height. Its fractional occupancy bar reads 75% of the allocated height, so it reaches 144 px. Raising the minimum to 216 px should move the bar's end to 162 px, without assigning a height to the booking or the bar in pixels. Those figures were recorded before running this trial.

## Independent review of the width threshold

A second author predicted the row widths before running the example. With cards of 52, 26, 26, 26, 26 and 26 px, two rows fit at exactly 104 px. The observed widths were 104 and 78. At 103 px, three rows are necessary in reading order. The engine chose 78, 52 and 52, as predicted. The equally balanced 52, 78 and 52 arrangement would also preserve reading order. The program's earlier-fuller tie convention chooses the first arrangement, so a host needs no explicit break at that last pixel. Equal card counts would serve a timetable that groups by performance count; this program explicitly asks to balance the occupied width.

Run `cargo test --example festival_program independent_review_one_pixel_below_two_row_capacity` for the threshold check.

For a right-to-left venue directory, a 30 px entry in a 50 px column should keep its right edge at x = 100 when wrapping switches on. With a second 50 px column its leading boundary stays at x = 50, so a 40 px entry in that column should start at x = 10. In this horizontal writing mode there is no vertical text baseline shared across a column.
