# Arena scoreboard

This example models a league operator's resizable score strip. A fixed clock column precedes a club column (2fr, content minimum) and a score column (1fr, zero minimum). A fixture update and a live-only filter operate on stable match cells. A promotional headline spans the club and score columns. The host supplies a fixed-pitch display font with 12 px advances and a 20 px line height.

## Predictions written before the first solve

The clock takes 48 px and the two gaps take 12 px each. The promotion's 26 characters measure 312 px, including the 12 px gap it spans. A 100 px fraction should give the headline exactly that room. The widest club on the full schedule is NORTHBRIDGE, 11 characters or 132 px. The operator wants a panel that fits this content, bounded by its available space. The first row is 40 px high, each match row is 26 px, and successive rows have a 4 px gap.

| Stage | Available width | Predicted panel width | Clock / club / score widths | Headline edges relative to panel | Predicted panel height |
| --- | ---: | ---: | --- | --- | ---: |
| All 14, wide | 580 | 372 | 48 / 200 / 100 | 60–372 | 460 |
| All 14, medium | 294 | 294 | 48 / 148 / 74 | 60–294 | 460 |
| All 14, narrow | 240 | 240 | 48 / 132 / 36 | 60–240 | 460 |
| Seven live games | 240 | 240 | 48 / 112 / 56 | 60–240 | 250 |
| Live feed renames a club to a 15-character name | 240 | 252 | 48 / 180 / 0 | 60–252 | 250 |
| Same live feed, wide | 580 | 372 | 48 / 200 / 100 | 60–372 | 250 |

At 240 px the normal 2:1 split would give the club 112 px. NORTHBRIDGE occupies 132 px, so I expect the score to yield 20 px. The filter removes NORTHBRIDGE and the remaining names are at most eight characters long. The next name update forces the panel beyond its 240 px budget. I expect the last track to reach zero width, with its preceding gap still present. Hidden matches should have unavailable rectangles and the remaining rows should compact. The display begins at the viewport's top left.

The independent host implementation should produce the same rectangles using sums, the two-to-one split, the club floor and explicit match-row indexing. It should need to rescan visible clubs on edit, measure the span including its internal gap, and advance the row index only for visible games. I expect the retained default solve, a newly built tree for each stage, and the optional Batch entry point to agree.

## What happened on the first run

All six rows above matched on the first execution. The check compares every track edge, the panel rectangle and the visibility and rectangle of each of the 44 header and match cells. Each frame uses a retained tree, an independently constructed tree for the current model state, and the host's arithmetic reference. With the Batch feature the same sequence also runs on a separate retained tree through the Batch API. The first Batch frame uses the engine's documented default-solver startup.

The 15-character club name forced the panel to 252 px. The last score cell had coincident horizontal edges at 252 px, while the column gap before it remained 12 px. Restoring the larger budget gave that score cell a full 100 px again. The filter placed the third scheduled match in the second visible match row and withdrew the finished match's cells. The arithmetic reference and each solver agreed exactly on these changes.

**Fixes required after the first run.** None. I made a source-formatting and readability pass after checking the predictions. The shared Cargo target was busy, so the first execution used a separate build directory.

**Choices made in advance.** I supplied the available width through `grid_fit_limit.x` when the viewport changed. The grid requests `Size::FitContent`, so the wide scoreboard should stop at the headline's preferred size. I used `grid_content_minimum.x = Some(Size::FitContent)` on the single-line club labels and a content-minimum track for that column. This explicitly protects a club name while allowing the score to shrink. Both declarations were in the original example. No guessed pixel widths, precomputed placements or special handling for the narrow screen were introduced in the managed grid.

**Author's conclusion.** I would ship the direct grid declaration for sizing and placement. The binding club floor and the disappearance of seven games fell out of the same three-column declaration. The handwritten version needs its own scan for the longest visible club and score, computation of the spanning headline's preferred fraction, handling for a binding club minimum, and a visible-row counter. I did have to discover that the item contribution and the track minimum are separate declarations. I would keep the host's text measurements and visibility decisions and leave rectangle arithmetic to the grid. A production renderer would still decide how to display a score when its box has zero width. The test measures its rectangle.

Run from the repository root with `cargo run --example scoreboard` or `cargo run --features batch-pilot --example scoreboard`.
