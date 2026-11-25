# News digest authoring trial

## Predictions before the first run

In a 320 px editorial column, a 96 × 60 portrait floating left and a 64 × 40 sponsor floating right should share the first 60 px of the article with nearby content. A 24 px ordinary heading still spans the column. A 36 px high independent summary box following the heading should fit between x=96 and x=256 at y=24. A footer clearing both floats starts at y=60. Narrowing the column to 224 reduces the summary width to 64 px. Hiding the sponsor frees its 64 px immediately, so the same summary becomes 128 px wide. A 100 px minimum on the summary makes it clear the sponsor at y=40 in the narrow, unfiltered view. Filter edits should release the old exclusion on the next solve.

The direct version gives the portrait and sponsor float sides and makes the summary its own formatting context. The test independently computes the rectangles a host would have to supply for manual placement. A footer with a declared clearance should require no extra spacer or guessed height.

## Observations

The retained tree, a rebuilt tree and the optional batch solver produced the same geometry in all six states. The summary moved to y=40 when its 100 px minimum first failed to fit. At 140 px the sponsor moved below the portrait, and the summary waited until y=100. Restoring the initial width and filter restored the original rectangles for all 30 application boxes.

I initially stored the return values of `add_node` as `NodeId`. Rust reports that they are `ChildId`, which dereferences to `NodeId`. Correcting the member types was the only change the sample needed before obtaining the predicted rectangles. No layout declarations changed after the first geometry run.

The manual calculation must account for the sponsor's width, visibility, wrapped location, height and intersection with the entire summary. Keeping its old 64 px trailing reservation on a filtered 224 px column would give a 64 px summary when 128 px are available. That discrepancy would come from the retained reservation in the application. The direct declarations released the space on the first solve after the edit.

Run `cargo test --features batch-pilot --example news_digest -- --nocapture` to replay all three solve paths.

A separate source-positioned article action revealed a genuine retained-layout defect. After a 30 px heading, the action started at y=30 as predicted. Scrolling its 50 px reader by 20 px initially reported y=0; the expected visible position was y=10. The engine now retains the static block offset during a scroll-only update and projects it through the parent's scroll offset. The same unmodified application declarations now produce y=10. The second regression assertion in this example covers this interaction, which the static XML snapshots cannot exercise.

## Independent fixture review

A nested RTL block with a declared width of 50 px and 1% margins inside a 50 px parent revealed an output-rounding choice. I replayed both box-sizing variants with pixel snapping disabled and measured the child at x=−0.5, y=0.5, width=50 and height=10. At pixel scale one, the engine rounds the two x edges, −0.5 and 49.5, away from zero. The published edges become −1 and 50, with a 51 px span. The browser archive publishes 0 and 50. The logical width stays 50 in both calculations. The native expectation records the entire tree for just those two rounded cases; no widget or CSS workaround is needed.

For comparison, I also reviewed the [festival schedule](../festival_program/README.md) at its exact 104 px two-row threshold and one pixel below it. Both outcomes matched the occupancy objective. The tie at 103 px admits several valid arrangements; earlier-fuller rows describe the chosen behavior precisely enough to test.

A third trial placed the article in a flexible column and gave its floated caption ten 20 px words. At a 100 px panel width and 20 px leading margin the caption fits four words per line, so the article needs 30 px. At 80 px it fits three words per line and needs 40 px. The first integration probe recomputed the enclosing section after its children had been explicitly positioned and lost their contribution. Retaining the height reported by the float formatter fixed the section and its ancestors through the 100 → 80 → 100 resize. The application supplied only a word measurer and its actual margin.
