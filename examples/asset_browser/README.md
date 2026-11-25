# Asset browser

An editor’s asset picker shows a toolbar, a contact sheet, eight thumbnail cards, and a sync indicator layered over the contact sheet. Each card owns its thumbnail, caption, and type badge. The cover art and the panorama are two-column previews. A filter can leave two favorites or hide every item. Compact layout preserves the minimum thumbnail width by wrapping.

## Predictions recorded before execution

The window stays at 600 × 420. The contact sheet starts at (16, 48). Its columns repeat with a 92 px minimum, equal fractional widths and 8 px gaps. Rows are 56 px tall with 8 px gaps. The sheet fits its rows. A card's 4 px padding encloses a flexible thumbnail and a 12 px caption with a 2 px gap. A badge in the top-right of each card and the sync indicator are out of flow.

The cards appear in source order as cover, icon, panorama, texture, model, swatch, glyph, and logo. The following predictions use zero-based (column, row) starts. They were written from the arrangement requirements and public API descriptions before running the example.

| State | Column width | Visible starts in source order | Sheet height |
| --- | ---: | --- | ---: |
| 392 px, sparse | 92 | (0,0), (2,0), (0,1), (2,1), (3,1), (0,2), (1,2), (2,2) | 184 |
| 392 px, dense | 92 | (0,0), (2,0), (0,1), (3,0), (2,1), (3,1), (0,2), (1,2) | 184 |
| 391 px, sparse | 125 | (0,0), (2,0), (0,1), (2,1), (0,2), (1,2), (2,2), (0,3) | 248 |
| 292 px, sparse | 92 | Same starts as 391 px | 248 |
| 502 px, favorite cover and icon, auto-fit | 162 | (0,0), (2,0) | 56 |
| 502 px, same favorites, auto-fill | 94 | (0,0), (2,0) | 56 |
| 502 px, empty filter, auto-fit | — | No visible cards | 0 |
| 392 px, reset | 92 | Same starts as the first state | 184 |

At 392 px the sparse layout leaves the last slot in row zero empty because the next two-column preview needs a new row. Dense placement backfills this slot with the texture, moving it from (216, 112) to (316, 48). At 391 px only three columns fit. The 1 px width reduction should move the logo to a fourth row.

At 502 px, auto-fit should collapse the two empty columns and their adjacent gaps. The cover should span x = 16..348 and the icon x = 356..518. With auto-fill the same two cards should span x = 16..212 and x = 220..314. The sync indicator should always occupy x = 23..41 and y = 51..59. It should add zero rows even when the sheet is empty.

For the paired counterfactual, the application gives every visible card its predicted explicit row and column at each breakpoint. The direct declaration supplies the two wide spans and lets the grid place all eight cards. Both declarations should yield the same rectangles and visibility throughout.

## Follow-up predictions for pinned assets

A seven-item shelf can run left-to-right or top-to-bottom. In the following table each start is written as (slot along flow, line). Every track is 24 px with a 4 px gap. Four leading tracks are explicit. An item placed at slot four creates a fifth track. Each item occupies one slot except the two wide previews, which span two along the flow. A vertical shelf transposes the predictions exactly.

| Source order | Declaration | Sparse start | Dense start |
| --- | --- | --- | --- |
| Cover | Automatic, span two | (1,0) | (1,0) |
| Panorama | Line 1, span two | (2,1) | (2,1) |
| Tag | Line 1 | (4,1) | (0,1) |
| Color swatch | Slot 0 | (0,1) | (0,2) |
| Glyph | Automatic | (0,2) | (3,0) |
| Pinned notice | Slot 1, line 1 | (1,1) | (1,1) |
| Pinned status | Slot 0, line 0 | (0,0) | (0,0) |

The two later fully pinned assets reserve their cells before the automatic cover is placed. The panorama cannot fit at the front of line 1 because the notice occupies slot 1. It takes slots 2 and 3. In sparse order, the later tag on that same line should follow the panorama in slot 4, and the swatch can use slot 0 on line 1. Dense placement should backfill that earlier hole with the tag, leaving the swatch to appear on the next line.

For example, in horizontal sparse flow the panorama's rectangle should be x = 56..108 and y = 28..52. The tag should start at x = 112. In dense flow its x coordinate should move to 0. These predictions precede the follow-up run.

## Column guides

A contact-sheet editor can draw guides by inspecting the sheet's published tracks. The 502 px sheet has room for five columns. The favorites state should return three 162 px tracks and two collapsed tracks at the final edge. Auto-fill should return five 94 px tracks. An empty auto-fit sheet should expose five zero-length columns and zero rows. Positions returned by this API are local to the sheet's content box. These expectations precede the guide check.

## Results and author reflection

The first contact-sheet run matched every prediction. The 1 px resize moved the logo from row two to row three. Filtering to two favorites produced 162 px tracks with auto-fit and 94 px tracks with auto-fill. Hiding all eight cards also hid their thumbnails, captions, and badges. The free sync indicator kept its window coordinates while the sheet contracted to zero height.

At each of the eight states the test checks the direct geometry of every card, thumbnail, caption and badge plus the sheet and sync indicator. It compares all 40 nodes’ rectangles or hidden states across a retained tree, an independently constructed tree and a retained tree using the Batch scheduler. Giving all visible cards explicit addresses reproduced those 40 results throughout. That paired declaration required looking up 44 cell addresses across the eight states. I kept automatic placement in the direct version and needed no corrective layout edit.

The geometry and pinning trials also passed on the preceding implementation at `4d20ad7`. On this revision the column-guide check additionally verified the returned track lists for every state and every comparison variant. With favorite filtering, the last two auto-fit columns both ended at the local edge x = 502. Their widths were zero. When the filter hid every card, all five guides collapsed to x = 0 and the row list was empty.

The pinned-asset follow-up matched the recorded starts in both horizontal and vertical flow. In sparse order, satisfying the tag's line constraint creates a fifth track after the panorama; in dense order the tag uses the hole before it. The late pinned status made the automatic cover skip slot zero as predicted. Explicitly assigning all seven rectangles reproduced the direct result in each orientation and mode. This outcome requires both the pin and the density mode to be deliberate product choices. A request to keep items in reading order should use sparse placement.

Run the sample and both regression tests from the repository root.

```sh
cargo run --locked --features batch-pilot --example asset_browser
cargo test --locked --features batch-pilot --example asset_browser
```
