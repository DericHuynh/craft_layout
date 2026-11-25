# Dispatch board author trial

A dispatch board displays 24 tickets. Each ticket row has an assignee, a route field containing two LTR chips, and a fixed action. The board can switch between LTR and RTL. The assignee and route field accept proportional shrink. A compact mode gives the assignee a minimum width of 145 pixels.

## Predictions written before running

| Direction and width | Assignee | Route | Action |
| --- | --- | --- | --- |
| LTR, 374 | 10..170 | 180..300 | 310..344 |
| LTR, 304 | 10..130 | 140..230 | 240..274 |
| RTL, 374 | 204..364 | 74..194 | 30..64 |
| RTL, 304 | 174..294 | 74..164 | 30..64 |
| LTR, 304, protected assignee | 10..155 | 165..230 | 240..274 |

Each row reserves logical start/end padding of 10 and 30 pixels. Two 10-pixel gaps and a fixed 34-pixel action leave 210 pixels for the 160- and 120-pixel fields at narrow width. The fields give up 40 and 30 pixels, respectively. In protected mode they give up 15 and 55. Each route field’s first chip spans local coordinates 0..12, and its second chip spans 15..30 in both interface directions. Row tops advance by 36 pixels for a 30-pixel row and a 6-pixel gap.

Run the 145-node example with `cargo run --example dispatch_board`.

## Run and author reflection

All five predictions matched on the first run. The experiment exercised 24 rows, both chips in every route field, repeated changes on one tree and independent fresh trees. The Batch check observes the same geometry after each retained solve. I needed no layout declaration changes to meet the predictions.

I then changed two declarations in a separate copy. Setting the flexible cells’ minimum inline size to zero produced identical rectangles. Applying the CSS initial shrink policy to every action made the action narrower than its intended 34 pixels. That discrepancy followed directly from granting the action permission to shrink. The original layout described the intended fixed control without a workaround.

Run the executable assertions with `cargo test --locked --all-features --example dispatch_board`. The board uses deterministic component sizes, with text shaping and device rendering outside this trial.
