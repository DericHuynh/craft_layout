# Editor workbench

Run a headless editor session that types into a source file, receives a compiler diagnostic, renames a file, opens and closes a tab, resizes the window twice, and drags the terminal divider. The workbench retains the same layout tree across all nine frames. The SVG renderer uses the published rectangles and the same 8 × 16 monospace metrics as the text measurer. Open a generated SVG in a browser to inspect a frame.

From the repository root:

```sh
cargo run --locked --manifest-path examples/editor_workbench/Cargo.toml
cargo run --locked --manifest-path examples/editor_workbench/Cargo.toml -- --paired --trace --svg target/editor-frames
```

## First attempt

The first author read the public sizing and placement declarations and wrote down the geometry before executing the scene on commit `146f57e55e39295d8b51bec3abf07b91c56767f7`. The main column reserves fixed heights for tabs, breadcrumbs and terminal. The rest goes to two `Fill` editors with weights 3 and 2 and a 2 px divider. Source rows derive their heights from wrapping text. Their 40 px gutters explicitly use `Pos::Start` so a line number stays at the top of a multi-line row. Tabs fit their text and horizontal padding.

| Case | Expected before running and observed on the first run |
| --- | --- |
| Desktop, 1284 × 800 | Explorer x=48..248, work area x=248..1060 and inspector x=1060..1284. The editors span x=248..734 and 736..1060, both at y=96..632. |
| Type and check | The first source row grows from 16 to 32 px. The second line moves down from y=112 to 128. The diagnostic also wraps. Fifteen rectangles change. The other editor and terminal stay in place. |
| Rename and open | Changing `main.rs` to `session.rs` moves the next tab's left edge from x=328 to 352. The new `lexer.rs` tab follows it at x=448. |
| Laptop, 960 × 660 | With the inspector hidden, the two editor widths are 426 and 284 px. The terminal starts at y=492. |
| Compact, 700 × 580 | With the navigator, inspector and second editor hidden, the sole editor spans x=48..700. The terminal starts at y=412 and moves to 364 after a 48 px drag. |
| Restore and close | Both original editor widths return. The terminal keeps its new 192 px height. Closing the last tab moves zero surviving rectangles. |

All visible rectangles and hidden states matched a fresh tree at every frame. Both trees had empty warning lists. The cold solve reported `FallbackNeverSolved`. The subsequent native solves reported 0, 9, 175, 223, 131, 7, 269 and 0 computed slots. These counts are diagnostic observations for this revision. The assertions check the geometry so implementation changes may legitimately produce other counts.

## Which code did the editor need?

The initial weighted declaration met the recorded intent without layout rework. As a counterfactual, `--paired` computes both editor widths in application code by subtracting the rail, visible sidebars and divider from the window width. Only the two editor width declarations change. The same content, hidden flags, sibling order, retained edits and fresh-build checks run in both modes. Across the nine frames, all 644 named rectangle or visibility entries agree between the two versions. The manual version duplicates knowledge of sibling chrome and has no geometric benefit in this session.

Hiding sidebars below 1150 and 800 px expresses the application's reading-space policy. Updating descendants when hiding a panel satisfies the documented `disabled` contract. The text callback supplies content metrics for rendering. None of those three jobs is replaced by weighted sizing. This exercise found no solver defect in the editor sequence. It exercises the listed breakpoints and character-based wrapping, without modeling scrolling or a full text editor.

The initial trace counted changes only among current keys, so closing the last tab printed zero. The shipped trace counts deleted keys too and reports one removal. This corrected the reporter without changing the layout declarations or oracle. `src/main.rs` contains the scene and edit sequence, `src/audit.rs` contains the independent coordinates and comparison, and `src/svg.rs` draws the result.
