# Native UI layout implementation goal

Let an application describe a localized, measured, responsive form with shared columns, shrinkable controls, nested scrolling and a sticky header directly. Resizing, editing a label, moving a subtree and changing text direction must produce the same rectangles as rebuilding the application in its new state.

| In dependency order | Acceptance example |
| --- | --- |
| Logical axes and inherited direction | An RTL form mirrors inline edges while an embedded LTR field retains its own direction. |
| Intrinsic sizes and baselines | A wrapped label and a differently sized control align on a measured baseline. |
| Flexible items and multiple lines | Two 160/120 preferred widths in 220 px with a 10 px gap shrink to 120/90. A binding minimum redistributes the deficit. |
| Scrollports and containing blocks | A nested scrollport clips content, reserves its scrollbar gutter, and stops a sticky header at its containing block. A popup can use another control as its anchor. |
| Grid tracks and shared tracks | A content-sized label column, fractional field column and fixed action column align across nested form rows. |
| Containment and container queries | A component changes arrangement on a panel resize with the same window; descendants cannot determine the queried axis and also change their own breakpoint. |

Evidence for acceptance comes from independently written app expectations, direct geometry assertions, retained-versus-fresh solves, and runs of the existing test, verification, and workload suites. Browser fixture coverage is a separate compatibility measurement.

## Results

| Acceptance check | Observation |
| --- | --- |
| Direction changes and reparenting | Twenty-four RTL ticket rows mirrored their inline positions. A nested LTR route editor kept the order of its two chips. A moved subtree adopted its destination’s direction. Vertical block tests cover signed collapsing margins, inline auto size and padding edits. |
| Text and baselines | Host min-content and max-content widths participate in preferred sizes and bounds. A multiline label contributes both baselines. Changing its width moves the neighbor aligned to its last line. Flex and grid baseline tests include nested shared tracks. |
| Flexible sizes | The 160/120 pair produced 120/90 at width 220. A 110 minimum on the second control changed the result to 100/110. The dispatch trial’s fixed 34-pixel action held its width on every direct run. |
| Scroll, sticky and popups | The maintenance console scrolled 56 pixels, kept its heading pinned and placed help below its scrolled action after initially placing it above. A separate section test moves a sticky header out of view as its containing section ends. |
| Shared tracks | The longest label measured 80 pixels across the five-row maintenance form. At panel widths of 430 and 280 the field widths were 278 and 128. Editing a label to measure 128 pixels moved all five fields to x = 152 and left the action column aligned. |
| Responsive layout | The console’s header grew from 24 to 32 pixels at the panel breakpoint in a constant 520 × 170 window. Another test selects subgrid, flex, local grid and native stack from overlapping queries, then returns to the authored layout. |

### What the authors had to change

The [dispatch-board author](../../examples/dispatch_board/README.md) and [maintenance-console author](../../examples/maintenance_console/README.md) wrote geometry predictions before executing their scenes. The direct declarations met both sets of first-run predictions. Setting minimum widths to zero and explicitly numbering the 15 form controls produced the same output as their respective direct counterparts. Enabling shrink on every dispatch action changed a product requirement and made those controls narrower. The console author needed to check how the original grid span and the new track-grid placement interact. The `GridItem` documentation now spells out their precedence.

Follow-up integration probes found two engine errors. A scroll-only frame could draw a fixed control at its 40-pixel authored width after a query had sized it to 80. A query could also read a panel’s 300-pixel preferred flex size after a sibling reduced its allocated width to 160. Both probes use direct declarations and check the published coordinates. These failures belong to engine integration. The comparison variants in the preceding paragraph exercise author choices.

### Implementation and verification boundaries

The owned tree retains the author’s declarations and projects the resolved rules into its existing measurement and placement machinery. Flexible lines reuse native spacing arithmetic. Grid auto-placement reuses the sparse first-fit search. Vertical block flow reuses the existing collapsing-margin and inline-edge kernels. Idle managed frames use the retained solve path. A scroll-only frame updates visual geometry without asking the host to measure text again. Changed managed scenes can require multiple measurements as widths, baselines and tracks settle. A bounded iteration reports `UnstableLayout` when a frame fails to settle.

`layout` publishes physical flow rectangles and `view_geometry` publishes the rectangles and clips used for drawing. A rejected managed Batch solve preserves the previous publication and a corrected subsequent edit can solve. Rich horizontal text measurement uses the ordinary owned solve entry point. The host supplies shaping and line breaks. Custom trees can invoke the logical, flex and track kernels directly. The built-in tree supplies the integrated responsive and visual publication APIs.

The [case ledger](current-cases.tsv) includes every pinned CSS input. The native track API uses numeric lines, auto-placement, single-track auto-repeat patterns and shared subgrid gutters. The CSS harness still lacks broad grid declaration translation. The current proof suite verifies its established arithmetic, graph, and publication kernels. Executable geometry and state-transition tests cover the new managed orchestration.

### Reproducing the checks

From the repository root, run the Cargo suites and the two new application trials.

```sh
cargo test --locked
cargo test --locked --all-features
cargo test --locked --no-default-features
cargo test --locked --all-features --example dispatch_board --example maintenance_console
cargo bench --locked --features batch-pilot --bench real_workloads -- --batch-pilot --verify-only
```

The [case review](README.md) includes the fixture checkout and harness commands. The [proof instructions](../../proofs/README.md) describe the Verus toolchain. The example READMEs give the commands to replay all four earlier applications.
