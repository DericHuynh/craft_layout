# Live mixing studio

This headless Rust example lays out a live audio console with an eight-channel input bank, scene browser, transport, stereo master, monitor controls and status bar. Each channel has a pan knob, three switches, a fader lane and thumb, two independently lit meters, input/output patches and a selection lamp. Opening the send rack adds four named destinations. The application model holds stable track names, levels, mute state, fader positions and the selected channel.

From the repository root, run

```sh
cargo run --locked --manifest-path examples/mixing_studio/Cargo.toml
```

The command replays the edits, checks the geometry, prints the solver's reported route and compares the two sizing declarations described below. A failed check exits with a panic and a nonzero status. Node counts include the window and disabled selection lamps.

## Intent recorded before the first solve

The transport and footer should stay 48 and 24 logical pixels tall. At 1,280 × 760 they occupy y = 8–56 and y = 728–752. The workspace between them runs from y = 64 to 720. The browser keeps 184 pixels, the stereo master keeps 112 pixels and each intervening gap uses 8 pixels. The mixer bank therefore runs from x = 204 to 1,148.

Inside the bank's 8-pixel insets, eight equal channels share x = 212–1,140 with seven 4-pixel gaps. A selection change should move a small overlay light while preserving this layout. Muting Guitar should reduce both of its lit meter heights to zero while retaining the rails. Riding the Vocal fader should put the thumb's center at the requested fraction down the lane. The sample drives these controls from a scripted rehearsal.

| Action | Viewport | Channels | Nodes | Width per strip in logical pixels |
| --- | --- | ---: | ---: | ---: |
| Open the rehearsal session | 1,280 × 760 | 8 | 205 | 112.500 |
| Mute Guitar | 1,280 × 760 | 8 | 205 | 112.500 |
| Select Vocal and ride its fader | 1,280 × 760 | 8 | 205 | 112.500 |
| Open the 156-pixel send rack immediately before Master | 1,280 × 760 | 8 | 227 | 92.000 |
| Insert Talkback immediately before Bass | 1,280 × 760 | 9 | 247 | 81.333 |
| Resize with the rack open | 1,200 × 660 | 9 | 247 | 72.444 |
| Close the send rack | 1,200 × 660 | 9 | 225 | 90.667 |

The resize takes all 100 lost vertical pixels out of the workspace. At that size, the open rack leaves 684 horizontal pixels inside the bank. Subtracting eight 4-pixel gaps leaves 652 pixels for nine channels. The last table column rounds that quotient for display. The assertions use the full quotient with an absolute tolerance of 0.002 pixels.

## What happened on first use

I wrote the direct declarations and geometry checks using the README and public API. The first program compiled and all seven frames met their recorded expectations on commit `146f57e`. I made no corrective layout edits and used no precomputed strip widths in that attempt. Each edit also matched a new tree built independently from the updated session. No solve produced a warning.

A horizontal stack of `Fill` children handled rack visibility, insertion and viewport changes without application-side arithmetic. A freely placed selection lamp reserved no space beside the seven in-flow controls in each vertical strip. For insertion I appended the new subtree and then called `move_node(..., Destination::Before(...))`. The extra operation is visible in the example. Defining the normalized fader position as the center of the thumb used the default center anchor directly.

The retained resize reported `FallbackTooMuchWork` on both declarations. The fresh and retained rectangles still agreed. The printed route is diagnostic output. A route change alone does not fail the sample.

## Paired experiment added after the first run

The second pass deliberately repeats the entire session with host-computed pixel widths. The host subtracts outer insets, browser and master widths, the optional rack width, panel gaps, bank padding and strip gaps, then divides by the current channel count. It updates the affected declarations when the resulting width changes. All other nodes, data, viewport sizes, edit order and geometry checks are identical.

For every frame, each variant solves its existing tree and builds a fresh tree from the same final session. It also checks that exactly two named rectangles change after mute and exactly three outputs change after the combined selection and fader edit. The program checks the two warning lists, compares every named rectangle for exact equality within each variant, and verifies that hidden selection lamps report `TreeError::LayoutUnavailable`. It then compares the two variants by stable control name, testing all four absolute edges within 0.002 logical pixels. Because fresh and retained agree exactly inside each pair, the cross-variant edge comparison applies to both.

On the recorded runs, the maximum cross-variant edge difference printed as 0.000000 pixels throughout and all warning lists were empty. The manual variant had to rewrite eight strip widths when the rack opened, then nine on insertion, resize and rack closure. In the direct variant those operations changed only the application structure or viewport. This probe measures the cost in application declarations. It makes no timing claim.
