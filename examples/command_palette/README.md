# Canvas command palette

Run from the repository root with `cargo run --locked --manifest-path examples/command_palette/Cargo.toml`. This headless Rust app prints the menu rectangle for each interaction and checks the published geometry.

A document canvas sits below a 28 px toolbar and above a 20 px status bar. A right-click opens a menu with a title, two command rows and a result count. Each row contains an icon, a label and a shortcut. Changing the selection updates “Rename” to “Rename selection” while the menu stays open. The user then invokes it at the opposite corner, resizes and invokes again, and dismisses it. A deterministic 8 × 16 monospace measurement callback gives the text leaves an intrinsic size.

## Two ways to place the menu

The first replay sets the panel’s anchor to `Start` and `window_overflow` to `Flip` on both axes. The app supplies the pointer relative to the canvas and solves once. The panel and its nested stacks use `FitContent`.

The second replay supplies identical inputs and sets overflow to `Ignore`. It solves at the requested position, reads the absolute panel and canvas rectangles, mirrors an overflowing axis around the pointer, clamps that result to the window, translates back to canvas coordinates and solves again. This is the precaution an author might take if the final menu size were needed to position it. Opening, updating, moving and resizing required four solves in the native replay and eight in the two-pass replay. Including the initial closed canvas and dismissal brings the totals to six and ten.

| Interaction | Window | Pointer in window | Native menu origin | Two-pass menu origin | Menu size |
| --- | --- | --- | --- | --- | --- |
| Right-click near the bottom right | 400 × 240 | (372, 216) | (244, 120) | (244, 120) | 128 × 96 |
| Selection changes while open | 400 × 240 | (372, 216) | (188, 120) | (188, 120) | 184 × 96 |
| Reinvoke near the top left | 400 × 240 | (32, 40) | (32, 40) | (32, 40) | 184 × 96 |
| Resize and invoke near the middle | 256 × 160 | (120, 90) | (72, 64) | (0, 0) | 184 × 96 |

The first three frames matched the coordinates calculated before the first run on `146f57e`. All 19 published rectangles agreed across the two replays. On the fourth frame, the original requirement was to keep the menu fully inside the window. Neither side of the pointer had room along either axis. Both replays met that requirement. Native placement clamped the requested side, putting the menu against the right and bottom edges. The two-pass code clamped the mirrored side, putting it against the left and top edges. The executable also checks those two observed rectangles as a follow-up. Removing the panel invalidates its descendant handles and restores the seven-node document view.
