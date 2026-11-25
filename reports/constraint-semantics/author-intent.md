# Which layout workarounds does a Craft author need?

A toolbar has a 40px action and an 8px gap. At 144px wide, the other slot should have 96px. A row of three equally wide cards in 300px should give each card 100px. We used constraints like these to predict rectangles before comparing engines. Each trial has a second size or a change in content, placement or tree structure that could invalidate a one-size workaround.

## Direct declarations and measured alternatives

Measurements use native Craft, Taffy 0.15.0 at the [fixture revision](../../benchmarks/conformance/fetch.sh), Yoga 3.2.1 WebAssembly, Chrome for Testing 158.0.8127.88, and Godot 4.7.2 for the equal-card comparison. The flex controls use equal growth, a zero basis and explicit shrink. Yoga was also run with its shorter `setFlex(1)` and both settings of `UseWebDefaults`. All dimensions below are logical pixels.

| Author request | Native Craft | Other engines and the previous workaround |
| --- | --- | --- |
| Keep a 40px action inside a 224px or 144px toolbar with a 288px title | `Size::Fill` on the slot gives 176 or 96. The action starts at 184 or 104. Visible and clipped overflow allocate the same width. With a genuinely requested minimum of 160, the 144px row overflows. | Taffy and Chrome's visible-overflow flex slot stays 288 wide at both sizes. Setting its minimum width to zero gives 176 or 96. Yoga gives 176 or 96 directly. All three keep the rigid child 288 wide. Cropping or wrapping the title is a separate choice. |
| Share a row equally, with 18px side padding on the middle card | Three `Fill` cards give 100/100/100 at width 300 and 80/80/80 at 240. The middle contents have 64 or 44. | Chrome Flexbox, Taffy and Yoga give 88/124/88 and 68/104/68. Moving the padding inside the cards yields equal outer widths with the explicit zero basis. Yoga's web-default shorthand still gives 88/124/88 for that nested control at 300. Chrome Grid with three fractional columns and Godot HBox with three Expand Fill controls both achieve equal widths directly. |
| Scroll eight rigid 30px rows below a 36px header, with an intermediate pane | `Fill` on the pane, scrolling on the list. At heights 160 and 112 the viewport gets 124 or 76, with maximum offsets 116 or 164. A zero minimum on the pane changes neither. | Taffy and Chrome's default flex wrapper grows to 240 at both heights. The inner list has zero scroll distance. Setting the wrapper's minimum height to zero yields the intended viewport and range. Yoga gives the intended viewport directly. Its final row ends at 240 in list coordinates. Yoga supplied geometry only. |
| Push a trailing 20px action to the end of each actual line | Two 34px labels, 6px horizontal spacing, 4px line spacing and a leading `Margin::AUTO` on the action give top-left positions (86,0), (80,0) and (79,14) at widths 106, 100 and 99. Native `Wrap` now handles this directly. | Chrome, Taffy and Yoga give the same positions with a leading auto margin. Without it, Chrome and Yoga put the action at (80,0), (80,0) and (0,14). The old simple Craft wrap did the same even when the author requested the margin. Switching to managed flex used to recover the desired layout. |
| Keep a rail visible beside a flexible grid track | Native `Track::Fr(1.)` gives the track a share of the available space. The separately specified scroll or clip policy determines what happens to a wide descendant. | In Taffy's 240px grid with a 40px rail and a 320px child, bare `fr(1.)` puts the rail at 320. Taffy's public `flex(1.)` track helper puts it at 200 directly, just like specifying `minmax(0, 1fr)` in CSS. The child remains 320 in both Taffy cases. |
| Wrap cards near 120px and fit a single card in a narrower pane | `TrackAxis::auto_fit_within(120.)` gives one 90px track at width 90. A hard 120px floor gives a 120px track in the same pane. | Taffy agrees with Craft's explicit hard floor at 380, 379, 250, 249, 120, 90 and 0px. The browser recipe for the softer preference uses `minmax(min(100%, 120px), 1fr)`. Craft's importer also accepts that expression. |
| Stop a sticky heading at the end of its own grid row | A direct grid item can choose `Placement::StickyInGridArea(insets)`. At offset 80 the example's 16px heading has top −16. Choosing whole-grid `Placement::Sticky(insets)` gives top 2. | The earlier Craft recipe introduced a section filling the row solely to supply a boundary. The earlier Chrome 83 and 158 trials also yielded −16 with the section and 2 for the unwrapped item. The direct native declaration covers single cells and multi-track spans, including in a scrolling grid with padding. |

The card trial also tested the point where the padding itself cannot fit. With 60px to share, Craft keeps three 20px boxes and the middle content shrinks to zero. Godot gives 12/36/12 to preserve the middle control's combined minimum. When asked for 30px or 0px, Godot gives the row an actual width of 36px. Craft keeps the requested outer widths. Inside each box the physical left/top padding takes the available space first, and the opposite edge stops there when the content size reaches zero. At a 30px row width, the middle box occupies x=10..20. Its empty child now sits at x=20. Before the fix it sat at x=28. At zero width it now sits at 0 instead of 18. A child with an explicitly requested positive width can still overflow. The [padding trials](../../tests/edge_padding.rs) exercise both placements and restored sizes. A [grid overlay control](../../tests/edge_scroll.rs) covers the related reference-box error. At a 30px grid width, an overlay assigned to the full padding box used to be 36px wide. It now uses all 30px, while a marker in the content area starts at x=18. At 10px, the marker starts at x=10 and the overlay spans x=0..10.

The [published flex minimum workaround](https://defensivecss.dev/tip/flexbox-min-content-size/) addresses a real consequence of the [CSS automatic minimum](https://www.w3.org/TR/css-flexbox-1/#min-size-auto). An app using the literal CSS importer should still expect the long-title fixture's automatic content floor. Native `Fill` already expresses the slot the author wants. In the padded-card and nested-scroll fixtures the importer itself gives the Craft results. [Yoga flexibility](https://www.yogalayout.dev/docs/styling/flex-basis-grow-shrink) · [Taffy track helper](https://docs.rs/taffy/0.15.0/taffy/style_helpers/fn.flex.html) · [Godot container sizing](https://docs.godotengine.org/en/stable/tutorials/ui/gui_containers.html)

Two changes are visible to existing native clients. A main-axis automatic margin on a simple stack or wrap now consumes positive spare space. Existing code that wants zero space can use the default margin. Adding `StickyInGridArea` to the public `Placement` enum requires downstream exhaustive matches to handle the new variant. On a parent without a managed track grid, it uses that parent's content boundary.

## What the component authors had to change

A separate Rust client used a horizontal timeline with tracks of 31, 67 and 109px, 7px gaps and a 90px viewport. Its 18px chip had a 5px inset and occupied the second track. The author predicted positions before running the client. At offsets 90 and 110, the chip moved to −3 and −23 with area scope. It stayed at 5 with whole-grid scope or when spanning the last two tracks. Editing the span back restored the original positions. Both solver paths matched all 48 [predicted rectangles](../../tests/edge_scroll.rs) on the first run. The author used one grid child and made no declaration revisions.

A second author built a vertical status list with 18, 20 and 10px items and two 5px gaps. The chip in the middle had automatic top and bottom margins. At height 88, the 30px remainder should yield 15px on either side and put the chip at y=38. With the last item removed, the remainder rises to 45 and the chip starts at 45.5. Reinstating the last item must return the chip to 38. Testing the same tree after edits exposed a retained batch path that left the chip at 45.5. A freshly built tree already gave 38. After the fix, all 36 fresh and retained solves matched the author's original geometry on both backends. A one-pixel change from 58 to 57 also tested the wrap threshold and allocation per column.

The same reviewer independently built a [24-control toolbar](../../tests/author_toolbar.rs). At 238px, 24 controls of 8px plus 23 gaps of 2px fit exactly. At 237px, the last control wraps and 9px is left on the first line. Four automatic edges share 2.25px each. All 1,920 predicted rectangles matched across both solvers, Stack and Wrap, ordinary and reversed order, fractional coordinates and half-pixel snapping. The author added no spacer, override or size estimate after seeing the output.

## Earlier recipes retested

| Previous workaround | Direct Craft request | Control that distinguishes the two |
| --- | --- | --- |
| Invisible last-row cards and compensated negative gutters | Use shared grid columns for a catalog, native spacing for pills. | Adding a dummy card creates an extra row at eight real cards. Leading margins alone change the pill wrap threshold from 94 to 100. |
| Clearfix and a one-pixel padding strip to prevent margin collapse | Give a block independent formatting context with `isolate_block_margins`. | Float enclosure, sibling clearance, real padding and collapsing margins each have distinct geometry. |
| Fixed footer reservations, guessed half-size offsets and ratio-padding wrappers | A growing middle section, `Pos::Center` and `Size::AspectRatio` express those three intents. | A larger footer and dialog break the old fixed offsets. Removing the width-defining wrapper doubles the ratio-padding example's height. |
| A zero-height parent for a percentage grandchild, or a hidden copy to hold a panel open | Use the definite assigned height or a fit-content free-layout parent with overlapping panels. | Both the direct percentage-height case and its redundant resets give 80px. In the panel trial, excluding an alternative from layout changes the parent's size. |
| Manual row reversal in RTL, fixed gutter reservations and sticky clipping ancestors | Choose logical edges, a scrollbar policy, and the desired sticky boundary. | Changing writing direction, overflowing by a single pixel, or changing `Clip` to `Hidden` can each change geometry. In the earlier padded hidden-ancestor trial, Craft and Chrome still differ by 2px. |

The full [workaround audit](css-workarounds.md) and [edge-case audit](edge-cases.md) retain the individual inputs, controls and browser versions. Geometry differences have concrete inputs and expected answers. Conflicting constraints, such as a 120px hard minimum inside a 90px parent, have a defined overflow result. The measurements cover sizing, placement, scroll ranges and clips. They do not establish pixel rendering or memory-safety properties.

The declaration audit checks all 58 CSS names in the pinned corpus. Renaming each selected fixture preserved its computed geometry. Removing each declaration changed it. Changing only a recorded expected coordinate failed the comparison and preserved the computed rectangles. All 58 removal trials, 58 rename controls and the corrupted-expectation control passed.

## Reproduce

From the repository root:

```sh
cargo test --locked --test workaround_flex --test workaround_flow --test workaround_grid --test workaround_position
cargo test --locked --test edge_grid --test edge_logical --test edge_scroll --test edge_wrap
cargo test --locked --features batch-pilot --test edge_wrap --test edge_scroll --test edge_padding --test author_toolbar
benchmarks/conformance/fetch.sh
cargo test --locked --test conformance -- --require-resolved
cargo test --locked --test conformance -- --workarounds
python benchmarks/conformance/check_declarations.py
cargo run --locked --manifest-path benchmarks/author-intent/taffy/Cargo.toml
python benchmarks/author-intent/chromium.py --browser /path/to/chrome-headless-shell
```

For Yoga, install the pinned package into an isolated directory and run the checked-in probe beside it:

```sh
yoga_dir=$(mktemp -d)
npm install --prefix "$yoga_dir" yoga-layout@3.2.1
cp benchmarks/author-intent/yoga.mjs "$yoga_dir/"
node "$yoga_dir/yoga.mjs"
node "$yoga_dir/yoga.mjs" --shorthand
```

The [Godot script](../../benchmarks/author-intent/godot.gd) includes the command for running its empty headless project. The [Chromium probe](../../benchmarks/author-intent/chromium.py) uses Python Playwright and constructs its DOM from the existing CSS inputs. The comparators are standalone programs. Craft's production crate requires none of these engines.
