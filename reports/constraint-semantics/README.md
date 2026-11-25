# Constraint resolution and authoring review

## Complete translation of the pinned corpus

All 6,604 Taffy XML fixtures at `4e59968eda29ceeb0bbaeb3993c8cd38baa3d0a6` build a Craft tree, run the native solver and reach geometry comparison. Compared with `124551a`, all 3,450 previously unsupported inputs now run. Every earlier browser match still passes. Four earlier native exceptions for the static position of an absolute child now also match the browser because a preceding block sibling supplies the source position.

| Formatting context | Browser agreement | Verified Craft difference | Translated |
| --- | ---: | ---: | ---: |
| block | 1,106 | 14 | 1,120 |
| blockflex | 44 | 8 | 52 |
| blockgrid | 56 | 0 | 56 |
| contain | 32 | 0 | 32 |
| flex | 2,632 | 108 | 2,740 |
| float | 160 | 0 | 160 |
| grid | 2,336 | 4 | 2,340 |
| gridflex | 44 | 0 | 44 |
| leaf | 60 | 0 | 60 |
| **All** | **6,470** | **134** | **6,604** |

The checks cover 27,728 node rectangles, 5,664 published grid-axis lists and 872 scroll extents (436 width/height pairs). Track sizes and names are compared before pixel snapping. Boxes follow the fixture’s pixel-scale setting. A difference of 0.1 px fails. Warnings, their paths and their multiplicities participate in each result. The [case ledger](current-cases.tsv) gives the previous and current classification, case check, diagnostics, parent-local rectangles, published tracks and observed scroll extents. The [feature inventory](css-layout-scope.md) lists the 58 declaration names the fixtures exercise.

A separate [declaration audit](../../benchmarks/conformance/check_declarations.py) removes one authored declaration from a source for each of the 58 names and checks for a change in observed layout. Its control cases rename the inputs and change an expected coordinate. Renaming must preserve geometry. Corrupting the expected coordinate must fail the comparison while preserving the geometry.

### Decisions with visible consequences

| Author request | Verified behavior |
| --- | --- |
| Give an item `height: 100%` inside a flexible region that ends up 200 px tall | The child receives the allocated 200 px. If it follows a 100 px sibling it can overflow. A fallback that collapses the child to zero would require the application to repeat an already available height. |
| Safely center a 35 px notice inside a 25 px positioning ancestor | Its leading edge remains reachable at 0 px, or at 2 px with a leading margin. The tentative browser fixture starts it at 6 or 8 px. |
| Snap a 50 px box whose unrounded RTL edges are −0.5 and 49.5 | Craft rounds signed half ties away from zero. Its edges are −1 and 50, and its published width is 51. The archived browser chooses 0 and 50. Adjacent boxes still share a snapped edge. |
| Request a minimum larger than the maximum | Craft honors the minimum and reports `MinAboveMax` on the affected axis. The fixture must match the complete expected geometry and warning list. |
| Place an absolute child after an ordinary block, with no vertical inset | Its static vertical position follows the preceding sibling. The default free-positioned native primitive remains available for ordinary overlays. |

### Independent authoring trials

* **News digest.** A 30-component article page combined a leading portrait float, a trailing sponsor, a summary with a width minimum and a clearing footer. Width and filtering changes matched the author's predictions. Keeping a manual 64 px sponsor reservation after hiding the sponsor wasted that space. Extending the trial to scrolling exposed a real error: a source-positioned action jumped from y=30 to y=0 after scrolling 20 px. Its corrected y=10 now has a retained regression test. A separate flexible magazine section checks wrapped heights of 30, 40 and 30 px across width edits. [Trial and reflection](../../examples/news_digest/README.md)
* **Festival program.** Ordered cards request balanced lines and a ticket action uses an automatic leading margin. At 104 px, two rows occupied 104 and 78 px. At 103 px a third row became necessary, and the occupied widths were 78, 52 and 52. Several orders tie on balance. The earlier-fuller rule predicts which break survives the resize. Another author checked this boundary independently. [Trial and cross-review](../../examples/festival_program/README.md)
* **Production timeline.** Named cues, a span, an overlay and a subgrid moved together when an 8 px preroll track was inserted. A scroll trial found a badge pinned to the grid incorrectly adding to the range of an intervening 40 px wrapper. The wrapper now scrolls its 90 px content by 50 px and the badge moves with the grid. [Predictions and observed results](grid-fixture-review.md) · [Executable trials](../../tests/grid_authoring.rs)

An underdetermined size, an unsatisfiable pair of bounds, a browser convention and a retained-layout defect have different evidence. The native expectations specify a full tree and diagnostic list for each accepted divergence. Explicit arithmetic, fresh rebuilds and retained edits test the author's intent independently. These trials give no evidence of Rust memory unsafety or of the motives of an upstream fixture author.

## Earlier Grid implementation at `124551a`

Compared with `4d20ad7`, **1,402 additional CSS fixtures execute and agree with the archived browser geometry**. The old 1,642 browser results and 110 native contracts retain their exact rectangles and diagnostics. The ledger exported at that revision used that commit as its previous result. An untranslated row names the first blocking input and has no geometry verdict.

| Result across all 6,604 fixtures | Before | At `124551a` |
| --- | ---: | ---: |
| Archived browser geometry | 1,642 | 3,044 |
| Independently specified native difference | 110 | 110 |
| Unresolved translated mismatch | 0 | 0 |
| Untranslated | 4,852 | 3,450 |

The added inputs contain 1,470 grid elements and 7,248 expected node rectangles. There are 1,336 grid roots and 66 grid-containing flex or block roots. In 1,354 inputs the archive additionally asserts both axes of every grid, giving 2,844 track-list assertions, including 24 empty axes. The remaining 48 inputs supply box geometry only. For a 15,000-column zero-width span, the recorded second item starts the next row at y = 20. Those rectangles alone cannot establish the number of zero-width columns.

The track oracle reads the edges published by the owned tree. It compares individual track lengths before pixel snapping, in template order even when RTL reverses their physical positions. Rectangles use the fixture's snapping setting. Both comparisons use the upstream tolerance of strictly less than 0.1 px. In the ledger, long runs of identical track lengths use `value × count`. The checker compares every track individually. Managed diagnostics also participate in the verdict.

For the 156 newly admitted grid content-alignment fixtures, a second calculation used rational arithmetic, authored tracks and gutters, available space, physical border and padding, direction and pixel snapping. It recovered all 1,608 source rectangles and 408 expected axis lists. The per-case ledger includes the resulting logical offsets and physical starts. In one space-between case, 152 px of usable height minus three 40 px rows leaves 32 px, producing row starts of 12, 68 and 124 px after the leading border and padding.

The [family-by-family audit](grid-mismatch-families.tsv) covers all 468 inputs that disagreed on the first Grid translation. It records the authored sizing request, the first numeric discrepancy and the final outcome for each box-model and direction variant. The [review](grid-fixture-review.md) explains the distinct causes and a case where the published CSS guidance and the pinned browser give different answers.

Two authors predicted their application layouts before execution. The asset browser exercised 40 nodes over eight states. Its 392-to-391 px transition lost a thumbnail column exactly where predicted. The scoreboard exercised 14 matches, a banner spanning unequal fractional tracks, filtering and a longer team name. Filtering restored the 2:1 club/score split. The longer name then required a 252 px panel in a 240 px viewport. The authored and host-computed versions agreed. [Asset browser trial](../../examples/asset_browser/README.md) · [Scoreboard trial](../../examples/scoreboard/README.md)

### Verification

The Cargo suites passed 317 tests and doctests with all features, 256 with defaults, and 58 without default features. The fixture executable separately checked all 6,604 source IDs. The asset browser, dispatch board and maintenance console passed six focused example tests. The scoreboard assertions passed with ordinary and Batch solving. The editor, kiosk, mixing studio and command-palette examples replayed successfully, as did all six release workload checks. Four Kani harnesses checked cache equality and edit classification against the actual Rust declaration structure. The separate native grid-intrinsics proof passed for the established uniform-grid code. Executable examples and tests cover the new heterogeneous-track arithmetic.

### Adopting the declarations

Code that builds `LayoutParams` or `NodeRules` with struct update syntax inherits the defaults. An exhaustive `LayoutParams` literal needs `isolate_block_margins: false` to retain the earlier setting. Exhaustive `NodeRules` literals also need the optional content-minimum and grid fit-limit fields. Exhaustive matches over `Track` or `TrackMax` need an `Auto` arm. Choose `Track::Content` when the column should stop at its content preference, and choose `Track::Auto` when it should also share leftover space.

### Track sizing allocations

The release benchmark prepares 4,096 item contributions on 64 content tracks before enabling the existing allocator counter. The mixed scene makes every eighth item span up to three tracks. Both versions use 3 px gaps and an 8,192 px available width. The counts below cover one call to the standalone track-sizing kernel. The immediate repeat gave the same counts.

| Scene | Earlier allocation calls | Current calls | Earlier bytes requested | Current bytes requested | Hash of all edges, both revisions |
| --- | ---: | ---: | ---: | ---: | --- |
| Single-span items | 15,154 | 17 | 224,528 | 69,664 | `56ac0cd971feed25` |
| Mixed spans | 13,314 | 23 | 209,904 | 71,776 | `e7aece4efe382af6` |

Single-track items fold into indexed maxima. For spanning items the solver reuses work buffers and plans competing increases from the same base sizes. The benchmark measures allocator calls and requested bytes. Run it with `cargo bench --locked --bench grid_tracks`. [Benchmark](../../benches/grid_tracks.rs)

## Writing modes, block margins and weighted flex bases

The following table records the earlier logical, block and flexible layout milestone. Its final column totals precede the Grid extension above.

| Earlier outcome | Current browser match | Current deliberate geometry difference | Current untranslated |
| --- | ---: | ---: | ---: |
| Browser match | 715 | 0 | 0 |
| Deliberate native difference | 0 | 55 | 0 |
| Untranslated | 927 | 55 | 4,852 |
| **Total** | **1,642** | **110** | **4,852** |

The first 906 newly translatable inputs cover inherited direction, nested overrides, self-alignment, physical insets, block auto margins and vertical Ahem measurement. Whole-tree RTL native contracts independently reflect each parent-local rectangle when the input has symmetric physical edges. Three fixture families need explicit treatment for physical margins or insets. The 100 px left margin on a centered child, for example, still places the child at x = 80 in both directions. The browser agreement count includes 44 cases that additionally require exact native diagnostics. All 1,752 supported fixtures have either a browser match or a deliberate whole-tree geometry contract.

A further 76 fixtures exercise single-line flex rows and columns with definite dimensions and empty leaf items. At least one growing item declares a positive pixel or percentage basis. The translator preserves every item’s preferred size and lowers its separate basis, grow factor, shrink factor and bounds into the managed flexible formatting context. For all 76 inputs, the ledger records a separate arithmetic derivation from the fixture declarations. Computing a shared growth multiplier, applying each item’s bounds, and rounding physical edges reproduced every child rectangle. In a 200 px row, for example, 50% and 25% bases give 100 and 50 px. Equal growth divides the remaining 50 px into two 25 px additions, yielding 125 and 75 px.

## Earlier constraint review

The review compares Craft at commit `146f57e` and the revised solver using Taffy revision `4e59968eda29ceeb0bbaeb3993c8cd38baa3d0a6`. It covers 6,604 individual XML inputs. Some pairs exercise identical declarations under different box-sizing defaults. Each variant has its own row.

- [Reviewed cases](reviewed-cases.tsv) contains all 772 fixtures that translated on either revision. Each row gives the original and revised outcome, the judgment about the declarations, expected warnings, and the revised Craft tree where a native translation exists. For deliberate geometric differences it includes Taffy’s coordinates at each differing node.
- [Remaining untranslated inputs](untranslated-cases.tsv) lists the other 5,832 fixture IDs and the first property that prevented translation. Two additional adapter limitations appear in the reviewed table because the baseline attempted a lossy translation.
- [Executable contracts](../../tests/conformance/native_expectations.xml) contain independently specified whole-tree geometry for the 55 intentional differences and the exact diagnostics for 22 cases that also match the browser. The [browser ratchet](../../tests/conformance/passing.txt) protects all 715 browser matches.
- [Source fixtures](https://github.com/DioxusLabs/taffy/tree/4e59968eda29ceeb0bbaeb3993c8cd38baa3d0a6/tests/xml) use the TSV fixture IDs as relative paths, with `.xml` appended. Coordinates in the review are `[x, y, width, height]` relative to the immediate parent. The fixture generator sometimes reports absolute-positioned children relative to a higher containing block. In those cases the comparison converts both positions into the same coordinate frame.

## What changed across the corpus

| Original outcome | Revised browser match | Revised native difference | Revised unsupported | Total |
| --- | ---: | ---: | ---: | ---: |
| Browser match | 545 | 0 | 0 | 545 |
| Verified native difference | 0 | 14 | 0 | 14 |
| Unresolved mismatch | 136 | 39 | 2 | 177 |
| Unsupported | 34 | 2 | 5,832 | 5,868 |
| **Total** | **715** | **55** | **5,834** | **6,604** |

The compiled Taffy engine matched all 27,728 node rectangles in the archived Chrome expectations. Its upstream whole-output check also passed every fixture. The run used the pinned checkout’s XML loader, text measurer, viewport and rounding settings. Craft compares the rectangles it publishes with the same 0.1 px tolerance. A change of less than the tolerance counts as an agreement. Untranslated input supplies no Craft geometry to evaluate.

## Authoring the applications

Four independent agents built scenes using the public API and wrote down their intended geometry before solving on the baseline. They did not consult the CSS fixtures. The authors retained their first-use observations in the sample READMEs. Each alternative then used the same content and sequence of edits as the direct declaration. These scripted trials test the expectations those four authors recorded for these scenes.

| Sample | First declaration and paired result | Rework observed |
| --- | --- | --- |
| [Editor workbench](../../examples/editor_workbench) | Two weighted editors came out 486 and 324 px with a 2 px divider. Computing the widths in the host gave the same 644 named rectangles or visibility states across nine frames. | The trace initially missed deleted keys when closing a tab. Correcting it counted one deletion and zero moved survivors. |
| [Mixing studio](../../examples/mixing_studio) | Eight strips at 112.5 px became 92 px on opening a send rack. A host calculation reproduced the widths across seven frames and up to 247 nodes. | No layout rework on the first run. The alternative rewrote eight widths on opening the rack and nine on each later structural or resize step. |
| [Check-in kiosk](../../examples/checkin_kiosk) | Native and hand-budgeted descriptions matched on all 44 nodes across nine states. With a 480 px viewport, moving the booking summary above the form left 252 px for the description. Keeping the desktop rail left zero. | The compact arrangement was a product decision. A test of a reconstructed 8 px gap needed a floating-point tolerance. Retained versus fresh comparisons remained bit-exact. |
| [Command palette](../../examples/command_palette) | Native flip handled a content-sized popup in one solve per open frame. A host measure-and-place pass matched all 19 rectangles in the three frames with an unambiguous placement. | Both variants kept the menu visible when neither side fit. Native clamped the requested side and the host clamped the mirrored side. The public documentation now states the native choice. |

The editor, mixer and kiosk checked every retained state against a newly constructed tree. The palette compared independent native and two-pass replays against the recorded positions and containment rules. A request to fall back to full sizing on a kiosk or mixer resize still produced the expected rectangles. No sample required a solver change to meet its recorded first-use expectations.

## Deciding what warranted an engine change

**Native behavior had to reproduce through the public API.** An auto-width child with 22 px of padding and 5 px of horizontal margin requires a fitted block 27 px wide. Giving the parent only 5 px violated its own fit rule. An empty stack inside a block also incorrectly permitted its two margins to collapse through it. Two other cases involved a nonbinding block minimum and an unwarranted collapsed-size warning. Four Rust regressions covering these issues fail on the baseline. The revised tests include a change in a child’s padding and transitions across a binding minimum.

**Different geometric policies have usable meanings.** Two children each requesting `Frac(1.0)` in a padded 384 px row with an 8 px gap each receive 376 px. If the product wants two equal panels in that row, two `Fill` declarations give each 188 px. A 40 px-wide picture with `AspectRatio(2)` on height is 20 px tall. A text container that must grow to show six lines can instead specify `FitContent` on height. Those choices are visible in the declaration.

**An underdetermined size and a contradictory bound get different diagnostics.** A fitted parent with only an unseeded full-width descendant has no independent width. Craft publishes the documented zero fallback and `FitContentCollapsed`. A minimum exceeding a maximum cannot satisfy both bounds. Craft keeps the minimum and identifies the axis with `MinAboveMax`. An independently measured extent of zero is valid. These geometry and diagnostic checks give no verdict about Rust memory unsafety.

**A compatibility score can reward the wrong change.** Two former mismatches combine an intrinsic flex parent, a zero flex basis, and an explicit preferred main size. Treating that preferred size as a hard minimum, or silently discarding it, changes the question. The adapter now identifies the unrepresented combination. Other fixtures have suggestive names without corresponding declarations. Sixteen variants mention a border or percentage border that their XML never supplies. The reviewed table describes what each input actually exercises.

To reproduce the Craft results, fetch the pinned fixtures and export the case table from the repository root.

```sh
benchmarks/conformance/fetch.sh
cargo test --locked --test conformance -- --case-report cases.tsv
```
