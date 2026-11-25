# Constraint resolution and authoring review

## Writing modes, block margins and weighted flex bases

The [current case ledger](current-cases.tsv) records the previous and current outcome for each of the 6,604 fixture IDs. For a supported input it includes physical parent-local rectangles and diagnostic expectations. For a pending input it identifies the first declaration the fixture translator cannot express. A pending row has no geometry verdict.

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
