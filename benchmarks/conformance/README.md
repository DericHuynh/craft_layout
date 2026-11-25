# Browser conformance

The conformance runner scores keru against the 6,604 browser-generated fixtures in Taffy's test suite. Each fixture describes a CSS tree and the rectangles Chrome computed for it. The runner translates each tree into keru parameters, solves it, and compares every node's parent-relative position and size with Taffy's 0.1 px tolerance. It reproduces Taffy's Ahem text measurer, where glyphs are 10 px squares and lines only break at zero-width spaces. [Runner](../../tests/conformance/main.rs) · [Translator](../../tests/conformance/translate.rs)

```sh
benchmarks/conformance/fetch.sh            # pinned Taffy revision into target/taffy-fixtures
cargo test --test conformance              # scoreboard and ratchet check
cargo test --test conformance -- --filter flex/ --verbose
cargo test --test conformance -- --update  # record the current passing set
cargo test --test conformance -- --case-report cases.tsv
```

A browser pass means that every rectangle matches Chrome. A native match means that the browser geometry differs and every rectangle matches a hand-derived expectation for the translated keru declarations. A failure is a translated fixture that satisfies neither check, or a violation of a registered native expectation. Unsupported means the translator could not map the input. The runner skips with a message when the fixture directory is absent. Set `KERU_CONFORMANCE_DIR` to another checkout's `tests/xml` directory to use its fixtures.

Two independent checks protect these results. The browser ratchet requires every recorded fixture to keep matching Chrome. Native expectations name individual fixtures, give the sizing rule, and specify a complete parent-relative rectangle tree. A missing protected fixture fails the run. An unexpected warning or a changed rectangle on a protected case also fails the run, including when updating the browser ratchet. An expected diagnostic records its kind, child path and axis. The runner checks its exact multiplicity as well as the geometry. Use `--verbose` to see the rule behind each native match. The TSV export contains every fixture ID, outcome, translation or failure reason, diagnostic list, and all published parent-local rectangles for a translated case. [Browser ratchet](../../tests/conformance/passing.txt) · [Native expectations](../../tests/conformance/native_expectations.xml)

| Category | Browser pass | Native match | Fail | Unsupported | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| block | 214 | 8 | 0 | 898 | 1,120 |
| blockflex | 18 | 2 | 0 | 32 | 52 |
| blockgrid | 0 | 0 | 0 | 56 | 56 |
| contain | 0 | 0 | 0 | 32 | 32 |
| flex | 469 | 45 | 0 | 2,226 | 2,740 |
| float | 0 | 0 | 0 | 160 | 160 |
| grid | 0 | 0 | 0 | 2,340 | 2,340 |
| gridflex | 0 | 0 | 0 | 44 | 44 |
| leaf | 14 | 0 | 0 | 46 | 60 |
| **All** | **715** | **55** | **0** | **5,834** | **6,604** |

The [case-by-case review](../../reports/constraint-semantics/README.md) records the reasoning for each layout Craft could run on either revision and the adapter reason for every other input. Coordinates for out-of-flow browser boxes are converted from the CSS containing block to the immediate parent before comparison.

For example, the translator maps two pixel flex bases of 100 and 50 to two pixel-sized stack children. In a 100 px row Chrome shrinks them to 67 and 33. Keru places the second child at 100 with width 50. A separate pair of fixtures gives a 40 px-wide child an aspect ratio of 2 inside a 100 px-high row. The translator puts the ratio on height, producing a 20 px-high child. Chrome's default cross-axis stretch gives it 100 px. Each comparison checks positions, sizes, and descendants under the same input.
