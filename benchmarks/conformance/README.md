# Browser conformance

The conformance runner scores keru against the 6,604 browser-generated fixtures in Taffy's test suite. Each fixture describes a CSS tree and the rectangles Chrome computed for it. The runner translates each tree into keru parameters, solves it, and compares every node's parent-relative position and size with Taffy's 0.1 px tolerance. It reproduces Taffy's Ahem text measurer, where glyphs are 10 px squares and lines only break at zero-width spaces. [Runner](../../tests/conformance/main.rs) · [Translator](../../tests/conformance/translate.rs)

```sh
benchmarks/conformance/fetch.sh            # pinned Taffy revision into target/taffy-fixtures
cargo test --test conformance -- --require-resolved  # pinned inventory, comparison and both ratchets
cargo test --test conformance -- --filter flex/ --verbose
cargo test --test conformance -- --update  # record the current passing set
cargo test --test conformance -- --case-report cases.tsv
```

A browser pass requires agreement with every archived rectangle, published grid-axis list and scroll extent, plus the expected diagnostics. A native match means that the browser geometry differs and every rectangle matches a hand-derived expectation for the translated keru declarations. A failure is a translated fixture that satisfies neither check, or a violation of a registered native expectation. Unsupported means the translator could not map the input. A normal test run skips when the fixture directory is absent. The explicit `--require-translated` and `--require-resolved` modes fail on a missing corpus. The first verifies that every pinned ID finished a native comparison. The second also fails on an unresolved comparison. A normal run against the fetched pinned corpus enforces both checks. Set `KERU_CONFORMANCE_DIR` to another checkout's `tests/xml` directory to use its fixtures.

Two independent checks protect these results. The browser ratchet requires every recorded fixture to keep matching Chrome. Native expectations name individual fixtures, give the sizing rule, and specify a complete parent-relative rectangle tree. A missing protected fixture fails the run. An unexpected warning or a changed rectangle on a protected case also fails the run, including when updating the browser ratchet. An expected diagnostic records its kind, child path and axis. The runner checks its exact multiplicity as well as the geometry. Use `--verbose` to see the rule behind each native match. The TSV export contains every fixture ID, outcome, translation or failure reason, diagnostic list, and all published parent-local rectangles for a translated case. [Browser ratchet](../../tests/conformance/passing.txt) · [Native expectations](../../tests/conformance/native_expectations.xml)

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

The [case-by-case ledger](../../reports/constraint-semantics/current-cases.tsv) records all 6,604 outcomes. The [authoring review](../../reports/constraint-semantics/README.md) explains the native differences and the defects exposed by interactive examples. Absolute positions are compared in the immediate parent’s coordinates.

For example, the translator maps two pixel flex bases of 100 and 50 to two pixel-sized stack children. In a 100 px row Chrome shrinks them to 67 and 33. Keru places the second child at 100 with width 50. A separate pair of fixtures gives a 40 px-wide child an aspect ratio of 2 inside a 100 px-high row. The translator puts the ratio on height, producing a 20 px-high child. Chrome's default cross-axis stretch gives it 100 px. Each comparison checks positions, sizes, and descendants under the same input.

### Declaration witnesses

Run `python3 benchmarks/conformance/check_declarations.py` after fetching the pinned fixtures. It checks one source per declaration in [the witness list](declaration-witnesses.tsv). Removing the named declaration must change at least one published rectangle, track, or scroll extent. Changing the source title and filename must preserve geometry. One additional control changes an expected root coordinate and checks that the native geometry stays identical while the comparison fails. The runner prints a partial mismatch tally for these deliberately altered inputs, followed by the witness result. The script exits unsuccessfully if a control fails or a declaration from the archive lacks a witness.
