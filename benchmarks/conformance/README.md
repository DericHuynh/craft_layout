# Browser conformance

The conformance runner scores keru against the 6,604 browser-generated fixtures in Taffy's test suite. Each fixture describes a CSS tree and the rectangles Chrome computed for it. The runner translates each tree into keru parameters, solves it, and compares every node's parent-relative position and size with Taffy's 0.1 px tolerance. It reproduces Taffy's Ahem text measurer, where glyphs are 10 px squares and lines only break at zero-width spaces. [Runner](../../tests/conformance/main.rs) · [Translator](../../tests/conformance/translate.rs)

```sh
benchmarks/conformance/fetch.sh            # pinned Taffy revision into target/taffy-fixtures
cargo test --test conformance              # scoreboard and ratchet check
cargo test --test conformance -- --filter flex/ --verbose
cargo test --test conformance -- --update  # record the current passing set
```

A fixture is unsupported when it uses CSS that keru cannot express yet. The translator only maps properties whose keru counterpart has the same meaning. Fixtures listed in [`passing.txt`](../../tests/conformance/passing.txt) must keep passing, so a change that breaks one fails the run. The runner skips with a message when the fixtures are absent. Set `KERU_CONFORMANCE_DIR` to use another checkout.

| Category | Pass | Fail | Unsupported | Total |
| --- | ---: | ---: | ---: | ---: |
| block | 170 | 34 | 916 | 1,120 |
| blockflex | 12 | 8 | 32 | 52 |
| blockgrid | 0 | 0 | 56 | 56 |
| contain | 0 | 0 | 32 | 32 |
| flex | 353 | 145 | 2,242 | 2,740 |
| float | 0 | 0 | 160 | 160 |
| grid | 0 | 0 | 2,340 | 2,340 |
| gridflex | 0 | 0 | 44 | 44 |
| leaf | 10 | 4 | 46 | 60 |
| **All** | **545** | **191** | **5,868** | **6,604** |

This baseline uses the full solver before the 0.2 changes. Most unsupported fixtures use right-to-left direction, grid, floats, overflow, or flex features keru lacks.
