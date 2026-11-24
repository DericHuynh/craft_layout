# arewelayoutyet benchmarks

The adapter uses the 13 PanGUI templates and parser from `arewelayoutyet` at `b1f5ff86eae840705950ae037f8d397e0f20a0a2`. It builds a dense `TreeAdapter`, adds a viewport root, and translates native Stack, Wrap, margins, padding, sizing modes, and constraints. The adapter writes absolute rectangles and uses the suite's viewport defaults. [Upstream benchmarks](https://github.com/DericHuynh/arewelayoutyet/tree/b1f5ff86eae840705950ae037f8d397e0f20a0a2/benchmarks)

## Compare two checkouts

```sh
python3 benchmarks/arewelayoutyet/compare.py --cpu 4 --pairs 15 \
  /path/to/arewelayoutyet /path/to/baseline-keru /path/to/candidate-keru
```

Use a CPU available on the host or omit `--cpu`. The probe compiles the same adapter twice in release mode with each checkout's default features. It excludes template parsing, tree construction, and geometry hashing from timing. The reported change is the median of paired warmed solve times. Process order alternates between pairs. The probe reports allocation counts and requested bytes for the first solve and the warmed batch, and checks the absolute edge hash across all runs. The measured node count excludes the viewport root.

## Use the upstream Criterion runner

Copy `adapter.rs` over `benchmarks/src/keru_layout_helpers.rs` in the upstream checkout. Run the following command from that checkout's `benchmarks` directory with an absolute path to the local Keru checkout. [Adapter source](adapter.rs)

```sh
cargo --config 'patch.crates-io.keru_layout.path="/path/to/keru"' \
  bench --bench pangui --features keru_layout -- keru_layout
```

The source adapter derives from the MIT-licensed upstream Keru adapter. [Upstream adapter](https://github.com/DericHuynh/arewelayoutyet/blob/b1f5ff86eae840705950ae037f8d397e0f20a0a2/benchmarks/src/keru_layout_helpers.rs) · [Upstream license](LICENSE)

## Cross-engine results

The paired PanGUI run with this adapter measured a **3.8190× minimum speedup** and a **5.4095× geometric mean** across all 13 workloads. The report includes the measurements against all 11 supported peers, allocation counts, and reproduction steps. [Original-adapter report](../../reports/pangui-2026-11-23-original-adapter/report.md)

## Optimization results

Across 19 alternating release pairs pinned to one logical CPU on an Intel Xeon Platinum 8573C host, the optimized crate reduced the equal-workload geometric mean of paired solve times by **9.98%** against the verified pre-optimization tree. All 13 workloads had lower median paired times. The reductions ranged from 3.7% to 26.9%. The absolute rectangle hashes matched throughout. Both builds made zero allocations in the initial and warmed solves of these templates. [Per-workload results](results.tsv)

### Supplemental workloads

| Workload | Observed change |
| --- | --- |
| 513-node chain of nested Fit containers | Warm solve went from 16 allocation calls and 40,800 requested bytes to zero |
| Depth-256 incremental reorders | Warm owned-tree edits went from 7 allocations to zero, and untracked adapter edits went from 14 to zero |
| Same-parent move at depth 256 | Median time for the edit went from 1,296 ns to 25 ns |
| Forward sparse grid with 8,000 tall spans | Median CPU time went from 467 ms to 1.48 ms |
| Start-aligned stacks with 1,024 leaves | Paired CPU time fell 19–27% across the measured axis, retained-output, and rounding cases |
| Single-context leaf churn | 32,768 insert and remove cycles went from 32,771 allocation calls to 3 |
| SVG with long escaped labels | Paired CPU time fell 42% with byte-identical output |

The reusable sizing and incremental worklists retain their peak backing capacity.
