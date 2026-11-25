# Paired first-solve benchmark

The Linux runner independently links the candidate, frozen owned, and prior Batch builds in one release binary. It reads the PanGUI parser and templates from the pinned Are We Layout Yet revision, uses the checked-in PanGUI adapters, and reuses the browser, compositor, and CAD fixture builders. Python 3.12 or later, Git, and Cargo are required. The archived run used Rust 1.99.1. The optional CPU pin uses Linux `taskset`. [Upstream fixtures](https://github.com/DericHuynh/arewelayoutyet/tree/b1f5ff86eae840705950ae037f8d397e0f20a0a2/benchmarks) · [PanGUI adapters](../arewelayoutyet) · [Application fixtures](../../benches/real_workloads)

## Reproduce the archived comparison

```sh
git fetch origin tag benchmark/first-solve-owned-2026-11-24 \
  tag benchmark/first-solve-prior-batch-2026-11-24
git clone https://github.com/DericHuynh/arewelayoutyet.git ../arewelayoutyet

python3 benchmarks/first_solve/run.py ../arewelayoutyet target/first-solve-owned.tsv \
  --candidate-ref 651e2e1ed49eb6baeea30a434d7c9c5703e1ed2d --cpu 4
python3 benchmarks/first_solve/run.py ../arewelayoutyet target/first-solve-prior.tsv \
  --candidate-ref 651e2e1ed49eb6baeea30a434d7c9c5703e1ed2d --cpu 4 \
  --modes prior_batch,candidate_batch
```

Use an available CPU or omit `--cpu`. Omit `--candidate-ref` to benchmark the current worktree. `--owned-ref` and `--prior-batch-ref` accept alternate local Git revisions that support the same Batch API and dependency lock. The upstream checkout must contain the pinned revision. Fetch it explicitly if the upstream checkout is shallow.

Each trial builds fresh trees, times only the first solve, and checks their rectangle bits. One block covers all four construction and solve order combinations for a two-mode run. The default eight blocks produce 608 pairs across 19 fixtures. The output records elapsed and thread CPU time. The companion `.summary.tsv` reports paired median ratios, trial wins, and block-bootstrap intervals. Ratios below 1 mean the candidate took less time. [Archived benchmark report](../../reports/pangui-2026-11-24-first-pass-optimization/report.md)

For a quick check, add `--blocks 1 --filter padding_and_margin`. Use `--suite real` for the application fixtures or `--suite pangui` for only PanGUI. `--modes candidate_owned,candidate_batch` compares both entry points from the candidate build. `--modes frozen_dense,candidate_batch --suite pangui` compares against the frozen dense adapter. Pass `--offline` when the Cargo registry cache already contains the dependencies.
