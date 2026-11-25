# Benchmark handoff

Run these commands from the `craft_layout` checkout. Use the recorded baseline references for historical comparisons, or pass the revisions you want to compare to the first-solve runner.

| Suite | What it measures | Runner and adapters |
| --- | --- | --- |
| First solve | Paired cold solves on 13 PanGUI and six application fixtures | [Setup and commands](first_solve/README.md) · [Runner](first_solve/run.py) · [Application driver](first_solve/driver.rs) |
| Are We Layout Yet | PanGUI against peer engines, including default and Batch modes | [Setup and commands](arewelayoutyet/README.md) · [Dense adapter](arewelayoutyet/adapter.rs) · [Owned adapter](arewelayoutyet/owned_adapter.rs) · [Paired timing code](arewelayoutyet/batch_sampling.rs) |
| Application edits | Browser, Linux compositor, and CAD edits, with default, Batch, and forced-full solves | [Setup and commands](real_workloads/README.md) · [Fixture builders](../benches/real_workloads) |
| Original Keru comparison | The application fixtures with the same operations supported by upstream Keru | [Setup and commands](real_workloads/README.md#compare-against-original-keru) · [Runner](real_workloads/compare_upstream) · [Upstream adapter](real_workloads/compare_upstream/src/bridge.rs) |
| Browser conformance | Translated Taffy fixtures scored against Chrome layouts | [Setup and results](conformance/README.md) · [Runner](../tests/conformance/main.rs) |
| Topological order | Graph repairs and rank admission on application traces | [Setup and commands](topological_order/README.md#reproduce) · [Trace patch](topological_order/trace.patch) |

The latest report includes the raw tables and paired summaries from the first-solve runs. [Report and samples](../reports/pangui-2026-11-24-first-pass-optimization/report.md)
