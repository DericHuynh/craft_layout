#!/usr/bin/env python3
"""Summarize paired runs from the real_workloads --phase-timings report."""

import argparse
import csv
from pathlib import Path
from statistics import median


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("--phases", action="store_true", help="include individual edit phases")
    options = parser.parse_args()

    groups = {}
    with options.report.open() as report:
        for row in csv.DictReader(report, delimiter="\t"):
            phase = row["phase"]
            mode = row["mode"]
            if (phase != "all" and not options.phases) or mode == "full":
                continue
            modes = groups.setdefault((row["workload"], phase), {}).setdefault(row["run"], {})
            if mode in modes:
                raise ValueError(f"duplicate sample for {row['workload']} run {row['run']} phase {phase}")
            modes[mode] = (float(row["p50_us"]), float(row["p95_us"]))

    print("workload\tphase\truns\tdefault_p50_us\tbatch_p50_us\tbatch_p95_us"
          "\tbatch_p95/default_p50\tbatch_p95/batch_p50")
    for (workload, phase), runs in groups.items():
        if any(modes.keys() != {"default", "batch"} for modes in runs.values()):
            raise ValueError(f"incomplete pair for {workload} phase {phase}")
        pairs = [(modes["default"][0], *modes["batch"]) for modes in runs.values()]
        default_p50, batch_p50, batch_p95 = map(median, zip(*pairs))
        over_default = median(p95 / default for default, _, p95 in pairs)
        over_batch = median(p95 / batch for _, batch, p95 in pairs)
        print(f"{workload}\t{phase}\t{len(runs)}\t{default_p50:.3f}\t{batch_p50:.3f}\t{batch_p95:.3f}"
              f"\t{over_default:.3f}\t{over_batch:.3f}")


if __name__ == "__main__":
    main()
