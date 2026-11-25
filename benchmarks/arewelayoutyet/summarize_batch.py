#!/usr/bin/env python3
"""Summarize paired PanGUI timings from a tab-separated file.

Each input row pairs all three Keru modes with one supported peer. For the
workload summary, take the median across peers within each sample, then the
median across samples, so differences in peer coverage do not weight samples.
The fastest peer has the lowest median peer time for that workload. Its
speedup uses only the ratios from its own paired rows. Each supported workload
contributes one paired median to its peer's geometric means.
"""

import argparse
import csv
from dataclasses import dataclass
from math import isfinite
from pathlib import Path
from statistics import geometric_mean, median


HEADER = ["workload", "engine", "sample", "dense_ns", "default_ns", "batch_ns", "peer_ns"]


@dataclass(frozen=True)
class Timing:
    dense_ns: float
    default_ns: float
    batch_ns: float
    peer_ns: float


def read_timings(path):
    workloads = {}
    with path.open(encoding="utf-8", newline="") as stream:
        rows = csv.reader(stream, delimiter="\t")
        if next(rows, None) != HEADER:
            raise ValueError(f"{path} must start with {', '.join(HEADER)}")
        for row in rows:
            if not row:
                continue
            if len(row) != len(HEADER):
                raise ValueError(f"{path}:{rows.line_num} must contain {len(HEADER)} fields")
            workload, engine, sample, *times = row
            try:
                sample = int(sample)
                times = [float(time) for time in times]
            except ValueError as error:
                raise ValueError(f"{path}:{rows.line_num} has an invalid sample or time") from error
            if not workload or not engine or any(not isfinite(time) or time <= 0 for time in times):
                raise ValueError(f"{path}:{rows.line_num} needs names and positive finite times")
            samples = workloads.setdefault(workload, {}).setdefault(engine, {})
            if sample in samples:
                raise ValueError(
                    f"{path}:{rows.line_num} repeats {workload}, {engine}, sample {sample}"
                )
            samples[sample] = Timing(*times)
    if not workloads:
        raise ValueError(f"{path} contains no paired observations")
    return workloads


def sample_median(samples, value):
    return median(median(map(value, rows)) for rows in samples.values())


def print_summary(workloads):
    print(
        "workload\tdense_ns\tdefault_ns\tbatch_ns\tfastest_peer\tfastest_peer_ns"
        "\tbatch_over_default\tdense_over_batch\tfastest_peer_over_batch"
    )
    engine_ratios = {}
    for workload, peers in sorted(workloads.items()):
        samples = {}
        peer_times = {}
        for engine, pairs in peers.items():
            rows = list(pairs.values())
            peer_times[engine] = median(row.peer_ns for row in rows)
            engine_ratios.setdefault(engine, []).append((
                median(row.peer_ns / row.dense_ns for row in rows),
                median(row.peer_ns / row.default_ns for row in rows),
                median(row.peer_ns / row.batch_ns for row in rows),
            ))
            for sample, row in pairs.items():
                samples.setdefault(sample, []).append(row)
        dense = sample_median(samples, lambda row: row.dense_ns)
        default = sample_median(samples, lambda row: row.default_ns)
        batch = sample_median(samples, lambda row: row.batch_ns)
        batch_over_default = sample_median(samples, lambda row: row.batch_ns / row.default_ns)
        dense_over_batch = sample_median(samples, lambda row: row.dense_ns / row.batch_ns)
        fastest = min(peer_times, key=lambda peer: (peer_times[peer], peer))
        peer_over_batch = median(row.peer_ns / row.batch_ns for row in peers[fastest].values())
        print(
            f"{workload}\t{dense:.3f}\t{default:.3f}\t{batch:.3f}\t{fastest}"
            f"\t{peer_times[fastest]:.3f}\t{batch_over_default:.4f}"
            f"\t{dense_over_batch:.4f}\t{peer_over_batch:.4f}"
        )

    print()
    print(
        "engine\tworkloads\ttotal_workloads"
        "\tpeer_over_dense_gm\tpeer_over_default_gm\tpeer_over_batch_gm"
    )
    for engine, ratios in sorted(engine_ratios.items()):
        dense, default, batch = map(geometric_mean, zip(*ratios))
        print(f"{engine}\t{len(ratios)}\t{len(workloads)}\t{dense:.4f}\t{default:.4f}\t{batch:.4f}")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    parser.add_argument("timings", type=Path, help="paired benchmark TSV")
    options = parser.parse_args()
    try:
        workloads = read_timings(options.timings)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    print_summary(workloads)


if __name__ == "__main__":
    main()
