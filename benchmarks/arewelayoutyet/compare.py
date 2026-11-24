#!/usr/bin/env python3
"""Build the same PanGUI adapter against two Keru checkouts and compare paired runs."""

import argparse
import json
import math
from pathlib import Path
import shutil
import statistics
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent


def build(directory, source, parser):
    rust = directory / 'src'
    rust.mkdir(parents=True)
    shutil.copyfile(HERE / 'probe.rs', rust / 'main.rs')
    shutil.copyfile(HERE / 'adapter.rs', rust / 'adapter.rs')
    shutil.copyfile(parser, rust / 'pangui_template.rs')
    (directory / 'Cargo.toml').write_text(
        '[package]\nname = "pangui-probe"\nversion = "0.0.0"\nedition = "2024"\n'
        f'[dependencies]\nkeru_layout = {{ path = {json.dumps(str(source))} }}\n'
    )
    shutil.copyfile(source / 'Cargo.lock', directory / 'Cargo.lock')
    subprocess.run(['cargo', 'build', '--release', '--target-dir', str(directory / 'target')],
                   cwd=directory, check=True, stdout=subprocess.DEVNULL)
    return directory / 'target' / 'release' / 'pangui-probe'


def sample(binary, templates, cpu):
    command = [str(binary), str(templates)]
    if cpu is not None:
        command[:0] = ['taskset', '-c', str(cpu)]
    output = subprocess.check_output(command, text=True)
    rows = {}
    for line in output.splitlines():
        name, nodes, digest, ns, *allocations = line.split('\t')
        rows[name] = (int(nodes), digest, float(ns), tuple(map(int, allocations)))
    return rows


def compare(baseline, candidate):
    if baseline[0].keys() != candidate[0].keys():
        raise ValueError('The checkouts did not run the same workloads')
    print('workload\tnodes\tbaseline_ns\tcandidate_ns\tpaired_change_pct\tgeometry_hash'
          '\tbaseline_cold_allocs/bytes\tcandidate_cold_allocs/bytes'
          '\tbaseline_warm_allocs/bytes\tcandidate_warm_allocs/bytes')
    ratios = []
    for name in baseline[0]:
        before = [sample[name] for sample in baseline]
        after = [sample[name] for sample in candidate]
        nodes, digest = before[0][:2]
        if any(row[:2] != (nodes, digest) for row in before + after):
            raise ValueError(f'Different node count or geometry for {name}')
        ratio = statistics.median(new[2] / old[2] for old, new in zip(before, after))
        ratios.append(ratio)
        old_allocs, old_bytes, old_warm, old_warm_bytes = before[0][3]
        new_allocs, new_bytes, new_warm, new_warm_bytes = after[0][3]
        if any(row[3] != before[0][3] for row in before) or any(row[3] != after[0][3] for row in after):
            raise ValueError(f'Non-reproducible allocation counts for {name}')
        print(f'{name}\t{nodes}\t{statistics.median(row[2] for row in before):.1f}'
              f'\t{statistics.median(row[2] for row in after):.1f}\t{100 * (ratio - 1):+.1f}\t{digest}'
              f'\t{old_allocs}/{old_bytes}\t{new_allocs}/{new_bytes}'
              f'\t{old_warm}/{old_warm_bytes}\t{new_warm}/{new_warm_bytes}')
    print(f'Geometric mean change: {100 * (math.exp(statistics.mean(map(math.log, ratios))) - 1):+.2f}%')


def main():
    arguments = argparse.ArgumentParser(description=__doc__)
    arguments.add_argument('arewelayoutyet', type=Path, help='path to the upstream checkout')
    arguments.add_argument('baseline', type=Path, help='path to the baseline Keru checkout')
    arguments.add_argument('candidate', type=Path, help='path to the candidate Keru checkout')
    arguments.add_argument('--pairs', type=int, default=9)
    arguments.add_argument('--cpu', type=int, help='Linux CPU ID to use for both binaries')
    options = arguments.parse_args()
    if options.pairs < 1:
        arguments.error('--pairs must be positive')
    upstream = options.arewelayoutyet.resolve() / 'benchmarks'
    with tempfile.TemporaryDirectory(prefix='pangui-compare-') as scratch:
        paths = (options.baseline.resolve(), options.candidate.resolve())
        binaries = [build(Path(scratch) / str(index), source, upstream / 'src/pangui_template.rs')
                    for index, source in enumerate(paths)]
        observations = ([], [])
        for pair in range(options.pairs):
            for index in (0, 1) if pair % 2 == 0 else (1, 0):
                observations[index].append(sample(binaries[index], upstream / 'pangui', options.cpu))
        compare(*observations)


if __name__ == '__main__':
    main()
