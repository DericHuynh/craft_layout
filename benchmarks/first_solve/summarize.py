import argparse
from collections import defaultdict
import csv
import math
import random
from statistics import median

parser = argparse.ArgumentParser()
parser.add_argument("samples", nargs="+")
parser.add_argument("--mode", default="candidate_batch")
parser.add_argument("--comparisons", nargs="+", default=["frozen_owned", "prior_batch", "frozen_batch", "frozen_dense"])
parser.add_argument("--resamples", default=3000, type=int)
args = parser.parse_args()

records = defaultdict(dict)
for run, path in enumerate(args.samples):
    with open(path, newline="") as file:
        for row in csv.DictReader(file, delimiter="\t"):
            record = (row["fixture"], run, int(row["block"]), int(row["sample"]))
            data = records[record]
            mode = row["mode"]
            assert mode not in data, (path, record, mode)
            data[mode] = tuple(int(row[clock]) for clock in ("wall_ns", "cpu_ns"))

def interval(blocks, rng):
    resampled = sorted(
        median([ratio for block in rng.choices(blocks, k=len(blocks)) for ratio in block])
        for _ in range(args.resamples)
    )
    if not resampled:
        return math.nan, math.nan
    return resampled[len(resampled) // 40], resampled[len(resampled) * 39 // 40]

rng = random.Random(0x1fa0833)
print("fixture\tcomparison\tclock\tref_median_ns\tcandidate_median_ns\tmedian_ratio\t95_low\t95_high\twins\ties\tsamples\tall_block_medians_win\tp95_ratio\tmax_ratio")
for comparison in args.comparisons:
    for clock_num, clock in enumerate(("wall", "cpu")):
        timings = defaultdict(lambda: defaultdict(list))
        for (fixture, run, block, _), values in records.items():
            if comparison in values:
                timings[fixture][run, block].append((values[args.mode][clock_num], values[comparison][clock_num]))
        fixture_medians = []
        for fixture, blocks in sorted(timings.items()):
            total = [pair for block in blocks.values() for pair in block]
            candidate, reference = zip(*total)
            ratios = [[left / right for left, right in block] for block in blocks.values()]
            flat = sorted(ratio for block in ratios for ratio in block)
            overall = median(flat)
            p95 = flat[math.ceil(0.95 * len(flat)) - 1]
            low, high = interval(ratios, rng)
            wins = sum(a < b for a, b in total)
            ties = sum(a == b for a, b in total)
            block_wins = sum(median(block) < 1 for block in ratios)
            fixture_medians.append(overall)
            print(f"{fixture}\t{comparison}\t{clock}\t{median(reference):.1f}\t{median(candidate):.1f}\t{overall:.5f}\t{low:.5f}\t{high:.5f}\t{wins}\t{ties}\t{len(flat)}\t{block_wins}/{len(ratios)}\t{p95:.5f}\t{flat[-1]:.5f}")
        if fixture_medians:
            geo = math.exp(sum(math.log(ratio) for ratio in fixture_medians) / len(fixture_medians))
            faster = sum(ratio < 1 for ratio in fixture_medians)
            print(f"ALL_FIXTURES\t{comparison}\t{clock}\t\t\t{geo:.5f}\t\t\t{faster}\t\t{len(fixture_medians)}\t\t\t")
