#!/usr/bin/env python3
"""Build and compare fresh layout solves from one candidate and two references."""

import argparse
from io import BytesIO
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile


RUNNER = Path(__file__).resolve().parent
REPO = RUNNER.parent.parent
UPSTREAM_REF = "b1f5ff86eae840705950ae037f8d397e0f20a0a2"
OWNED_REF = "benchmark/first-solve-owned-2026-11-24"
PRIOR_BATCH_REF = "benchmark/first-solve-prior-batch-2026-11-24"
SOURCE_FILES = ("src", "Cargo.toml", "build.rs", "README.md")
MODES = {"frozen_owned", "candidate_batch", "prior_batch", "frozen_batch", "frozen_dense", "candidate_owned"}


def archive(repo, revision, files, destination):
    data = subprocess.check_output(["git", "-C", repo, "archive", revision, "--", *files])
    with tarfile.open(fileobj=BytesIO(data)) as archive_file:
        archive_file.extractall(destination, filter="data")


def install_solver(destination, revision, version):
    destination.mkdir()
    if revision:
        archive(REPO, revision, SOURCE_FILES, destination)
    else:
        shutil.copytree(REPO / "src", destination / "src")
        for name in SOURCE_FILES[1:]:
            shutil.copyfile(REPO / name, destination / name)
    manifest = destination / "Cargo.toml"
    # Give each snapshot its own Cargo package identity in the paired binary.
    text = manifest.read_text().split("[dev-dependencies]", 1)[0]
    text = re.sub(r'^version = ".*"$', f'version = "{version}"', text, count=1, flags=re.MULTILINE)
    manifest.write_text(text)


def package(name):
    return f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2024"\n'


def prepare(build, args):
    archive(args.upstream, UPSTREAM_REF,
            ("benchmarks/src/pangui_template.rs", "benchmarks/pangui"), build / "upstream")
    split = build / "split"
    (split / "src").mkdir(parents=True)
    shutil.copyfile(RUNNER / "main.rs", split / "src/main.rs")
    shutil.copyfile(RUNNER / "Cargo.lock", split / "Cargo.lock")
    common = split / "common"
    (common / "src").mkdir(parents=True)
    (common / "Cargo.toml").write_text(package("harness-common"))
    shutil.copyfile(RUNNER / "common.rs", common / "src/lib.rs")
    shutil.copyfile(build / "upstream/benchmarks/src/pangui_template.rs", common / "src/pangui_template.rs")

    manifest = package("cold-layout-harness-split") + '''
[workspace]
members = ["common", "candidate", "frozen", "previous"]
resolver = "3"

[dependencies]
harness-common = { path = "common" }
'''
    for role, revision, version in (
        ("candidate", args.candidate_ref, "0.1.101"),
        ("frozen", args.owned_ref, "0.1.100"),
        ("previous", args.prior_batch_ref, "0.1.99"),
    ):
        install_solver(build / role, revision, version)
        name = f"cold-layout-driver-{role}"
        manifest += f'{role} = {{ package = "{name}", path = "{role}" }}\n'
        driver = split / role
        (driver / "src").mkdir(parents=True)
        (driver / "Cargo.toml").write_text(package(name) + f'''
[dependencies]
harness-common = {{ path = "../common" }}
keru_layout = {{ path = "../../{role}", features = ["batch-pilot"] }}
''')
        source = (RUNNER / "driver.rs").read_text()
        if role != "frozen":
            source = source.replace("pub fn dense(", "fn dense(").replace("pub fn names(", "fn names(")
        (driver / "src/lib.rs").write_text(source)
        for fixture in ("browser.rs", "cad.rs", "compositor.rs"):
            shutil.copyfile(REPO / "benches/real_workloads" / fixture, driver / "src" / fixture)
        adapters = REPO / "benchmarks/arewelayoutyet"
        shutil.copyfile(adapters / "adapter.rs", driver / "src/keru_layout_helpers.rs")
        shutil.copyfile(adapters / "owned_adapter.rs", driver / "src/owned_adapter.rs")
    (split / "Cargo.toml").write_text(manifest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("upstream", type=Path, help="arewelayoutyet checkout containing the pinned revision")
    parser.add_argument("output", type=Path, help="path for the paired samples TSV")
    parser.add_argument("--candidate-ref", help="candidate git revision, defaults to the current worktree")
    parser.add_argument("--owned-ref", default=OWNED_REF)
    parser.add_argument("--prior-batch-ref", default=PRIOR_BATCH_REF)
    parser.add_argument("--modes", default="frozen_owned,candidate_batch", help="comma-separated modes")
    parser.add_argument("--suite", choices=("all", "pangui", "real"), default="all")
    parser.add_argument("--filter", default="", help="fixture name substring")
    parser.add_argument("--blocks", type=int, default=8)
    parser.add_argument("--seed", type=int, default=135840098089)
    parser.add_argument("--cpu", type=int, help="pin the timed binary to a logical CPU with taskset")
    parser.add_argument("--offline", action="store_true", help="build using Cargo's existing registry cache")
    args = parser.parse_args()
    modes = args.modes.split(",")
    if len(set(modes)) != len(modes) or not set(modes) <= MODES:
        parser.error(f"--modes must contain distinct names from {', '.join(sorted(MODES))}")
    if "candidate_batch" not in modes or len(modes) < 2:
        parser.error("--modes needs candidate_batch and at least one reference")
    if "frozen_dense" in modes and args.suite != "pangui":
        parser.error("frozen_dense requires --suite pangui")
    if args.blocks < 1 or not 0 < args.seed < 2**64 or (args.cpu is not None and args.cpu < 0):
        parser.error("--blocks and --seed must be positive, and --cpu must be nonnegative")

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="keru-first-solve-") as temp:
        build = Path(temp)
        prepare(build, args)
        target = build / "target"
        cargo = ["cargo", "build", "--locked", "--release", "--manifest-path", build / "split/Cargo.toml",
                 "--target-dir", target]
        if args.offline:
            cargo.append("--offline")
        subprocess.run(cargo, check=True)
        run = [] if args.cpu is None else ["taskset", "-c", str(args.cpu)]
        run += [target / "release/cold-layout-harness-split", build / "upstream/benchmarks/pangui",
                str(args.blocks), args.filter, str(args.seed), args.suite]
        with args.output.open("w") as samples:
            subprocess.run(run, env={**os.environ, "COLD_LAYOUT_MODES": args.modes}, stdout=samples, check=True)

    with args.output.open() as samples:
        samples.readline()
        if not samples.readline():
            parser.error("no fixture matched --suite and --filter")
    summary = args.output.with_suffix(".summary.tsv")
    with summary.open("w") as out:
        subprocess.run([sys.executable, RUNNER / "summarize.py", args.output, "--comparisons",
                        *(mode for mode in modes if mode != "candidate_batch")], stdout=out, check=True)
    print(f"Samples {args.output}\nSummary {summary}")


if __name__ == "__main__":
    main()
