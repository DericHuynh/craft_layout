"""Verify that removing each pinned CSS declaration can change native geometry."""
import csv
import os
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory
import xml.etree.ElementTree as ET


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
GEOMETRY = ("native_rectangles", "native_tracks", "native_scroll_extents")


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def read_rows(path):
    with path.open(newline="", encoding="utf-8") as source:
        return list(csv.DictReader(source, delimiter="\t"))


def geometry(row):
    require(row["native_rectangles"], f"No native geometry for {row['fixture']}")
    return tuple(row[key] for key in GEOMETRY)


def run():
    archive = Path(os.getenv("KERU_CONFORMANCE_DIR", ROOT / "target/taffy-fixtures/tests/xml"))
    require(archive.is_dir(), "Missing pinned XML. Run benchmarks/conformance/fetch.sh.")
    witnesses = read_rows(HERE / "declaration-witnesses.tsv")
    properties = {attribute for fixture in archive.glob("*/*.xml")
                  for element in ET.parse(fixture).find("input").iter()
                  for attribute in element.attrib}
    listed = {row["declaration"] for row in witnesses}
    require(len(listed) == len(witnesses) and listed == properties,
            f"Declaration inventory differs: {sorted(listed ^ properties)} or duplicate records")

    with TemporaryDirectory(prefix="keru-declarations-") as workspace:
        fixture_root = Path(workspace)
        group = fixture_root / "declaration-witness"
        group.mkdir()
        checks = []
        for i, row in enumerate(witnesses):
            key = row["declaration"]
            source = archive / (row["fixture"] + ".xml")
            tree = ET.parse(source)
            # Preserve the original source title and basename for comparison.
            source_id = source.stem
            tree.write(group / (source_id + ".xml"), encoding="utf-8")
            opaque_id = f"input{i:02}"
            tree.getroot().set("name", opaque_id)
            tree.write(group / (opaque_id + ".xml"), encoding="utf-8")
            if key == "position":
                expected = tree.find("expectations/node")
                original = expected.attrib["x"]
                expected.set("x", str(float(original) + 4096.0))
                tree.write(group / "poisoned.xml", encoding="utf-8")
                expected.set("x", original)
                position_control = opaque_id

            touched = 0
            for node in tree.find("input").iter():
                # Keep the viewport root intact in the source-order example.
                if key == "position" and node is tree.find("input")[0]:
                    continue
                if node.attrib.pop(key, None) is not None:
                    touched += 1
            require(touched, f"{source} lacks applicable {key}")
            mutated_id = f"removed{i:02}"
            tree.write(group / (mutated_id + ".xml"), encoding="utf-8")
            checks.append((key, source_id, opaque_id, mutated_id))

        report = fixture_root / "results.tsv"
        subprocess.run(["cargo", "test", "--locked", "--test", "conformance", "--",
                        "--filter", "declaration-witness/", "--case-report", str(report)],
                       cwd=ROOT, env={**os.environ, "KERU_CONFORMANCE_DIR": str(fixture_root)}, check=True)
        rows = {row["fixture"].split("/", 1)[1]: row for row in read_rows(report)}
        for key, source, opaque, mutated in checks:
            require(rows[source]["outcome"] == rows[opaque]["outcome"] == "browser",
                    f"{key}: control failed or changed status after renaming")
            require(geometry(rows[source]) == geometry(rows[opaque]),
                    f"{key}: geometry changed after renaming")
            require(rows[mutated]["outcome"] == "mismatch" and rows[mutated]["reason"] != "panic"
                    and geometry(rows[opaque]) != geometry(rows[mutated]),
                    f"{key}: removing the declaration produced no independently measured geometry change")
        require(rows["poisoned"]["outcome"] == "mismatch" and "root:" in rows["poisoned"]["reason"]
                and geometry(rows["poisoned"]) == geometry(rows[position_control]),
                "Changing the recorded answer should change only the comparison")
        print(f"{len(checks)}/{len(properties)} declarations changed native geometry; "
              f"{len(checks)} rename controls and 1 poisoned expectation passed.")


if __name__ == "__main__":
    run()
