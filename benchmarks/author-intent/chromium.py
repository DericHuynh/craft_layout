"""Measure the original CSS recipes and alternatives in an installed Chromium."""

import argparse
import json
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

from playwright.sync_api import sync_playwright

CONFORMANCE = Path(__file__).resolve().parents[1] / "conformance"
sys.path.insert(0, str(CONFORMANCE))
from compare_workaround_browser import MEASURE, styles


def fixture(name):
    return ET.parse(CONFORMANCE / "workarounds" / f"{name}.xml").find("input")[0]


def toolbar(auto):
    row = ET.Element("div", {
        "display": "flex", "flex-wrap": "wrap", "gap": "4px 6px",
        "align-content": "start",
    })
    for width in [34, 34, 20]:
        action = ET.SubElement(row, "div", {
            "width": f"{width}px", "height": "10px", "flex": "none",
        })
    if auto:
        action.set("margin-left", "auto")
    return row


def measure(page, node, axis, sizes, read):
    samples = []
    for size in [*sizes, sizes[0]]:
        node.set(axis, f"{size}px")
        rects = page.evaluate(MEASURE, styles(node))
        samples.append(read(rects))
    assert samples[-1] == samples[0], samples
    return dict(zip(sizes, samples[:-1], strict=True))


def run(page):
    page.set_content("<!doctype html><style>body{margin:0}::-webkit-scrollbar{width:0;height:0}</style>")
    page.set_viewport_size({"width": 400, "height": 400})
    output = {}
    for case in ["auto_minimum", "zero_minimum"]:
        title = fixture(f"flex_toolbar_{case}")
        output[f"title/{case}"] = measure(
            page, title, "width", [224, 144],
            lambda r: {"slot": r["root.0"][2], "actionX": r["root.1"][0], "title": r["root.0.0"][2]},
        )
        panel = fixture(f"flex_scroller_{case}")
        output[f"list/{case}"] = measure(
            page, panel, "height", [160, 112],
            lambda r: {"wrapper": r["root.1"][3], "list": r["root.1.0"][3],
                       "maxOffset": page.locator("body > div > div:nth-child(2) > div").evaluate(
                           "n => {n.scrollTop = n.scrollHeight; return n.scrollTop;}")},
        )
    for case in ["outer_padding", "inner_padding", "grid"]:
        cards = fixture(f"flex_cards_{'outer_padding' if case == 'grid' else case}")
        if case == "grid":
            cards.set("display", "grid")
            cards.set("grid-template-columns", "repeat(3, 1fr)")
        output[f"cards/{case}"] = measure(
            page, cards, "width", [300, 240],
            lambda r: {"cards": [r[f"root.{i}"][2] for i in range(3)]},
        )
    for auto in [False, True]:
        output[f"wrap/{'auto' if auto else 'start'}"] = measure(
            page, toolbar(auto), "width", [106, 100, 99], lambda r: {"action": r["root.2"][:2]},
        )
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--browser", help="Path to a Chromium executable")
    args = parser.parse_args()
    with sync_playwright() as playwright:
        with playwright.chromium.launch(executable_path=args.browser) as browser:
            print(json.dumps({"Chromium": browser.version, "samples": run(browser.new_page())}, indent=2))
