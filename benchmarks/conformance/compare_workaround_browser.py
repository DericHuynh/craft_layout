"""Compare the local workaround fixtures' parent-relative rectangles with a browser.

Requires the Playwright Python package. Pass --browser to use an installed
Chromium executable, or use Playwright's installed Chromium by default.
A nonzero exit status means at least one fixture differs from Craft's contract.
"""

import argparse
import xml.etree.ElementTree as ET
from pathlib import Path

from playwright.sync_api import sync_playwright


def styles(node):
    return [node.tag, node.attrib, [styles(child) for child in node]]


def expected(node, path="root"):
    yield path, [float(node.attrib[k]) for k in ("x", "y", "width", "height")]
    for i, child in enumerate(node):
        yield from expected(child, f"{path}.{i}")


MEASURE = """tree => {
    function build([tag, css, children]) {
        const node = document.createElement(tag);
        for (const [key, value] of Object.entries(css)) node.style.setProperty(key, value);
        node.append(...children.map(build));
        return node;
    }
    const root = build(tree);
    document.body.replaceChildren(root);
    const boxes = {};
    function visit(node, path, x, y) {
        const r = node.getBoundingClientRect();
        boxes[path] = [r.left - x, r.top - y, r.width, r.height];
        Array.from(node.children).forEach((child, i) => visit(child, path + '.' + i, r.left, r.top));
    }
    visit(root, 'root', 0, 0);
    return boxes;
}"""


def run(browser, directory, pattern):
    # A zero-width gutter matches the box geometry in the XML importer.
    page = browser.new_page()
    page.set_content(
        "<!doctype html><style>body{margin:0}::-webkit-scrollbar{width:0;height:0}</style>"
    )
    files = sorted(directory.glob(pattern))
    if not files:
        raise ValueError(f"No XML fixtures in {directory}")
    differences = 0
    rectangles = 0
    for file in files:
        fixture = ET.parse(file).getroot()
        viewport = fixture.find("viewport")
        page.set_viewport_size({
            axis: int(viewport.attrib[axis].removesuffix("px")) for axis in ("width", "height")
        })
        boxes = page.evaluate(MEASURE, styles(fixture.find("input")[0]))
        rectangles += len(boxes)
        errors = []
        for path, want in expected(fixture.find("expectations")[0]):
            actual = boxes.pop(path, None)
            if actual is None or any(abs(a - b) >= 0.1 for a, b in zip(actual, want)):
                errors.append(f"  {path}  Craft {want}  browser {actual}")
        errors.extend(f"  unexpected browser node {path}" for path in boxes)
        if errors:
            differences += 1
            print(file.stem, *errors, sep="\n")
    print(f"Chromium {browser.version}: {len(files) - differences}/{len(files)} rectangle trees match ({rectangles} boxes)")
    return differences


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--browser", help="Path to a Chromium executable")
    parser.add_argument("--pattern", default="*.xml", help="Fixture file glob")
    args = parser.parse_args()
    with sync_playwright() as playwright:
        with playwright.chromium.launch(executable_path=args.browser) as browser:
            if run(browser, Path(__file__).with_name("workarounds"), args.pattern):
                raise SystemExit(1)
