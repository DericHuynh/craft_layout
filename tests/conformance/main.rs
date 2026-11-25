//! Scores keru_layout against the browser-generated layout fixtures from Taffy.
//!
//! Each fixture holds a CSS tree and the rectangles Chrome computed for it.
//! Fetch the fixtures with `benchmarks/conformance/fetch.sh`, then run:
//!
//! ```sh
//! cargo test --test conformance                     # scoreboard + ratchet check
//! cargo test --test conformance -- --filter flex/   # restrict by category or name
//! cargo test --test conformance -- --verbose        # print every failure
//! cargo test --test conformance -- --update         # rewrite the ratchet
//! cargo test --test conformance -- --case-report cases.tsv
//! cargo test --test conformance -- --workarounds    # local CSS authoring probes only
//! ```
//!
//! Fixtures in `passing.txt` must match Chrome. Cases in
//! `native_expectations.xml` must also satisfy their native sizing contract.

mod ahem;
mod css;
mod translate;

use keru_layout::{Axis, LayoutWarning, NodeId, PixelScale, TreeError, Xy};
use std::collections::{BTreeMap, BTreeSet};
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use translate::{Built, Parent, Tree};

/// Taffy's comparison tolerance for positions and sizes.
const TOLERANCE: f32 = 0.1;
/// Stands in for an unbounded max-content viewport.
const UNBOUNDED: f32 = 1.0e6;

#[derive(Debug)]
enum Outcome {
    Pass,
    NativeMatch,
    Fail(String),
    Unsupported(String),
}

struct Expected {
    rect: [f32; 4],
    columns: Option<String>,
    rows: Option<String>,
    inline_axis: Axis,
    scroll: Xy<Option<f32>>,
    children: Vec<Expected>,
}

fn expectation(node: roxmltree::Node) -> Expected {
    let number = |name: &str| {
        node.attribute(name)
            .and_then(|v| v.parse().ok())
            .unwrap_or(f32::NAN)
    };
    Expected {
        rect: [number("x"), number("y"), number("width"), number("height")],
        columns: node.attribute("resolved-columns").map(str::to_owned),
        rows: node.attribute("resolved-rows").map(str::to_owned),
        inline_axis: Axis::X,
        scroll: Xy::new(
            node.attribute("scroll_width").and_then(|v| v.parse().ok()),
            node.attribute("scroll_height").and_then(|v| v.parse().ok()),
        ),
        children: node
            .children()
            .filter(|c| c.is_element())
            .map(expectation)
            .collect(),
    }
}

// A fixture can opt into this transformation only when its physical inputs
// are symmetric. Absolute physical insets and asymmetric margins have their
// own independently specified RTL rectangles.
fn reflect_children(parent: &mut Expected) {
    for child in &mut parent.children {
        child.rect[0] = parent.rect[2] - child.rect[0] - child.rect[2];
        reflect_children(child);
    }
}

struct NativeCase<'a> {
    reason: &'a str,
    expected: Expected,
    warnings: Vec<String>,
}

fn native_cases<'a>(document: &'a roxmltree::Document) -> BTreeMap<&'a str, NativeCase<'a>> {
    let mut cases = BTreeMap::new();
    for case in document
        .root_element()
        .children()
        .filter(|node| node.is_element())
    {
        let root = case
            .children()
            .find(|n| n.has_tag_name("node"))
            .expect("native rectangle tree");
        let mut warnings: Vec<_> = case
            .children()
            .filter(|n| n.has_tag_name("warning"))
            .map(|n| {
                let path = n.attribute("path").expect("warning path");
                let kind = n.attribute("kind").expect("warning kind");
                format!(
                    "{kind}@{path}{}",
                    n.attribute("axis")
                        .map(|axis| format!(".{axis}"))
                        .unwrap_or_default()
                )
            })
            .collect();
        warnings.sort();
        let reason = case.attribute("reason").expect("native sizing rule");
        for (names, reflect) in [
            (case.attribute("fixtures").expect("fixture names"), false),
            (
                case.attribute("mirrored-fixtures").unwrap_or_default(),
                true,
            ),
        ] {
            for name in names.split_whitespace() {
                let mut expected = expectation(root);
                if reflect {
                    reflect_children(&mut expected);
                }
                let previous = cases.insert(
                    name,
                    NativeCase {
                        reason,
                        expected,
                        warnings: warnings.clone(),
                    },
                );
                assert!(
                    previous.is_none(),
                    "duplicate native expectation for {name}"
                );
            }
        }
    }
    cases
}

// The fixture generator measures out-of-flow positions from their CSS containing
// block. Convert those reference coordinates to the parent-local frame used here.
fn browser_positions(
    expected: &mut Expected,
    input: roxmltree::Node,
    parent: [f32; 2],
    containing: [f32; 2],
    viewport: Option<[f32; 2]>,
    inherited_inline: Axis,
) {
    expected.inline_axis = match input.attribute("writing-mode") {
        Some("vertical-rl" | "vertical-lr") => Axis::Y,
        Some("horizontal-tb") => Axis::X,
        _ => inherited_inline,
    };
    // The XML serializer omits the computed value "static".
    let position = input.attribute("position").unwrap_or("static");
    let reference = match (viewport, position) {
        (Some(_), "absolute") => containing,
        (Some(viewport), "fixed") => viewport,
        _ => parent,
    };
    let absolute = [
        reference[0] + expected.rect[0],
        reference[1] + expected.rect[1],
    ];
    if reference != parent {
        expected.rect[0] = absolute[0] - parent[0];
        expected.rect[1] = absolute[1] - parent[1];
    }
    let has_containing_box = viewport.is_none()
        || position != "static"
        || matches!(
            input.attribute("contain"),
            Some("layout" | "paint" | "content" | "strict")
        );
    let next = if has_containing_box {
        absolute
    } else {
        containing
    };
    for (node, child) in input
        .children()
        .filter(|n| n.is_element())
        .zip(&mut expected.children)
    {
        browser_positions(
            child,
            node,
            absolute,
            next,
            Some(viewport.unwrap_or(absolute)),
            expected.inline_axis,
        );
    }
}

fn viewport_axis(raw: Option<&str>) -> Option<f32> {
    raw.and_then(|v| v.strip_suffix("px"))
        .and_then(|v| v.parse().ok())
}

fn measure(_: NodeId, text: Option<&mut ahem::AhemText>, wrap: Option<f32>) -> Xy<f32> {
    let Some(text) = text else {
        return Xy::new(0.0, 0.0);
    };
    let (width, height) = text.wrap(wrap.unwrap_or(f32::INFINITY));
    Xy::new(width, height)
}

fn node_path(node: &NodeId, built: &Built) -> Option<String> {
    if node == &built.node {
        return Some("root".into());
    }
    for (i, child) in built.children.iter().enumerate() {
        if let Some(path) = node_path(node, child) {
            return Some(format!("root.{i}{}", &path["root".len()..]));
        }
    }
    None
}

fn diagnostic(warning: &LayoutWarning<NodeId>, built: &Built) -> String {
    use LayoutWarning::*;
    let (kind, node, axis) = match warning {
        Cycle { node, axis } => ("Cycle", node, Some(axis)),
        AspectRatioOnBothAxes { node } => ("AspectRatioOnBothAxes", node, None),
        FitContentCollapsed { node, axis } => ("FitContentCollapsed", node, Some(axis)),
        MinAboveMax { node, axis } => ("MinAboveMax", node, Some(axis)),
        ImpossibleFracChildren { node, axis } => ("ImpossibleFracChildren", node, Some(axis)),
        NotFinite { node, axis } => ("NotFinite", node, Some(axis)),
        other => return format!("{other}"),
    };
    let path = node_path(node, built).unwrap_or_else(|| "viewport".to_owned());
    let axis = match axis {
        Some(Axis::X) => ".x",
        Some(Axis::Y) => ".y",
        None => "",
    };
    format!("{kind}@{path}{axis}")
}

fn rule_diagnostic(issue: &keru_layout::layout_rules::RuleIssue, built: &Built) -> String {
    use keru_layout::layout_rules::RuleIssue::*;
    let (kind, node, axis) = match issue {
        MissingReference(node) => ("MissingReference", node, None),
        CyclicReference(node) => ("CyclicReference", node, None),
        MissingContainer(node) => ("MissingContainer", node, None),
        ConflictingFormattingContexts(node) => ("ConflictingFormattingContexts", node, None),
        MissingParentTracks(node, axis) => ("MissingParentTracks", node, Some(axis)),
        UnstableLayout => return "UnstableLayout".into(),
    };
    let path = node_path(node, built).unwrap_or_else(|| "viewport".to_owned());
    let suffix = match axis {
        Some(Axis::X) => ".x",
        Some(Axis::Y) => ".y",
        None => "",
    };
    format!("{kind}@{path}{suffix}")
}

#[derive(Default)]
struct Details {
    compared: bool,
    scroll: Vec<String>,
    rectangles: Vec<String>,
    tracks: Vec<String>,
    warnings: Vec<String>,
}

fn run(path: &Path, native: Option<&NativeCase>, details: &mut Details, capture: bool) -> Outcome {
    let raw = match std::fs::read_to_string(path) {
        Ok(raw) => raw,
        Err(error) => return Outcome::Fail(error.to_string()),
    };
    let document = match roxmltree::Document::parse(&raw) {
        Ok(document) => document,
        Err(error) => return Outcome::Fail(error.to_string()),
    };
    let test = document.root_element();
    let child = |tag: &str| test.children().find(|n| n.has_tag_name(tag));
    let (Some(viewport), Some(input), Some(expectations)) =
        (child("viewport"), child("input"), child("expectations"))
    else {
        return Outcome::Fail("malformed fixture".into());
    };
    let rounding = test.attribute("use-rounding") != Some("false");
    let window = Xy::new(
        viewport_axis(viewport.attribute("width")),
        viewport_axis(viewport.attribute("height")),
    );

    let mut tree = Tree::new();
    let root = tree.root();
    let Some(input_root) = input.first_element_child() else {
        return Outcome::Fail("empty input".into());
    };
    let context = Parent::Viewport { size: window };
    let built = match translate::build(&mut tree, &root, input_root, context) {
        Ok(built) => built,
        Err(reason) => return Outcome::Unsupported(reason),
    };
    if rounding {
        tree.set_pixel_scale(Some(PixelScale::ONE));
    }
    let window = Xy::new(window.x.unwrap_or(UNBOUNDED), window.y.unwrap_or(UNBOUNDED));
    tree.solve_layout_with_measurers(window, measure, |_, text, input| {
        let Some(text) = text else {
            return Xy::new_symm(0.);
        };
        // Vertical Ahem lines wrap against physical height and accumulate width.
        let inline = input
            .known_dimensions
            .y
            .or(input.max_size.y)
            .unwrap_or(f32::INFINITY);
        let (height, width) = text.wrap(inline);
        Xy::new(width, height)
    });
    details.warnings = tree
        .warnings()
        .iter()
        .map(|w| diagnostic(w, &built))
        .collect();
    details.warnings.extend(
        tree.rule_issues()
            .iter()
            .map(|i| rule_diagnostic(i, &built)),
    );
    details.warnings.sort();
    let Some(mut expected) = expectations.first_element_child().map(expectation) else {
        return Outcome::Fail("no expectations".into());
    };
    browser_positions(&mut expected, input_root, [0.0; 2], [0.0; 2], None, Axis::X);
    let mut failures = Vec::new();
    compare(
        rounding,
        &tree,
        &built,
        &expected,
        &expected,
        Some([0.0, 0.0]),
        "root",
        &mut failures,
        &mut capture.then_some(&mut *details),
    );
    details.compared = true;
    let expected_warnings = native
        .map(|case| case.warnings.as_slice())
        .unwrap_or_default();
    if details.warnings != expected_warnings {
        failures.push(format!(
            "expected warnings {expected_warnings:?}, got {:?}",
            details.warnings
        ));
        return Outcome::Fail(failures.join("; "));
    }
    if let Some(native) = native {
        let mut native_failures = Vec::new();
        compare(
            rounding,
            &tree,
            &built,
            &native.expected,
            &expected,
            Some([0.0, 0.0]),
            "root",
            &mut native_failures,
            &mut None,
        );
        if !native_failures.is_empty() {
            return Outcome::Fail(format!("{} {}", native.reason, native_failures.join("; ")));
        }
        if !failures.is_empty() {
            return Outcome::NativeMatch;
        }
    }
    if failures.is_empty() {
        Outcome::Pass
    } else {
        Outcome::Fail(failures.join("; "))
    }
}

// Chrome serializes used CSS track sizes (without gutters or pixel snapping)
// in logical track order. "none" is an assertion of zero tracks. An omitted
// attribute opts out of that axis. Names belong to boundaries between tracks.
fn track_sizes_match(
    expected: &str,
    actual: &[f32],
    names: Option<&keru_layout::tracks::LineNames>,
) -> bool {
    let mut rest = expected.trim();
    if rest == "none" || rest.is_empty() {
        return actual.is_empty() && names.is_none();
    }
    for i in 0..=actual.len() {
        let labels = names
            .and_then(|m| m.get(&i))
            .map(Vec::as_slice)
            .unwrap_or(&[]);
        if let Some(after) = rest.strip_prefix('[') {
            let Some((group, tail)) = after.split_once(']') else {
                return false;
            };
            if !group
                .split_whitespace()
                .eq(labels.iter().map(String::as_str))
            {
                return false;
            }
            rest = tail.trim_start();
        } else if !labels.is_empty() {
            return false;
        }
        if let Some(&size) = actual.get(i) {
            let Some((num, tail)) = rest.split_once("px") else {
                return false;
            };
            if !num
                .parse::<f32>()
                .is_ok_and(|v| (size - v).abs() < TOLERANCE)
            {
                return false;
            }
            rest = tail.trim_start();
        }
    }
    rest.is_empty()
}

// Very large grids can publish tens of thousands of identical lengths.
// Compress only the human-readable trace. Comparison always sees every track.
fn describe_tracks(sizes: &[f32]) -> String {
    if sizes.len() < 32 {
        return format!("{sizes:?}");
    }
    use std::fmt::Write;
    let mut description = String::from("[");
    for run in sizes.chunk_by(|a, b| a.to_bits() == b.to_bits()) {
        if description.len() > 1 {
            description.push_str(", ");
        }
        if run.len() >= 4 {
            write!(description, "{:?} × {}", run[0], run.len()).unwrap();
        } else {
            for (i, value) in run.iter().enumerate() {
                if i > 0 {
                    description.push_str(", ");
                }
                write!(description, "{value:?}").unwrap();
            }
        }
    }
    description.push(']');
    description
}

fn compare(
    rounding: bool,
    tree: &Tree,
    built: &Built,
    expected: &Expected,
    browser: &Expected,
    origin: Option<[f32; 2]>,
    path: &str,
    failures: &mut Vec<String>,
    details: &mut Option<&mut Details>,
) {
    // A hidden subtree has zero boxes in the fixture and no published rectangles.
    let (actual, child_origin) = match (
        origin.filter(|_| !built.disabled),
        tree.view_geometry(&built.node).map(|view| {
            for a in [Axis::X, Axis::Y] {
                if let Some(wanted) = expected.scroll[a].or(browser.scroll[a]) {
                    let range = view.scroll_range[a];
                    let actual = range[1] - range[0];
                    if let Some(details) = details.as_deref_mut() {
                        details.scroll.push(format!("{path}.{a:?} {actual}"));
                    }
                    if !((actual - wanted).abs() < TOLERANCE) {
                        failures.push(format!(
                            "{path}: expected scroll {a:?} {wanted}, got {actual}"
                        ));
                    }
                }
            }
            let mut rect = view.rect;
            if rounding {
                for a in [Axis::X, Axis::Y] {
                    rect[a] = rect[a].map(f32::round);
                }
            }
            rect
        }),
    ) {
        (Some([x, y]), Ok(rect)) => (
            [
                rect.x[0] - x,
                rect.y[0] - y,
                rect.x[1] - rect.x[0],
                rect.y[1] - rect.y[0],
            ],
            Some([rect.x[0], rect.y[0]]),
        ),
        (None, Err(TreeError::LayoutUnavailable)) => ([0.0; 4], None),
        (None, Ok(_)) => {
            failures.push(format!("{path}: hidden node published a rectangle"));
            return;
        }
        (_, Err(error)) => {
            failures.push(format!("{path}: {error}"));
            return;
        }
    };
    if let Some(details) = details {
        details.rectangles.push(format!("{path} {:?}", actual));
    }
    if actual
        .iter()
        .zip(expected.rect)
        .any(|(a, e)| !((a - e).abs() < TOLERANCE))
    {
        failures.push(format!(
            "{path}: expected {:?}, got {:?}",
            expected.rect, actual
        ));
    }
    // A deliberate native rectangle difference does not waive a track
    // assertion. It takes an explicit native track list to override one.
    for (axis, label, wanted) in [
        (
            browser.inline_axis,
            "columns",
            expected.columns.as_deref().or(browser.columns.as_deref()),
        ),
        (
            browser.inline_axis.other(),
            "rows",
            expected.rows.as_deref().or(browser.rows.as_deref()),
        ),
    ] {
        if wanted.is_none() && details.is_none() {
            continue;
        }
        match tree.resolved_grid_tracks(&built.node, axis) {
            Ok(Some(edges)) => {
                let sizes: Vec<f32> = edges.iter().map(|[low, high]| high - low).collect();
                let names = tree
                    .resolved_grid_line_names(&built.node, axis)
                    .ok()
                    .flatten();
                let describe = || {
                    let sizes = describe_tracks(&sizes);
                    names.map_or_else(|| sizes.clone(), |n| format!("{sizes} lines {n:?}"))
                };
                if let Some(details) = details {
                    details
                        .tracks
                        .push(format!("{path}.{label} {}", describe()));
                }
                if let Some(expected) = wanted
                    && !track_sizes_match(expected, &sizes, names)
                {
                    failures.push(format!(
                        "{path}: expected {label} {expected:?}, got {}",
                        describe()
                    ));
                }
            }
            _ if wanted.is_some() => failures.push(format!("{path}: no published grid {label}")),
            _ => {}
        }
    }
    if built.children.len() != expected.children.len()
        || built.children.len() != browser.children.len()
    {
        failures.push(format!(
            "{path}: child count {} != {}",
            built.children.len(),
            expected.children.len()
        ));
        return;
    }
    for (index, child) in built.children.iter().enumerate() {
        compare(
            rounding,
            tree,
            child,
            &expected.children[index],
            &browser.children[index],
            child_origin,
            &format!("{path}.{index}"),
            failures,
            details,
        );
    }
}

fn fixture_dir() -> Option<PathBuf> {
    let dir = std::env::var_os("KERU_CONFORMANCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("target/taffy-fixtures/tests/xml")
        });
    dir.is_dir().then_some(dir)
}

fn fixtures(dir: &Path) -> Vec<(String, PathBuf)> {
    let mut found = Vec::new();
    for category in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        if !category.path().is_dir() {
            continue;
        }
        let name = category.file_name().to_string_lossy().into_owned();
        for file in std::fs::read_dir(category.path())
            .into_iter()
            .flatten()
            .flatten()
        {
            let path = file.path();
            if path.extension().is_some_and(|e| e == "xml") {
                let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
                found.push((format!("{name}/{stem}"), path));
            }
        }
    }
    found.sort();
    found
}

#[derive(Default)]
struct Tally {
    pass: usize,
    native: usize,
    fail: usize,
    unsupported: usize,
}

impl Tally {
    fn print(&self, name: &str) {
        let total = self.pass + self.native + self.fail + self.unsupported;
        println!(
            "{name:<12} {:>6} {:>6} {:>6} {:>12} {total:>6}",
            self.pass, self.native, self.fail, self.unsupported
        );
    }
}

// These local probes assert the documented Craft result. Some intentionally
// differ from the measured browser geometry. Keep them outside the Taffy tally.
fn check_workarounds() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmarks/conformance/workarounds");
    let mut paths: Vec<_> = std::fs::read_dir(dir)
        .expect("CSS workaround fixtures")
        .map(|entry| entry.expect("workaround fixture entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "xml"))
        .collect();
    paths.sort();
    assert!(!paths.is_empty(), "no CSS workaround fixtures found");
    for path in &paths {
        let result = run(path, None, &mut Details::default(), false);
        assert!(
            matches!(result, Outcome::Pass),
            "{}: {result:?}",
            path.display()
        );
    }
    println!("CSS workaround fixtures: {} verified", paths.len());
}

fn main() {
    check_workarounds();
    translate::check_sibling_composition();
    let args: Vec<String> = std::env::args().collect();
    let flag = |name: &str| args.iter().any(|a| a == name);
    if flag("--workarounds") {
        return;
    }
    let filter = args
        .iter()
        .position(|a| a == "--filter")
        .and_then(|i| args.get(i + 1))
        .cloned()
        .unwrap_or_default();
    let verbose = flag("--verbose");
    let update = flag("--update");
    let ratchet_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/conformance/passing.txt");

    let resolved = flag("--require-resolved");
    let required = flag("--require-translated") || resolved;
    let Some(dir) = fixture_dir() else {
        assert!(
            !required,
            "required pinned fixtures missing; run benchmarks/conformance/fetch.sh"
        );
        println!("conformance: fixtures not found; run benchmarks/conformance/fetch.sh (skipping)");
        return;
    };
    let strict = required || std::env::var_os("KERU_CONFORMANCE_DIR").is_none();
    let ratchet: BTreeSet<String> = std::fs::read_to_string(&ratchet_path)
        .expect("read browser ratchet")
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(String::from)
        .collect();
    let native_document = roxmltree::Document::parse(include_str!("native_expectations.xml"))
        .expect("parse native expectations");
    let native_cases = native_cases(&native_document);

    let mut tallies: BTreeMap<String, Tally> = BTreeMap::new();
    let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
    let mut report = args.iter().position(|arg| arg == "--case-report").map(|i| {
        let path = args.get(i + 1).expect("--case-report needs a TSV path");
        let mut out = BufWriter::new(std::fs::File::create(path).expect("create case report"));
        writeln!(out, "fixture\toutcome\treason\twarnings\tnative_rectangles\tnative_tracks\tnative_scroll_extents").expect("write case report");
        out
    });
    let mut incomplete = Vec::new();
    let mut pinned: BTreeSet<String> = if strict {
        std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("reports/constraint-semantics/current-cases.tsv"),
        )
        .expect("read pinned fixture inventory")
        .lines()
        .skip(1)
        .map(|line| line.split_once('\t').expect("case TSV").0.to_owned())
        .filter(|id| id.contains(&filter))
        .collect()
    } else {
        BTreeSet::new()
    };
    if strict && filter.is_empty() {
        assert_eq!(pinned.len(), 6604, "pinned fixture inventory changed");
    }
    let mut passing = Vec::new();
    let mut regressions = Vec::new();
    let mut required_cases: BTreeSet<&str> = ratchet
        .iter()
        .map(String::as_str)
        .chain(native_cases.keys().copied())
        .filter(|name| name.contains(&filter))
        .collect();
    for (name, path) in fixtures(&dir) {
        if !name.contains(&filter) {
            continue;
        }
        let category = name.split('/').next().unwrap().to_string();
        let tally = tallies.entry(category).or_default();
        required_cases.remove(name.as_str());
        let native = native_cases.get(name.as_str());
        let mut details = Details::default();
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run(&path, native, &mut details, report.is_some())
        }))
        .unwrap_or_else(|_| Outcome::Fail("panic".into()));
        if strict && (!pinned.remove(&name) || !details.compared) {
            incomplete.push(format!("{name}: {outcome:?}"));
        }
        if let Some(out) = &mut report {
            let (status, reason) = match &outcome {
                Outcome::Pass => ("browser", native.map(|c| c.reason).unwrap_or("")),
                Outcome::NativeMatch => ("native", native.unwrap().reason),
                Outcome::Fail(why) => ("mismatch", why.as_str()),
                Outcome::Unsupported(why) => ("unsupported", why.as_str()),
            };
            writeln!(
                out,
                "{name}\t{status}\t{}\t{}\t{}\t{}\t{}",
                reason.replace(['\t', '\n', '\r'], " "),
                details.warnings.join("; "),
                details.rectangles.join("; "),
                details.tracks.join("; "),
                details.scroll.join("; ")
            )
            .expect("write case report");
        }
        match &outcome {
            Outcome::Pass => {
                tally.pass += 1;
                passing.push(name.clone());
            }
            Outcome::NativeMatch => {
                tally.native += 1;
                if verbose {
                    println!("NATIVE {name}: {}", native.unwrap().reason);
                }
            }
            Outcome::Fail(reason) => {
                tally.fail += 1;
                if verbose {
                    println!("FAIL {name}: {reason}");
                }
            }
            Outcome::Unsupported(reason) => {
                tally.unsupported += 1;
                let key = reason
                    .split(['=', ' '])
                    .next()
                    .unwrap_or(reason)
                    .to_string();
                *reasons.entry(key).or_default() += 1;
            }
        }
        let lost_browser_match = ratchet.contains(&name) && !matches!(outcome, Outcome::Pass);
        let lost_native_match =
            native.is_some() && !matches!(outcome, Outcome::Pass | Outcome::NativeMatch);
        if lost_browser_match || lost_native_match {
            regressions.push(format!("{name}: {outcome:?}"));
        }
    }
    if let Some(out) = &mut report {
        out.flush().expect("flush case report");
    }
    regressions.extend(
        required_cases
            .into_iter()
            .map(|name| format!("{name}: fixture missing")),
    );

    println!(
        "{:<12} {:>6} {:>6} {:>6} {:>12} {:>6}",
        "category", "pass", "native", "fail", "unsupported", "total"
    );
    let mut total = Tally::default();
    for (category, tally) in &tallies {
        tally.print(category);
        total.pass += tally.pass;
        total.native += tally.native;
        total.fail += tally.fail;
        total.unsupported += tally.unsupported;
    }
    total.print("all");
    if strict {
        assert!(
            pinned.is_empty(),
            "missing {} pinned fixtures, first {:?}",
            pinned.len(),
            pinned.first()
        );
        assert!(
            incomplete.is_empty(),
            "{} fixtures did not complete translation and native comparison, first {:?}",
            incomplete.len(),
            incomplete.first()
        );
    }
    let mut top: Vec<_> = reasons.into_iter().collect();
    top.sort_by(|a, b| b.1.cmp(&a.1));
    println!(
        "top unsupported: {}",
        top.iter()
            .take(12)
            .map(|(r, n)| format!("{r} ({n})"))
            .collect::<Vec<_>>()
            .join(", ")
    );

    if (resolved || (strict && !required)) && total.fail > 0 {
        regressions.push(format!(
            "{} translated fixtures lack a verified resolution",
            total.fail
        ));
    }
    if !regressions.is_empty() {
        for regression in regressions.iter().take(50) {
            println!("REGRESSION {regression}");
        }
        panic!("{} fixture expectations regressed", regressions.len());
    }
    if update {
        assert!(
            filter.is_empty(),
            "--update rewrites the whole ratchet; drop --filter"
        );
        let mut contents = String::from(
            "# Fixtures that must keep passing. Regenerate with `cargo test --test conformance -- --update`.\n",
        );
        for name in &passing {
            contents.push_str(name);
            contents.push('\n');
        }
        std::fs::write(&ratchet_path, contents).expect("write ratchet");
        println!("ratchet: {} fixtures", passing.len());
    }
}
