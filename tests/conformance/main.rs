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
//! ```
//!
//! Fixtures listed in `tests/conformance/passing.txt` must keep passing.

mod ahem;
mod css;
mod translate;

use keru_layout::{NodeId, PixelScale, Xy};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use translate::{Built, Parent, Tree};

/// Taffy's comparison tolerance for positions and sizes.
const TOLERANCE: f32 = 0.1;
/// Stands in for an unbounded max-content viewport.
const UNBOUNDED: f32 = 1.0e6;

#[derive(Debug)]
enum Outcome {
    Pass,
    Fail(String),
    Unsupported(String),
}

struct Expected {
    rect: [f32; 4],
    tracks: bool,
    children: Vec<Expected>,
}

fn expectation(node: roxmltree::Node) -> Expected {
    let number = |name: &str| node.attribute(name).and_then(|v| v.parse().ok()).unwrap_or(f32::NAN);
    Expected {
        rect: [number("x"), number("y"), number("width"), number("height")],
        tracks: node.attribute("resolved-rows").is_some() || node.attribute("resolved-columns").is_some(),
        children: node.children().filter(|c| c.is_element()).map(expectation).collect(),
    }
}

fn viewport_axis(raw: Option<&str>) -> Option<f32> {
    raw.and_then(|v| v.strip_suffix("px")).and_then(|v| v.parse().ok())
}

fn measure(_: NodeId, text: Option<&mut ahem::AhemText>, wrap: Option<f32>) -> Xy<f32> {
    let Some(text) = text else { return Xy::new(0.0, 0.0) };
    let (width, height) = text.wrap(wrap.unwrap_or(f32::INFINITY));
    Xy::new(width, height)
}

fn run(path: &Path) -> Outcome {
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
    let (Some(viewport), Some(input), Some(expectations)) = (child("viewport"), child("input"), child("expectations")) else {
        return Outcome::Fail("malformed fixture".into());
    };
    let rounding = test.attribute("use-rounding") != Some("false");
    let window = Xy::new(viewport_axis(viewport.attribute("width")), viewport_axis(viewport.attribute("height")));

    let mut tree = Tree::new();
    let root = tree.root();
    let Some(input_root) = input.first_element_child() else { return Outcome::Fail("empty input".into()) };
    let context = Parent::Viewport { definite: Xy::new(window.x.is_some(), window.y.is_some()) };
    let built = match translate::build(&mut tree, &root, input_root, context) {
        Ok(built) => built,
        Err(reason) => return Outcome::Unsupported(reason),
    };
    if rounding {
        tree.set_pixel_scale(Some(PixelScale::ONE));
    }
    let window = Xy::new(window.x.unwrap_or(UNBOUNDED), window.y.unwrap_or(UNBOUNDED));
    tree.solve_layout_with_measure(window, measure);
    if let Some(warning) = tree.warnings().first() {
        return Outcome::Fail(format!("warning: {warning}"));
    }
    let Some(expected) = expectations.first_element_child().map(expectation) else {
        return Outcome::Fail("no expectations".into());
    };
    let mut failures = Vec::new();
    compare(&tree, &built, &expected, [0.0, 0.0], "root", &mut failures);
    if failures.is_empty() { Outcome::Pass } else { Outcome::Fail(failures.join("; ")) }
}

fn compare(tree: &Tree, built: &Built, expected: &Expected, origin: [f32; 2], path: &str, failures: &mut Vec<String>) {
    let absolute = tree.layout(&built.node).map(|r| [r.x[0], r.y[0], r.x[1], r.y[1]]).unwrap_or([0.0; 4]);
    let actual = [absolute[0] - origin[0], absolute[1] - origin[1], absolute[2] - absolute[0], absolute[3] - absolute[1]];
    if actual.iter().zip(expected.rect).any(|(a, e)| !((a - e).abs() < TOLERANCE)) {
        failures.push(format!("{path}: expected {:?}, got {:?}", expected.rect, actual));
    }
    if expected.tracks {
        failures.push(format!("{path}: resolved grid tracks are not reported"));
    }
    if built.children.len() != expected.children.len() {
        failures.push(format!("{path}: child count {} != {}", built.children.len(), expected.children.len()));
        return;
    }
    for (index, (child, expected)) in built.children.iter().zip(&expected.children).enumerate() {
        compare(tree, child, expected, [absolute[0], absolute[1]], &format!("{path}.{index}"), failures);
    }
}

fn fixture_dir() -> Option<PathBuf> {
    let dir = std::env::var_os("KERU_CONFORMANCE_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("target/taffy-fixtures/tests/xml"));
    dir.is_dir().then_some(dir)
}

fn fixtures(dir: &Path) -> Vec<(String, PathBuf)> {
    let mut found = Vec::new();
    for category in std::fs::read_dir(dir).into_iter().flatten().flatten() {
        if !category.path().is_dir() {
            continue;
        }
        let name = category.file_name().to_string_lossy().into_owned();
        for file in std::fs::read_dir(category.path()).into_iter().flatten().flatten() {
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
    fail: usize,
    unsupported: usize,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let flag = |name: &str| args.iter().any(|a| a == name);
    let filter = args.iter().position(|a| a == "--filter").and_then(|i| args.get(i + 1)).cloned().unwrap_or_default();
    let verbose = flag("--verbose");
    let update = flag("--update");
    let ratchet_path = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/conformance/passing.txt");

    let Some(dir) = fixture_dir() else {
        println!("conformance: fixtures not found; run benchmarks/conformance/fetch.sh (skipping)");
        return;
    };
    let ratchet: Vec<String> = std::fs::read_to_string(&ratchet_path)
        .unwrap_or_default()
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(String::from)
        .collect();

    let mut tallies: BTreeMap<String, Tally> = BTreeMap::new();
    let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
    let mut passing = Vec::new();
    let mut regressions = Vec::new();
    for (name, path) in fixtures(&dir) {
        if !name.contains(&filter) {
            continue;
        }
        let category = name.split('/').next().unwrap().to_string();
        let tally = tallies.entry(category).or_default();
        let outcome = std::panic::catch_unwind(|| run(&path)).unwrap_or_else(|_| Outcome::Fail("panic".into()));
        match &outcome {
            Outcome::Pass => {
                tally.pass += 1;
                passing.push(name.clone());
            }
            Outcome::Fail(reason) => {
                tally.fail += 1;
                if verbose {
                    println!("FAIL {name}: {reason}");
                }
            }
            Outcome::Unsupported(reason) => {
                tally.unsupported += 1;
                let key = reason.split(['=', ' ']).next().unwrap_or(reason).to_string();
                *reasons.entry(key).or_default() += 1;
            }
        }
        if !matches!(outcome, Outcome::Pass) && ratchet.binary_search(&name).is_ok() {
            regressions.push(format!("{name}: {outcome:?}"));
        }
    }

    println!("{:<12} {:>6} {:>6} {:>12} {:>6}", "category", "pass", "fail", "unsupported", "total");
    let mut total = Tally::default();
    for (category, tally) in &tallies {
        let sum = tally.pass + tally.fail + tally.unsupported;
        println!("{category:<12} {:>6} {:>6} {:>12} {sum:>6}", tally.pass, tally.fail, tally.unsupported);
        total.pass += tally.pass;
        total.fail += tally.fail;
        total.unsupported += tally.unsupported;
    }
    println!(
        "{:<12} {:>6} {:>6} {:>12} {:>6}",
        "all", total.pass, total.fail, total.unsupported, total.pass + total.fail + total.unsupported
    );
    let mut top: Vec<_> = reasons.into_iter().collect();
    top.sort_by(|a, b| b.1.cmp(&a.1));
    println!("top unsupported: {}", top.iter().take(12).map(|(r, n)| format!("{r} ({n})")).collect::<Vec<_>>().join(", "));

    if update {
        assert!(filter.is_empty(), "--update rewrites the whole ratchet; drop --filter");
        let mut contents = String::from("# Fixtures that must keep passing. Regenerate with `cargo test --test conformance -- --update`.\n");
        for name in &passing {
            contents.push_str(name);
            contents.push('\n');
        }
        std::fs::write(&ratchet_path, contents).expect("write ratchet");
        println!("ratchet: {} fixtures", passing.len());
    } else if !regressions.is_empty() {
        for regression in regressions.iter().take(50) {
            println!("REGRESSION {regression}");
        }
        panic!("{} ratcheted fixtures no longer pass", regressions.len());
    }
}
