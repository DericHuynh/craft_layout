use super::*;
use std::collections::BTreeSet;

pub(super) struct Frame {
    pub rects: Rects,
    pub outcome: IncrementalRelayoutOutcome,
    pub warnings: Vec<String>,
    pub fresh_outcome: IncrementalRelayoutOutcome,
    pub fresh_warnings: Vec<String>,
}

impl Frame {
    pub fn run(app: &mut App, view: &View, s: Session, frame: &str) -> Result<Self, TreeError> {
        app.update(view)?;
        let outcome = app.solve(s);
        let rects = app.rects()?;
        let warnings = app.warning_names();
        let mut fresh = App::default();
        fresh.update(view)?;
        let fresh_outcome = fresh.solve(s);
        let fresh_warnings = fresh.warning_names();
        assert_eq!(rects, fresh.rects()?, "{frame}: retained versus fresh");
        assert!(warnings.is_empty() && fresh_warnings.is_empty(),
            "{frame}: warm {warnings:?}, fresh {fresh_warnings:?}");
        Ok(Self { rects, outcome, warnings, fresh_outcome, fresh_warnings })
    }

    pub fn trace(&self, changes: &[String]) {
        println!("  warnings={:?}, fresh={:?}, fresh warnings={:?}", self.warnings, self.fresh_outcome, self.fresh_warnings);
        for key in changes {
            match self.rects.get(key) {
                Some(Some(r)) => println!("    {key:<24} x={:?} y={:?}", r.x, r.y),
                Some(None) => println!("    {key:<24} hidden"),
                None => println!("    {key:<24} removed"),
            }
        }
    }
}

pub(super) fn changes(old: &Rects, new: &Rects) -> Vec<String> {
    let keys: BTreeSet<_> = old.keys().chain(new.keys()).collect();
    keys.into_iter().filter(|key| old.get(*key) != new.get(*key)).cloned().collect()
}

// Corresponds to the design recorded before the first run. Use literal expected
// edges so the checks are independent of the code that divides available space.
pub(super) fn oracle(frame: &str, r: &Rects) {
    let (w, h, work_x, left_x, right_x, footer) = match frame {
        "desktop" | "idle" | "type-and-check" | "rename-and-open" =>
            (1284., 800., [248., 1060.], [248., 734.], Some([736., 1060.]), 632.),
        "laptop" => (960., 660., [248., 960.], [248., 674.], Some([676., 960.]), 492.),
        "compact" => (700., 580., [48., 700.], [48., 700.], None, 412.),
        "drag-terminal" => (700., 580., [48., 700.], [48., 700.], None, 364.),
        "restore" | "close-tab" =>
            (1284., 800., [248., 1060.], [248., 734.], Some([736., 1060.]), 584.),
        _ => unreachable!(),
    };
    let expect = |k: &str, x, y| assert_eq!(r[k], Some(Xy::new(x, y)), "{frame} {k}");
    expect("title", [0., w], [0., 40.]);
    expect("rail", [0., 48.], [40., h-24.]);
    expect("status", [0., w], [h-24., h]);
    expect("work", work_x, [40., h-24.]);
    expect("left", left_x, [96., footer]);
    expect("terminal", work_x, [footer, h-24.]);
    if let Some(rx) = right_x {
        expect("explorer", [48., 248.], [40., h-24.]);
        expect("right", rx, [96., footer]);
        expect("divider", [left_x[1], rx[0]], [96., footer]);
    } else {
        for k in ["explorer", "right", "divider", "right-row-1-code"] { assert_eq!(r[k], None, "{frame} {k}"); }
    }
    if w == 1284. { expect("inspector", [1060., 1284.], [40., h-24.]); }
    else { assert_eq!(r["inspector"], None); }
    let first_h = if matches!(frame, "desktop" | "idle") { 16. } else { 32. };
    let code = [left_x[0] + 40., left_x[1]];
    expect("left-row-1-code", code, [96., 96.+first_h]);
    expect("left-row-2-code", code, [96.+first_h, 112.+first_h]);
    let renamed = !matches!(frame, "desktop" | "idle" | "type-and-check");
    let tab_x = work_x[0] + if renamed { 104. } else { 80. };
    expect("tab-parse", [tab_x, tab_x+96.], [40., 72.]);
    if renamed && frame != "close-tab" {
        expect("tab-lexer", [tab_x+96., tab_x+184.], [40., 72.]);
    } else {
        assert!(!r.contains_key("tab-lexer"), "{frame}: lexer closed");
    }
}

// Counterfactual. Apply this after producing the exact same content, ordering,
// breakpoints and chrome as the native scene. Only two Size::Fill values change.
pub(super) fn manual_split(view: &mut View, s: Session) {
    let explorer = if s.explorer() { 200.0 } else { 0.0 };
    let inspector = if s.inspector() { 224.0 } else { 0.0 };
    let work = s.width as f32 - 48.0 - explorer - inspector;
    let (left, right) = if s.split() {
        let after_divider = work - 2.0;
        (after_divider * 3.0 / 5.0, after_divider * 2.0 / 5.0)
    } else { (work, 0.0) };
    for node in &mut view.0 {
        match node.key.as_str() {
            "left" => node.params.size.x = Pixels(left),
            "right" => node.params.size.x = Pixels(right),
            _ => {}
        }
    }
}
