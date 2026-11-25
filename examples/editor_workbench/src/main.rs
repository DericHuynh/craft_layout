use keru_layout::{
    Arrange, Axis, ChildId, ChildrenLayout, IncrementalRelayoutOutcome, LayoutParams, LayoutTree,
    LayoutWarning, Pos, Size, TextContent, TreeError, Xy, XyRect,
};
use Size::{Fill, FitContent, Pixels};
use std::collections::BTreeMap;

#[derive(Clone, Copy)]
struct Session {
    width: u32,
    height: u32,
    edited: bool,
    renamed: bool,
    lexer_open: bool,
    terminal_height: u32,
}

impl Session {
    fn explorer(self) -> bool { self.width >= 800 }
    fn inspector(self) -> bool { self.width >= 1150 }
    fn split(self) -> bool { self.width >= 800 }
}

struct Widget {
    key: String,
    parent: String,
    params: LayoutParams,
    text: Option<String>,
}

#[derive(Default)]
struct View(Vec<Widget>);

fn size(x: Size, y: Size) -> LayoutParams {
    LayoutParams { size: Xy::new(x, y), ..LayoutParams::DEFAULT }
}

fn stack(axis: Axis, x: Size, y: Size, spacing: f32) -> LayoutParams {
    LayoutParams {
        children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing },
        ..size(x, y)
    }
}

fn pad(mut params: LayoutParams, horizontal: f32, vertical: f32) -> LayoutParams {
    params.padding = Xy::new([horizontal; 2], [vertical; 2]);
    params
}

impl View {
    fn add(&mut self, parent: &str, key: &str, params: LayoutParams) {
        self.0.push(Widget { parent: parent.into(), key: key.into(), params, text: None });
    }

    fn label(&mut self, parent: &str, key: &str, text: &str, params: LayoutParams, mode: TextContent) {
        self.0.push(Widget {
            parent: parent.into(), key: key.into(),
            params: LayoutParams { text: mode, ..params }, text: Some(text.into()),
        });
    }

    fn row_label(&mut self, parent: &str, key: &str, text: &str) {
        self.label(parent, key, text, pad(size(Fill, FitContent), 8.0, 3.0), TextContent::Fixed);
    }

    fn tab(&mut self, key: &str, title: &str) {
        self.label("tabs", key, title, pad(size(FitContent, Fill), 12.0, 8.0), TextContent::Fixed);
    }

    fn editor(&mut self, key: &str, params: LayoutParams, lines: &[&str]) {
        self.add("panes", key, params);
        for (i, line) in lines.iter().enumerate() {
            let row = format!("{key}-row-{}", i + 1);
            self.add(key, &row, stack(Axis::X, Fill, FitContent, 0.0));
            self.label(&row, &format!("{row}-number"), &(i + 1).to_string(),
                LayoutParams { position: Xy::new(Pos::Start, Pos::Start),
                    ..pad(size(Pixels(40.0), FitContent), 8.0, 0.0) }, TextContent::Fixed);
            self.label(&row, &format!("{row}-code"), line, size(Fill, FitContent), TextContent::Wrapping);
        }
    }

    fn build(s: Session) -> Self {
        let mut v = Self::default();
        v.add("root", "screen", stack(Axis::Y, Fill, Fill, 0.0));
        v.add("screen", "title", pad(stack(Axis::X, Fill, Pixels(40.0), 8.0), 12.0, 8.0));
        v.label("title", "project", "Keystone / workbench", size(Fill, FitContent), TextContent::Fixed);
        v.label("title", "branch", "main", size(FitContent, FitContent), TextContent::Fixed);
        v.add("screen", "body", stack(Axis::X, Fill, Fill, 0.0));
        v.add("body", "rail", stack(Axis::Y, Pixels(48.0), Fill, 8.0));
        for (id, label) in [("files-tool", "DIR"), ("search-tool", "FND"), ("scm-tool", "GIT")] {
            v.row_label("rail", id, label);
        }
        v.add("body", "explorer", LayoutParams { disabled: !s.explorer(),
            ..stack(Axis::Y, Pixels(200.0), Fill, 0.0) });
        let file = if s.renamed { "session.rs" } else { "main.rs" };
        for (id, label) in [("explorer-title", "EXPLORER"), ("folder", "v src"),
            ("file-current", file), ("file-parse", "parser.rs"), ("file-lex", "lexer.rs"),
            ("manifest", "Cargo.toml"), ("readme", "README.md")] {
            v.row_label("explorer", id, label);
        }

        v.add("body", "work", stack(Axis::Y, Fill, Fill, 0.0));
        v.add("work", "tabs", stack(Axis::X, Fill, Pixels(32.0), 0.0));
        v.tab("tab-current", file);
        v.tab("tab-parse", "parser.rs");
        if s.lexer_open { v.tab("tab-lexer", "lexer.rs"); }
        v.label("work", "crumb", &format!("src  /  {file}  /  run"),
            pad(size(Fill, Pixels(24.0)), 8.0, 4.0), TextContent::Fixed);

        v.add("work", "panes", stack(Axis::X, Fill, Fill, 0.0));
        let code = if s.edited {
            "pub fn run_with_config(input: &SourceFile, diagnostics: &mut Diagnostics) -> ParseResult {"
        } else { "pub fn run() {" };
        v.editor("left", LayoutParams { fill_weight: 3.0, ..stack(Axis::Y, Fill, Fill, 0.0) },
            &[code, "    let source = input.read();", "    let tokens = lex(&source);",
                "    Parser::new(tokens).parse()", "}"]);
        v.add("panes", "divider", LayoutParams { disabled: !s.split(), ..size(Pixels(2.0), Fill) });
        v.editor("right", LayoutParams { fill_weight: 2.0, disabled: !s.split(),
            ..stack(Axis::Y, Fill, Fill, 0.0) }, &["use crate::lexer::Token;", "impl Parser {",
                "    fn parse(&mut self) {", "        self.expression();", "    }", "}"]);

        v.add("work", "terminal", pad(stack(Axis::Y, Fill, Pixels(s.terminal_height as f32), 0.0), 8.0, 4.0));
        v.row_label("terminal", "terminal-title", "TERMINAL  /  shell");
        v.row_label("terminal", "command", "$ cargo check");
        let result = if s.edited { "error[E0412]: cannot find type SourceFile" } else { "Finished dev profile" };
        v.row_label("terminal", "command-output", result);
        v.add("body", "inspector", LayoutParams { disabled: !s.inspector(),
            ..pad(stack(Axis::Y, Pixels(224.0), Fill, 4.0), 8.0, 4.0) });
        v.row_label("inspector", "outline-title", "OUTLINE");
        v.row_label("inspector", "symbol", if s.edited { "fn run_with_config" } else { "fn run" });
        v.row_label("inspector", "problems-title", "PROBLEMS");
        v.label("inspector", "problem", if s.edited {
            "Cannot find type SourceFile in this scope. Import the type from the source module."
        } else { "No problems." }, size(Fill, FitContent), TextContent::Wrapping);

        v.add("screen", "status", pad(stack(Axis::X, Fill, Pixels(24.0), 8.0), 8.0, 4.0));
        v.label("status", "status-project", if s.edited { "main*   1 problem" } else { "main   0 problems" },
            size(Fill, FitContent), TextContent::Fixed);
        v.label("status", "status-cursor", "Ln 1, Col 1   Rust", size(FitContent, FitContent), TextContent::Fixed);
        v
    }
}

// Deterministic monospace source wrapping. The same columns drive the SVG renderer.
const CHAR: f32 = 8.0;
const LINE: f32 = 16.0;

fn lines(text: &str, width: Option<f32>) -> Vec<String> {
    let columns = width.map_or(usize::MAX, |v| (v / CHAR).floor().max(1.0) as usize);
    let mut out = Vec::new();
    for line in text.split('\n') {
        let chars: Vec<char> = line.chars().collect();
        if chars.is_empty() { out.push(String::new()); }
        else { out.extend(chars.chunks(columns).map(|chunk| chunk.iter().collect::<String>())); }
    }
    out
}

fn measure(_: keru_layout::NodeId, text: Option<&mut String>, width: Option<f32>) -> Xy<f32> {
    let lines = lines(text.map_or("", |s| s.as_str()), width);
    Xy::new(lines.iter().map(|line| line.chars().count()).max().unwrap_or(0) as f32 * CHAR,
        lines.len() as f32 * LINE)
}

struct Mounted { id: ChildId, params: LayoutParams, text: Option<String> }

type Rects = BTreeMap<String, Option<XyRect>>;

#[derive(Default)]
struct App {
    tree: LayoutTree<String>,
    mounted: BTreeMap<String, Mounted>,
}

impl App {
    // The parent precedes its children. Keep the same handles when declarations change.
    fn update(&mut self, view: &View) -> Result<(), TreeError> {
        if !view.0.iter().any(|n| n.key == "tab-lexer") && let Some(tab) = self.mounted.remove("tab-lexer") {
            self.tree.remove(&tab.id)?;
        }
        for n in &view.0 {
            let mut params = n.params;
            let parent = match self.mounted.get(&n.parent) {
                Some(p) => {
                    // LayoutParams::disabled requires descendants to be disabled too.
                    params.disabled |= p.params.disabled;
                    (*p.id).clone()
                }
                None => { assert_eq!(n.parent, "root"); self.tree.root() }
            };
            if let Some(m) = self.mounted.get_mut(&n.key) {
                if params != m.params {
                    self.tree.update_node_params(&m.id, params)?;
                    m.params = params;
                }
                if n.text != m.text {
                    self.tree.update_node_context(&m.id, n.text.clone())?;
                    m.text.clone_from(&n.text);
                }
            } else {
                let id = match &n.text {
                    Some(t) => self.tree.add_node_with_context(&parent, params, t.clone())?,
                    None => self.tree.add_node(&parent, params)?,
                };
                self.mounted.insert(n.key.clone(), Mounted { id, params, text: n.text.clone() });
            }
        }
        Ok(())
    }

    fn solve(&mut self, s: Session) -> IncrementalRelayoutOutcome {
        self.tree.solve_layout_with_measure(Xy::new(s.width as f32, s.height as f32), measure)
    }

    fn rects(&self) -> Result<Rects, TreeError> {
        self.mounted.iter().map(|(key, m)| {
            let rect = match self.tree.layout(&m.id) {
                Ok(r) => Some(r),
                Err(TreeError::LayoutUnavailable) => None,
                Err(e) => return Err(e),
            };
            Ok((key.clone(), rect))
        }).collect()
    }

    fn warning_names(&self) -> Vec<String> {
        self.tree.warnings().iter().map(|w| {
            use LayoutWarning::*;
            let node = match w {
                Cycle { node, .. } | AspectRatioOnBothAxes { node } | FitContentCollapsed { node, .. }
                | MinAboveMax { node, .. } | ImpossibleFracChildren { node, .. } | NotFinite { node, .. } => node,
                other => return format!("{other:?}"),
            };
            let label = self.mounted.iter().find(|(_, m)| &*m.id == node).map(|(k, _)| k.as_str()).unwrap_or("root");
            format!("{label} {w:?}")
        }).collect()
    }
}

fn frames() -> Vec<(&'static str, Session)> {
    let mut s = Session { width: 1284, height: 800, edited: false, renamed: false, lexer_open: false, terminal_height: 144 };
    let mut out = vec![("desktop", s), ("idle", s)];
    s.edited = true;
    out.push(("type-and-check", s));
    s.renamed = true;
    s.lexer_open = true;
    out.push(("rename-and-open", s));
    s.width = 960; s.height = 660;
    out.push(("laptop", s));
    s.width = 700; s.height = 580;
    out.push(("compact", s));
    s.terminal_height = 192;
    out.push(("drag-terminal", s));
    s.width = 1284; s.height = 800;
    out.push(("restore", s));
    s.lexer_open = false;
    out.push(("close-tab", s));
    out
}

mod audit;
mod svg;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut paired = false;
    let mut trace = false;
    let mut svg_dir = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--paired" => paired = true,
            "--trace" => trace = true,
            "--svg" => svg_dir = Some(std::path::PathBuf::from(args.next().ok_or("--svg requires a directory")?)),
            "--help" | "-h" => {
                println!("editor_workbench [--paired] [--trace] [--svg DIRECTORY]");
                return Ok(());
            }
            _ => return Err(format!("unknown argument {arg}").into()),
        }
    }
    if let Some(dir) = &svg_dir { std::fs::create_dir_all(dir)?; }
    let mut app = App::default();
    let mut manual_app = App::default();
    let mut previous = Rects::default();
    for (i, (name, state)) in frames().into_iter().enumerate() {
        let mut view = View::build(state);
        let native = audit::Frame::run(&mut app, &view, state, name)?;
        audit::oracle(name, &native.rects);
        let changed = audit::changes(&previous, &native.rects);
        if name == "idle" { assert!(changed.is_empty()); }
        if let Some(dir) = &svg_dir {
            svg::write(&dir.join(format!("{i:02}-{name}.svg")), state, &view, &native.rects)?;
        }
        let left = native.rects["left"].unwrap();
        let terminal = native.rects["terminal"].unwrap();
        println!("{name:15} {}x{}   left x={:?}   terminal y={:?}   {:?}   {} changed",
            state.width, state.height, left.x, terminal.y, native.outcome, changed.len());
        if trace { native.trace(&changed); }
        if paired {
            audit::manual_split(&mut view, state);
            let manual = audit::Frame::run(&mut manual_app, &view, state, name)?;
            assert_eq!(native.rects, manual.rects, "{name}: native versus host-sized");
            println!("  host-sized {:?}, {} rectangle/visibility entries match", manual.outcome, native.rects.len());
            if trace { println!("  host warnings={:?}, fresh={:?}, fresh warnings={:?}", manual.warnings, manual.fresh_outcome, manual.fresh_warnings); }
        }
        previous = native.rects;
    }
    Ok(())
}
