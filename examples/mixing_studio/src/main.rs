use keru_layout::*;
use std::collections::BTreeMap;

use Size::{Fill, Pixels};

#[derive(Clone)]
struct Channel {
    name: &'static str,
    level: [f32; 2],
    fader: f32,
    muted: bool,
}

impl Channel {
    fn new(name: &'static str, level: f32, fader: f32) -> Self {
        Self {
            name,
            level: [level, level * 0.88],
            fader,
            muted: false,
        }
    }

    fn lit(&self, side: usize) -> f32 {
        if self.muted { 0.0 } else { self.level[side] }
    }
}

struct Session {
    viewport: Xy<f32>,
    channels: Vec<Channel>,
    selected: &'static str,
    aux_open: bool,
}

impl Session {
    fn rehearsal() -> Self {
        Self {
            viewport: Xy::new(1280.0, 760.0),
            channels: vec![
                Channel::new("Kick", 0.8, 0.35),
                Channel::new("Snare", 0.65, 0.4),
                Channel::new("Bass", 0.74, 0.32),
                Channel::new("Guitar", 0.56, 0.48),
                Channel::new("Keys", 0.7, 0.5),
                Channel::new("Vocal", 0.84, 0.22),
                Channel::new("Room", 0.45, 0.68),
                Channel::new("FX Return", 0.43, 0.71),
            ],
            selected: "Kick",
            aux_open: false,
        }
    }
}

fn sized(x: Size, y: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(x, y),
        ..LayoutParams::DEFAULT
    }
}

fn stack(x: Size, y: Size, axis: Axis, spacing: f32) -> LayoutParams {
    LayoutParams {
        children_layout: ChildrenLayout::Stack {
            axis,
            spacing,
            arrange: Arrange::Start,
        },
        ..sized(x, y)
    }
}

fn padded(params: LayoutParams, x: f32, y: f32) -> LayoutParams {
    LayoutParams {
        padding: Xy::new([x; 2], [y; 2]),
        ..params
    }
}

fn at(x: Pos, y: Pos, params: LayoutParams) -> LayoutParams {
    LayoutParams {
        position: Xy::new(x, y),
        ..params
    }
}

// Keys describe application controls and survive fresh tree construction.
struct Desk {
    tree: LayoutTree,
    nodes: BTreeMap<String, ChildId>,
}

impl Desk {
    fn id(&self, key: &str) -> &ChildId {
        &self.nodes[key]
    }

    fn add(&mut self, parent: &str, name: &str, params: LayoutParams) -> String {
        let key = if parent.is_empty() {
            name.to_owned()
        } else {
            format!("{parent}/{name}")
        };
        let parent = if parent.is_empty() {
            self.tree.root()
        } else {
            self.id(parent).clone().into()
        };
        let id = self.tree.add_node(&parent, params).unwrap();
        assert!(self.nodes.insert(key.clone(), id).is_none());
        key
    }

    fn edit(&mut self, key: &str, edit: impl FnOnce(&mut LayoutParams)) {
        let id = self.id(key).clone();
        let mut p = *self.tree.params(&id).unwrap();
        edit(&mut p);
        self.tree.update_node_params(&id, p).unwrap();
    }

    fn build(session: &Session) -> Self {
        let mut d = Desk {
            tree: LayoutTree::new(),
            nodes: BTreeMap::new(),
        };
        let root = d.tree.root();
        d.tree
            .update_node_params(&root, padded(stack(Fill, Fill, Axis::Y, 8.0), 12.0, 8.0))
            .unwrap();
        let top = d.add(
            "",
            "Transport",
            padded(stack(Fill, Pixels(48.0), Axis::X, 6.0), 8.0, 4.0),
        );
        for (name, w) in [
            ("Rewind", 34.0),
            ("Stop", 34.0),
            ("Play", 34.0),
            ("Record", 34.0),
            ("Timecode", 130.0),
        ] {
            d.add(&top, name, sized(Pixels(w), Fill));
        }
        d.add(&top, "Song title", sized(Fill, Fill));
        d.add(&top, "Tempo", sized(Pixels(80.0), Fill));
        d.add(&top, "Clock source", sized(Pixels(100.0), Fill));

        let workspace = d.add("", "Deck", stack(Fill, Fill, Axis::X, 8.0));
        let browser = d.add(
            &workspace,
            "Browser",
            padded(stack(Pixels(184.0), Fill, Axis::Y, 6.0), 8.0, 8.0),
        );
        d.add(&browser, "Session", sized(Fill, Pixels(28.0)));
        d.add(&browser, "Search", sized(Fill, Pixels(26.0)));
        let scenes = d.add(&browser, "Scenes", stack(Fill, Fill, Axis::Y, 4.0));
        for name in [
            "Soundcheck",
            "Entrance",
            "First verse",
            "Chorus",
            "Solo",
            "Encore",
        ] {
            d.add(&scenes, name, sized(Fill, Pixels(26.0)));
        }
        let cues = d.add(
            &browser,
            "Scene controls",
            stack(Fill, Pixels(30.0), Axis::X, 4.0),
        );
        for name in ["Previous", "Recall", "Next"] {
            d.add(&cues, name, sized(Fill, Fill));
        }

        let bank = d.add(
            &workspace,
            "Bank",
            padded(stack(Fill, Fill, Axis::Y, 6.0), 8.0, 8.0),
        );
        let head = d.add(&bank, "Header", stack(Fill, Pixels(28.0), Axis::X, 4.0));
        d.add(&head, "Mix name", sized(Fill, Fill));
        d.add(&head, "Edit sends", sized(Pixels(92.0), Fill));
        d.add(&bank, "Channels", stack(Fill, Fill, Axis::X, 4.0));
        for c in &session.channels {
            d.channel(c, session.selected);
        }

        if session.aux_open {
            d.auxiliary();
        }
        let master = d.add(
            &workspace,
            "Master",
            padded(stack(Pixels(112.0), Fill, Axis::Y, 6.0), 6.0, 8.0),
        );
        d.add(&master, "Output bus", sized(Fill, Pixels(28.0)));
        d.add(&master, "Limiter", sized(Fill, Pixels(24.0)));
        let meters = d.add(
            &master,
            "Stereo",
            padded(stack(Fill, Fill, Axis::X, 4.0), 8.0, 0.0),
        );
        for (name, level) in [("Left", 0.81), ("Right", 0.76)] {
            d.meter(&meters, name, Fill, level);
        }
        d.add(&master, "Loudness", sized(Fill, Pixels(38.0)));
        d.add(&master, "Monitor level", sized(Fill, Pixels(56.0)));
        let status = d.add("", "Status", stack(Fill, Pixels(24.0), Axis::X, 8.0));
        for (name, x) in [
            ("Engine state", Pixels(124.0)),
            ("Session location", Fill),
            ("Sample rate", Pixels(88.0)),
            ("Buffer size", Pixels(92.0)),
        ] {
            d.add(&status, name, sized(x, Fill));
        }
        d
    }

    fn meter(&mut self, parent: &str, name: &str, width: Size, level: f32) {
        let rail = self.add(parent, name, sized(width, Fill));
        self.add(
            &rail,
            "Lit",
            at(Pos::Center, Pos::End, sized(Fill, Size::Frac(level))),
        );
    }

    fn channel(&mut self, c: &Channel, selected: &str) {
        let strip = self.add(
            "Deck/Bank/Channels",
            c.name,
            padded(stack(Fill, Fill, Axis::Y, 4.0), 4.0, 4.0),
        );
        self.add(&strip, "Input name", sized(Fill, Pixels(24.0)));
        self.add(&strip, "Input patch", sized(Fill, Pixels(20.0)));
        let pan = self.add(&strip, "Pan", sized(Fill, Pixels(34.0)));
        self.add(&pan, "Knob", sized(Size::AspectRatio(1.0), Fill));
        let switches = self.add(&strip, "Switches", stack(Fill, Pixels(20.0), Axis::X, 2.0));
        for name in ["Mute", "Solo", "Arm"] {
            self.add(&switches, name, sized(Fill, Fill));
        }
        let levels = self.add(&strip, "Levels", stack(Fill, Fill, Axis::X, 2.0));
        let lane = self.add(&levels, "Fader", sized(Fill, Fill));
        self.add(&lane, "Travel", sized(Pixels(2.0), Fill));
        self.add(
            &lane,
            "Thumb",
            at(
                Pos::Center,
                Pos::Frac(c.fader),
                sized(Pixels(22.0), Pixels(10.0)),
            ),
        );
        self.meter(&levels, "Left", Pixels(6.0), c.lit(0));
        self.meter(&levels, "Right", Pixels(6.0), c.lit(1));
        self.add(&strip, "dB readout", sized(Fill, Pixels(22.0)));
        self.add(&strip, "Output patch", sized(Fill, Pixels(20.0)));
        let lamp = LayoutParams {
            free_placement: true,
            disabled: c.name != selected,
            ..sized(Pixels(5.0), Pixels(5.0))
        };
        self.add(&strip, "Selected", at(Pos::End, Pos::Start, lamp));
    }

    fn auxiliary(&mut self) {
        let aux = self.add(
            "Deck",
            "Aux",
            padded(stack(Pixels(156.0), Fill, Axis::Y, 6.0), 8.0, 8.0),
        );
        self.add(&aux, "Send masters", sized(Fill, Pixels(28.0)));
        for name in ["Reverb", "Delay", "Stage left", "Stage right"] {
            let send = self.add(
                &aux,
                name,
                padded(stack(Fill, Pixels(64.0), Axis::Y, 4.0), 4.0, 4.0),
            );
            self.add(&send, "Destination", sized(Fill, Pixels(20.0)));
            let dial = self.add(&send, "Gain", stack(Fill, Fill, Axis::X, 4.0));
            self.add(&dial, "Knob", sized(Size::AspectRatio(1.0), Fill));
            self.add(&dial, "Readout", sized(Fill, Fill));
        }
    }

    fn before(&mut self, key: &str, next: &str) {
        let (child, next) = (self.id(key).clone(), self.id(next).clone());
        self.tree
            .move_node(&child, Destination::Before(&next))
            .unwrap();
    }

    fn close_aux(&mut self) {
        let aux = self.id("Deck/Aux").clone();
        self.tree.remove(&aux).unwrap();
        self.nodes
            .retain(|key, _| key != "Deck/Aux" && !key.starts_with("Deck/Aux/"));
    }

    fn rect(&self, key: &str) -> XyRect {
        self.tree.layout(self.id(key)).unwrap()
    }
}

fn near(a: f32, b: f32) {
    assert!((a - b).abs() < 0.002, "observed {a}, expected {b}");
}

fn dimension(edges: [f32; 2]) -> f32 {
    edges[1] - edges[0]
}

fn check(d: &Desk, s: &Session) {
    let width = s.viewport.x;
    let height = s.viewport.y;
    let bank_end = width - 132.0 - if s.aux_open { 164.0 } else { 0.0 };
    near(d.rect("Transport").y[0], 8.0);
    near(d.rect("Transport").y[1], 56.0);
    near(d.rect("Deck").y[0], 64.0);
    near(d.rect("Deck").y[1], height - 40.0);
    near(d.rect("Status").y[0], height - 32.0);
    near(d.rect("Status").y[1], height - 8.0);
    near(dimension(d.rect("Deck/Browser").x), 184.0);
    near(dimension(d.rect("Deck/Master").x), 112.0);
    near(d.rect("Deck/Bank").x[0], 204.0);
    near(d.rect("Deck/Bank").x[1], bank_end);
    if s.aux_open {
        let aux = d.rect("Deck/Aux");
        near(aux.x[0], bank_end + 8.0);
        near(dimension(aux.x), 156.0);
    }
    let n = s.channels.len() as f32;
    let strip_width = (bank_end - 8.0 - 212.0 - (n - 1.0) * 4.0) / n;
    for (i, c) in s.channels.iter().enumerate() {
        let path = format!("Deck/Bank/Channels/{}", c.name);
        let strip = d.rect(&path);
        near(strip.x[0], 212.0 + i as f32 * (strip_width + 4.0));
        near(dimension(strip.x), strip_width);
        near(strip.y[0], 106.0);
        near(strip.y[1], height - 48.0);
        let pan = d.rect(&format!("{path}/Pan/Knob"));
        near(dimension(pan.x), 34.0);
        near(dimension(pan.y), 34.0);
        let rail = d.rect(&format!("{path}/Levels/Fader"));
        let thumb = d.rect(&format!("{path}/Levels/Fader/Thumb"));
        near(
            (thumb.y[0] + thumb.y[1]) / 2.0,
            rail.y[0] + c.fader * dimension(rail.y),
        );
        for (side, name) in ["Left", "Right"].iter().enumerate() {
            let meter = d.rect(&format!("{path}/Levels/{name}"));
            let lit = d.rect(&format!("{path}/Levels/{name}/Lit"));
            near(lit.y[1], meter.y[1]);
            near(dimension(lit.y), c.lit(side) * dimension(meter.y));
        }
        let lamp = d.tree.layout(d.id(&format!("{path}/Selected")));
        if s.selected == c.name {
            let lamp = lamp.unwrap();
            near(lamp.x[1], strip.x[1] - 4.0);
            near(lamp.y[0], strip.y[0] + 4.0);
        } else {
            assert_eq!(lamp, Err(TreeError::LayoutUnavailable));
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum StripSizing {
    FillAvailable,
    PrecomputedPixels,
}

impl StripSizing {
    fn apply(self, d: &mut Desk, s: &Session) {
        if let Self::PrecomputedPixels = self {
            // This version deliberately duplicates the bank's surrounding geometry.
            let panel_widths = 184.0 + 112.0 + if s.aux_open { 156.0 } else { 0.0 };
            let panel_gaps = 8.0 * if s.aux_open { 3.0 } else { 2.0 };
            let channel_area = s.viewport.x - 24.0 - panel_widths - panel_gaps - 16.0;
            let n = s.channels.len() as f32;
            let width = (channel_area - 4.0 * (n - 1.0)) / n;
            for c in &s.channels {
                let key = format!("Deck/Bank/Channels/{}", c.name);
                if d.tree.params(d.id(&key)).unwrap().size.x != Pixels(width) {
                    d.edit(&key, |p| p.size.x = Pixels(width));
                }
            }
        }
    }
}

type View = BTreeMap<String, Result<XyRect, TreeError>>;

fn view(desk: &Desk) -> View {
    let mut rects: View = desk
        .nodes
        .iter()
        .map(|(key, id)| (key.clone(), desk.tree.layout(id)))
        .collect();
    rects.insert("Window".to_owned(), desk.tree.layout(&desk.tree.root()));
    rects
}

fn frame(
    label: &'static str,
    desk: &mut Desk,
    s: &Session,
    model: StripSizing,
) -> (&'static str, View) {
    model.apply(desk, s);
    let route = desk.tree.solve_layout(s.viewport);
    let mut fresh = Desk::build(s);
    model.apply(&mut fresh, s);
    fresh.tree.solve_layout(s.viewport);
    assert!(
        desk.tree.warnings().is_empty(),
        "{label}: {:?}",
        desk.tree.warnings()
    );
    assert!(
        fresh.tree.warnings().is_empty(),
        "{label}: fresh {:?}",
        fresh.tree.warnings()
    );
    check(desk, s);
    check(&fresh, s);
    let retained = view(desk);
    let rebuilt = view(&fresh);
    assert!(retained.keys().eq(rebuilt.keys()));
    for (key, rect) in &retained {
        assert_eq!(rect, &rebuilt[key], "{label}, {key}: retained/fresh");
    }
    let first = format!("Deck/Bank/Channels/{}", s.channels[0].name);
    println!(
        "{label:16} {}x{}, {} nodes, {:.3} strip, warnings=0, {:?}",
        s.viewport.x,
        s.viewport.y,
        retained.len(),
        dimension(desk.rect(&first).x),
        route
    );
    (label, retained)
}

fn run(model: StripSizing) -> Vec<(&'static str, View)> {
    println!("\n{model:?}");
    let mut frames = Vec::new();
    let mut s = Session::rehearsal();
    let mut d = Desk::build(&s);
    frames.push(frame("Rehearsal", &mut d, &s, model));

    s.channels[3].muted = true;
    for side in ["Left", "Right"] {
        d.edit(
            &format!("Deck/Bank/Channels/Guitar/Levels/{side}/Lit"),
            |p| p.size.y = Size::Frac(0.0),
        );
    }
    frames.push(frame("Mute Guitar", &mut d, &s, model));

    d.edit("Deck/Bank/Channels/Kick/Selected", |p| p.disabled = true);
    s.selected = "Vocal";
    s.channels[5].fader = 0.38;
    d.edit("Deck/Bank/Channels/Vocal/Selected", |p| p.disabled = false);
    d.edit("Deck/Bank/Channels/Vocal/Levels/Fader/Thumb", |p| {
        p.position.y = Pos::Frac(0.38)
    });
    frames.push(frame("Select and ride", &mut d, &s, model));

    s.aux_open = true;
    d.auxiliary();
    d.before("Deck/Aux", "Deck/Master");
    frames.push(frame("Send masters", &mut d, &s, model));

    s.channels.insert(2, Channel::new("Talkback", 0.36, 0.56));
    d.channel(&s.channels[2], s.selected);
    d.before("Deck/Bank/Channels/Talkback", "Deck/Bank/Channels/Bass");
    frames.push(frame("Insert Talkback", &mut d, &s, model));

    s.viewport = Xy::new(1200.0, 660.0);
    frames.push(frame("Resize", &mut d, &s, model));
    s.aux_open = false;
    d.close_aux();
    frames.push(frame("Close rack", &mut d, &s, model));
    assert_only_changed(
        &frames[0].1,
        &frames[1].1,
        &[
            "Deck/Bank/Channels/Guitar/Levels/Left/Lit",
            "Deck/Bank/Channels/Guitar/Levels/Right/Lit",
        ],
    );
    assert_only_changed(
        &frames[1].1,
        &frames[2].1,
        &[
            "Deck/Bank/Channels/Kick/Selected",
            "Deck/Bank/Channels/Vocal/Levels/Fader/Thumb",
            "Deck/Bank/Channels/Vocal/Selected",
        ],
    );
    frames
}

fn assert_only_changed(before: &View, after: &View, expected: &[&str]) {
    assert!(before.keys().eq(after.keys()));
    let changed: Vec<_> = before
        .iter()
        .filter_map(|(key, rect)| (rect != &after[key]).then_some(key.as_str()))
        .collect();
    assert_eq!(changed, expected);
}

fn compare_styles(label: &str, direct: &View, manual: &View) {
    let mut max_error: f32 = 0.0;
    assert!(direct.keys().eq(manual.keys()));
    for (key, direct_rect) in direct {
        match (direct_rect, &manual[key]) {
            (Ok(a), Ok(b)) => {
                for (u, v) in a.x.iter().chain(&a.y).zip(b.x.iter().chain(&b.y)) {
                    max_error = max_error.max((u - v).abs());
                    assert!((u - v).abs() < 0.002, "{label}, {key}: {u} vs {v}");
                }
            }
            (Err(TreeError::LayoutUnavailable), Err(TreeError::LayoutUnavailable)) => {}
            pair => panic!("{label}, {key}: inconsistent availability {pair:?}"),
        }
    }
    println!("{label:16} max absolute edge difference {max_error:.6} px");
}

fn main() {
    let direct = run(StripSizing::FillAvailable);
    let manual = run(StripSizing::PrecomputedPixels);
    assert_eq!(direct.len(), manual.len());
    println!("\nFill vs precomputed pixels");
    for ((label, a), (other, b)) in direct.iter().zip(&manual) {
        assert_eq!(label, other);
        compare_styles(label, a, b);
    }
}
