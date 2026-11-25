use keru_layout::{
    measure_monospace_text, Arrange, Axis, ChildrenLayout, LayoutParams as Params,
    LayoutTree, NodeId, Size, TextContent, TreeError, Xy, XyRect,
};
use Size::{Fill, FitContent as Fit, Pixels as Px};
use std::{collections::BTreeMap, env, fs};

struct Booking {
    time: &'static str,
    service: &'static str,
    translated: &'static str,
    room: &'static str,
    note: &'static str,
}

const BOOKINGS: [Booking; 3] = [
    Booking { time: "09:10", service: "Card renewal", translated: "Renouvellement de la carte de résident", room: "A12", note: "Bring your existing card to the desk." },
    Booking { time: "09:35", service: "Permit collection", translated: "Collecte du permis et vérification des pièces justificatives de votre dossier", room: "B04", note: "Have your collection reference ready." },
    Booking { time: "10:20", service: "Address update", translated: "Mise à jour de votre adresse postale", room: "C08", note: "Bring one recent proof of address." },
];
const SLOTS: [&str; 4] = ["08:55", "09:00", "09:05", "09:10"];
const INTRO: &str = "Choose your booking and arrival time.";
const LONG_INTRO: &str = "Sélectionnez votre rendez-vous, vérifiez le numéro de votre salle et choisissez votre heure d’arrivée au centre municipal.";
const ERROR: &str = "This arrival time has just been taken. Choose another time to check in.";

#[derive(Clone, Copy)]
struct State {
    screen: Xy<f32>,
    french_copy: bool,
    error: bool,
    booking: usize,
    slot: usize,
}

impl State {
    fn service(self, index: usize) -> &'static str {
        if self.french_copy { BOOKINGS[index].translated } else { BOOKINGS[index].service }
    }
    fn intro(self) -> &'static str {
        if self.french_copy { LONG_INTRO } else { INTRO }
    }
}

#[derive(Clone, Copy, Default)]
struct Policy {
    manual_label_width: bool,
    keep_side_rail: bool,
}

fn box_size(w: Size, h: Size) -> Params {
    Params { size: Xy::new(w, h), ..Params::DEFAULT }
}

fn stack(w: Size, h: Size, axis: Axis, gap: f32) -> Params {
    Params { children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: gap }, ..box_size(w, h) }
}

fn inset(mut p: Params, x: f32, y: f32) -> Params {
    p.padding = Xy::new([x; 2], [y; 2]); p
}

fn wrapped(width: Size) -> Params {
    Params { text: TextContent::Wrapping, ..box_size(width, Fit) }
}

fn fixed_text(width: Size, height: Size) -> Params {
    Params { text: TextContent::Fixed, ..box_size(width, height) }
}

fn enabled(mut p: Params, visible: bool) -> Params {
    p.disabled = !visible; p
}

fn compact(state: State, policy: Policy) -> bool {
    state.screen.x < 760.0 && !policy.keep_side_rail
}

fn body(state: State, policy: Policy) -> Params {
    stack(Fill, Fill, if compact(state, policy) { Axis::Y } else { Axis::X }, 16.0)
}

fn summary(state: State, policy: Policy) -> Params {
    if compact(state, policy) {
        inset(stack(Fill, Fit, Axis::X, 12.0), 12.0, 10.0)
    } else {
        inset(stack(Px(240.0), Fill, Axis::Y, 18.0), 12.0, 12.0)
    }
}

fn service_label(state: State, policy: Policy) -> Params {
    let width = if policy.manual_label_width {
        let rail_budget = if compact(state, policy) { 0.0 } else { 240.0 + 16.0 };
        let width = state.screen.x - 40.0 - rail_budget - 32.0 - 24.0 - 24.0 - 44.0 - 64.0;
        Px(width.max(0.0))
    } else { Fill };
    wrapped(width)
}

fn note(show: bool) -> Params {
    enabled(inset(wrapped(Fill), 12.0, 4.0), show)
}

fn alert(show: bool) -> Params {
    enabled(inset(wrapped(Fill), 10.0, 6.0), show)
}

fn slot_label(index: usize, selected: usize) -> String {
    if index == selected { format!("✓ {}", SLOTS[index]) } else { SLOTS[index].to_string() }
}

struct Kiosk {
    tree: LayoutTree<String>,
    ids: BTreeMap<String, NodeId>,
}

impl Kiosk {
    fn build(state: State, policy: Policy) -> Self {
        let mut tree = LayoutTree::new();
        let root = tree.root();
        tree.update_node_params(&root, inset(stack(Fill, Fill, Axis::Y, 14.0), 20.0, 20.0)).unwrap();
        let mut kiosk = Self { tree, ids: BTreeMap::from([("root".into(), root)]) };
        kiosk.add("root", "header", stack(Fill, Px(48.0), Axis::X, 12.0), None);
        kiosk.add("header", "masthead", wrapped(Fill), Some("City appointments"));
        kiosk.add("header", "step", fixed_text(Fit, Fit), Some("Step 2 of 3"));
        kiosk.add("root", "body", body(state, policy), None);
        kiosk.add("body", "summary", summary(state, policy), None);
        kiosk.add("summary", "reference", stack(Fill, Fit, Axis::Y, 4.0), None);
        kiosk.add("reference", "ticket-label", wrapped(Fill), Some("BOOKING REFERENCE"));
        kiosk.add("reference", "ticket", wrapped(Fill), Some("NV-4718"));
        kiosk.add("summary", "destination", stack(Fill, Fit, Axis::Y, 4.0), None);
        kiosk.add("destination", "desk-label", wrapped(Fill), Some("YOUR DESK"));
        kiosk.add("destination", "desk", wrapped(Fill), Some(BOOKINGS[state.booking].room));
        kiosk.add("body", "form", inset(stack(Fill, Fill, Axis::Y, 8.0), 16.0, 16.0), None);
        kiosk.add("form", "heading", wrapped(Fill), Some("Check in for your visit"));
        kiosk.add("form", "instructions", wrapped(Fill), Some(state.intro()));
        kiosk.add("form", "error", alert(state.error), Some(ERROR));
        kiosk.add("form", "list", stack(Fill, Fit, Axis::Y, 6.0), None);
        for (i, booking) in BOOKINGS.iter().enumerate() {
            let name = format!("booking-{i}");
            let row = format!("row-{i}");
            kiosk.add("list", &name, stack(Fill, Fit, Axis::Y, 0.0), None);
            let mut row_params = inset(stack(Fill, Fit, Axis::X, 12.0), 12.0, 6.0);
            row_params.min_size.y = Some(Px(48.0));
            kiosk.add(&name, &row, row_params, None);
            kiosk.add(&row, &format!("time-{i}"), fixed_text(Px(44.0), Fit), Some(booking.time));
            kiosk.add(&row, &format!("service-{i}"), service_label(state, policy), Some(state.service(i)));
            kiosk.add(&row, &format!("room-{i}"), fixed_text(Px(64.0), Fit), Some(booking.room));
            kiosk.add(&name, &format!("note-{i}"), note(i == state.booking), Some(booking.note));
        }
        kiosk.add("form", "arrival-label", wrapped(Fill), Some("Available arrival times"));
        let slots = Params { children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 8.0, line_spacing: 8.0 }, ..box_size(Fill, Fit) };
        kiosk.add("form", "slots", slots, None);
        for i in 0..SLOTS.len() {
            kiosk.add("slots", &format!("slot-{i}"), fixed_text(Px(100.0), Px(44.0)), Some(&slot_label(i, state.slot)));
        }
        kiosk.add("root", "footer", stack(Fill, Px(52.0), Axis::X, 12.0), None);
        kiosk.add("footer", "back", fixed_text(Px(100.0), Fill), Some("Back"));
        kiosk.add("footer", "continue", fixed_text(Fill, Fill), Some("Check in"));
        kiosk
    }

    fn add(&mut self, parent: &str, key: &str, params: Params, label: Option<&str>) {
        let parent = &self.ids[parent];
        let id = match label {
            Some(text) => self.tree.add_node_with_context(parent, params, text.to_string()),
            None => self.tree.add_node(parent, params),
        }.unwrap();
        assert!(self.ids.insert(key.into(), id.into()).is_none());
    }

    fn set(&mut self, name: &str, p: Params) {
        self.tree.update_node_params(&self.ids[name], p).unwrap();
    }

    fn text(&mut self, name: &str, text: &str) {
        self.tree.update_node_context(&self.ids[name], Some(text.to_string())).unwrap();
    }

    fn update(&mut self, old: State, next: State, policy: Policy) {
        if old.screen != next.screen {
            self.set("body", body(next, policy));
            self.set("summary", summary(next, policy));
            for i in 0..BOOKINGS.len() {
                self.set(&format!("service-{i}"), service_label(next, policy));
            }
        }
        if old.french_copy != next.french_copy {
            self.text("instructions", next.intro());
            for i in 0..BOOKINGS.len() {
                self.text(&format!("service-{i}"), next.service(i));
            }
        }
        if old.booking != next.booking {
            self.set(&format!("note-{}", old.booking), note(false));
            self.set(&format!("note-{}", next.booking), note(true));
            self.text("desk", BOOKINGS[next.booking].room);
        }
        if old.slot != next.slot {
            for i in [old.slot, next.slot] {
                self.text(&format!("slot-{i}"), &slot_label(i, next.slot));
            }
        }
        if old.error != next.error { self.set("error", alert(next.error)); }
    }

    fn solve(&mut self, state: State) -> String {
        let outcome = self.tree.solve_layout_with_measure(state.screen, measure_monospace_text);
        format!("{outcome:?}")
    }

    fn rect(&self, key: &str) -> XyRect { self.tree.layout(&self.ids[key]).unwrap() }

    fn view(&self) -> BTreeMap<&str, Option<[u32; 4]>> {
        self.ids.iter().map(|(key, id)| {
            let bits = match self.tree.layout(id) {
                Ok(r) => Some([r.x[0], r.y[0], r.x[1], r.y[1]].map(f32::to_bits)),
                Err(TreeError::LayoutUnavailable) => None,
                Err(error) => panic!("{key}: {error}"),
            };
            (&**key, bits)
        }).collect()
    }
}

fn height(r: XyRect) -> f32 { r.y[1] - r.y[0] }
fn width(r: XyRect) -> f32 { r.x[1] - r.x[0] }

fn near(a: f32, b: f32) {
    assert!((a - b).abs() < 0.002, "expected {a} and {b} within 0.002 px");
}

fn near_edges(a: [f32; 2], b: [f32; 2]) {
    near(a[0], b[0]);
    near(a[1], b[1]);
}

fn inside(child: XyRect, parent: XyRect) -> bool {
    child.x[0] >= parent.x[0] - 0.002 && child.y[0] >= parent.y[0] - 0.002 &&
        child.x[1] <= parent.x[1] + 0.002 && child.y[1] <= parent.y[1] + 0.002
}

fn verify(k: &Kiosk, state: State) {
    assert!(k.tree.warnings().is_empty(), "{:?}", k.tree.warnings());
    let root = k.rect("root");
    assert_eq!(root, Xy::new([0.0, state.screen.x], [0.0, state.screen.y]));
    assert_eq!(k.rect("header").y, [20.0, 68.0]);
    assert_eq!(k.rect("footer").y, [state.screen.y - 72.0, state.screen.y - 20.0]);
    assert_eq!(k.rect("body").y, [82.0, state.screen.y - 86.0]);
    let form = k.rect("form");
    let summary = k.rect("summary");
    if state.screen.x >= 760.0 {
        assert_eq!(summary.x, [20.0, 260.0]);
        assert_eq!(form.x, [276.0, state.screen.x - 20.0]);
    } else {
        assert_eq!(form.x, [20.0, state.screen.x - 20.0]);
        assert_eq!(form.y[0] - summary.y[1], 16.0);
        assert_eq!(k.rect("reference").x[1] + 12.0, k.rect("destination").x[0]);
    }
    let active: Vec<_> = ["heading", "instructions", "error", "list", "arrival-label", "slots"]
        .into_iter().filter(|key| *key != "error" || state.error).collect();
    for pair in active.windows(2) { near(k.rect(pair[0]).y[1] + 8.0, k.rect(pair[1]).y[0]); }
    assert_eq!(k.tree.layout(&k.ids["error"]).is_ok(), state.error);
    for (name, id) in &k.ids {
        if let Ok(child) = k.tree.layout(id) {
            assert!(inside(child, root), "{name} outside screen: {child:?}");
            if let Some(parent) = k.tree.parent(id).unwrap() {
                assert!(inside(child, k.tree.layout(&parent).unwrap()), "{name} outside parent: {child:?}");
            }
        }
    }
    for i in 0..BOOKINGS.len() {
        let row = k.rect(&format!("row-{i}"));
        let service = k.rect(&format!("service-{i}"));
        let room = k.rect(&format!("room-{i}"));
        assert!(height(row) >= 48.0 && height(row) + 0.002 >= height(service) + 12.0);
        assert_eq!(room.x[0] - service.x[1], 12.0);
        assert_eq!(room.x[1], row.x[1] - 12.0);
        assert_eq!(width(room), 64.0);
        assert_eq!(k.tree.layout(&k.ids[&format!("note-{i}")]).is_ok(), i == state.booking);
        if i > 0 {
            near(k.rect(&format!("booking-{}", i - 1)).y[1] + 6.0, row.y[0]);
        }
    }
    if state.french_copy && state.screen == Xy::new(480.0, 960.0) {
        let single_line = height(k.rect("desk"));
        near(height(k.rect("instructions")), 3.0 * single_line);
        near(height(k.rect("service-1")), 3.0 * single_line);
        assert!(height(k.rect("row-1")) > 48.0);
    }

    let svg = k.tree.to_svg_with_text();
    // A room number appears once in the booking row and again in the summary only if selected.
    for (i, booking) in BOOKINGS.iter().enumerate() {
        assert_eq!(svg.matches(&format!(">{}</text>", booking.room)).count(), 1 + usize::from(i == state.booking));
    }
    assert!(svg.contains(&format!(">{}</text>", slot_label(state.slot, state.slot))));

    let slots = k.rect("slots");
    let per_line = ((width(slots) + 8.0) / 108.0).floor() as usize;
    for i in 0..SLOTS.len() {
        let slot = k.rect(&format!("slot-{i}"));
        near_edges(slot.x, [slots.x[0] + (i % per_line) as f32 * 108.0, slots.x[0] + (i % per_line) as f32 * 108.0 + 100.0]);
        near_edges(slot.y, [slots.y[0] + (i / per_line) as f32 * 52.0, slots.y[0] + (i / per_line) as f32 * 52.0 + 44.0]);
    }
}

fn main() {
    let options: Vec<_> = env::args().skip(1).collect();
    let svg_dir = match options.as_slice() {
        [] => None,
        [opt, path] if opt == "--svg" => { fs::create_dir_all(path).unwrap(); Some(path) }
        _ => panic!("usage: checkin_kiosk [--svg OUTPUT_DIRECTORY]"),
    };
    let start = State { screen: Xy::new(1024.0, 768.0), french_copy: false, error: false, booking: 0, slot: 0 };
    let compact_state = State { screen: Xy::new(480.0, 960.0), ..start };
    let translated = State { french_copy: true, ..compact_state };
    let validation = State { error: true, ..translated };
    let picked = State { booking: 1, slot: 2, error: false, ..validation };
    let rotated = State { screen: start.screen, ..picked };
    let below_line_break = State { screen: Xy::new(495.0, 960.0), ..compact_state };
    let exact_line_fit = State { screen: Xy::new(496.0, 960.0), ..compact_state };
    let cases = [("regular", start), ("compact", compact_state), ("translated", translated), ("validation", validation), ("picked", picked), ("rotated", rotated), ("restored", start), ("one-pixel-short", below_line_break), ("exact-fit", exact_line_fit)];
    let mut kiosk = Kiosk::build(start, Policy::default());
    let mut previous = start;
    for (name, state) in cases {
        kiosk.update(previous, state, Policy::default());
        let outcome = kiosk.solve(state);
        let mut fresh = Kiosk::build(state, Policy::default());
        fresh.solve(state);
        let mut manual = Kiosk::build(state, Policy { manual_label_width: true, ..Policy::default() });
        manual.solve(state);
        println!(
            "{name:>16}  {outcome:<26}  form {:>5.1}px  instructions {:>4.1}px  service {:>5.1} × {:>4.1}px  slots y {:.1}..{:.1}",
            width(kiosk.rect("form")),
            height(kiosk.rect("instructions")),
            width(kiosk.rect("service-1")),
            height(kiosk.rect("service-1")),
            kiosk.rect("slots").y[0],
            kiosk.rect("slots").y[1],
        );
        verify(&kiosk, state);
        assert!(fresh.tree.warnings().is_empty(), "fresh tree warnings at {name}");
        assert!(manual.tree.warnings().is_empty(), "manual-width warnings at {name}");
        assert_eq!(kiosk.view(), fresh.view(), "fresh tree at {name}");
        assert_eq!(manual.view(), fresh.view(), "manual-width alternative at {name}");
        if name == "validation" {
            let mut without_error = Kiosk::build(State { error: false, ..state }, Policy::default());
            without_error.solve(State { error: false, ..state });
            near(kiosk.rect("slots").y[1] - without_error.rect("slots").y[1], height(kiosk.rect("error")) + 8.0);
            assert_eq!(kiosk.rect("footer"), without_error.rect("footer"));
        }
        if let Some(path) = svg_dir { fs::write(format!("{path}/{name}.svg"), kiosk.tree.to_svg_with_text()).unwrap(); }
        previous = state;
    }
    let mut rail = Kiosk::build(validation, Policy { keep_side_rail: true, ..Policy::default() });
    rail.solve(validation);
    println!("Compact with side rail: form {}px, service {}px, last slot bottom {}, footer top {}", width(rail.rect("form")), width(rail.rect("service-1")), rail.rect("slot-3").y[1], rail.rect("footer").y[0]);
    assert!(rail.rect("slot-3").y[1] > rail.rect("footer").y[0]);
    assert_eq!(width(rail.rect("service-1")), 0.0);
    if let Some(path) = svg_dir {
        fs::write(format!("{path}/side-rail-counterexample.svg"), rail.tree.to_svg_with_text()).unwrap();
    }
}
