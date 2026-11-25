//! An editor's asset contact sheet, exercised through the public owned-tree API.
use keru_layout::layout_rules::NodeRules;
use keru_layout::tracks::{GridItem, Track, TrackAxis, TrackGrid};
use keru_layout::{
    Anchor, Arrange, Axis, ChildrenLayout, LayoutParams, LayoutTree, NodeId, Pos, Size, TreeError,
    Xy, XyRect,
};

const WINDOW: Xy<f32> = Xy::new(600., 420.);
const ASSETS: [&str; 8] = [
    "Cover", "Icon", "Panorama", "Texture", "Model", "Swatch", "Glyph", "Logo",
];
type Cell = (u16, u16);
const SPARSE: &[Cell] = &[
    (0, 0),
    (2, 0),
    (0, 1),
    (2, 1),
    (3, 1),
    (0, 2),
    (1, 2),
    (2, 2),
];
const DENSE: &[Cell] = &[
    (0, 0),
    (2, 0),
    (0, 1),
    (3, 0),
    (2, 1),
    (3, 1),
    (0, 2),
    (1, 2),
];
const COMPACT: &[Cell] = &[
    (0, 0),
    (2, 0),
    (0, 1),
    (2, 1),
    (0, 2),
    (1, 2),
    (2, 2),
    (0, 3),
];
const FAVORITE_CELLS: &[Cell] = &[(0, 0), (2, 0)];

#[derive(Clone, Copy)]
enum Filter {
    All,
    Favorites,
    Empty,
}
impl Filter {
    fn shows(self, index: usize) -> bool {
        match self {
            Self::All => true,
            Self::Favorites => index < 2,
            Self::Empty => false,
        }
    }
}
#[derive(Clone, Copy)]
struct Scenario {
    name: &'static str,
    width: f32,
    dense: bool,
    filter: Filter,
    reserve_empty: bool,
    predicted_width: f32,
    predicted_height: f32,
    cells: &'static [Cell],
}
const START: Scenario = Scenario {
    name: "Full sheet",
    width: 392.,
    dense: false,
    filter: Filter::All,
    reserve_empty: false,
    predicted_width: 92.,
    predicted_height: 184.,
    cells: SPARSE,
};
const FAVORITES: Scenario = Scenario {
    name: "Fit favorites",
    width: 502.,
    filter: Filter::Favorites,
    predicted_width: 162.,
    predicted_height: 56.,
    cells: FAVORITE_CELLS,
    ..START
};
const SCENES: [Scenario; 8] = [
    START,
    Scenario {
        name: "Backfill holes",
        dense: true,
        cells: DENSE,
        ..START
    },
    Scenario {
        name: "One pixel below threshold",
        width: 391.,
        predicted_width: 125.,
        predicted_height: 248.,
        cells: COMPACT,
        ..START
    },
    Scenario {
        name: "Three minimum tracks",
        width: 292.,
        predicted_height: 248.,
        cells: COMPACT,
        ..START
    },
    FAVORITES,
    Scenario {
        name: "Reserve empty columns",
        reserve_empty: true,
        predicted_width: 94.,
        ..FAVORITES
    },
    Scenario {
        name: "No filter matches",
        filter: Filter::Empty,
        predicted_width: 0.,
        predicted_height: 0.,
        cells: &[],
        ..FAVORITES
    },
    Scenario {
        name: "Reset",
        ..START
    },
];

fn span(index: usize) -> u16 {
    if matches!(index, 0 | 2) { 2 } else { 1 }
}
fn stack(axis: Axis, spacing: f32) -> ChildrenLayout {
    ChildrenLayout::Stack {
        axis,
        spacing,
        arrange: Arrange::Start,
    }
}
fn style(width: Size, height: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(width, height),
        anchor: Xy::new_symm(Anchor::Start),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    }
}
fn at(left: f32, top: f32) -> Xy<Pos> {
    Xy::new(Pos::Pixels(left), Pos::Pixels(top))
}
fn rect(left: f32, top: f32, width: f32, height: f32) -> XyRect {
    Xy::new([left, left + width], [top, top + height])
}

struct Card {
    container: NodeId,
    thumbnail: NodeId,
    caption: NodeId,
    badge: NodeId,
}
impl Card {
    fn nodes(&self) -> [&NodeId; 4] {
        [&self.container, &self.thumbnail, &self.caption, &self.badge]
    }
}
struct Browser {
    tree: LayoutTree,
    sheet: NodeId,
    cards: Vec<Card>,
    indicator: NodeId,
    toolbar: Vec<NodeId>,
}

impl Browser {
    fn new() -> Result<Self, TreeError> {
        let mut tree = LayoutTree::new();
        let root = tree.root();
        let tools = tree.add_node(
            &root,
            LayoutParams {
                position: at(16., 12.),
                children_layout: stack(Axis::X, 8.),
                ..style(Size::Pixels(392.), Size::Pixels(28.))
            },
        )?;
        let mut toolbar = vec![NodeId::from(tools.clone())];
        for width in [72., 96., 70., 48.] {
            toolbar.push(
                tree.add_node(&tools, style(Size::Pixels(width), Size::Fill))?
                    .into(),
            );
        }
        let sheet: NodeId = tree
            .add_node(
                &root,
                LayoutParams {
                    position: at(16., 48.),
                    ..style(Size::Pixels(392.), Size::FitContent)
                },
            )?
            .into();
        let mut cards = Vec::new();
        for _ in ASSETS {
            let tile = tree.add_node(
                &sheet,
                LayoutParams {
                    padding: Xy::new_symm([4.; 2]),
                    children_layout: stack(Axis::Y, 2.),
                    ..style(Size::Fill, Size::Fill)
                },
            )?;
            let thumbnail = tree.add_node(&tile, style(Size::Fill, Size::Fill))?;
            let caption = tree.add_node(&tile, style(Size::Fill, Size::Pixels(12.)))?;
            let badge = tree.add_node(
                &tile,
                LayoutParams {
                    free_placement: true,
                    position: Xy::new(Pos::End, Pos::Start),
                    ..style(Size::Pixels(10.), Size::Pixels(8.))
                },
            )?;
            cards.push(Card {
                container: tile.into(),
                thumbnail: thumbnail.into(),
                caption: caption.into(),
                badge: badge.into(),
            });
        }
        let indicator = tree
            .add_node(
                &sheet,
                LayoutParams {
                    free_placement: true,
                    position: at(7., 3.),
                    ..style(Size::Pixels(18.), Size::Pixels(8.))
                },
            )?
            .into();
        Ok(Self {
            tree,
            sheet,
            cards,
            indicator,
            toolbar,
        })
    }
    fn configure(&mut self, scene: Scenario, addresses: Option<&[Cell]>) -> Result<(), TreeError> {
        let mut panel = *self.tree.params(&self.sheet)?;
        panel.size.x = Size::Pixels(scene.width);
        self.tree.update_node_params(&self.sheet, panel)?;
        let column = if scene.reserve_empty {
            TrackAxis::AutoFill {
                minimum: 92.,
                track: Track::Fr(1.),
            }
        } else {
            TrackAxis::AutoFit {
                minimum: 92.,
                track: Track::Fr(1.),
            }
        };
        self.tree.set_rules(
            &self.sheet,
            NodeRules {
                grid: Some(TrackGrid {
                    tracks: Xy::new(column, TrackAxis::default()),
                    implicit: Xy::new(Track::Content, Track::Pixels(56.)),
                    gap: Xy::new_symm(8.),
                    dense: scene.dense,
                    ..Default::default()
                }),
                ..Default::default()
            },
        )?;
        let mut visible = 0;
        for (index, card) in self.cards.iter().enumerate() {
            let mut params = *self.tree.params(&card.container)?;
            params.disabled = !scene.filter.shows(index);
            self.tree.update_node_params(&card.container, params)?;
            let mut placement = GridItem {
                span: Xy::new(span(index), 1),
                ..Default::default()
            };
            if !params.disabled {
                if let Some(cells) = addresses {
                    let (column, row) = cells[visible];
                    placement.start = Xy::new(Some(column), Some(row));
                }
                visible += 1;
            }
            self.tree.set_rules(
                &card.container,
                NodeRules {
                    grid_item: placement,
                    ..Default::default()
                },
            )?;
        }
        Ok(())
    }
    fn expect(&self, scene: Scenario) -> Result<(), TreeError> {
        let get = |node: &NodeId| self.tree.layout(node);
        assert!(
            self.tree.rule_issues().is_empty(),
            "{}: {:?}",
            scene.name,
            self.tree.rule_issues()
        );
        assert_eq!(
            get(&self.sheet)?,
            rect(16., 48., scene.width, scene.predicted_height),
            "{} sheet",
            scene.name
        );
        assert_eq!(
            get(&self.indicator)?,
            rect(23., 51., 18., 8.),
            "{} sync",
            scene.name
        );
        let mut cells = scene.cells.iter();
        for (index, card) in self.cards.iter().enumerate() {
            if !scene.filter.shows(index) {
                for node in card.nodes() {
                    assert_eq!(
                        get(node),
                        Err(TreeError::LayoutUnavailable),
                        "{} hidden {}",
                        scene.name,
                        ASSETS[index]
                    );
                }
                continue;
            }
            let &(col, row) = cells.next().unwrap();
            let left = 16. + f32::from(col) * (scene.predicted_width + 8.);
            let top = 48. + 64. * f32::from(row);
            let width = f32::from(span(index)) * (scene.predicted_width + 8.) - 8.;
            let expected = [
                rect(left, top, width, 56.),
                rect(left + 4., top + 4., width - 8., 34.),
                rect(left + 4., top + 40., width - 8., 12.),
                rect(left + width - 14., top + 4., 10., 8.),
            ];
            for (node, edges) in card.nodes().into_iter().zip(expected) {
                assert_eq!(get(node)?, edges, "{} / {}", scene.name, ASSETS[index]);
            }
        }
        assert!(cells.next().is_none());
        Ok(())
    }
    fn check_guides(&self, scene: Scenario) -> Result<(), TreeError> {
        let columns = self
            .tree
            .resolved_grid_tracks(&self.sheet, Axis::X)?
            .expect("visible contact sheet");
        let rows = self
            .tree
            .resolved_grid_tracks(&self.sheet, Axis::Y)?
            .expect("visible contact sheet");
        let capacity = ((scene.width + 8.) / 100.).floor() as usize;
        let used = match (scene.filter, scene.reserve_empty) {
            (_, true) | (Filter::All, false) => capacity,
            (Filter::Favorites, false) => 3,
            (Filter::Empty, false) => 0,
        };
        assert_eq!(columns.len(), capacity, "{} column count", scene.name);
        for (index, edges) in columns.iter().enumerate() {
            let expected = if index < used {
                let start = index as f32 * (scene.predicted_width + 8.);
                [start, start + scene.predicted_width]
            } else {
                [if used == 0 { 0. } else { scene.width }; 2]
            };
            assert_eq!(*edges, expected, "{} column {index} guide", scene.name);
        }
        let row_count = ((scene.predicted_height + 8.) / 64.) as usize;
        assert_eq!(rows.len(), row_count, "{} row count", scene.name);
        for (index, edges) in rows.iter().enumerate() {
            let start = index as f32 * 64.;
            assert_eq!(
                *edges,
                [start, start + 56.],
                "{} row {index} guide",
                scene.name
            );
        }
        Ok(())
    }
    fn snapshot(&self) -> Vec<Result<XyRect, TreeError>> {
        let root = self.tree.root();
        [&root, &self.sheet, &self.indicator]
            .into_iter()
            .chain(&self.toolbar)
            .chain(self.cards.iter().flat_map(Card::nodes))
            .map(|n| self.tree.layout(n))
            .collect()
    }
}

fn trial() -> Result<(), TreeError> {
    let mut direct = Browser::new()?;
    let mut explicit = Browser::new()?;
    #[cfg(feature = "batch-pilot")]
    let mut batch = Browser::new()?;
    for scene in SCENES {
        direct.configure(scene, None)?;
        direct.tree.solve_layout(WINDOW);
        direct.expect(scene)?;
        direct.check_guides(scene)?;
        let expected = direct.snapshot();
        let mut fresh = Browser::new()?;
        fresh.configure(scene, None)?;
        fresh.tree.solve_layout(WINDOW);
        fresh.check_guides(scene)?;
        assert_eq!(fresh.snapshot(), expected, "{} fresh", scene.name);
        explicit.configure(scene, Some(scene.cells))?;
        explicit.tree.solve_layout(WINDOW);
        explicit.check_guides(scene)?;
        assert_eq!(explicit.snapshot(), expected, "{} explicit", scene.name);
        #[cfg(feature = "batch-pilot")]
        {
            batch.configure(scene, None)?;
            batch
                .tree
                .solve_layout_batch(WINDOW)
                .expect("acyclic contact sheet");
            batch.check_guides(scene)?;
            assert_eq!(batch.snapshot(), expected, "{} batch", scene.name);
        }
        println!(
            "{}: {} visible cards, {} px of rows",
            scene.name,
            scene.cells.len(),
            scene.predicted_height
        );
    }
    Ok(())
}
fn main() -> Result<(), TreeError> {
    trial()?;
    pin_trial()
}

#[test]
fn contact_sheet_edits_match_authored_geometry() {
    trial().unwrap();
}

fn along<T>(axis: Axis, slot: T, line: T) -> Xy<T> {
    match axis {
        Axis::X => Xy::new(slot, line),
        Axis::Y => Xy::new(line, slot),
    }
}

// The order is cover, panorama, tag, swatch, glyph, pinned notice, pinned status.
const PINNED_SPARSE: [Cell; 7] = [(1, 0), (2, 1), (4, 1), (0, 1), (0, 2), (1, 1), (0, 0)];
const PINNED_DENSE: [Cell; 7] = [(1, 0), (2, 1), (0, 1), (0, 2), (3, 0), (1, 1), (0, 0)];

fn pin_trial() -> Result<(), TreeError> {
    for axis in [Axis::X, Axis::Y] {
        for dense in [false, true] {
            let expected = if dense { PINNED_DENSE } else { PINNED_SPARSE };
            for explicit in [false, true] {
                let mut tree = LayoutTree::<()>::new();
                let root = tree.root();
                tree.set_rules(
                    &root,
                    NodeRules {
                        grid: Some(TrackGrid {
                            tracks: along(
                                axis,
                                TrackAxis::repeat(4, Track::Pixels(24.)),
                                TrackAxis::default(),
                            ),
                            implicit: Xy::new_symm(Track::Pixels(24.)),
                            gap: Xy::new_symm(4.),
                            flow: axis,
                            dense,
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                )?;
                let items = [
                    (None, None, 2),
                    (None, Some(1), 2),
                    (None, Some(1), 1),
                    (Some(0), None, 1),
                    (None, None, 1),
                    (Some(1), Some(1), 1),
                    (Some(0), Some(0), 1),
                ];
                let mut ids = Vec::new();
                for (index, (slot, line, span)) in items.into_iter().enumerate() {
                    let id = tree.add_node(&root, style(Size::Fill, Size::Fill))?;
                    let start = if explicit {
                        along(axis, Some(expected[index].0), Some(expected[index].1))
                    } else {
                        along(axis, slot, line)
                    };
                    tree.set_rules(
                        &id,
                        NodeRules {
                            grid_item: GridItem {
                                start,
                                span: along(axis, span, 1),
                                ..Default::default()
                            },
                            ..Default::default()
                        },
                    )?;
                    ids.push(id);
                }
                tree.solve_layout(Xy::new_symm(136.));
                assert!(tree.rule_issues().is_empty());
                for ((id, (slot, line)), (_, _, span)) in ids.iter().zip(expected).zip(items) {
                    let main = 28. * f32::from(slot);
                    let cross = 28. * f32::from(line);
                    let edges = along(
                        axis,
                        [main, main + 28. * f32::from(span) - 4.],
                        [cross, cross + 24.],
                    );
                    assert_eq!(
                        tree.layout(id)?,
                        edges,
                        "{axis:?} dense={dense} explicit={explicit} slot={slot}, line={line}"
                    );
                }
            }
        }
    }
    Ok(())
}

#[test]
fn sparse_pinned_items_keep_their_order_in_both_orientations() {
    pin_trial().unwrap();
}
