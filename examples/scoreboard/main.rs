//! A league operator's resizable score strip. Run with --features batch-pilot
//! to check the same edit history through the Batch API.
use keru_layout::layout_rules::NodeRules;
use keru_layout::tracks::{GridItem, Track, TrackAxis, TrackGrid, TrackMax, TrackMin};
use keru_layout::{
    Axis, ChildId, LayoutParams, LayoutTree, NodeId, Pos, Size, TextContent, TreeError, Xy, XyRect,
};

const PROMOTION: &str = "TONIGHT AROUND THE CIRCUIT";
const UPDATE: &str = "NORTHSHORE CITY";
const CLOCK: f32 = 48.;
const GAP: f32 = 12.;
const HEADER: f32 = 40.;
const ROW: f32 = 26.;
const ROW_GAP: f32 = 4.;

struct Game {
    time: &'static str,
    club: &'static str,
    score: &'static str,
    live: bool,
}

impl Game {
    const fn new(time: &'static str, club: &'static str, score: &'static str, live: bool) -> Self {
        Self {
            time,
            club,
            score,
            live,
        }
    }
}

const GAMES: [Game; 14] = [
    Game::new("12'", "BAY CITY", "1-0", true),
    Game::new("FT", "NORTHBRIDGE", "2-1", false),
    Game::new("31'", "LARCH", "0-0", true),
    Game::new("FT", "MILTON", "0-3", false),
    Game::new("HT", "ROVERS", "1-1", true),
    Game::new("FT", "UPTON", "1-2", false),
    Game::new("8'", "COAST", "0-0", true),
    Game::new("FT", "HAMPTON", "4-2", false),
    Game::new("67'", "UNITED", "2-0", true),
    Game::new("FT", "WANDERERS", "0-1", false),
    Game::new("72'", "VALE", "2-2", true),
    Game::new("FT", "SOUTH END", "1-1", false),
    Game::new("45'", "PARKSIDE", "1-1", true),
    Game::new("FT", "CROSS KEYS", "3-0", false),
];

#[derive(Clone, Copy)]
struct Stage {
    available: f32,
    live_only: bool,
    renamed: bool,
}

const STAGES: [Stage; 6] = [
    Stage {
        available: 580.,
        live_only: false,
        renamed: false,
    },
    Stage {
        available: 294.,
        live_only: false,
        renamed: false,
    },
    Stage {
        available: 240.,
        live_only: false,
        renamed: false,
    },
    Stage {
        available: 240.,
        live_only: true,
        renamed: false,
    },
    Stage {
        available: 240.,
        live_only: true,
        renamed: true,
    },
    Stage {
        available: 580.,
        live_only: true,
        renamed: true,
    },
];

fn club(index: usize, stage: Stage) -> &'static str {
    if index == 0 && stage.renamed {
        UPDATE
    } else {
        GAMES[index].club
    }
}

fn advance(text: &str) -> f32 {
    12. * text.chars().count() as f32
}

fn measure(_: NodeId, content: Option<&mut &'static str>, _: Option<f32>) -> Xy<f32> {
    Xy::new(advance(content.map_or("", |text| *text)), 20.)
}

fn panel_rules(available: f32) -> NodeRules {
    NodeRules {
        grid: Some(TrackGrid {
            tracks: Xy::new(
                TrackAxis::Tracks(vec![
                    Track::Pixels(CLOCK),
                    Track::MinMax(TrackMin::Content, TrackMax::Fr(2.)),
                    Track::Fr(1.),
                ]),
                TrackAxis::Tracks(vec![Track::Pixels(HEADER)]),
            ),
            implicit: Xy::new(Track::Content, Track::Pixels(ROW)),
            gap: Xy::new(GAP, ROW_GAP),
            ..Default::default()
        }),
        grid_fit_limit: Xy::new(Some(available), None),
        ..Default::default()
    }
}

struct Board {
    tree: LayoutTree<&'static str>,
    panel: ChildId,
    header: [ChildId; 2],
    games: Vec<[ChildId; 3]>,
}

fn add_cell(
    tree: &mut LayoutTree<&'static str>,
    panel: &ChildId,
    text: &'static str,
    disabled: bool,
) -> Result<ChildId, TreeError> {
    tree.add_node_with_context(
        panel,
        LayoutParams {
            size: Xy::new_symm(Size::Auto),
            text: TextContent::Fixed,
            disabled,
            ..LayoutParams::DEFAULT
        },
        text,
    )
}

impl Board {
    fn new(stage: Stage) -> Result<Self, TreeError> {
        let mut tree = LayoutTree::new();
        let panel = tree.add_node(
            &tree.root(),
            LayoutParams {
                size: Xy::new_symm(Size::FitContent),
                position: Xy::new_symm(Pos::Start),
                ..LayoutParams::DEFAULT
            },
        )?;
        tree.set_rules(&panel, panel_rules(stage.available))?;
        let badge = add_cell(&mut tree, &panel, "LIVE", false)?;
        let promo = add_cell(&mut tree, &panel, PROMOTION, false)?;
        tree.set_rules(
            &promo,
            NodeRules {
                grid_item: GridItem {
                    span: Xy::new(2, 1),
                    ..Default::default()
                },
                ..Default::default()
            },
        )?;
        let mut games = Vec::new();
        for (i, game) in GAMES.iter().enumerate() {
            let hidden = stage.live_only && !game.live;
            let clock = add_cell(&mut tree, &panel, game.time, hidden)?;
            let name = add_cell(&mut tree, &panel, club(i, stage), hidden)?;
            tree.set_rules(
                &name,
                NodeRules {
                    grid_content_minimum: Xy::new(Some(Size::FitContent), None),
                    ..Default::default()
                },
            )?;
            let score = add_cell(&mut tree, &panel, game.score, hidden)?;
            games.push([clock, name, score]);
        }
        Ok(Self {
            tree,
            panel,
            header: [badge, promo],
            games,
        })
    }

    fn edit(&mut self, old: Stage, new: Stage) -> Result<(), TreeError> {
        if old.available != new.available {
            self.tree
                .set_rules(&self.panel, panel_rules(new.available))?;
        }
        if old.live_only != new.live_only {
            for (_, nodes) in GAMES.iter().zip(&self.games).filter(|(game, _)| !game.live) {
                for node in nodes {
                    let mut params = *self.tree.params(node)?;
                    params.disabled = new.live_only;
                    self.tree.update_node_params(node, params)?;
                }
            }
        }
        if old.renamed != new.renamed {
            self.tree
                .update_node_context(&self.games[0][1], Some(club(0, new)))?;
        }
        Ok(())
    }

    fn snapshot(&self) -> Result<Geometry, TreeError> {
        let axis = |axis| -> Result<_, TreeError> {
            Ok(self
                .tree
                .resolved_grid_tracks(&self.panel, axis)?
                .expect("scoreboard is a grid")
                .to_vec())
        };
        let mut cells = Vec::new();
        for id in self.header.iter().chain(self.games.iter().flatten()) {
            cells.push(match self.tree.layout(id) {
                Ok(rect) => Some(rect),
                Err(TreeError::LayoutUnavailable) => None,
                Err(error) => return Err(error),
            });
        }
        Ok(Geometry {
            panel: self.tree.layout(&self.panel)?,
            tracks: Xy::new(axis(Axis::X)?, axis(Axis::Y)?),
            cells,
        })
    }
}

#[derive(Debug, PartialEq)]
struct Geometry {
    panel: XyRect,
    tracks: Xy<Vec<[f32; 2]>>,
    cells: Vec<Option<XyRect>>,
}

// Independent host alternative. This function has no tree or grid operations.
fn host_geometry(stage: Stage) -> Geometry {
    let mut club_floor = 0.0_f32;
    let mut score_pref = 0.0_f32;
    for (i, game) in GAMES
        .iter()
        .enumerate()
        .filter(|(_, g)| !stage.live_only || g.live)
    {
        club_floor = club_floor.max(advance(club(i, stage)));
        score_pref = score_pref.max(advance(game.score));
    }
    let fixed = CLOCK + 2. * GAP;
    let fraction = ((advance(PROMOTION) - GAP) / 3.)
        .max(club_floor / 2.)
        .max(score_pref);
    let width = stage
        .available
        .clamp(fixed + club_floor, fixed + 3. * fraction);
    let pool = width - fixed;
    let team = (2. * pool / 3.).max(club_floor);
    let x = vec![
        [0., CLOCK],
        [CLOCK + GAP, CLOCK + GAP + team],
        [fixed + team, width],
    ];
    let mut y = vec![[0., HEADER]];
    let mut cells = vec![
        Some(Xy::new(x[0], y[0])),
        Some(Xy::new([x[1][0], width], y[0])),
    ];
    let mut bottom = HEADER;
    for game in &GAMES {
        if stage.live_only && !game.live {
            cells.extend([None; 3]);
        } else {
            let top = bottom + ROW_GAP;
            bottom = top + ROW;
            y.push([top, bottom]);
            cells.extend(x.iter().map(|&column| Some(Xy::new(column, [top, bottom]))));
        }
    }
    Geometry {
        panel: Xy::new([0., width], [0., bottom]),
        tracks: Xy::new(x, y),
        cells,
    }
}

fn compare(label: &str, actual: &Geometry, expected: &Geometry) {
    assert_eq!(actual.panel, expected.panel, "{label} panel");
    assert_eq!(actual.tracks, expected.tracks, "{label} track edges");
    assert_eq!(
        actual.cells.len(),
        expected.cells.len(),
        "{label} cell count"
    );
    for (i, (actual, expected)) in actual.cells.iter().zip(&expected.cells).enumerate() {
        assert_eq!(actual, expected, "{label} cell {i}");
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut retained = Board::new(STAGES[0])?;
    #[cfg(feature = "batch-pilot")]
    let mut batch = Board::new(STAGES[0])?;
    let mut previous = STAGES[0];
    for (i, stage) in STAGES.into_iter().enumerate() {
        let window = Xy::new(stage.available, 500.);
        retained.edit(previous, stage)?;
        retained.tree.solve_layout_with_measure(window, measure);
        assert!(
            retained.tree.rule_issues().is_empty(),
            "{:?}",
            retained.tree.rule_issues()
        );
        let actual = retained.snapshot()?;
        let mut fresh = Board::new(stage)?;
        fresh.tree.solve_layout_with_measure(window, measure);
        compare("fresh", &actual, &fresh.snapshot()?);
        #[cfg(feature = "batch-pilot")]
        {
            batch.edit(previous, stage)?;
            batch
                .tree
                .solve_layout_batch_with_measure(window, measure)?;
            compare("Batch", &actual, &batch.snapshot()?);
        }
        compare("host", &actual, &host_geometry(stage));
        println!(
            "frame {}  budget {:3}  panel {:3} × {:3}  columns {:?}",
            i + 1,
            stage.available,
            actual.panel.x[1],
            actual.panel.y[1],
            actual
                .tracks
                .x
                .iter()
                .map(|c| c[1] - c[0])
                .collect::<Vec<_>>()
        );
        previous = stage;
    }
    Ok(())
}
