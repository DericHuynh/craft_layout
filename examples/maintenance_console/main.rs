//! A machine settings form built with the owned native layout tree.
use keru_layout::layout_rules::{
    Container, ContainerQuery, Length, NodeRules, Overflow, Placement, QueryStyle, ScrollStyle,
    Side,
};
use keru_layout::tracks::{GridItem, Track, TrackAxis, TrackGrid};
use keru_layout::{
    Axis, ChildrenLayout, LayoutParams, LayoutTree, LogicalAxis, NodeId, Pos, Size, TextContent,
    TreeError, Xy, XyRect,
};

const WINDOW: Xy<f32> = Xy::new(520., 170.);
const LABELS: [&str; 5] = ["Zone", "Pump speed", "Valve ID", "Cycle", "Channel"];

struct FormRow {
    group: NodeId,
    label: NodeId,
    field: NodeId,
    action: NodeId,
}

struct Console {
    tree: LayoutTree<&'static str>,
    panel: NodeId,
    header: NodeId,
    form: NodeId,
    rows: Vec<FormRow>,
    help: NodeId,
}

fn panel_params(width: f32) -> LayoutParams {
    LayoutParams {
        size: Xy::new(Size::Pixels(width), Size::Pixels(140.)),
        position: Xy::new(Pos::Pixels(16.), Pos::Pixels(12.)),
        anchor: Xy::new_symm(keru_layout::Anchor::Start),
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    }
}

impl Console {
    fn new(width: f32) -> Result<Self, TreeError> {
        let mut tree = LayoutTree::new();
        let root = tree.root();
        let panel = tree.add_node(&root, panel_params(width))?;
        tree.set_rules(
            &panel,
            NodeRules {
                container: Some(Container {
                    name: Some("settings".into()),
                    ..Container::axis(Axis::X)
                }),
                scroll: ScrollStyle {
                    overflow: Xy::new(Overflow::Clip, Overflow::Auto),
                    ..Default::default()
                },
                ..Default::default()
            },
        )?;

        let header = tree.add_node(
            &panel,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::Pixels(24.)),
                ..LayoutParams::DEFAULT
            },
        )?;
        tree.set_rules(
            &header,
            NodeRules {
                placement: Placement::Sticky(Xy::new([None; 2], [Some(Length::px(0.)), None])),
                queries: vec![ContainerQuery {
                    name: Some("settings".into()),
                    axis: LogicalAxis::Inline,
                    min: None,
                    max: Some(300.),
                    style: QueryStyle {
                        size: Xy::new(None, Some(Size::Pixels(32.))),
                        ..Default::default()
                    },
                }],
                ..Default::default()
            },
        )?;

        let form = tree.add_node(
            &panel,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                ..LayoutParams::DEFAULT
            },
        )?;
        tree.set_rules(
            &form,
            NodeRules {
                grid: Some(TrackGrid {
                    tracks: Xy::new(
                        TrackAxis::Tracks(vec![Track::Content, Track::Fr(1.), Track::Pixels(56.)]),
                        TrackAxis::default(),
                    ),
                    implicit: Xy::new(Track::Content, Track::Pixels(32.)),
                    gap: Xy::new(8., 4.),
                    ..Default::default()
                }),
                ..Default::default()
            },
        )?;

        let mut rows = Vec::new();
        for name in LABELS {
            let group = tree.add_node(&form, LayoutParams::DEFAULT)?;
            tree.set_rules(
                &group,
                NodeRules {
                    grid_item: GridItem {
                        span: Xy::new(3, 1),
                        ..Default::default()
                    },
                    grid: Some(TrackGrid {
                        tracks: Xy::new(TrackAxis::Subgrid, TrackAxis::repeat(1, Track::Fr(1.))),
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            )?;
            let label = tree.add_node_with_context(
                &group,
                LayoutParams {
                    size: Xy::new(Size::FitContent, Size::Fill),
                    text: TextContent::Fixed,
                    ..LayoutParams::DEFAULT
                },
                name,
            )?;
            let field = tree.add_node(&group, LayoutParams::DEFAULT)?;
            let action = tree.add_node(&group, LayoutParams::DEFAULT)?;
            rows.push(FormRow {
                group: group.into(),
                label: label.into(),
                field: field.into(),
                action: action.into(),
            });
        }

        let help = tree.add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Pixels(66.), Size::Pixels(44.)),
                ..LayoutParams::DEFAULT
            },
        )?;
        tree.set_rules(
            &help,
            NodeRules {
                placement: Placement::Anchor {
                    target: rows[2].action.clone(),
                    sides: vec![Side::Below, Side::Above],
                    gap: 4.,
                },
                ..Default::default()
            },
        )?;
        Ok(Self {
            tree,
            panel: panel.into(),
            header: header.into(),
            form: form.into(),
            rows,
            help: help.into(),
        })
    }

    fn set_state(&mut self, width: f32, scroll: f32) -> Result<(), TreeError> {
        self.tree
            .update_node_params(&self.panel, panel_params(width))?;
        self.tree
            .set_scroll_offset(&self.panel, Xy::new(0., scroll))?;
        self.tree.solve_layout_with_measure(WINDOW, |_, text, _| {
            let width = text.map_or(0., |text| text.chars().count() as f32 * 8.);
            Xy::new(width, 16.)
        });
        Ok(())
    }

    #[cfg(test)]
    fn snapshot(&self) -> Result<Vec<keru_layout::layout_rules::ViewGeometry>, TreeError> {
        let mut nodes = vec![&self.panel, &self.header, &self.form, &self.help];
        for row in &self.rows {
            nodes.extend([&row.group, &row.label, &row.field, &row.action]);
        }
        nodes
            .into_iter()
            .map(|id| self.tree.view_geometry(id))
            .collect()
    }

    fn check(&self, width: f32, scroll: f32) -> Result<(), TreeError> {
        let height = if width <= 300. { 32. } else { 24. };
        let form_top = 12. + height - scroll;
        let field_right = 16. + width - 64.;
        let panel = self.tree.view_geometry(&self.panel)?;
        assert_eq!(panel.scrollport, rect(16., 12., width, 140.), "scrollport");
        assert_eq!(panel.offset, Xy::new(0., scroll), "scroll offset");
        assert_eq!(
            panel.scroll_range.y,
            [0., height + 176. - 140.],
            "scroll range"
        );
        assert_eq!(
            self.tree.view_geometry(&self.header)?.rect,
            rect(16., 12., width, height),
            "header"
        );
        assert_eq!(
            self.tree.view_geometry(&self.form)?.rect,
            rect(16., form_top, width, 176.),
            "form"
        );

        for (i, row) in self.rows.iter().enumerate() {
            let top = form_top + i as f32 * 36.;
            assert_eq!(
                self.tree.view_geometry(&row.group)?.rect,
                rect(16., top, width, 32.),
                "row {i}"
            );
            let field = self.tree.view_geometry(&row.field)?;
            assert_eq!(field.clip, panel.scrollport, "field {i} inherited clip");
            assert_eq!(
                field.rect,
                Xy::new([104., field_right], [top, top + 32.]),
                "field {i}"
            );
            let action = self.tree.view_geometry(&row.action)?.rect;
            assert_eq!(action, rect(field_right + 8., top, 56., 32.), "action {i}");
            let label = self.tree.view_geometry(&row.label)?.rect;
            assert_eq!(
                label,
                rect(16., top, LABELS[i].len() as f32 * 8., 32.),
                "label {i}"
            );
        }
        let target_top = form_top + 72.;
        let popover_top = if target_top + 32. + 4. + 44. <= WINDOW.y {
            target_top + 36.
        } else {
            target_top - 48.
        };
        assert_eq!(
            self.tree.view_geometry(&self.help)?.rect,
            rect(field_right + 8., popover_top, 66., 44.),
            "help"
        );
        assert!(
            self.tree.rule_issues().is_empty(),
            "{:?}",
            self.tree.rule_issues()
        );
        Ok(())
    }
}

fn rect(x: f32, y: f32, width: f32, height: f32) -> XyRect {
    Xy::new([x, x + width], [y, y + height])
}

fn main() -> Result<(), TreeError> {
    let mut console = Console::new(430.)?;
    for (width, scroll) in [(430., 0.), (280., 0.), (280., 56.), (430., 56.)] {
        console.set_state(width, scroll)?;
        console.check(width, scroll)?;
        let header = console.tree.view_geometry(&console.header)?.rect;
        let help = console.tree.view_geometry(&console.help)?.rect;
        println!("panel {width}, scroll {scroll}, header {header:?}, help {help:?}");
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn responsive_valve_row(width: f32) -> Result<Console, TreeError> {
        use keru_layout::{Arrange, flex::FlexLayout, layout_rules::QueryLayout};

        let mut console = Console::new(width)?;
        let row = &console.rows[2].group;
        let mut rules = console.tree.rules(row)?.unwrap().clone();
        let layouts = [
            (
                380.,
                QueryLayout::Flex(FlexLayout {
                    gap: 8.,
                    ..Default::default()
                }),
            ),
            (
                320.,
                QueryLayout::Grid(TrackGrid {
                    tracks: Xy::new(
                        TrackAxis::Tracks(vec![
                            Track::Pixels(100.),
                            Track::Fr(1.),
                            Track::Pixels(32.),
                        ]),
                        TrackAxis::repeat(1, Track::Fr(1.)),
                    ),
                    gap: Xy::new(4., 0.),
                    ..Default::default()
                }),
            ),
            (
                260.,
                QueryLayout::Native(ChildrenLayout::Stack {
                    axis: Axis::X,
                    arrange: Arrange::Start,
                    spacing: 2.,
                }),
            ),
        ];
        rules.queries = layouts
            .into_iter()
            .map(|(maximum, layout)| ContainerQuery {
                name: Some("settings".into()),
                axis: LogicalAxis::Inline,
                min: None,
                max: Some(maximum),
                style: QueryStyle {
                    layout: Some(layout),
                    ..Default::default()
                },
            })
            .collect();
        console.tree.set_rules(row, rules)?;
        Ok(console)
    }

    #[test]
    fn row_switches_among_shared_tracks_flex_local_grid_and_stack() -> Result<(), TreeError> {
        let mut retained = responsive_valve_row(430.)?;
        let wide_to_compact = [
            (430., 104., 390.),
            (340., 88., 226.),
            (300., 120., 284.),
            (240., 82., 170.),
        ];
        for (width, field_left, action_left) in wide_to_compact
            .into_iter()
            .chain(wide_to_compact.into_iter().rev())
        {
            retained.set_state(width, 0.)?;
            assert!(
                retained.tree.rule_issues().is_empty(),
                "{:?}",
                retained.tree.rule_issues()
            );
            let row = &retained.rows[2];
            assert_eq!(
                retained.tree.layout(&row.field)?.x[0],
                field_left,
                "field at {width}"
            );
            assert_eq!(
                retained.tree.layout(&row.action)?.x[0],
                action_left,
                "action at {width}"
            );
            let rules = retained.tree.rules(&row.group)?.unwrap();
            assert_eq!(rules.grid.as_ref().unwrap().tracks.x, TrackAxis::Subgrid);
            let mut fresh = responsive_valve_row(width)?;
            fresh.set_state(width, 0.)?;
            assert_eq!(retained.snapshot()?, fresh.snapshot()?, "width {width}");
        }
        Ok(())
    }

    #[test]
    fn edited_label_resizes_every_subgrid() -> Result<(), TreeError> {
        let mut retained = Console::new(280.)?;
        retained.set_state(280., 56.)?;
        for (name, field_left) in [("Emergency cutoff", 152.), ("Zone", 104.)] {
            retained
                .tree
                .update_node_context(&retained.rows[0].label, Some(name))?;
            retained.set_state(280., 56.)?;
            for row in &retained.rows {
                assert_eq!(
                    retained.tree.view_geometry(&row.field)?.rect.x,
                    [field_left, 232.]
                );
                assert_eq!(
                    retained.tree.view_geometry(&row.action)?.rect.x,
                    [240., 296.]
                );
            }
            let mut fresh = Console::new(280.)?;
            fresh
                .tree
                .update_node_context(&fresh.rows[0].label, Some(name))?;
            fresh.set_state(280., 56.)?;
            assert_eq!(retained.snapshot()?, fresh.snapshot()?);
        }
        Ok(())
    }

    #[test]
    fn retained_snapshots_match_fresh_and_explicit_cells() -> Result<(), TreeError> {
        let mut retained = Console::new(430.)?;
        for (width, scroll) in [(430., 0.), (280., 0.), (280., 56.), (430., 56.), (430., 0.)] {
            retained.set_state(width, scroll)?;
            retained.check(width, scroll)?;
            let snapshot = retained.snapshot()?;

            let mut fresh = Console::new(width)?;
            fresh.set_state(width, scroll)?;
            assert_eq!(
                snapshot,
                fresh.snapshot()?,
                "fresh at width {width} offset {scroll}"
            );

            for row in &fresh.rows {
                for (column, child) in [&row.label, &row.field, &row.action]
                    .into_iter()
                    .enumerate()
                {
                    fresh.tree.set_rules(
                        child,
                        NodeRules {
                            grid_item: GridItem {
                                start: Xy::new(Some(column as u16), Some(0)),
                                ..Default::default()
                            },
                            ..Default::default()
                        },
                    )?;
                }
            }
            fresh.set_state(width, scroll)?;
            assert_eq!(
                snapshot,
                fresh.snapshot()?,
                "explicit cells at width {width} offset {scroll}"
            );
        }
        Ok(())
    }
}
