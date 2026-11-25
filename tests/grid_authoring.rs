#![cfg(feature = "incremental")]

use keru_layout::layout_rules::{Length, NodeRules};
use keru_layout::tracks::{
    GridAlign, GridItem, GridLine, Track, TrackAxis, TrackGrid, TrackMax, TrackMin,
};
use keru_layout::{Axis, LayoutParams, LayoutTree, Size, Xy};

fn named(name: &str) -> GridLine {
    GridLine::Named {
        name: name.into(),
        occurrence: 1,
        area_edge: true,
    }
}

#[test]
fn production_timeline_keeps_named_cues_when_a_preroll_is_inserted() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let mut grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::Tracks(vec![
                Track::Pixels(40.),
                Track::Pixels(80.),
                Track::Pixels(20.),
            ]),
            TrackAxis::repeat(4, Track::Pixels(24.)),
        ),
        implicit_pattern: Xy::new(vec![Track::Pixels(4.), Track::Pixels(8.)], Vec::new()),
        ..Default::default()
    };
    grid.line_names.x.insert(1, vec!["kickoff".into()]);
    grid.line_names.x.insert(3, vec!["finish".into()]);
    grid.areas.insert("rehearsal".into(), Xy::new(1..3, 1..3));
    tree.set_rules(
        &root,
        NodeRules {
            grid: Some(grid),
            ..Default::default()
        },
    )
    .unwrap();
    let mut add = |params, rules| {
        let id = tree.add_node(&root, params).unwrap();
        tree.set_rules(&id, rules).unwrap();
        id
    };
    let caption = add(
        LayoutParams {
            size: Xy::new_symm(Size::Auto),
            ..Default::default()
        },
        NodeRules {
            grid_lines: Xy::new(
                Some([named("kickoff"), named("finish")]),
                Some([GridLine::Index(1), GridLine::Auto]),
            ),
            ..Default::default()
        },
    );
    let rehearsal = add(
        LayoutParams {
            size: Xy::new_symm(Size::Auto),
            ..Default::default()
        },
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(TrackAxis::Subgrid, TrackAxis::Subgrid),
                ..Default::default()
            }),
            grid_lines: Xy::new(
                Some([named("rehearsal"), named("rehearsal")]),
                Some([named("rehearsal"), named("rehearsal")]),
            ),
            ..Default::default()
        },
    );
    let tooltip = add(
        LayoutParams {
            size: Xy::new(Size::Pixels(20.), Size::Pixels(12.)),
            ..Default::default()
        },
        NodeRules {
            grid_lines: Xy::new(Some([named("kickoff"), named("finish")]), None),
            grid_overlay: Some(Xy::new(
                [None, Some(Length::px(8.))],
                [Some(Length::px(0.)), None],
            )),
            ..Default::default()
        },
    );
    let long_label = add(
        LayoutParams {
            size: Xy::new(Size::Pixels(80.), Size::Pixels(12.)),
            ..Default::default()
        },
        NodeRules {
            grid_lines: Xy::new(
                Some([GridLine::Index(1), GridLine::Index(2)]),
                Some([GridLine::Index(4), GridLine::Auto]),
            ),
            grid_item: GridItem {
                align: Xy::new(Some(GridAlign::SafeCenter), None),
                ..Default::default()
            },
            ..Default::default()
        },
    );
    let cue = tree
        .add_node(
            &rehearsal,
            LayoutParams {
                size: Xy::new_symm(Size::Auto),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &cue,
        NodeRules {
            grid_lines: Xy::new(Some([named("kickoff"), named("finish")]), None),
            ..Default::default()
        },
    )
    .unwrap();
    for preroll in [0., 8.] {
        if preroll > 0. {
            let id = tree
                .add_node(
                    &root,
                    LayoutParams {
                        size: Xy::new_symm(Size::Auto),
                        ..Default::default()
                    },
                )
                .unwrap();
            tree.set_rules(
                &id,
                NodeRules {
                    grid_lines: Xy::new(Some([GridLine::Index(-5), GridLine::Index(1)]), None),
                    ..Default::default()
                },
            )
            .unwrap();
        }
        tree.solve_layout(Xy::new(160., 96.));
        assert_eq!(tree.rule_issues(), &[]);
        assert_eq!(
            tree.layout(&caption).unwrap().x,
            [40. + preroll, 140. + preroll]
        );
        assert_eq!(
            tree.layout(&tooltip).unwrap().x,
            [112. + preroll, 132. + preroll]
        );
        assert_eq!(
            tree.layout(&long_label).unwrap().x,
            [preroll, 80. + preroll]
        );
        assert_eq!(tree.layout(&rehearsal).unwrap().y, [24., 72.]);
        assert_eq!(
            tree.layout(&cue).unwrap().x,
            tree.layout(&caption).unwrap().x
        );
        assert_eq!(
            tree.resolved_grid_line_names(&rehearsal, Axis::X)
                .unwrap()
                .unwrap()
                .get(&0)
                .unwrap(),
            &["kickoff"]
        );
    }
}

#[test]
fn repeated_pair_and_wrapping_track_use_their_declared_lengths() {
    use keru_layout::tracks::TrackContribution;
    let mut schedule = TrackGrid {
        implicit_pattern: Xy::new(vec![Track::Pixels(4.), Track::Pixels(8.)], Vec::new()),
        ..Default::default()
    };
    schedule.areas.insert("titles".into(), Xy::new(0..3, 0..2));
    let (whole, _) = schedule.place_cells(Xy::default(), &[], Xy::default());
    assert_eq!(whole, Xy::new(3, 2));
    assert_eq!(
        schedule.resolve_axis(Axis::X, None, whole.x, &[]).0,
        [[0., 4.], [4., 12.], [12., 16.]]
    );
    let grid = TrackGrid {
        gap: Xy::new(5., 0.),
        tracks: Xy::new(
            TrackAxis::AutoRepeat {
                before: vec![Track::Pixels(10.)],
                pattern: vec![Track::Pixels(20.), Track::Pixels(30.)],
                after: vec![Track::Pixels(5.)],
                fit: false,
            },
            TrackAxis::Tracks(vec![
                Track::MinMax(TrackMin::MinContent, TrackMax::MinContent),
                Track::MinMax(TrackMin::MaxContent, TrackMax::Content),
            ]),
        ),
        ..Default::default()
    };
    let (counts, _) = grid.place_cells(Xy::new(150., 120.), &[], Xy::default());
    assert_eq!(counts.x, 6);
    assert_eq!(
        grid.resolve_axis(Axis::X, Some(150.), counts.x, &[]).1,
        140.
    );
    let items: Vec<_> = (0..2)
        .map(|i| TrackContribution {
            tracks: i..i + 1,
            minimum: 30.,
            preferred: 90.,
        })
        .collect();
    assert_eq!(
        grid.resolve_axis(Axis::Y, None, counts.y, &items).0,
        [[0., 30.], [30., 120.]]
    );
}

#[test]
fn safe_center_on_a_static_card_keeps_an_oversized_notice_reachable() {
    use keru_layout::layout_rules::{BoxReference, BoxStyle, Placement};

    let mut tree = LayoutTree::<()>::new();
    let outer = tree.root();
    let card = tree
        .add_node(
            &outer,
            LayoutParams {
                size: Xy::new(Size::Pixels(80.), Size::Pixels(24.)),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &card,
        NodeRules {
            grid: Some(TrackGrid::default()),
            ..Default::default()
        },
    )
    .unwrap();
    let notice = tree
        .add_node(
            &card,
            LayoutParams {
                size: Xy::new(Size::Pixels(40.), Size::Pixels(50.)),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &notice,
        NodeRules {
            placement: Placement::Absolute {
                containing: BoxReference::Node(outer.clone()),
                insets: Xy::default(),
            },
            box_model: BoxStyle {
                absolute_static: Xy::new_symm(Some(0.5)),
                safe_static: Xy::new_symm(true),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    tree.solve_layout(Xy::new(160., 30.));
    let port = tree.view_geometry(&outer).unwrap().scrollport.y;
    let visible = tree.view_geometry(&notice).unwrap().rect.y;
    assert_eq!(visible, [port[0], port[0] + 50.]);
    assert_eq!(tree.rule_issues(), &[]);
}

#[test]
fn a_grid_overlay_uses_its_positioning_ancestor_through_a_scroll_wrapper() {
    use keru_layout::layout_rules::{BoxReference, Overflow, Placement, ScrollStyle};
    use keru_layout::{Anchor, Pos};

    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let fixed = |w, h| LayoutParams {
        size: Xy::new(Size::Pixels(w), Size::Pixels(h)),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..Default::default()
    };
    let grid = tree.add_node(&root, fixed(140., 60.)).unwrap();
    let scroll = ScrollStyle {
        overflow: Xy::new_symm(Overflow::Hidden),
        ..Default::default()
    };
    tree.set_rules(
        &grid,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::Tracks(vec![Track::Pixels(40.), Track::Pixels(160.)]),
                    TrackAxis::repeat(1, Track::Pixels(50.)),
                ),
                ..Default::default()
            }),
            scroll,
            ..Default::default()
        },
    )
    .unwrap();
    let wrapper = tree.add_node(&grid, fixed(40., 30.)).unwrap();
    tree.set_rules(
        &wrapper,
        NodeRules {
            scroll,
            ..Default::default()
        },
    )
    .unwrap();
    let _content = tree.add_node(&wrapper, fixed(90., 70.)).unwrap();
    let badge = tree.add_node(&wrapper, fixed(180., 20.)).unwrap();
    tree.set_rules(
        &badge,
        NodeRules {
            placement: Placement::Absolute {
                containing: BoxReference::Node((*grid).clone()),
                insets: Xy::new([Some(Length::px(5.)), None], [Some(Length::px(3.)), None]),
            },
            grid_lines: Xy::new(Some([GridLine::Index(2), GridLine::Index(3)]), None),
            ..Default::default()
        },
    )
    .unwrap();
    // The badge ends at 225 in the 140px grid. Only the 90px content scrolls inside the 40px wrapper.
    for (grid_scroll, wrapper_scroll) in [(0., 0.), (0., 15.), (20., 15.), (20., 0.), (0., 0.)] {
        tree.set_scroll_offset(&grid, Xy::new(grid_scroll, 0.))
            .unwrap();
        tree.set_scroll_offset(&wrapper, Xy::new(wrapper_scroll, 0.))
            .unwrap();
        tree.solve_layout(Xy::new(260., 100.));
        let badge = tree.view_geometry(&badge).unwrap();
        assert_eq!(
            tree.view_geometry(&wrapper).unwrap().scroll_range.x,
            [0., 50.]
        );
        assert_eq!(tree.view_geometry(&grid).unwrap().scroll_range.x, [0., 85.]);
        assert_eq!(badge.clip.x, [0., 140.]);
        assert_eq!(badge.rect.x, [45. - grid_scroll, 225. - grid_scroll]);
    }
}
