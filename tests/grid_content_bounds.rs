#![cfg(feature = "incremental")]

use keru_layout::layout_rules::NodeRules;
use keru_layout::tracks::{Track, TrackAxis, TrackGrid, TrackMax, TrackMin};
use keru_layout::{Axis, LayoutParams, LayoutTree, Margin, Pos, Size, Xy};

#[test]
fn nested_auto_fit_rechecks_percentage_caps_and_deducts_item_margins() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.set_rules(
        &root,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(TrackAxis::repeat(1, Track::Fr(1.)), TrackAxis::default()),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let nested = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Auto, Size::Pixels(30.)),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &nested,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::AutoFit {
                        minimum: 30.,
                        track: Track::MinMax(TrackMin::Content, TrackMax::Percent(0.5)),
                    },
                    TrackAxis::default(),
                ),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let child = tree
        .add_node(
            &nested,
            LayoutParams {
                size: Xy::new(Size::Auto, Size::Pixels(10.)),
                margin: Xy::new(
                    [Margin::px(2.).unwrap(), Margin::px(4.).unwrap()],
                    [Margin::ZERO; 2],
                ),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &child,
        NodeRules {
            grid_content_minimum: Xy::new(Some(Size::Pixels(90.)), None),
            ..Default::default()
        },
    )
    .unwrap();
    for (width, track) in [(100., 50.), (200., 100.), (100., 50.)] {
        tree.solve_layout(Xy::new(width, 30.));
        assert_eq!(tree.rule_issues(), &[]);
        assert_eq!(
            tree.resolved_grid_tracks(&nested, Axis::X)
                .unwrap()
                .unwrap(),
            [[0., track], [track, track]]
        );
        assert_eq!(tree.layout(&child).unwrap().x, [2., track - 4.]);
    }
    // Item percentage maxima resolve against its allocated 50px area,
    // and take precedence over its conditional content floor.
    let mut params = *tree.params(&child).unwrap();
    params.max_size.x = Some(Size::Frac(0.5));
    tree.update_node_params(&child, params).unwrap();
    tree.solve_layout(Xy::new(100., 30.));
    assert_eq!(tree.layout(&child).unwrap().x, [2., 27.]);
}

#[test]
fn intrinsic_grid_fit_limit_clamps_between_item_floor_and_preferred_size() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let grid = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::FitContent, Size::Pixels(20.)),
                position: Xy::new_symm(Pos::Start),
                ..Default::default()
            },
        )
        .unwrap();
    let item = tree
        .add_node(
            &grid,
            LayoutParams {
                size: Xy::new(Size::Auto, Size::Pixels(20.)),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &item,
        NodeRules {
            grid_content_minimum: Xy::new(Some(Size::Pixels(40.)), None),
            ..Default::default()
        },
    )
    .unwrap();
    tree.add_node(
        &item,
        LayoutParams {
            size: Xy::new(Size::Pixels(90.), Size::Pixels(20.)),
            ..Default::default()
        },
    )
    .unwrap();
    for (track, portion) in [(Track::Auto, 1.), (Track::Percent(0.5), 0.5)] {
        for (limit, used) in [(25., 40.), (70., 70.), (100., 90.)] {
            tree.set_rules(
                &grid,
                NodeRules {
                    grid: Some(TrackGrid {
                        tracks: Xy::new(TrackAxis::repeat(1, track), TrackAxis::default()),
                        ..Default::default()
                    }),
                    grid_fit_limit: Xy::new(Some(limit), None),
                    ..Default::default()
                },
            )
            .unwrap();
            tree.solve_layout(Xy::new(240., 30.));
            assert_eq!(tree.rule_issues(), &[]);
            assert_eq!(tree.layout(&grid).unwrap().x, [0., used]);
            // A cyclic percentage is intrinsic while measuring the grid,
            // then resolves against that grid's used width during placement.
            assert_eq!(tree.layout(&item).unwrap().x, [0., used * portion]);
        }
    }
}
