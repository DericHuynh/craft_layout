#![cfg(feature = "incremental")]

use keru_layout::layout_rules::NodeRules;
use keru_layout::tracks::{GridLine, Track, TrackAxis, TrackGrid};
use keru_layout::{Axis, LayoutParams, LayoutTree, Size, Xy};

fn lines(start: GridLine, end: GridLine) -> NodeRules {
    NodeRules {
        grid_lines: Xy::new(
            Some([start, end]),
            Some([GridLine::Index(1), GridLine::Index(2)]),
        ),
        ..Default::default()
    }
}

#[test]
fn a_status_rail_before_the_first_line_preserves_the_repeated_card_minimum() {
    let tile = LayoutParams {
        size: Xy::new_symm(Size::Auto),
        ..Default::default()
    };
    for template in [
        TrackAxis::AutoFit {
            minimum: 100.,
            track: Track::Fr(1.),
        },
        TrackAxis::AutoFill {
            minimum: 100.,
            track: Track::Fr(1.),
        },
    ] {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        tree.set_rules(
            &root,
            NodeRules {
                grid: Some(TrackGrid {
                    tracks: Xy::new(template, TrackAxis::repeat(1, Track::Pixels(20.))),
                    implicit: Xy::new(Track::Pixels(36.), Track::Content),
                    gap: Xy::new(8., 0.),
                    ..Default::default()
                }),
                ..Default::default()
            },
        )
        .unwrap();
        let status = tree.add_node(&root, tile).unwrap();
        tree.set_rules(&status, lines(GridLine::Auto, GridLine::Index(1)))
            .unwrap();
        let card = tree.add_node(&root, tile).unwrap();
        tree.set_rules(&card, lines(GridLine::Index(1), GridLine::Index(2)))
            .unwrap();
        for (panel, hidden, expected) in [
            (116., false, [44., 144.]),
            (116., true, [0., 116.]),
            (116., false, [44., 144.]),
            (160., false, [44., 160.]),
            (100., false, [44., 144.]),
            (116., true, [0., 116.]),
        ] {
            tree.update_node_params(
                &status,
                LayoutParams {
                    disabled: hidden,
                    ..tile
                },
            )
            .unwrap();
            tree.solve_layout(Xy::new(panel, 20.));
            assert!(tree.rule_issues().is_empty());
            assert!(tree.warnings().is_empty());
            assert_eq!(
                tree.layout(&card).unwrap().x,
                expected,
                "panel={panel}, hidden={hidden}"
            );
            let tracks = tree.resolved_grid_tracks(&root, Axis::X).unwrap().unwrap();
            if hidden {
                assert_eq!(tracks, [expected]);
            } else {
                assert_eq!(tree.layout(&status).unwrap().x, [0., 36.]);
                assert_eq!(tracks, [[0., 36.], expected]);
            }
        }
    }
}
