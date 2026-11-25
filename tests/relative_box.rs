#![cfg(feature = "incremental")]
use keru_layout::layout_rules::{BoxStyle, Length, NodeRules, Overflow, Placement, ScrollStyle};
use keru_layout::tracks::{Track, TrackAxis, TrackGrid};
use keru_layout::{Anchor, Axis, LayoutParams, LayoutTree, Pos, Size, Xy};

fn fixed(width: f32, height: f32) -> LayoutParams {
    LayoutParams {
        size: Xy::new(Size::Pixels(width), Size::Pixels(height)),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}

#[test]
fn percentage_edges_follow_the_allocated_column_after_resize() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let grid = tree.add_node(&root, fixed(200., 60.)).unwrap();
    tree.set_rules(
        &grid,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::Tracks(vec![Track::Fr(1.), Track::Fr(3.)]),
                    TrackAxis::default(),
                ),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let children = [0, 1].map(|_| {
        let child = tree.add_node(&grid, fixed(10., 8.)).unwrap();
        tree.set_rules(
            &child,
            NodeRules {
                box_model: BoxStyle {
                    margin_fraction: Xy::new([0.2, 0.], [0.1, 0.]),
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap();
        child
    });
    for width in [200., 320., 200.] {
        tree.update_node_params(&grid, fixed(width, 60.)).unwrap();
        tree.solve_layout(Xy::new(500., 100.));
        let first = width / 4.;
        let second = width - first;
        for ((id, origin), area) in children.iter().zip([0., first]).zip([first, second]) {
            let r = tree.view_geometry(id).unwrap().rect;
            assert_eq!(r.x[0], origin + 0.2 * area);
            assert_eq!(r.y[0], 0.1 * area);
        }
        assert!(tree.rule_issues().is_empty());
    }
}

#[test]
fn relative_subtree_resolves_against_content_and_scroll_excludes_border() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let mut panel = fixed(100., 50.);
    panel.padding.x = [10., 10.];
    let panel = tree.add_node(&root, panel).unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            box_model: BoxStyle {
                border: Xy::new([2., 2.], [0., 0.]),
                scroll_origin: Some(Xy::new_symm(false)),
                ..Default::default()
            },
            scroll: ScrollStyle {
                overflow: Xy::new(Overflow::Hidden, Overflow::Visible),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let note = tree.add_node(&panel, fixed(80., 10.)).unwrap();
    tree.set_rules(
        &note,
        NodeRules {
            placement: Placement::Relative(Xy::new(
                Length {
                    fraction: 0.25,
                    pixels: 0.,
                },
                Length::px(0.),
            )),
            ..Default::default()
        },
    )
    .unwrap();
    for scroll in [0., 8., 0.] {
        tree.set_scroll_offset(&panel, Xy::new(scroll, 0.)).unwrap();
        tree.solve_layout(Xy::new(200., 100.));
        let view = tree.view_geometry(&panel).unwrap();
        assert_eq!(view.scrollport[Axis::X], [2., 98.]);
        assert_eq!(view.scroll_range.x, [0., 20.]);
        assert_eq!(
            tree.view_geometry(&note).unwrap().rect.x,
            [30. - scroll, 110. - scroll]
        );
    }
}
