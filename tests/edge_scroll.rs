#![cfg(feature = "incremental")]

use keru_layout::layout_rules::{Length, NodeRules, Overflow, Placement, ScrollStyle};
use keru_layout::tracks::{GridAlign, Track, TrackAxis, TrackGrid};
use keru_layout::{
    Anchor, Arrange, Axis, ChildId, ChildrenLayout, LayoutParams, LayoutTree, Margin, Pos, Size, Xy,
};

fn solve(tree: &mut LayoutTree<()>, window: Xy<f32>) {
    #[cfg(feature = "batch-pilot")]
    tree.solve_layout_batch(window).unwrap();
    #[cfg(not(feature = "batch-pilot"))]
    tree.solve_layout(window);
}

fn tile(width: f32, height: f32) -> LayoutParams {
    LayoutParams {
        size: Xy::new(Size::Pixels(width), Size::Pixels(height)),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}

fn column(width: f32, height: f32) -> LayoutParams {
    LayoutParams {
        children_layout: ChildrenLayout::Stack {
            axis: Axis::Y,
            arrange: Arrange::Start,
            spacing: 0.,
        },
        ..tile(width, height)
    }
}

fn scroll(style: ScrollStyle) -> NodeRules {
    NodeRules {
        scroll: style,
        ..Default::default()
    }
}

// https://www.bram.us/2021/07/23/prevent-unwanted-layout-shifts-caused-by-scrollbars-with-the-scrollbar-gutter-css-property/
#[test]
fn a_one_pixel_document_edit_can_add_then_remove_both_scrollbars() {
    for (bars, stable, expected) in [
        (
            Xy::new(8., 10.),
            false,
            [
                (100., 100.),
                (90., 92.),
                (100., 100.),
                (90., 92.),
                (100., 100.),
            ],
        ),
        (Xy::new(8., 10.), true, [(90., 92.); 5]),
        (Xy::new(0., 0.), false, [(100., 100.); 5]),
    ] {
        let make = |width, height| {
            let mut t = LayoutTree::<()>::new();
            let pane = t.add_node(&t.root(), tile(100., 100.)).unwrap();
            let page = t.add_node(&pane, tile(width, height)).unwrap();
            t.set_rules(
                &pane,
                scroll(ScrollStyle {
                    overflow: Xy::new_symm(Overflow::Auto),
                    scrollbar: bars,
                    stable_gutter: stable,
                }),
            )
            .unwrap();
            t.set_scroll_offset(&pane, Xy::new_symm(1000.)).unwrap();
            (t, pane, page)
        };
        let (mut tree, pane, page) = make(100., 100.);
        for ((w, h), (port_w, port_h)) in [
            (100., 100.),
            (100., 101.),
            (97., 99.),
            (100., 101.),
            (80., 80.),
        ]
        .into_iter()
        .zip(expected)
        {
            tree.update_node_params(&page, tile(w, h)).unwrap();
            let (mut rebuilt, new_pane, new_page) = make(w, h);
            for (t, container, sheet) in [
                (&mut tree, &pane, &page),
                (&mut rebuilt, &new_pane, &new_page),
            ] {
                solve(t, Xy::new(120., 120.));
                assert!(t.rule_issues().is_empty(), "{:?}", t.rule_issues());
                assert!(t.warnings().is_empty());
                let port = t.view_geometry(container).unwrap();
                let dx = (w - port_w).max(0.);
                let dy = (h - port_h).max(0.);
                assert_eq!(port.scrollport, Xy::new([0., port_w], [0., port_h]));
                assert_eq!(port.scroll_range, Xy::new([0., dx], [0., dy]));
                assert_eq!(port.offset, Xy::new(dx, dy));
                let doc = t.view_geometry(sheet).unwrap();
                assert_eq!(doc.rect, Xy::new([-dx, w - dx], [-dy, h - dy]));
                assert_eq!(doc.clip, port.scrollport);
            }
        }
    }
}

fn reader(spacer: f32, margin: f32) -> (LayoutTree<()>, ChildId, ChildId, ChildId) {
    let mut tree = LayoutTree::<()>::new();
    let pane = tree.add_node(&tree.root(), column(120., 60.)).unwrap();
    tree.set_rules(
        &pane,
        scroll(ScrollStyle {
            overflow: Xy::new(Overflow::Visible, Overflow::Auto),
            ..Default::default()
        }),
    )
    .unwrap();
    tree.add_node(&pane, tile(120., 20.)).unwrap();
    let mut padded = column(120., 80.);
    padded.padding.y = [8., 12.];
    let section = tree.add_node(&pane, padded).unwrap();
    tree.add_node(&section, tile(120., spacer)).unwrap();
    let mut heading = tile(120., 16.);
    heading.margin.y[1] = Margin::px(margin).unwrap();
    let title = tree.add_node(&section, heading).unwrap();
    tree.set_rules(
        &title,
        NodeRules {
            placement: Placement::Sticky(Xy::new([None, None], [Some(Length::px(2.)), None])),
            ..Default::default()
        },
    )
    .unwrap();
    tree.add_node(&section, tile(120., (44. - spacer - margin).max(0.)))
        .unwrap();
    tree.add_node(&pane, tile(120., 100.)).unwrap();
    (tree, pane, section, title)
}

// https://benfrain.com/yes-you-can-use-position-sticky-and-overflow-together/
#[test]
fn a_sticky_heading_respects_its_sections_padding_and_scroll_ancestor() {
    let (mut tree, pane, section, title) = reader(0., 0.);
    for (overflow, expected_y) in [
        (Overflow::Visible, [28., 2., -8., -16., 28.]),
        (Overflow::Clip, [28., 2., -8., -16., 28.]),
        (Overflow::Hidden, [28., -12., -52., -60., 28.]),
        (Overflow::Clip, [28., 2., -8., -16., 28.]),
    ] {
        let rule = scroll(ScrollStyle {
            overflow: Xy::new_symm(overflow),
            ..Default::default()
        });
        tree.set_rules(&section, rule).unwrap();
        for (offset, expected) in [0., 40., 80., 88., 0.].into_iter().zip(expected_y) {
            let (mut fresh, fresh_pane, fresh_section, fresh_title) = reader(0., 0.);
            fresh
                .set_rules(
                    &fresh_section,
                    scroll(ScrollStyle {
                        overflow: Xy::new_symm(overflow),
                        ..Default::default()
                    }),
                )
                .unwrap();
            for (t, scrollpane, wrapper, header) in [
                (&mut tree, &pane, &section, &title),
                (&mut fresh, &fresh_pane, &fresh_section, &fresh_title),
            ] {
                t.set_scroll_offset(scrollpane, Xy::new(0., offset))
                    .unwrap();
                solve(t, Xy::new(150., 140.));
                assert!(t.rule_issues().is_empty());
                assert!(t.warnings().is_empty());
                assert_eq!(
                    t.view_geometry(wrapper).unwrap().scrollport.y,
                    [20. - offset, 100. - offset]
                );
                let header = t.view_geometry(header).unwrap();
                assert_eq!(
                    header.rect.y,
                    [expected, expected + 16.],
                    "{overflow:?}, scroll {offset}"
                );
                let clip = if overflow == Overflow::Visible {
                    [0., 60.]
                } else {
                    [(20. - offset).max(0.), (100. - offset).min(60.)]
                };
                assert_eq!(header.clip.y, clip);
            }
        }
    }
}

#[test]
fn a_sticky_title_keeps_its_margin_and_never_moves_against_a_top_only_inset() {
    for (spacer, initial, scrolled) in [
        (0., 28., -12.),
        (38., 66., -12.),
        (42., 70., -10.),
        (44., 72., -8.),
    ] {
        let (mut tree, pane, _, title) = reader(spacer, 4.);
        for (offset, top) in [(0., initial), (80., scrolled), (0., initial)] {
            tree.set_scroll_offset(&pane, Xy::new(0., offset)).unwrap();
            solve(&mut tree, Xy::new(150., 140.));
            assert_eq!(tree.view_geometry(&title).unwrap().rect.y, [top, top + 16.]);
            assert!(tree.rule_issues().is_empty());
        }
    }

    // The normal heading is taller than the section and already crosses its
    // trailing edge. A top-only inset cannot pull it back into the section.
    let (mut tree, pane, section, title) = reader(12., 0.);
    tree.update_node_params(&section, column(120., 24.))
        .unwrap();
    tree.update_node_params(&title, tile(120., 32.)).unwrap();
    for (offset, top) in [(0., 32.), (40., -8.), (80., -48.), (0., 32.)] {
        tree.set_scroll_offset(&pane, Xy::new(0., offset)).unwrap();
        solve(&mut tree, Xy::new(150., 140.));
        assert_eq!(tree.view_geometry(&title).unwrap().rect.y, [top, top + 32.]);
        assert!(tree.rule_issues().is_empty());
    }
}

#[test]
fn a_heading_can_stick_across_the_grid_or_within_one_section() {
    let top = Xy::new([None; 2], [Some(Length::px(2.)), None]);
    for (placement, wrap_in_section, tops) in [
        (Placement::Sticky(top), false, [20., 2., 2., 2., 20.]),
        (Placement::Sticky(top), true, [20., 2., -16., -24., 20.]),
        (
            Placement::StickyInGridArea(top),
            false,
            [20., 2., -16., -24., 20.],
        ),
        (
            Placement::StickyInGridArea(top),
            true,
            [20., 2., -16., -24., 20.],
        ),
    ] {
        let mut tree = LayoutTree::<()>::new();
        let pane = tree.add_node(&tree.root(), column(120., 60.)).unwrap();
        tree.set_rules(
            &pane,
            scroll(ScrollStyle {
                overflow: Xy::new(Overflow::Visible, Overflow::Auto),
                ..Default::default()
            }),
        )
        .unwrap();
        tree.add_node(&pane, tile(120., 20.)).unwrap();
        let grid = tree.add_node(&pane, tile(120., 120.)).unwrap();
        tree.set_rules(
            &grid,
            NodeRules {
                grid: Some(TrackGrid {
                    tracks: Xy::new(
                        TrackAxis::repeat(1, Track::Pixels(120.)),
                        TrackAxis::repeat(2, Track::Pixels(60.)),
                    ),
                    align_items: Xy::new_symm(GridAlign::Start),
                    ..Default::default()
                }),
                ..Default::default()
            },
        )
        .unwrap();
        let section = if wrap_in_section {
            tree.add_node(&grid, column(120., 60.)).unwrap()
        } else {
            grid.clone()
        };
        let header = tree.add_node(&section, tile(120., 16.)).unwrap();
        tree.set_rules(
            &header,
            NodeRules {
                placement,
                ..Default::default()
            },
        )
        .unwrap();
        tree.add_node(&grid, tile(120., 60.)).unwrap();
        tree.add_node(&pane, tile(120., 100.)).unwrap();
        for (offset, top) in [0., 40., 80., 88., 0.].into_iter().zip(tops) {
            tree.set_scroll_offset(&pane, Xy::new(0., offset)).unwrap();
            solve(&mut tree, Xy::new(150., 140.));
            assert_eq!(
                tree.view_geometry(&header).unwrap().rect.y,
                [top, top + 16.]
            );
            assert!(tree.rule_issues().is_empty());
        }
    }
}

#[test]
fn a_bottom_sticky_action_keeps_the_sections_leading_padding_and_margin() {
    let mut tree = LayoutTree::<()>::new();
    let pane = tree.add_node(&tree.root(), column(120., 60.)).unwrap();
    tree.set_rules(
        &pane,
        scroll(ScrollStyle {
            overflow: Xy::new(Overflow::Visible, Overflow::Auto),
            ..Default::default()
        }),
    )
    .unwrap();
    tree.add_node(&pane, tile(120., 40.)).unwrap();
    let mut article = column(120., 80.);
    article.padding.y = [12., 8.];
    let section = tree.add_node(&pane, article).unwrap();
    tree.add_node(&section, tile(120., 40.)).unwrap();
    let mut action = tile(120., 16.);
    action.margin.y[0] = Margin::px(4.).unwrap();
    let action = tree.add_node(&section, action).unwrap();
    tree.set_rules(
        &action,
        NodeRules {
            placement: Placement::Sticky(Xy::new([None; 2], [None, Some(Length::px(2.))])),
            ..Default::default()
        },
    )
    .unwrap();
    tree.add_node(&pane, tile(120., 100.)).unwrap();
    for (offset, top) in [(0., 56.), (20., 42.), (50., 42.), (70., 26.), (0., 56.)] {
        tree.set_scroll_offset(&pane, Xy::new(0., offset)).unwrap();
        solve(&mut tree, Xy::new(150., 140.));
        assert_eq!(
            tree.view_geometry(&action).unwrap().rect.y,
            [top, top + 16.]
        );
        assert!(tree.rule_issues().is_empty());
    }
}

#[test]
fn a_sticky_spanning_item_uses_its_current_area_inside_a_scrolling_grid() {
    use keru_layout::tracks::GridLine;
    let mut tree = LayoutTree::<()>::new();
    let mut panel = tile(120., 80.);
    panel.padding.y = [8., 4.];
    let grid = tree.add_node(&tree.root(), panel).unwrap();
    let heading = tree.add_node(&grid, tile(120., 16.)).unwrap();
    let last_row = tree.add_node(&grid, tile(120., 96.)).unwrap();
    tree.set_rules(
        &last_row,
        NodeRules {
            grid_lines: Xy::new(None, Some([GridLine::Index(3), GridLine::Index(4)])),
            ..Default::default()
        },
    )
    .unwrap();
    for (first_row, end_line, offset, y) in [
        (36., 3, 0., 8.),
        (36., 3, 40., 2.),
        (36., 3, 80., -12.),
        (36., 2, 80., -52.),
        (46., 3, 80., -2.),
        (36., 3, 0., 8.),
    ] {
        let panel_rules = NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::repeat(1, Track::Pixels(120.)),
                    TrackAxis::Tracks(vec![
                        Track::Pixels(first_row),
                        Track::Pixels(36.),
                        Track::Pixels(96.),
                    ]),
                ),
                gap: Xy::new(0., 4.),
                align_items: Xy::new_symm(GridAlign::Start),
                ..Default::default()
            }),
            ..scroll(ScrollStyle {
                overflow: Xy::new(Overflow::Visible, Overflow::Auto),
                ..Default::default()
            })
        };
        tree.set_rules(&grid, panel_rules).unwrap();
        let heading_rules = NodeRules {
            placement: Placement::StickyInGridArea(Xy::new(
                [None; 2],
                [Some(Length::px(2.)), None],
            )),
            grid_lines: Xy::new(None, Some([GridLine::Index(1), GridLine::Index(end_line)])),
            ..Default::default()
        };
        tree.set_rules(&heading, heading_rules).unwrap();
        tree.set_scroll_offset(&grid, Xy::new(0., offset)).unwrap();
        solve(&mut tree, Xy::new(150., 140.));
        assert_eq!(tree.view_geometry(&grid).unwrap().offset.y, offset);
        assert_eq!(tree.view_geometry(&heading).unwrap().rect.y, [y, y + 16.]);
        assert!(tree.rule_issues().is_empty());
    }
}

#[test]
fn a_timeline_chip_can_stick_to_one_column_or_its_full_span() {
    use keru_layout::tracks::GridLine;
    let mut tree = LayoutTree::<()>::new();
    let pane = tree.add_node(&tree.root(), tile(90., 34.)).unwrap();
    tree.set_rules(
        &pane,
        NodeRules {
            scroll: ScrollStyle {
                overflow: Xy::new(Overflow::Auto, Overflow::Visible),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let timeline = tree.add_node(&pane, tile(221., 34.)).unwrap();
    tree.set_rules(
        &timeline,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::Tracks(vec![
                        Track::Pixels(31.),
                        Track::Pixels(67.),
                        Track::Pixels(109.),
                    ]),
                    TrackAxis::repeat(1, Track::Pixels(34.)),
                ),
                gap: Xy::new(7., 0.),
                align_items: Xy::new_symm(GridAlign::Start),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let chip = tree.add_node(&timeline, tile(18., 12.)).unwrap();
    let insets = Xy::new([Some(Length::px(5.)), None], [None; 2]);
    for (span_to, placement, expected) in [
        (
            3,
            Placement::StickyInGridArea(insets),
            [38., 8., 5., -3., -23., 38.],
        ),
        (3, Placement::Sticky(insets), [38., 8., 5., 5., 5., 38.]),
        (
            4,
            Placement::StickyInGridArea(insets),
            [38., 8., 5., 5., 5., 38.],
        ),
        (
            3,
            Placement::StickyInGridArea(insets),
            [38., 8., 5., -3., -23., 38.],
        ),
    ] {
        tree.set_rules(
            &chip,
            NodeRules {
                grid_lines: Xy::new(Some([GridLine::Index(2), GridLine::Index(span_to)]), None),
                placement,
                ..Default::default()
            },
        )
        .unwrap();
        for (offset, want) in [0., 30., 50., 90., 110., 0.].into_iter().zip(expected) {
            tree.set_scroll_offset(&pane, Xy::new(offset, 0.)).unwrap();
            solve(&mut tree, Xy::new(90., 34.));
            let chip_x = tree.view_geometry(&chip).unwrap().rect.x;
            assert_eq!(chip_x, [want, want + 18.]);
            assert_eq!(
                tree.view_geometry(&pane).unwrap().scroll_range.x,
                [0., 131.]
            );
            assert!(tree.rule_issues().is_empty() && tree.warnings().is_empty());
        }
    }
}

#[test]
fn a_squeezed_grid_keeps_content_and_padding_box_references_distinct() {
    use keru_layout::layout_rules::BoxReference;
    use keru_layout::tracks::GridLine;
    let mut tree = LayoutTree::<()>::new();
    let mut style = tile(44., 20.);
    style.padding.x = [18.; 2];
    let panel = tree.add_node(&tree.root(), style).unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::repeat(1, Track::Fr(1.)),
                    TrackAxis::repeat(1, Track::Pixels(20.)),
                ),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let marker = tree.add_node(&panel, tile(0., 6.)).unwrap();
    let insets = Xy::new([Some(Length::px(0.)); 2], [None; 2]);
    tree.set_rules(
        &marker,
        NodeRules {
            placement: Placement::StickyInGridArea(insets),
            ..Default::default()
        },
    )
    .unwrap();
    let mut fill = tile(0., 6.);
    fill.size.x = Size::Fill;
    let overlay = tree.add_node(&panel, fill).unwrap();
    tree.set_rules(
        &overlay,
        NodeRules {
            grid_lines: Xy::new(None, Some([GridLine::Index(1), GridLine::Index(2)])),
            placement: Placement::Absolute {
                containing: BoxReference::Node((*panel).clone()),
                insets,
            },
            ..Default::default()
        },
    )
    .unwrap();
    for (width, content_start) in [(44., 18.), (30., 18.), (10., 10.), (0., 0.), (44., 18.)] {
        style.size.x = Size::Pixels(width);
        tree.update_node_params(&panel, style).unwrap();
        solve(&mut tree, Xy::new(120., 60.));
        assert_eq!(
            tree.view_geometry(&marker).unwrap().rect.x,
            [content_start; 2]
        );
        assert_eq!(tree.view_geometry(&overlay).unwrap().rect.x, [0., width]);
        assert!(tree.rule_issues().is_empty());
    }
}
