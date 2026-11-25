//! Direct layouts for the automatic-minimum and equal-column CSS workarounds.
#![cfg(feature = "incremental")]

use keru_layout::{
    Anchor, Arrange, Axis, ChildrenLayout, LayoutParams, LayoutTree, Pos, Size, TextContent, Xy,
    flex::{FlexItem, FlexLayout, FlexMetrics},
    layout_rules::{NodeRules, Overflow, ScrollStyle},
};

fn box_size(width: Size, height: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(width, height),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}

fn stack(axis: Axis, gap: f32) -> LayoutParams {
    LayoutParams {
        children_layout: ChildrenLayout::Stack {
            axis,
            arrange: Arrange::Start,
            spacing: gap,
        },
        ..box_size(Size::Fill, Size::Fill)
    }
}

fn overflow(x: Overflow, y: Overflow) -> NodeRules {
    NodeRules {
        scroll: ScrollStyle {
            overflow: Xy::new(x, y),
            ..Default::default()
        },
        ..Default::default()
    }
}

#[test]
fn a_nested_title_yields_the_actions_space_without_a_zero_minimum() {
    let mut tree = LayoutTree::<()>::new();
    let row = tree.add_node(&tree.root(), stack(Axis::X, 8.)).unwrap();
    let mut slot_params = box_size(Size::Fill, Size::Fill);
    let slot = tree.add_node(&row, slot_params).unwrap();
    let title = tree
        .add_node(
            &slot,
            LayoutParams {
                text: TextContent::Fixed,
                ..box_size(Size::FitContent, Size::FitContent)
            },
        )
        .unwrap();
    let action = tree
        .add_node(&row, box_size(Size::Pixels(40.), Size::Fill))
        .unwrap();
    // Allocation and clipping are separate requests. Exercise both on the same tree.
    for paint in [Overflow::Visible, Overflow::Clip] {
        tree.set_rules(&slot, overflow(paint, Overflow::Visible))
            .unwrap();
        // Explicit zero is a CSS workaround. Check the default before applying it.
        for min in [None, Some(0.), Some(160.)] {
            slot_params.min_size.x = min.map(Size::Pixels);
            tree.update_node_params(&slot, slot_params).unwrap();
            for width in [224., 144., 224.] {
                tree.solve_layout_with_measure(Xy::new(width, 32.), |_, _, _| Xy::new(288., 16.));
                let slot_width = (width - 48.).max(min.unwrap_or(0.));
                assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
                assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
                assert_eq!(tree.layout(&slot).unwrap().x, [0., slot_width]);
                assert_eq!(
                    tree.layout(&action).unwrap().x,
                    [slot_width + 8., slot_width + 48.]
                );
                assert_eq!(tree.layout(&title).unwrap().x, [0., 288.]);
                assert_eq!(
                    tree.view_geometry(&title).unwrap().clip.x,
                    [
                        0.,
                        if paint == Overflow::Clip {
                            slot_width.min(width)
                        } else {
                            width
                        }
                    ]
                );
            }
        }
    }
}

#[test]
fn a_nested_scrollport_gets_the_space_below_a_fixed_header() {
    let mut tree = LayoutTree::<()>::new();
    let app = tree.add_node(&tree.root(), stack(Axis::Y, 0.)).unwrap();
    let header = tree
        .add_node(&app, box_size(Size::Fill, Size::Pixels(36.)))
        .unwrap();
    let mut pane_params = box_size(Size::Fill, Size::Fill);
    let pane = tree.add_node(&app, pane_params).unwrap();
    let list = tree.add_node(&pane, stack(Axis::Y, 0.)).unwrap();
    tree.set_rules(&list, overflow(Overflow::Clip, Overflow::Auto))
        .unwrap();
    let rows: Vec<_> = (0..8)
        .map(|_| {
            tree.add_node(&list, box_size(Size::Fill, Size::Pixels(30.)))
                .unwrap()
        })
        .collect();
    tree.set_scroll_offset(&list, Xy::new(0., 1000.)).unwrap();
    for min in [None, Some(Size::Pixels(0.))] {
        pane_params.min_size.y = min;
        tree.update_node_params(&pane, pane_params).unwrap();
        for height in [160., 112., 160.] {
            tree.solve_layout(Xy::new(224., height));
            assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
            assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
            assert_eq!(tree.view_geometry(&header).unwrap().rect.y, [0., 36.]);
            assert_eq!(tree.layout(&pane).unwrap().y, [36., height]);
            let view = tree.view_geometry(&list).unwrap();
            assert_eq!(view.scrollport.y, [36., height]);
            let max_scroll = 240. - (height - 36.);
            assert_eq!(view.scroll_range.y, [0., max_scroll]);
            assert_eq!(view.offset.y, max_scroll);
            assert_eq!(
                tree.view_geometry(rows.last().unwrap()).unwrap().rect.y,
                [height - 30., height]
            );
        }
    }
}

#[test]
fn equal_fill_cards_keep_equal_outer_widths_with_unequal_padding() {
    let mut tree = LayoutTree::<()>::new();
    let shelf = tree.add_node(&tree.root(), stack(Axis::X, 0.)).unwrap();
    let mut cards = Vec::new();
    for padding in [0., 18., 0.] {
        let params = LayoutParams {
            padding: Xy::new([padding; 2], [0.; 2]),
            ..box_size(Size::Fill, Size::Fill)
        };
        let card = tree.add_node(&shelf, params).unwrap();
        let content = tree
            .add_node(&card, box_size(Size::Fill, Size::Fill))
            .unwrap();
        cards.push((card, content, padding));
    }
    for width in [300., 240., 300.] {
        tree.solve_layout(Xy::new(width, 40.));
        assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
        assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
        let share = width / 3.;
        for (index, (card, content, padding)) in cards.iter().enumerate() {
            let start = index as f32 * share;
            let end = start + share;
            assert_eq!(tree.layout(card).unwrap().x, [start, end]);
            assert_eq!(
                tree.layout(content).unwrap().x,
                [start + padding, end - padding]
            );
        }
    }

    // Equal growth from different starting widths carries a different instruction.
    let items = [40., 116., 72.].map(|w| FlexMetrics {
        preferred: Xy::new(w, 16.),
        item: FlexItem {
            grow: 1.,
            ..Default::default()
        },
        ..Default::default()
    });
    let grown = FlexLayout::default().resolve(Xy::new(300., 40.), &items);
    assert_eq!(
        grown.iter().map(|r| r.x[1] - r.x[0]).collect::<Vec<_>>(),
        [64., 140., 96.]
    );
}
