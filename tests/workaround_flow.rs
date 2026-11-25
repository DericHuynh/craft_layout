#![cfg(feature = "incremental")]

use keru_layout::flex::{FlexItem, FlexLayout};
use keru_layout::layout_rules::{
    BlockStyle, BoxReference, Clear, Float, Length, NodeRules, Overflow, Placement, ScrollStyle,
};
use keru_layout::{Anchor, Axis, ChildrenLayout, LayoutParams, LayoutTree, Margin, Pos, Size, Xy};

fn block(width: Size, height: Size) -> LayoutParams {
    LayoutParams {
        children_layout: ChildrenLayout::Block,
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        size: Xy::new(width, height),
        ..LayoutParams::DEFAULT
    }
}

fn solve(tree: &mut LayoutTree<()>, window: Xy<f32>, check: impl Fn(&LayoutTree<()>)) {
    tree.solve_layout(window);
    assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
    check(tree);
    #[cfg(feature = "batch-pilot")]
    {
        tree.invalidate();
        tree.solve_layout_batch(window).unwrap();
        assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
        check(tree);
    }
}

#[derive(Debug, Copy, Clone)]
enum FloatBoundary {
    Ordinary,
    Isolated,
    OverflowHidden,
    Clearfix,
}

// Rachel Andrew's float enclosure example, with an overhanging status badge.
// https://rachelandrew.co.uk/archives/2017/01/24/the-end-of-the-clearfix-hack/
#[test]
fn article_card_encloses_the_thumbnail_without_clipping_its_badge() {
    use FloatBoundary::*;
    for (boundary, expected_height, visible_width) in [
        (Isolated, 64., 20.),
        (Ordinary, 16., 20.),
        (OverflowHidden, 64., 8.),
        (Clearfix, 64., 20.),
    ] {
        let mut tree = LayoutTree::<()>::new();
        let page = tree
            .add_node(&tree.root(), block(Size::Fill, Size::Fill))
            .unwrap();
        let mut card_params = block(Size::Pixels(160.), Size::FitContent);
        card_params.isolate_block_margins = matches!(boundary, Isolated);
        let card = tree.add_node(&page, card_params).unwrap();
        if matches!(boundary, OverflowHidden) {
            tree.set_rules(
                &card,
                NodeRules {
                    scroll: ScrollStyle {
                        overflow: Xy::new_symm(Overflow::Hidden),
                        ..Default::default()
                    },
                    ..Default::default()
                },
            )
            .unwrap();
        }
        let picture = tree
            .add_node(&card, block(Size::Pixels(40.), Size::Pixels(64.)))
            .unwrap();
        tree.set_rules(
            &picture,
            NodeRules {
                block_flow: BlockStyle {
                    float: Float::Left,
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap();
        tree.add_node(&card, block(Size::Auto, Size::Pixels(16.)))
            .unwrap();
        if matches!(boundary, Clearfix) {
            let clear = tree
                .add_node(&card, block(Size::Auto, Size::Pixels(0.)))
                .unwrap();
            tree.set_rules(
                &clear,
                NodeRules {
                    block_flow: BlockStyle {
                        clear: Clear::Both,
                        ..Default::default()
                    },
                    ..Default::default()
                },
            )
            .unwrap();
        }
        let badge = tree
            .add_node(&card, block(Size::Pixels(20.), Size::Pixels(12.)))
            .unwrap();
        tree.set_rules(
            &badge,
            NodeRules {
                placement: Placement::Absolute {
                    containing: BoxReference::Parent,
                    insets: Xy::new(
                        [
                            Some(Length {
                                fraction: 1.,
                                pixels: -8.,
                            }),
                            None,
                        ],
                        [Some(Length::px(0.)), None],
                    ),
                },
                ..Default::default()
            },
        )
        .unwrap();
        let byline = tree
            .add_node(&page, block(Size::Auto, Size::Pixels(12.)))
            .unwrap();
        for width in [160., 120., 160.] {
            card_params.size.x = Size::Pixels(width);
            tree.update_node_params(&card, card_params).unwrap();
            solve(&mut tree, Xy::new(260., 180.), |tree| {
                assert_eq!(tree.layout(&picture).unwrap().y, [0., 64.], "{boundary:?}");
                assert_eq!(
                    tree.layout(&card).unwrap().y,
                    [0., expected_height],
                    "{boundary:?}"
                );
                assert_eq!(
                    tree.layout(&byline).unwrap().y[0],
                    expected_height,
                    "{boundary:?}"
                );
                let view = tree.view_geometry(&badge).unwrap();
                assert_eq!(view.rect.x, [width - 8., width + 12.], "{boundary:?}");
                let visible =
                    view.rect.x[1].min(view.clip.x[1]) - view.rect.x[0].max(view.clip.x[0]);
                assert_eq!(visible, visible_width, "{boundary:?}");
            });
        }
    }
}

// The separator padding workaround adds a real pixel to the card.
// https://www.smashingmagazine.com/2019/07/margins-in-css/
#[test]
fn card_contains_the_heading_margin_at_its_requested_distance() {
    let mut tree = LayoutTree::<()>::new();
    let page = tree
        .add_node(&tree.root(), block(Size::Fill, Size::Fill))
        .unwrap();
    let mut card_params = block(Size::Auto, Size::FitContent);
    let card = tree.add_node(&page, card_params).unwrap();
    let mut heading_params = block(Size::Auto, Size::Pixels(20.));
    heading_params.margin.y[0] = Margin::px(12.).unwrap();
    let heading = tree.add_node(&card, heading_params).unwrap();
    for (isolate, separator, card_edges, inset) in [
        (true, 0., [0., 32.], 12.),
        (false, 0., [12., 32.], 0.),
        (false, 1., [0., 33.], 13.),
        (true, 0., [0., 32.], 12.),
    ] {
        card_params.isolate_block_margins = isolate;
        card_params.padding.y[0] = separator;
        tree.update_node_params(&card, card_params).unwrap();
        solve(&mut tree, Xy::new(260., 180.), |tree| {
            let card_edges_actual = tree.layout(&card).unwrap().y;
            assert_eq!(
                card_edges_actual, card_edges,
                "isolate={isolate}, padding={separator}"
            );
            assert_eq!(
                tree.layout(&heading).unwrap().y[0] - card_edges_actual[0],
                inset
            );
        });
    }
}

// Philip Walton's unknown-height footer, where only the content area grows.
// https://philipwalton.github.io/solved-by-flexbox/demos/sticky-footer/
#[test]
fn reader_footer_follows_content_or_reaches_the_viewport_bottom() {
    let mut tree = LayoutTree::<()>::new();
    let mut page_params = block(Size::Fill, Size::FitContent);
    page_params.min_size.y = Some(Size::Frac(1.));
    let page = tree.add_node(&tree.root(), page_params).unwrap();
    tree.set_rules(
        &page,
        NodeRules {
            flex: Some(FlexLayout {
                axis: Axis::Y,
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    tree.add_node(&page, block(Size::Auto, Size::Pixels(20.)))
        .unwrap();
    let main = tree
        .add_node(&page, block(Size::Auto, Size::FitContent))
        .unwrap();
    tree.set_rules(
        &main,
        NodeRules {
            flex_item: FlexItem {
                grow: 1.,
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let story = tree
        .add_node(&main, block(Size::Auto, Size::Pixels(24.)))
        .unwrap();
    let footer = tree
        .add_node(&page, block(Size::Auto, Size::FitContent))
        .unwrap();
    let links = tree
        .add_node(&footer, block(Size::Auto, Size::Pixels(30.)))
        .unwrap();
    for (viewport, content, links_height, footer_top) in [
        (120., 24., 30., 90.),
        (120., 175., 30., 195.),
        (120., 175., 44., 195.),
        (120., 24., 44., 76.),
        (160., 24., 44., 116.),
        (120., 24., 30., 90.),
    ] {
        tree.update_node_params(&story, block(Size::Auto, Size::Pixels(content)))
            .unwrap();
        tree.update_node_params(&links, block(Size::Auto, Size::Pixels(links_height)))
            .unwrap();
        solve(&mut tree, Xy::new(260., viewport), |tree| {
            assert_eq!(
                tree.layout(&footer).unwrap().y,
                [footer_top, footer_top + links_height],
                "viewport={viewport} story={content} links={links_height}"
            );
            assert_eq!(tree.layout(&main).unwrap().y, [20., footer_top]);
            assert_eq!(tree.layout(&story).unwrap().y, [20., 20. + content]);
            assert_eq!(
                tree.layout(&page).unwrap().y,
                [0., footer_top + links_height]
            );
        });
    }
}

// The fixed deduction from Chris Coyier's calc() example assumes a known footer
// height. With no bottom margin, the deduction is exactly that height.
// https://codepen.io/chriscoyier/pen/jqRXBz/
#[test]
fn a_guessed_footer_reservation_expires_when_the_footer_grows() {
    let mut tree = LayoutTree::<()>::new();
    let page = tree
        .add_node(&tree.root(), block(Size::Fill, Size::FitContent))
        .unwrap();
    let viewport = 120.;
    let guessed_footer_height = 30.;
    let mut wrapper_params = block(Size::Auto, Size::FitContent);
    wrapper_params.min_size.y = Some(Size::Pixels(viewport - guessed_footer_height));
    let wrapper = tree.add_node(&page, wrapper_params).unwrap();
    tree.add_node(&wrapper, block(Size::Auto, Size::Pixels(20.)))
        .unwrap();
    tree.add_node(&wrapper, block(Size::Auto, Size::Pixels(24.)))
        .unwrap();
    let footer = tree
        .add_node(&page, block(Size::Auto, Size::FitContent))
        .unwrap();
    let links = tree
        .add_node(&footer, block(Size::Auto, Size::Pixels(30.)))
        .unwrap();
    for (height, expected_bottom) in [(30., 120.), (44., 134.)] {
        tree.update_node_params(&links, block(Size::Auto, Size::Pixels(height)))
            .unwrap();
        solve(&mut tree, Xy::new(260., viewport), |tree| {
            assert_eq!(tree.layout(&footer).unwrap().y, [90., expected_bottom]);
        });
    }
}
