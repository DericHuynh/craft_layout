#![cfg(feature = "incremental")]

use keru_layout::layout_rules::{BoxReference, NodeRules, Overflow, Placement, ScrollStyle};
use keru_layout::tracks::{Track, TrackAxis, TrackContribution, TrackGrid, TrackMax, TrackMin};
use keru_layout::{Anchor, Arrange, Axis, ChildrenLayout, LayoutParams, LayoutTree, Pos, Size, Xy};

fn item(width: Size, height: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(width, height),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..Default::default()
    }
}

fn columns(template: TrackAxis, gap: f32) -> TrackGrid {
    TrackGrid {
        tracks: Xy::new(template, TrackAxis::default()),
        gap: Xy::new(gap, 0.),
        ..Default::default()
    }
}

fn horizontal_scroll() -> ScrollStyle {
    ScrollStyle {
        overflow: Xy::new(Overflow::Auto, Overflow::Visible),
        ..Default::default()
    }
}

// https://defensivecss.dev/tip/grid-min-content-size/
#[test]
fn carousel_scrolls_inside_its_column_with_a_plain_fractional_track() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let main = tree
        .add_node(&root, item(Size::Auto, Size::Pixels(30.)))
        .unwrap();
    let sidebar = tree
        .add_node(&root, item(Size::Auto, Size::Pixels(30.)))
        .unwrap();
    let carousel = tree
        .add_node(
            &main,
            LayoutParams {
                children_layout: ChildrenLayout::Stack {
                    axis: Axis::X,
                    arrange: Arrange::Start,
                    spacing: 0.,
                },
                ..item(Size::Fill, Size::Pixels(20.))
            },
        )
        .unwrap();
    tree.set_rules(
        &carousel,
        NodeRules {
            scroll: horizontal_scroll(),
            ..Default::default()
        },
    )
    .unwrap();
    let cards: Vec<_> = (0..3)
        .map(|_| {
            tree.add_node(&carousel, item(Size::Pixels(120.), Size::Pixels(20.)))
                .unwrap()
        })
        .collect();
    for (track, floor, hard) in [
        (Track::Fr(1.), None, false),
        (
            Track::MinMax(TrackMin::Pixels(0.), TrackMax::Fr(1.)),
            None,
            false,
        ),
        (
            Track::MinMax(TrackMin::Content, TrackMax::Fr(1.)),
            Some(Size::Pixels(360.)),
            true,
        ),
    ] {
        tree.set_rules(
            &root,
            NodeRules {
                grid: Some(columns(
                    TrackAxis::Tracks(vec![track, Track::Pixels(72.)]),
                    12.,
                )),
                scroll: horizontal_scroll(),
                ..Default::default()
            },
        )
        .unwrap();
        tree.set_rules(
            &main,
            NodeRules {
                grid_content_minimum: Xy::new(floor, None),
                ..Default::default()
            },
        )
        .unwrap();
        for window in [320., 260., 320.] {
            tree.solve_layout(Xy::new(window, 60.));
            let main_width = if hard { 360. } else { window - 84. };
            assert!(tree.rule_issues().is_empty());
            assert_eq!(tree.layout(&main).unwrap().x, [0., main_width]);
            assert_eq!(
                tree.layout(&sidebar).unwrap().x,
                [main_width + 12., main_width + 84.]
            );
            for (index, card) in cards.iter().enumerate() {
                assert_eq!(
                    tree.layout(card).unwrap().x,
                    [120. * index as f32, 120. * (index + 1) as f32]
                );
            }
            assert_eq!(
                tree.view_geometry(&carousel).unwrap().scroll_range.x,
                [0., 360. - main_width]
            );
            assert_eq!(
                tree.view_geometry(&root).unwrap().scroll_range.x,
                [0., main_width + 84. - window]
            );
        }
    }
}

// https://smolcss.dev/#smol-responsive-css-grid
#[test]
fn a_responsive_card_can_fit_within_the_container_or_enforce_its_minimum() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let cards: Vec<_> = (0..3)
        .map(|_| {
            tree.add_node(&root, item(Size::Auto, Size::Pixels(20.)))
                .unwrap()
        })
        .collect();
    for (template, hard) in [
        (TrackAxis::auto_fit_within(120.), false),
        (
            TrackAxis::AutoFit {
                minimum: 120.,
                track: Track::Fr(1.),
            },
            true,
        ),
    ] {
        tree.set_rules(
            &root,
            NodeRules {
                grid: Some(columns(template, 10.)),
                scroll: horizontal_scroll(),
                ..Default::default()
            },
        )
        .unwrap();
        for (window, count, width) in [
            (380., 3, 120.),
            (379., 2, 184.5),
            (250., 2, 120.),
            (249., 1, 249.),
            (120., 1, 120.),
            (90., 1, 90.),
            (0., 1, 0.),
            (380., 3, 120.),
        ] {
            tree.solve_layout(Xy::new(window, 100.));
            assert!(tree.rule_issues().is_empty());
            let used = if hard && window < 120. { 120. } else { width };
            assert_eq!(
                tree.resolved_grid_tracks(&root, Axis::X)
                    .unwrap()
                    .unwrap()
                    .len(),
                count
            );
            for (i, card) in cards.iter().enumerate() {
                let x = (i % count) as f32 * (used + 10.);
                let y = (i / count) as f32 * 20.;
                let rect = tree.layout(card).unwrap();
                assert_eq!(rect.x, [x, x + used]);
                assert_eq!(rect.y, [y, y + 20.]);
            }
            assert_eq!(
                tree.view_geometry(&root).unwrap().scroll_range.x,
                [0., (used - window).max(0.)]
            );
        }
    }
}

// https://ishadeed.com/article/defensive-css/#auto-fit-vs-auto-fill
#[test]
fn sparse_catalogs_can_expand_cards_or_preserve_empty_slots() {
    for fit in [true, false] {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let track = Track::Fr(1.);
        let axis = if fit {
            TrackAxis::AutoFit {
                minimum: 120.,
                track,
            }
        } else {
            TrackAxis::AutoFill {
                minimum: 120.,
                track,
            }
        };
        tree.set_rules(
            &root,
            NodeRules {
                grid: Some(columns(axis, 10.)),
                ..Default::default()
            },
        )
        .unwrap();
        let mut cards = Vec::new();
        for (i, fit_width) in [380., 185., 120., 120.].into_iter().enumerate() {
            cards.push(
                tree.add_node(&root, item(Size::Auto, Size::Pixels(20.)))
                    .unwrap(),
            );
            tree.solve_layout(Xy::new(380., 100.));
            let width = if fit { fit_width } else { 120. };
            let x = (i % 3) as f32 * (width + 10.);
            let y = (i / 3) as f32 * 20.;
            assert!(tree.rule_issues().is_empty());
            assert_eq!(tree.layout(&cards[0]).unwrap().x, [0., width]);
            let rect = tree.layout(&cards[i]).unwrap();
            assert_eq!(rect.x, [x, x + width]);
            assert_eq!(rect.y, [y, y + 20.]);
        }
    }
}

// https://www.hsablonniere.com/prevent-layout-shifts-with-css-grid-stacks--qcj5jo/
#[test]
fn overlapping_chart_and_help_size_to_the_tallest_in_flow_panel() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let group = tree
        .add_node(
            &root,
            LayoutParams {
                children_layout: ChildrenLayout::Free,
                ..item(Size::Pixels(200.), Size::FitContent)
            },
        )
        .unwrap();
    let chart = tree
        .add_node(&group, item(Size::Fill, Size::Pixels(42.)))
        .unwrap();
    let help = tree
        .add_node(&group, item(Size::Fill, Size::Pixels(70.)))
        .unwrap();
    for (chart_height, group_height) in [(42., 70.), (90., 90.), (42., 70.)] {
        tree.update_node_params(&chart, item(Size::Fill, Size::Pixels(chart_height)))
            .unwrap();
        tree.solve_layout(Xy::new(200., 100.));
        assert!(tree.rule_issues().is_empty());
        assert_eq!(tree.layout(&chart).unwrap().y, [0., chart_height]);
        assert_eq!(tree.layout(&help).unwrap().y, [0., 70.]);
        assert_eq!(tree.layout(&group).unwrap().y, [0., group_height]);
    }
    tree.set_rules(
        &help,
        NodeRules {
            placement: Placement::Absolute {
                containing: BoxReference::Parent,
                insets: Default::default(),
            },
            ..Default::default()
        },
    )
    .unwrap();
    tree.solve_layout(Xy::new(200., 100.));
    assert!(tree.rule_issues().is_empty());
    assert_eq!(tree.layout(&group).unwrap().y, [0., 42.]);
    assert_eq!(tree.layout(&help).unwrap().y, [0., 70.]);
}

#[test]
fn a_capped_percentage_uses_content_until_the_grid_has_a_definite_extent() {
    let floor = TrackMin::CappedPercent {
        fraction: 0.5,
        pixels: 40.,
    };
    let bounds = |min, max| columns(TrackAxis::repeat(1, Track::MinMax(min, max)), 0.);
    let contribution = [TrackContribution {
        tracks: 0..1,
        minimum: 70.,
        preferred: 95.,
    }];
    for min in [floor, TrackMin::Percent(0.5)] {
        assert_eq!(
            bounds(min, TrackMax::Fr(1.)).intrinsic_extents(Axis::X, 1, &contribution),
            (70., 95.)
        );
    }
    // A definite zero maximum isolates the minimum; a track's minimum wins over its maximum.
    let capped = bounds(floor, TrackMax::Pixels(0.));
    for (extent, expected) in [(0., 0.), (50., 25.), (200., 40.)] {
        assert_eq!(
            capped.resolve_axis(Axis::X, Some(extent), 1, &[]).0,
            [[0., expected]]
        );
    }
}
