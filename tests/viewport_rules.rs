#![cfg(feature = "incremental")]
use keru_layout::layout_rules::{
    BoxReference, Edges, Length, NodeRules, Overflow, Placement, RuleIssue, ScrollStyle, Side,
};
use keru_layout::{Anchor, Arrange, Axis, ChildrenLayout, LayoutParams, LayoutTree, Pos, Size, Xy};

fn box_size(w: f32, h: f32) -> LayoutParams {
    LayoutParams {
        size: Xy::new(Size::Pixels(w), Size::Pixels(h)),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}

fn column(w: f32, h: f32) -> LayoutParams {
    LayoutParams {
        children_layout: ChildrenLayout::Stack {
            axis: Axis::Y,
            arrange: Arrange::Start,
            spacing: 0.,
        },
        ..box_size(w, h)
    }
}

fn top(y: f32) -> Edges {
    Xy::new([None; 2], [Some(Length::px(y)), None])
}

#[test]
fn sticky_stops_at_its_section_and_fixed_control_stays_in_window() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let panel = tree.add_node(&root, column(100., 70.)).unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            scroll: ScrollStyle {
                overflow: Xy::new(Overflow::Clip, Overflow::Auto),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let section = tree.add_node(&panel, column(100., 70.)).unwrap();
    let header = tree.add_node(&section, box_size(100., 20.)).unwrap();
    tree.set_rules(
        &header,
        NodeRules {
            placement: Placement::Sticky(top(0.)),
            ..Default::default()
        },
    )
    .unwrap();
    tree.add_node(&section, box_size(100., 50.)).unwrap();
    tree.add_node(&panel, box_size(100., 90.)).unwrap();
    let fixed = tree.add_node(&section, box_size(12., 12.)).unwrap();
    tree.set_rules(
        &fixed,
        NodeRules {
            placement: Placement::Fixed(top(4.)),
            ..Default::default()
        },
    )
    .unwrap();
    let window = Xy::new(220., 120.);
    for (asked, clipped, y) in [
        (0., 0., 0.),
        (40., 40., 0.),
        (60., 60., -10.),
        (200., 90., -40.),
    ] {
        tree.set_scroll_offset(&panel, Xy::new(0., asked)).unwrap();
        tree.solve_layout(window);
        assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
        let scroll = tree.view_geometry(&panel).unwrap();
        assert_eq!(scroll.scroll_range.y, [0., 90.]);
        assert_eq!(scroll.offset.y, clipped);
        let header = tree.view_geometry(&header).unwrap();
        assert_eq!(header.rect.y, [y, y + 20.]);
        assert_eq!(header.clip, Xy::new([0., 100.], [0., 70.]));
        let fixed = tree.view_geometry(&fixed).unwrap();
        assert_eq!(fixed.rect.y, [4., 16.]);
        assert_eq!(fixed.clip, Xy::new([0., 220.], [0., 120.]));
    }
}

#[test]
fn auto_gutter_changes_inline_fill_and_disappears_when_content_fits() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let panel = tree.add_node(&root, column(100., 70.)).unwrap();
    let mut parameters = LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(100.)),
        ..LayoutParams::DEFAULT
    };
    let sheet = tree.add_node(&panel, parameters).unwrap();
    let rules = NodeRules {
        scroll: ScrollStyle {
            overflow: Xy::new(Overflow::Clip, Overflow::Auto),
            scrollbar: Xy::new(0., 9.),
            stable_gutter: false,
        },
        ..Default::default()
    };
    tree.set_rules(&panel, rules.clone()).unwrap();
    let window = Xy::new(220., 120.);
    tree.solve_layout(window);
    assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
    assert_eq!(tree.view_geometry(&panel).unwrap().scrollport.x, [0., 91.]);
    assert_eq!(tree.layout(&sheet).unwrap().x, [0., 91.]);
    parameters.size.y = Size::Pixels(60.);
    tree.update_node_params(&sheet, parameters).unwrap();
    tree.solve_layout(window);
    assert_eq!(tree.view_geometry(&panel).unwrap().scrollport.x, [0., 100.]);
    assert_eq!(tree.layout(&sheet).unwrap().x, [0., 100.]);
    tree.set_rules(
        &panel,
        NodeRules {
            scroll: ScrollStyle {
                stable_gutter: true,
                ..rules.scroll
            },
            ..rules
        },
    )
    .unwrap();
    tree.solve_layout(window);
    assert_eq!(tree.layout(&sheet).unwrap().x, [0., 91.]);
}

#[test]
fn popup_can_anchor_to_a_later_sibling_and_select_a_visible_side() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let popup = tree.add_node(&root, box_size(40., 20.)).unwrap();
    let target = tree
        .add_node(
            &root,
            LayoutParams {
                position: Xy::new(Pos::Pixels(30.), Pos::Pixels(80.)),
                ..box_size(20., 12.)
            },
        )
        .unwrap();
    let popup_rule = NodeRules {
        placement: Placement::Anchor {
            target: (&*target).clone(),
            sides: vec![Side::Below, Side::Above],
            gap: 2.,
        },
        ..Default::default()
    };
    tree.set_rules(&popup, popup_rule).unwrap();
    let window = Xy::new(150., 100.);
    tree.solve_layout(window);
    assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
    assert_eq!(
        tree.view_geometry(&popup).unwrap().rect,
        Xy::new([30., 70.], [58., 78.])
    );
    tree.set_rules(
        &target,
        NodeRules {
            placement: Placement::Relative(Xy::new(Length::px(0.), Length::px(-50.))),
            ..Default::default()
        },
    )
    .unwrap();
    tree.solve_layout(window);
    assert_eq!(tree.view_geometry(&popup).unwrap().rect.y, [44., 64.]);
    tree.remove(&target).unwrap();
    tree.solve_layout(window);
    assert!(
        tree.rule_issues()
            .contains(&RuleIssue::MissingReference((&*popup).clone()))
    );
}

#[test]
fn positioned_box_can_span_both_insets_against_an_explicit_ancestor() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let panel = tree
        .add_node(
            &root,
            LayoutParams {
                position: Xy::new(Pos::Pixels(10.), Pos::Pixels(7.)),
                ..box_size(100., 50.)
            },
        )
        .unwrap();
    let wrapper = tree
        .add_node(
            &panel,
            LayoutParams {
                position: Xy::new(Pos::Pixels(30.), Pos::Pixels(10.)),
                ..box_size(40., 20.)
            },
        )
        .unwrap();
    let overlay = tree
        .add_node(
            &wrapper,
            LayoutParams {
                size: Xy::new(Size::Auto, Size::Pixels(12.)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    tree.set_rules(
        &overlay,
        NodeRules {
            placement: Placement::Absolute {
                containing: BoxReference::Node((&*panel).clone()),
                insets: Xy::new(
                    [
                        Some(Length {
                            fraction: 0.1,
                            pixels: 0.,
                        }),
                        Some(Length::px(5.)),
                    ],
                    [Some(Length::px(2.)), None],
                ),
            },
            ..Default::default()
        },
    )
    .unwrap();
    tree.solve_layout(Xy::new(200., 100.));
    let expected = Xy::new([20., 105.], [9., 21.]);
    assert_eq!(tree.view_geometry(&overlay).unwrap().rect, expected);
    assert_eq!(tree.layout(&overlay).unwrap(), expected);
    let mut resized = *tree.params(&overlay).unwrap();
    resized.size.x = Size::Frac(0.6);
    resized.max_size.x = Some(Size::Frac(0.5));
    tree.update_node_params(&overlay, resized).unwrap();
    tree.solve_layout(Xy::new(200., 100.));
    assert_eq!(tree.view_geometry(&overlay).unwrap().rect.x, [20., 70.]);
    assert_eq!(tree.layout(&overlay).unwrap().x, [20., 70.]);
}

#[test]
fn nested_scrollports_propagate_visible_overflow_on_each_axis_independently() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let outer = tree.add_node(&root, box_size(80., 80.)).unwrap();
    let inner = tree
        .add_node(
            &outer,
            LayoutParams {
                position: Xy::new(Pos::Pixels(10.), Pos::Pixels(50.)),
                ..box_size(50., 50.)
            },
        )
        .unwrap();
    let child = tree
        .add_node(
            &inner,
            LayoutParams {
                position: Xy::new(Pos::Start, Pos::Pixels(30.)),
                ..box_size(130., 100.)
            },
        )
        .unwrap();
    for (id, overflow) in [
        (&outer, Xy::new(Overflow::Clip, Overflow::Hidden)),
        (&inner, Xy::new(Overflow::Visible, Overflow::Auto)),
    ] {
        tree.set_rules(
            id,
            NodeRules {
                scroll: ScrollStyle {
                    overflow,
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap();
    }
    tree.set_scroll_offset(&outer, Xy::new(30., 100.)).unwrap();
    tree.set_scroll_offset(&inner, Xy::new(30., 25.)).unwrap();
    tree.solve_layout(Xy::new(200., 200.));
    let panel = tree.view_geometry(&outer).unwrap();
    assert_eq!(panel.content, Xy::new([0., 140.], [0., 100.]));
    assert_eq!(panel.offset, Xy::new(0., 20.));
    let view = tree.view_geometry(&child).unwrap();
    assert_eq!(view.rect, Xy::new([10., 140.], [35., 135.]));
    assert_eq!(view.clip, Xy::new([0., 80.], [30., 80.]));
    assert!(tree.rule_issues().is_empty());
}

#[test]
fn a_mutual_anchor_cycle_has_a_deterministic_fallback() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let a = tree.add_node(&root, box_size(30., 15.)).unwrap();
    let b = tree.add_node(&root, box_size(10., 12.)).unwrap();
    for (item, target) in [(&a, &b), (&b, &a)] {
        tree.set_rules(
            item,
            NodeRules {
                placement: Placement::Anchor {
                    target: (**target).clone(),
                    sides: vec![Side::Right],
                    gap: 2.,
                },
                ..Default::default()
            },
        )
        .unwrap();
    }
    tree.solve_layout(Xy::new(100., 60.));
    assert_eq!(
        tree.rule_issues(),
        &[RuleIssue::CyclicReference((*a).clone())]
    );
    assert_eq!(tree.view_geometry(&a).unwrap().rect.x, [0., 30.]);
    assert_eq!(tree.view_geometry(&b).unwrap().rect.x, [32., 42.]);
}
