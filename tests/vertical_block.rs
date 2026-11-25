#![cfg(feature = "incremental")]

use keru_layout::layout_rules::NodeRules;
use keru_layout::{
    Anchor, ChildrenLayout, Destination, Direction, LayoutParams, LayoutTree, Logical, LogicalAxis,
    LogicalStyle, Margin, Pos, Size, WritingMode, Xy,
};

fn box_at_start() -> LayoutParams {
    LayoutParams {
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}
fn px(value: f32) -> Option<Margin> {
    Margin::px(value)
}

#[test]
fn mixed_margins_and_inline_auto_size_rotate_with_the_block_and_preserve_order() {
    for (mode, direction, first, second, inline) in [
        (
            WritingMode::HorizontalTb,
            Direction::Ltr,
            [8., 28.],
            [43., 63.],
            [2., 96.],
        ),
        (
            WritingMode::VerticalLr,
            Direction::Ltr,
            [8., 28.],
            [43., 63.],
            [2., 96.],
        ),
        (
            WritingMode::VerticalRl,
            Direction::Rtl,
            [92., 112.],
            [57., 77.],
            [4., 98.],
        ),
    ] {
        let mut tree = LayoutTree::<()>::new();
        let panel = tree
            .add_node(
                &tree.root(),
                LayoutParams {
                    children_layout: ChildrenLayout::Block,
                    ..box_at_start()
                },
            )
            .unwrap();
        let rules = LogicalStyle {
            writing_mode: Some(mode),
            direction: Some(direction),
            size: Logical::new(Some(Size::Pixels(100.)), Some(Size::Pixels(120.))),
            padding: Logical::new([None, None], [Some(3.), Some(4.)]),
            ..Default::default()
        };
        tree.set_rules(
            &panel,
            NodeRules {
                logical: rules,
                ..Default::default()
            },
        )
        .unwrap();
        let a = tree.add_node(&panel, box_at_start()).unwrap();
        let b = tree.add_node(&panel, box_at_start()).unwrap();
        for (id, start, end) in [(&a, 5., 10.), (&b, 15., 7.)] {
            tree.set_rules(
                id,
                NodeRules {
                    logical: LogicalStyle {
                        size: Logical::new(Some(Size::Auto), Some(Size::Pixels(20.))),
                        margin: Logical::new([px(2.), px(4.)], [px(start), px(end)]),
                        ..Default::default()
                    },
                    ..Default::default()
                },
            )
            .unwrap();
        }
        let window = Xy::new(160., 160.);
        tree.solve_layout(window);
        assert!(
            tree.rule_issues().is_empty(),
            "{mode:?} {:?}",
            tree.rule_issues()
        );
        let block = rules.context(Default::default()).axis(LogicalAxis::Block);
        assert_eq!(tree.layout(&a).unwrap()[block], first, "{mode:?}");
        assert_eq!(tree.layout(&b).unwrap()[block], second, "{mode:?}");
        assert_eq!(tree.layout(&a).unwrap()[block.other()], inline, "{mode:?}");
        #[cfg(feature = "batch-pilot")]
        {
            tree.invalidate();
            tree.solve_layout_batch(window).unwrap();
            assert_eq!(tree.layout(&b).unwrap()[block], second);
        }
    }
}

#[test]
fn nested_vertical_block_exports_its_margin_until_padding_separates_it() {
    let mut tree = LayoutTree::<()>::new();
    let panel = tree
        .add_node(
            &tree.root(),
            LayoutParams {
                children_layout: ChildrenLayout::Block,
                size: Xy::new(Size::Pixels(120.), Size::Pixels(80.)),
                ..box_at_start()
            },
        )
        .unwrap();
    let logical = LogicalStyle {
        writing_mode: Some(WritingMode::VerticalLr),
        ..Default::default()
    };
    tree.set_rules(
        &panel,
        NodeRules {
            logical,
            ..Default::default()
        },
    )
    .unwrap();
    let group = tree
        .add_node(
            &panel,
            LayoutParams {
                children_layout: ChildrenLayout::Block,
                size: Xy::new(Size::FitContent, Size::Auto),
                ..box_at_start()
            },
        )
        .unwrap();
    let child = tree
        .add_node(
            &group,
            LayoutParams {
                size: Xy::new(Size::Pixels(20.), Size::Auto),
                margin: Xy::new([px(7.).unwrap(), px(9.).unwrap()], [Margin::ZERO; 2]),
                ..box_at_start()
            },
        )
        .unwrap();
    let next = tree
        .add_node(
            &panel,
            LayoutParams {
                size: Xy::new(Size::Pixels(15.), Size::Auto),
                margin: Xy::new([px(-3.).unwrap(), Margin::ZERO], [Margin::ZERO; 2]),
                ..box_at_start()
            },
        )
        .unwrap();
    let window = Xy::new(200., 160.);
    tree.solve_layout(window);
    assert_eq!(tree.layout(&group).unwrap().x, [7., 27.]);
    assert_eq!(tree.layout(&child).unwrap().x, [7., 27.]);
    assert_eq!(tree.layout(&next).unwrap().x, [33., 48.]); // 9 and -3 collapse to 6.
    let mut edited = *tree.params(&group).unwrap();
    edited.padding.x = [2., 3.];
    tree.update_node_params(&group, edited).unwrap();
    tree.solve_layout(window);
    assert!(tree.rule_issues().is_empty());
    assert_eq!(tree.layout(&group).unwrap().x, [0., 41.]);
    assert_eq!(tree.layout(&child).unwrap().x, [9., 29.]);
    assert_eq!(tree.layout(&next).unwrap().x, [38., 53.]);
}

#[test]
fn moving_an_inherited_subtree_reprojects_from_its_authored_edges() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let rail = LayoutParams {
        size: Xy::new(Size::Pixels(100.), Size::Pixels(30.)),
        ..box_at_start()
    };
    let rtl = tree.add_node(&root, rail).unwrap();
    let ltr = tree
        .add_node(
            &root,
            LayoutParams {
                position: Xy::new(Pos::Start, Pos::Pixels(40.)),
                ..rail
            },
        )
        .unwrap();
    tree.set_rules(
        &rtl,
        NodeRules {
            logical: LogicalStyle {
                direction: Some(Direction::Rtl),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let group = tree
        .add_node(
            &rtl,
            LayoutParams {
                children_layout: ChildrenLayout::Block,
                ..rail
            },
        )
        .unwrap();
    let control = tree
        .add_node(
            &group,
            LayoutParams {
                size: Xy::new(Size::Pixels(20.), Size::Pixels(10.)),
                ..box_at_start()
            },
        )
        .unwrap();
    tree.set_rules(
        &control,
        NodeRules {
            logical: LogicalStyle {
                margin: Logical::new([px(4.), None], [None; 2]),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let window = Xy::new(200., 100.);
    for (parent, expected) in [(&rtl, [76., 96.]), (&ltr, [4., 24.]), (&rtl, [76., 96.])] {
        tree.move_node(&group, Destination::LastChildOf(parent))
            .unwrap();
        tree.solve_layout(window);
        assert_eq!(tree.layout(&control).unwrap().x, expected);
        assert_eq!(tree.params(&control).unwrap().margin.x, [Margin::ZERO; 2]);
        assert!(tree.rule_issues().is_empty());
    }
}

#[test]
fn contained_auto_box_under_free_parent_uses_its_placeholder() {
    use keru_layout::layout_rules::Container;
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let panel = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new_symm(Size::Auto),
                ..box_at_start()
            },
        )
        .unwrap();
    let text = tree
        .add_node(
            &panel,
            LayoutParams {
                size: Xy::new_symm(Size::FitContent),
                content_measure: keru_layout::ContentMeasure::Independent,
                ..box_at_start()
            },
        )
        .unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            container: Some(Container {
                name: None,
                axes: Xy::new(true, false),
                placeholder: Xy::new(37., 0.),
            }),
            ..Default::default()
        },
    )
    .unwrap();
    tree.solve_layout_with_content_measure(Xy::new(200., 100.), |_, _, _| Xy::new(120., 19.));
    assert_eq!(tree.layout(&panel).unwrap(), Xy::new([0., 37.], [0., 19.]));
    assert_eq!(tree.layout(&text).unwrap().x, [0., 120.]);
    assert!(tree.rule_issues().is_empty());
}
