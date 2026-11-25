//! An editable localized dispatch board. Predicted rectangles are in README.md.
#[cfg(feature = "incremental")]
mod app {
    use keru_layout::flex::{FlexItem, FlexLayout};
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::*;

    struct Row {
        owner: ChildId,
        route: ChildId,
        action: ChildId,
        first_chip: ChildId,
        second_chip: ChildId,
    }

    fn stack(axis: Axis, spacing: f32) -> ChildrenLayout {
        ChildrenLayout::Stack {
            axis,
            arrange: Arrange::Start,
            spacing,
        }
    }

    fn box_of(width: Size, height: f32) -> LayoutParams {
        LayoutParams {
            size: Xy::new(width, Size::Pixels(height)),
            position: Xy::new_symm(Pos::Start),
            ..LayoutParams::DEFAULT
        }
    }

    fn direction(tree: &mut LayoutTree<()>, direction: Direction) {
        tree.set_rules(
            &tree.root(),
            NodeRules {
                logical: LogicalStyle {
                    direction: Some(direction),
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap();
    }

    fn build(direction_value: Direction, protected: bool) -> (LayoutTree<()>, Vec<Row>) {
        let mut tree = LayoutTree::new();
        let root = tree.root();
        tree.update_node_params(
            &root,
            LayoutParams {
                children_layout: stack(Axis::Y, 6.0),
                position: Xy::new_symm(Pos::Start),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
        direction(&mut tree, direction_value);
        let mut rows = Vec::new();
        for _ in 0..24 {
            let panel = tree.add_node(&root, box_of(Size::Fill, 30.0)).unwrap();
            tree.set_rules(
                &panel,
                NodeRules {
                    logical: LogicalStyle {
                        main_axis: Some(LogicalAxis::Inline),
                        padding: Logical::new([Some(10.0), Some(30.0)], [None; 2]),
                        ..Default::default()
                    },
                    flex: Some(FlexLayout {
                        gap: 10.0,
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            )
            .unwrap();
            let owner = tree
                .add_node(&panel, box_of(Size::Pixels(160.0), 30.0))
                .unwrap();
            let route = tree
                .add_node(
                    &panel,
                    LayoutParams {
                        children_layout: stack(Axis::X, 3.0),
                        ..box_of(Size::Pixels(120.0), 30.0)
                    },
                )
                .unwrap();
            let action = tree
                .add_node(&panel, box_of(Size::Pixels(34.0), 30.0))
                .unwrap();
            tree.set_rules(&owner, owner_style(protected)).unwrap();
            tree.set_rules(
                &route,
                NodeRules {
                    logical: LogicalStyle {
                        direction: Some(Direction::Ltr),
                        ..Default::default()
                    },
                    flex_item: FlexItem {
                        shrink: 1.0,
                        ..Default::default()
                    },
                    ..Default::default()
                },
            )
            .unwrap();
            let first_chip = tree
                .add_node(&route, box_of(Size::Pixels(12.0), 18.0))
                .unwrap();
            let second_chip = tree
                .add_node(&route, box_of(Size::Pixels(15.0), 18.0))
                .unwrap();
            rows.push(Row {
                owner,
                route,
                action,
                first_chip,
                second_chip,
            });
        }
        (tree, rows)
    }

    fn owner_style(protected: bool) -> NodeRules {
        NodeRules {
            logical: LogicalStyle {
                min_size: Logical::new(protected.then_some(Size::Pixels(145.0)), None),
                ..Default::default()
            },
            flex_item: FlexItem {
                shrink: 1.0,
                ..Default::default()
            },
            ..Default::default()
        }
    }

    fn expect_board(tree: &LayoutTree<()>, rows: &[Row], expected: [[f32; 2]; 3]) {
        assert_eq!(tree.rule_issues(), &[]);
        for (index, row) in rows.iter().enumerate() {
            for (id, x) in [&row.owner, &row.route, &row.action]
                .into_iter()
                .zip(expected)
            {
                let r = tree.layout(id).unwrap();
                assert_eq!(r.x, x, "row {index}");
                assert_eq!(r.y, [36.0 * index as f32, 36.0 * index as f32 + 30.0]);
            }
            let left = expected[1][0];
            assert_eq!(tree.layout(&row.first_chip).unwrap().x, [left, left + 12.0]);
            assert_eq!(
                tree.layout(&row.second_chip).unwrap().x,
                [left + 15.0, left + 30.0]
            );
        }
    }

    pub fn run() {
        use Direction::{Ltr, Rtl};
        let cases = [
            (Ltr, 374.0, false, [[10., 170.], [180., 300.], [310., 344.]]),
            (Ltr, 304.0, false, [[10., 130.], [140., 230.], [240., 274.]]),
            (Rtl, 374.0, false, [[204., 364.], [74., 194.], [30., 64.]]),
            (Rtl, 304.0, false, [[174., 294.], [74., 164.], [30., 64.]]),
            (Ltr, 304.0, true, [[10., 155.], [165., 230.], [240., 274.]]),
        ];
        let (mut tree, rows) = build(Ltr, false);
        for (dir, width, protected, predicted) in cases {
            let window = Xy::new(width, 900.);
            direction(&mut tree, dir);
            for row in &rows {
                tree.set_rules(&row.owner, owner_style(protected)).unwrap();
            }
            tree.solve_layout(window);
            expect_board(&tree, &rows, predicted);
            let (mut fresh, fresh_rows) = build(dir, protected);
            fresh.solve_layout(window);
            expect_board(&fresh, &fresh_rows, predicted);
            #[cfg(feature = "batch-pilot")]
            {
                tree.solve_layout_batch(window).unwrap();
                expect_board(&tree, &rows, predicted);
            }
        }
        // A second author porting CSS might proactively zero the minimum on both
        // flexible cells or apply the same shrink declaration to the action.
        let (mut paired, pairs) = build(Ltr, false);
        let window = Xy::new(304.0, 900.0);
        for row in &pairs {
            for id in [&row.owner, &row.route] {
                let mut style = paired.rules(id).unwrap().unwrap().clone();
                style.logical.min_size.inline = Some(Size::Pixels(0.0));
                paired.set_rules(id, style).unwrap();
            }
        }
        paired.solve_layout(window);
        expect_board(&paired, &pairs, cases[1].3);
        for row in &pairs {
            paired
                .set_rules(
                    &row.action,
                    NodeRules {
                        flex_item: FlexItem::css(),
                        ..Default::default()
                    },
                )
                .unwrap();
        }
        paired.solve_layout(window);
        let button = paired.layout(&pairs[0].action).unwrap();
        assert!(button.x[1] - button.x[0] < 34.0);
    }
}

fn main() {
    #[cfg(feature = "incremental")]
    app::run();
}

#[test]
fn author_predictions() {
    main();
}
