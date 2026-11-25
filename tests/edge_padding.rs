#![cfg(feature = "incremental")]

use keru_layout::{
    Anchor, Arrange, Axis, ChildrenLayout, LayoutParams, LayoutTree, MainAxisCellSize, Pos, Size,
    Xy,
};

fn box_size(width: Size, height: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(width, height),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}

fn stack(axis: Axis) -> ChildrenLayout {
    ChildrenLayout::Stack {
        axis,
        arrange: Arrange::Start,
        spacing: 0.,
    }
}

const SOLVERS: &[bool] = &[
    false,
    #[cfg(feature = "batch-pilot")]
    true,
];

fn solve(tree: &mut LayoutTree<()>, width: f32, height: f32, batch: bool) {
    let window = Xy::new(width, height);
    #[cfg(feature = "batch-pilot")]
    if batch {
        tree.solve_layout_batch(window).unwrap();
    }
    if !batch {
        tree.solve_layout(window);
    }
    assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
    assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
}

#[test]
fn equal_cards_keep_their_share_and_collapsed_content_stays_in_its_card() {
    for &batch in SOLVERS {
        let mut tree = LayoutTree::<()>::new();
        let fill = box_size(Size::Fill, Size::Fill);
        let row = tree
            .add_node(
                &tree.root(),
                LayoutParams {
                    children_layout: stack(Axis::X),
                    ..fill
                },
            )
            .unwrap();
        let cards = [0., 18., 0.].map(|pad| {
            let card = tree
                .add_node(
                    &row,
                    LayoutParams {
                        padding: Xy::new([pad; 2], [0.; 2]),
                        ..fill
                    },
                )
                .unwrap();
            let contents = tree.add_node(&card, fill).unwrap();
            (card, contents)
        });
        for (width, inside) in [
            (300., [118., 182.]),
            (108., [54., 54.]),
            (60., [38., 38.]),
            (30., [20., 20.]),
            (0., [0., 0.]),
            (300., [118., 182.]),
        ] {
            solve(&mut tree, width, 40., batch);
            let share = width / 3.;
            for (index, (card, contents)) in cards.iter().enumerate() {
                let outer = [index as f32 * share, (index + 1) as f32 * share];
                assert_eq!(tree.layout(card).unwrap().x, outer);
                assert_eq!(
                    tree.layout(contents).unwrap().x,
                    if index == 1 { inside } else { outer }
                );
            }
        }
    }
}

#[test]
fn flows_and_reversed_origins_agree_on_the_collapsed_physical_content_box() {
    let grid = ChildrenLayout::Grid {
        columns: MainAxisCellSize::Count(1),
        spacing_x: 0.,
        spacing_y: 0.,
        main_axis: Axis::X,
        backfill: false,
    };
    let wrap = ChildrenLayout::Wrap {
        axis: Axis::X,
        arrange: Arrange::Start,
        spacing: 0.,
        line_spacing: 0.,
    };
    for &batch in SOLVERS {
        for layout in [
            ChildrenLayout::Free,
            stack(Axis::X),
            stack(Axis::Y),
            wrap,
            grid,
        ] {
            let mut tree = LayoutTree::<()>::new();
            let mut params = LayoutParams {
                children_layout: layout,
                padding: Xy::new([18., 4.], [4., 9.]),
                ..box_size(Size::Pixels(10.), Size::Pixels(6.))
            };
            let card = tree.add_node(&tree.root(), params).unwrap();
            let marker = tree
                .add_node(&card, box_size(Size::Pixels(0.), Size::Pixels(0.)))
                .unwrap();
            for flipped in [false, true, false] {
                params.children_origin_flipped = Xy::new_symm(flipped);
                tree.update_node_params(&card, params).unwrap();
                solve(&mut tree, 50., 50., batch);
                let rect = tree.layout(&marker).unwrap();
                assert_eq!(
                    (rect.x, rect.y),
                    ([10.; 2], [4.; 2]),
                    "{layout:?}, flipped={flipped}, batch={batch}"
                );
            }
        }
    }
}

#[test]
fn requested_child_size_can_overflow_the_collapsed_content_box() {
    for &batch in SOLVERS {
        let mut tree = LayoutTree::<()>::new();
        let mut params = LayoutParams {
            padding: Xy::new([18., 4.], [4., 9.]),
            ..box_size(Size::Pixels(10.), Size::Pixels(6.))
        };
        let card = tree.add_node(&tree.root(), params).unwrap();
        let label = tree
            .add_node(&card, box_size(Size::Pixels(3.), Size::Pixels(2.)))
            .unwrap();
        for (flipped, x, y) in [(false, [10., 13.], [4., 6.]), (true, [7., 10.], [2., 4.])] {
            params.children_origin_flipped = Xy::new_symm(flipped);
            tree.update_node_params(&card, params).unwrap();
            solve(&mut tree, 50., 50., batch);
            let rect = tree.layout(&label).unwrap();
            assert_eq!((rect.x, rect.y), (x, y));
        }
    }
}
