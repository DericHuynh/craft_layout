#![cfg(feature = "incremental")]

use keru_layout::{
    Anchor, Arrange, Axis, ChildrenLayout, LayoutParams, LayoutTree, Margin, PixelScale, Pos, Size,
    Xy,
};

const LIGHTS: usize = 24;
const CENTERED: [usize; 2] = [11, 21];

fn check_toolbar(solve: impl Fn(&mut LayoutTree<()>, Xy<f32>)) {
    let at_start = LayoutParams {
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    };
    let stack = ChildrenLayout::Stack {
        axis: Axis::X,
        arrange: Arrange::Start,
        spacing: 2.,
    };
    let wrap = ChildrenLayout::Wrap {
        axis: Axis::X,
        arrange: Arrange::Start,
        spacing: 2.,
        line_spacing: 3.,
    };

    // Each tuple gives the width, the number of lights per row and the auto margin
    // on each row. A full row uses 238px. At 237px Wrap moves the last light to
    // the next row and divides the first row's spare 9px among four edges.
    let stack_sizes = [
        (320., LIGHTS, [20.5, 0., 0.]),
        (238., LIGHTS, [0.; 3]),
        (237., LIGHTS, [0.; 3]),
        (110., LIGHTS, [0.; 3]),
        (320., LIGHTS, [20.5, 0., 0.]),
    ];
    let wrap_sizes = [
        (320., LIGHTS, [20.5, 0., 0.]),
        (238., LIGHTS, [0.; 3]),
        (237., 23, [2.25, 0., 0.]),
        (110., 11, [0., 0.5, 0.]),
        (320., LIGHTS, [20.5, 0., 0.]),
    ];

    for (layout, sizes) in [(stack, stack_sizes), (wrap, wrap_sizes)] {
        for mirrored in [false, true] {
            for snapped in [false, true] {
                let mut tree = LayoutTree::new();
                if snapped {
                    tree.set_pixel_scale(PixelScale::new(2.));
                }
                let bar = tree
                    .add_node(
                        &tree.root(),
                        LayoutParams {
                            size: Xy::new(Size::Fill, Size::FitContent),
                            children_layout: layout,
                            children_origin_flipped: Xy::new(mirrored, false),
                            ..at_start
                        },
                    )
                    .unwrap();
                let mut lights = Vec::new();
                for index in 0..LIGHTS {
                    let mut light = LayoutParams {
                        size: Xy::new_symm(Size::Pixels(8.)),
                        ..at_start
                    };
                    if CENTERED.contains(&index) {
                        light.margin.x = [Margin::AUTO; 2];
                    }
                    lights.push(tree.add_node(&bar, light).unwrap());
                }

                for (width, capacity, margin) in sizes {
                    solve(&mut tree, Xy::new(width, 100.));
                    assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
                    assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
                    for (index, id) in lights.iter().enumerate() {
                        let row = index / capacity;
                        let column = index % capacity;
                        let preceding = row * capacity..index;
                        let centered_before =
                            CENTERED.iter().filter(|i| preceding.contains(i)).count();
                        let edges = 2 * centered_before + usize::from(CENTERED.contains(&index));
                        let x = (10 * column) as f32 + edges as f32 * margin[row];
                        let x = if mirrored { width - 8. - x } else { x };
                        let y = (11 * row) as f32;
                        let x_edges = [x, x + 8.].map(|edge| {
                            if snapped {
                                (edge * 2.).round() / 2.
                            } else {
                                edge
                            }
                        });
                        assert_eq!(
                            tree.layout(id).unwrap(),
                            Xy::new(x_edges, [y, y + 8.]),
                            "{layout:?} width={width} mirrored={mirrored} snapped={snapped} light={index}",
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn indicator_toolbar_preserves_spacing_across_resizes() {
    check_toolbar(|tree, viewport| {
        tree.solve_layout(viewport);
    });
}

#[cfg(feature = "batch-pilot")]
#[test]
fn batch_indicator_toolbar_preserves_spacing_across_resizes() {
    check_toolbar(|tree, viewport| {
        tree.solve_layout_batch(viewport).unwrap();
    });
}
