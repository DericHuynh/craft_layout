#![cfg(feature = "batch-pilot")]

use keru_layout::{
    Arrange, Axis, BatchLayoutError, BatchLayoutStats, ChildrenLayout, ContentMeasure,
    ContentMeasureInput, Destination, LayoutParams, LayoutTree, MainAxisCellSize, Margin, NodeId,
    Pos, Size, TextContent, Xy, XyRect,
};

fn pixels(width: f32, height: f32) -> LayoutParams {
    LayoutParams {
        size: Xy::new(Size::Pixels(width), Size::Pixels(height)),
        ..LayoutParams::DEFAULT
    }
}

fn text(_: NodeId, value: Option<&mut usize>, _: Option<f32>) -> Xy<f32> {
    Xy::new(value.map_or(0.0, |value| *value as f32), 4.0)
}

fn words(rect: XyRect) -> [[u32; 2]; 2] {
    [rect.x.map(f32::to_bits), rect.y.map(f32::to_bits)]
}

fn capture_batch<T>(tree: &mut LayoutTree<T>, window: Xy<f32>) {
    capture_batch_with(tree, |tree| tree.solve_layout_batch(window));
}

fn capture_batch_with<T>(
    tree: &mut LayoutTree<T>,
    mut solve: impl FnMut(&mut LayoutTree<T>) -> Result<BatchLayoutStats, BatchLayoutError>,
) {
    assert_eq!(solve(tree).unwrap(), BatchLayoutStats::default());
    tree.invalidate();
    assert!(solve(tree).unwrap().rebuilt_graph);
}

fn matches_full<T: Clone>(
    tree: &LayoutTree<T>,
    window: Xy<f32>,
    measure: impl FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>,
) {
    let mut full = tree.clone();
    full.invalidate();
    full.solve_layout_with_measure(window, measure);
    let mut nodes = vec![(tree.root(), full.root())];
    while let Some((left, right)) = nodes.pop() {
        assert_eq!(
            tree.layout(&left).map(words),
            full.layout(&right).map(words)
        );
        let left = tree.children(&left).unwrap().collect::<Vec<_>>();
        let right = full.children(&right).unwrap().collect::<Vec<_>>();
        assert_eq!(left.len(), right.len());
        nodes.extend(
            left.into_iter()
                .zip(right)
                .map(|(a, b)| (a.into(), b.into())),
        );
    }
}

#[test]
fn first_stack_solve_checks_an_inexact_allocation_range() {
    for move_first in [false, true] {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let stack = tree
            .add_node(
                &root,
                LayoutParams {
                    children_layout: ChildrenLayout::Stack {
                        axis: Axis::X,
                        arrange: Arrange::Start,
                        spacing: 0.0,
                    },
                    ..pixels(1_600.0, 40.0)
                },
            )
            .unwrap();
        let other = tree.add_node(&root, pixels(20.0, 40.0)).unwrap();
        let leaf = pixels(10.0, 10.0);
        let first = tree.add_node(&stack, leaf).unwrap();
        for index in 1..128 {
            if index == 48 {
                tree.add_node(&other, leaf).unwrap();
            }
            tree.add_node(&stack, leaf).unwrap();
        }
        if move_first {
            tree.move_node(&first, Destination::LastChildOf(&stack))
                .unwrap();
        }
        let viewport = Xy::new(1_600.0, 100.0);
        assert_eq!(
            tree.solve_layout_batch(viewport).unwrap(),
            BatchLayoutStats::default()
        );
        matches_full(&tree, viewport, |_, _, _| Xy::new_symm(0.0));
    }
}

#[test]
fn forced_stack_recompute_uses_the_new_sibling_weight_order() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.update_node_params(
        &root,
        LayoutParams {
            children_layout: ChildrenLayout::Stack {
                axis: Axis::X,
                arrange: Arrange::Start,
                spacing: 0.0,
            },
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let fill = LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(8.0)),
        ..LayoutParams::DEFAULT
    };
    let first = tree.add_node(&root, fill).unwrap();
    let second = tree.add_node(&root, fill).unwrap();
    tree.add_node(
        &root,
        LayoutParams {
            fill_weight: 16_777_216.0,
            ..fill
        },
    )
    .unwrap();
    let viewport = Xy::new(16_777_216.0, 100.0);
    capture_batch(&mut tree, viewport);
    tree.invalidate();
    assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
    let rect = tree.layout(&second).unwrap();
    assert!(rect.x[1] - rect.x[0] < 1.0);

    tree.move_node(&first, Destination::LastChildOf(&root))
        .unwrap();
    tree.invalidate();
    assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
    assert_eq!(tree.layout(&second).unwrap().x, [0.0, 1.0]);
    matches_full(&tree, viewport, |_, _, _| Xy::new_symm(0.0));
}

#[test]
fn warm_stack_runs_rebind_prepared_sizes_and_margins() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.update_node_params(
        &root,
        LayoutParams {
            children_layout: ChildrenLayout::Stack {
                axis: Axis::Y,
                arrange: Arrange::Start,
                spacing: 0.5,
            },
            size: Xy::new(Size::Fill, Size::FitContent),
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let child = LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(8.0)),
        ..LayoutParams::DEFAULT
    };
    let first = tree.add_node(&root, child).unwrap();
    for _ in 0..11 {
        tree.add_node(&root, child).unwrap();
    }
    let viewport = Xy::new(320.0, 160.0);
    capture_batch(&mut tree, viewport);
    tree.invalidate();
    assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);

    let edited = LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(14.0)),
        margin: Xy::new([Margin::px(3.25).unwrap(); 2], child.margin.y),
        ..child
    };
    for style in [edited, child] {
        tree.update_node_params(&first, style).unwrap();
        tree.invalidate();
        assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
        matches_full(&tree, viewport, |_, _, _| Xy::new_symm(0.0));
    }
}

#[test]
fn a_new_structural_dependency_repairs_the_retained_order() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let first = tree.add_node(&root, pixels(25.0, 20.0)).unwrap();
    let second = tree.add_node(&root, pixels(30.0, 10.0)).unwrap();
    let window = Xy::new(200.0, 100.0);
    capture_batch(&mut tree, window);
    let fit = LayoutParams {
        size: Xy::new(Size::FitContent, Size::Fill),
        children_layout: ChildrenLayout::Stack {
            axis: Axis::X,
            arrange: Arrange::Start,
            spacing: 2.0,
        },
        ..LayoutParams::DEFAULT
    };
    tree.update_node_params(&root, fit).unwrap();
    let repaired = tree.solve_layout_batch(window).unwrap();
    assert!(repaired.rebuilt_graph && repaired.repaired_intervals > 0);
    assert_eq!(tree.layout(&root).unwrap().x, [0.0, 57.0]);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));

    tree.move_node(&second, Destination::Before(&first))
        .unwrap();
    assert!(!tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
    tree.remove(&first).unwrap();
    tree.add_node(&root, pixels(44.0, 14.0)).unwrap();
    assert!(tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
}

#[test]
fn the_first_batch_edit_captures_an_order_that_later_edits_can_repair() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.update_node_params(
        &root,
        LayoutParams {
            size: Xy::new(Size::AspectRatio(1.25), Size::Fill),
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let child = tree.add_node(&root, pixels(25.0, 20.0)).unwrap();
    let window = Xy::new(200.0, 100.0);
    let zero = |_: NodeId, _: Option<&mut ()>, _: Option<f32>| Xy::new_symm(0.0);
    let cold = tree.solve_layout_batch(window).unwrap();
    assert_eq!(cold, BatchLayoutStats::default());
    matches_full(&tree, window, zero);

    let fixed = pixels(25.0, 22.0);
    tree.update_node_params(&child, fixed).unwrap();
    let captured = tree.solve_layout_batch(window).unwrap();
    assert!(captured.rebuilt_graph && captured.repaired_intervals > 0);
    matches_full(&tree, window, zero);

    // The child's Regular width was dormant on the first solve. The new
    // intrinsic root needs it before the root's existing width producers.
    let fit = LayoutParams {
        size: Xy::new(Size::FitContent, Size::Fill),
        children_layout: ChildrenLayout::Stack {
            axis: Axis::X,
            arrange: Arrange::Start,
            spacing: 0.0,
        },
        ..LayoutParams::DEFAULT
    };
    tree.update_node_params(&root, fit).unwrap();
    let repaired = tree.solve_layout_batch(window).unwrap();
    assert!(repaired.rebuilt_graph && repaired.repaired_intervals > 0);
    assert_eq!(tree.layout(&root).unwrap().x, [0.0, 25.0]);
    matches_full(&tree, window, zero);

    let before = [
        tree.layout(&root).map(words),
        tree.layout(&child).map(words),
    ];
    tree.update_node_params(
        &child,
        LayoutParams {
            size: Xy::new_symm(Size::AspectRatio(1.0)),
            ..fixed
        },
    )
    .unwrap();
    let resized = Xy::new(210.0, 108.0);
    assert_eq!(
        tree.solve_layout_batch(resized),
        Err(BatchLayoutError::Cycle)
    );
    assert_eq!(
        [
            tree.layout(&root).map(words),
            tree.layout(&child).map(words)
        ],
        before,
    );
    tree.update_node_params(&child, fixed).unwrap();
    assert!(tree.solve_layout_batch(resized).unwrap().rebuilt_graph);
    matches_full(&tree, resized, zero);
}

#[test]
fn a_content_edit_uses_the_retained_order_and_leaves_unrelated_text_cached() {
    let mut tree = LayoutTree::<usize>::new();
    let root = tree.root();
    let style = LayoutParams {
        size: Xy::new(Size::FitContent, Size::Pixels(4.0)),
        text: TextContent::Fixed,
        ..LayoutParams::DEFAULT
    };
    let edited = tree.add_node_with_context(&root, style, 8).unwrap();
    tree.add_node_with_context(&root, style, 19).unwrap();
    let window = Xy::new(114.0, 45.0);
    let first = tree.solve_layout_batch_with_measure(window, text).unwrap();
    assert_eq!(first, BatchLayoutStats::default());
    let idle = tree
        .solve_layout_batch_with_measure(window, |_, _, _| {
            panic!("an idle bootstrap measured text")
        })
        .unwrap();
    assert_eq!(idle, BatchLayoutStats::default());

    tree.update_node_context(&edited, Some(11)).unwrap();
    let captured = tree.solve_layout_batch_with_measure(window, text).unwrap();
    assert!(captured.rebuilt_graph);
    let idle = tree
        .solve_layout_batch_with_measure(window, |_, _, _| panic!("an idle frame measured text"))
        .unwrap();
    assert!(!idle.rebuilt_graph && idle.computed == 0);
    tree.update_node_context(&edited, Some(26)).unwrap();
    let mut measured = 0;
    let warm = tree
        .solve_layout_batch_with_measure(window, |id, value, width| {
            measured += 1;
            text(id, value, width)
        })
        .unwrap();
    assert!(!warm.rebuilt_graph && warm.computed < captured.computed);
    assert_eq!(measured, 1);
    matches_full(&tree, window, text);
}

#[test]
fn a_returning_wrap_width_reuses_height_until_the_content_changes() {
    let mut tree = LayoutTree::<usize>::new();
    let root = tree.root();
    let node = tree
        .add_node_with_context(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                text: TextContent::Wrapping,
                ..LayoutParams::DEFAULT
            },
            70,
        )
        .unwrap();
    let measure = |_: NodeId, size: Option<&mut usize>, width: Option<f32>| {
        let size = *size.unwrap() as f32;
        Xy::new(size, (size / width.unwrap()).ceil() * 10.0)
    };
    let initial = tree
        .solve_layout_batch_with_measure(Xy::new(100.0, 200.0), measure)
        .unwrap();
    assert_eq!(initial, BatchLayoutStats::default());
    tree.invalidate();
    for (width, calls) in [(100.0, 1), (50.0, 1), (100.0, 0)] {
        let mut actual_calls = 0;
        let window = Xy::new(width, 200.0);
        tree.solve_layout_batch_with_measure(window, |id, size, width| {
            actual_calls += 1;
            measure(id, size, width)
        })
        .unwrap();
        assert_eq!(actual_calls, calls);
        matches_full(&tree, window, measure);
    }
    tree.update_node_context(&node, Some(170)).unwrap();
    let window = Xy::new(100.0, 200.0);
    tree.solve_layout_batch_with_measure(window, measure)
        .unwrap();
    let [start, end] = tree.layout(&node).unwrap().y;
    assert_eq!(end - start, 20.0);
    matches_full(&tree, window, measure);
}

#[test]
fn a_pixel_value_edit_reseeds_the_prepared_producer_without_rebuilding() {
    let mut tree = LayoutTree::<()>::new();
    let parent = tree.add_node(&tree.root(), pixels(62.0, 20.0)).unwrap();
    let child = tree
        .add_node(
            &parent,
            LayoutParams {
                size: Xy::new(Size::Frac(0.5), Size::Pixels(10.0)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    let window = Xy::new(300.0, 200.0);
    capture_batch(&mut tree, window);
    tree.update_node_params(&parent, pixels(90.0, 20.0))
        .unwrap();
    let stats = tree.solve_layout_batch(window).unwrap();
    assert!(!stats.rebuilt_graph && stats.computed > 0);
    let rect = tree.layout(&child).unwrap();
    assert_eq!(rect.x[1] - rect.x[0], 45.0);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
}

#[test]
fn visibility_reuses_a_complete_schedule_and_reseeds_a_reopened_subtree() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let parent = tree.add_node(&root, pixels(100.0, 35.0)).unwrap();
    let child = tree.add_node(&parent, pixels(20.0, 10.0)).unwrap();
    let fractional = tree
        .add_node(
            &child,
            LayoutParams {
                size: Xy::new(Size::Frac(0.5), Size::Pixels(10.0)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    let window = Xy::new(200.0, 150.0);
    capture_batch(&mut tree, window);
    tree.update_node_params(
        &parent,
        LayoutParams {
            disabled: true,
            ..pixels(100.0, 35.0)
        },
    )
    .unwrap();
    let hidden = tree.solve_layout_batch(window).unwrap();
    assert!(!hidden.rebuilt_graph && tree.layout(&fractional).is_err());
    tree.update_node_params(&child, pixels(48.0, 10.0)).unwrap();
    tree.solve_layout_batch(window).unwrap();
    tree.update_node_params(&parent, pixels(100.0, 35.0))
        .unwrap();
    let restored = tree.solve_layout_batch(window).unwrap();
    assert!(!restored.rebuilt_graph);
    let [left, right] = tree.layout(&fractional).unwrap().x;
    assert_eq!(right - left, 24.0);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
}

#[test]
fn reenabled_text_reuses_unwrapped_width_until_its_context_changes() {
    let mut tree = LayoutTree::<usize>::new();
    let style = LayoutParams {
        size: Xy::new(Size::FitContent, Size::Pixels(4.0)),
        text: TextContent::Fixed,
        ..LayoutParams::DEFAULT
    };
    let node = tree.add_node_with_context(&tree.root(), style, 12).unwrap();
    let window = Xy::new(114.0, 45.0);
    capture_batch_with(&mut tree, |tree| {
        tree.solve_layout_batch_with_measure(window, text)
    });
    let hidden = LayoutParams {
        disabled: true,
        ..style
    };
    tree.update_node_params(&node, hidden).unwrap();
    tree.solve_layout_batch_with_measure(window, text).unwrap();
    tree.update_node_params(&node, style).unwrap();
    let window = Xy::new(127.0, 45.0);
    let stats = tree
        .solve_layout_batch_with_measure(window, |_, _, _| {
            panic!("a returning node with unchanged text was remeasured")
        })
        .unwrap();
    assert!(!stats.rebuilt_graph);

    tree.update_node_params(&node, hidden).unwrap();
    tree.update_node_context(&node, Some(24)).unwrap();
    tree.solve_layout_batch_with_measure(window, text).unwrap();
    tree.update_node_params(&node, style).unwrap();
    tree.solve_layout_batch_with_measure(window, text).unwrap();
    let [start, end] = tree.layout(&node).unwrap().x;
    assert_eq!(end - start, 24.0);
    matches_full(&tree, window, text);
}

#[test]
fn visibility_recomputes_a_stack_fraction_when_its_parent_keeps_the_same_size() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.update_node_params(
        &root,
        LayoutParams {
            children_layout: ChildrenLayout::Stack {
                axis: Axis::X,
                arrange: Arrange::Start,
                spacing: 10.0,
            },
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let fractional = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Frac(0.5), Size::Pixels(10.0)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    let sibling = tree.add_node(&root, pixels(40.0, 10.0)).unwrap();
    let window = Xy::new(200.0, 150.0);
    capture_batch(&mut tree, window);
    let [left, right] = tree.layout(&fractional).unwrap().x;
    assert_eq!(right - left, 95.0);

    tree.update_node_params(
        &sibling,
        LayoutParams {
            disabled: true,
            ..pixels(40.0, 10.0)
        },
    )
    .unwrap();
    assert!(!tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    let [left, right] = tree.layout(&fractional).unwrap().x;
    assert_eq!(right - left, 100.0);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
}

#[test]
fn initially_hidden_subtree_can_reuse_the_all_visible_schedule() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let style = LayoutParams {
        size: Xy::new(Size::Frac(0.5), Size::Pixels(10.0)),
        ..LayoutParams::DEFAULT
    };
    let hidden = tree
        .add_node(
            &root,
            LayoutParams {
                disabled: true,
                ..style
            },
        )
        .unwrap();
    let window = Xy::new(200.0, 150.0);
    capture_batch(&mut tree, window);
    assert!(tree.layout(&hidden).is_err());
    tree.update_node_params(&hidden, style).unwrap();
    let shown = tree.solve_layout_batch(window).unwrap();
    assert!(!shown.rebuilt_graph);
    assert_eq!(tree.layout(&hidden).unwrap().x, [50.0, 150.0]);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
}

#[test]
fn hidden_sizing_cycle_falls_back_to_the_visible_requests() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let style = LayoutParams {
        size: Xy::new_symm(Size::AspectRatio(1.0)),
        ..LayoutParams::DEFAULT
    };
    let hidden = tree
        .add_node(
            &root,
            LayoutParams {
                disabled: true,
                ..style
            },
        )
        .unwrap();
    let window = Xy::new(200.0, 150.0);
    capture_batch(&mut tree, window);
    assert!(tree.layout(&hidden).is_err());
    let previous = tree.layout(&root).unwrap();
    tree.update_node_params(&hidden, style).unwrap();
    assert_eq!(
        tree.solve_layout_batch(window),
        Err(BatchLayoutError::Cycle)
    );
    assert_eq!(tree.layout(&root).unwrap(), previous);
}

#[test]
fn dependent_content_reads_the_current_prepared_width() {
    let mut tree = LayoutTree::<f32>::new();
    let mut style = LayoutParams {
        size: Xy::new(Size::Pixels(32.0), Size::FitContent),
        padding: Xy::new([1.0; 2], [2.0; 2]),
        max_size: Xy::new(None, Some(Size::Pixels(55.0))),
        content_measure: ContentMeasure::HeightForWidth,
        ..LayoutParams::DEFAULT
    };
    let child = tree
        .add_node_with_context(&tree.root(), style, 2.0)
        .unwrap();
    let window = Xy::new_symm(100.0);
    let no_text = |_, _: Option<&mut f32>, _| Xy::new_symm(0.0);
    let measure = |_, factor: Option<&mut f32>, input: ContentMeasureInput| {
        assert_eq!(input.axis, Axis::Y);
        assert_eq!(input.max_size.y, Some(51.0));
        Xy::new(0.0, input.known_dimensions.x.unwrap() / *factor.unwrap())
    };

    capture_batch_with(&mut tree, |tree| {
        tree.solve_layout_batch_with_measurers(window, no_text, measure)
    });
    assert_eq!(tree.layout(&child).unwrap().y, [40.5, 59.5]);
    style.size.x = Size::Pixels(42.0);
    tree.update_node_params(&child, style).unwrap();
    tree.update_node_context(&child, Some(4.0)).unwrap();
    let stats = tree
        .solve_layout_batch_with_measurers(window, no_text, measure)
        .unwrap();
    assert!(!stats.rebuilt_graph && stats.computed > 0);
    assert_eq!(tree.layout(&child).unwrap().y, [43.0, 57.0]);

    let mut full = tree.clone();
    full.invalidate();
    full.solve_layout_with_measurers(window, no_text, measure);
    let full_child = full.children(&full.root()).unwrap().next().unwrap();
    assert_eq!(
        tree.layout(&child).map(words),
        full.layout(&full_child).map(words)
    );
}

#[test]
fn wrap_resize_replaces_old_line_boundaries() {
    let mut tree = LayoutTree::<()>::new();
    let wrap = tree
        .add_node(
            &tree.root(),
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                children_layout: ChildrenLayout::Wrap {
                    axis: Axis::X,
                    arrange: Arrange::Start,
                    spacing: 2.0,
                    line_spacing: 3.0,
                },
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    for width in [18.0, 42.0, 30.0, 22.0, 49.0] {
        tree.add_node(&wrap, pixels(width, 11.0)).unwrap();
    }
    for (index, width) in [100.0, 48.0, 195.0, 125.0, 52.0, 195.0]
        .into_iter()
        .enumerate()
    {
        let window = Xy::new(width, 300.0);
        let stats = tree.solve_layout_batch(window).unwrap();
        assert_eq!(stats.rebuilt_graph, index == 1);
        matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
    }
}

#[test]
fn forward_stack_placement_matches_full_across_size_and_style_edits() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let mut root_style = LayoutParams {
        children_layout: ChildrenLayout::Stack {
            axis: Axis::Y,
            arrange: Arrange::Start,
            spacing: 0.375,
        },
        padding: Xy::new([0.125, 0.25], [-0.0, 1.5]),
        ..LayoutParams::DEFAULT
    };
    tree.update_node_params(&root, root_style).unwrap();
    let mut group_style = LayoutParams {
        size: Xy::new(Size::Pixels(62.5), Size::FitContent),
        children_layout: ChildrenLayout::Stack {
            axis: Axis::X,
            arrange: Arrange::Start,
            spacing: 0.625,
        },
        margin: Xy::new(
            [Margin::px(-0.625).unwrap(), Margin::ZERO],
            [Margin::ZERO; 2],
        ),
        ..LayoutParams::DEFAULT
    };
    let group = tree.add_node(&root, group_style).unwrap();
    let child = tree.add_node(&group, pixels(9.25, 11.75)).unwrap();
    tree.add_node(&group, pixels(10.5, 12.75)).unwrap();
    tree.add_node(&root, pixels(23.75, 17.5)).unwrap();
    let window = Xy::new(211.25, 83.875);
    let zero = |_: NodeId, _: Option<&mut ()>, _: Option<f32>| Xy::new_symm(0.0);
    capture_batch(&mut tree, window);
    matches_full(&tree, window, zero);

    tree.update_node_params(&child, pixels(9.25, 17.875))
        .unwrap();
    assert!(!tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    matches_full(&tree, window, zero);

    group_style.position.x = Pos::Start;
    tree.update_node_params(&group, group_style).unwrap();
    assert!(!tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    matches_full(&tree, window, zero);

    root_style.children_layout = ChildrenLayout::Stack {
        axis: Axis::Y,
        arrange: Arrange::Center,
        spacing: 0.375,
    };
    tree.update_node_params(&root, root_style).unwrap();
    assert!(!tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    matches_full(&tree, window, zero);
}

#[test]
fn a_cold_cycle_preserves_legacy_geometry_and_a_subsequent_edit_recovers() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let baseline = Xy::new(80.0, 100.0);
    tree.solve_layout(baseline);
    let previous = words(tree.layout(&root).unwrap());
    let cycle = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new_symm(Size::AspectRatio(1.0)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    let changed = Xy::new(100.0, 120.0);
    assert_eq!(
        tree.solve_layout_batch(changed),
        Err(BatchLayoutError::Cycle)
    );
    assert_eq!(words(tree.layout(&root).unwrap()), previous);
    assert!(tree.layout(&cycle).is_err());
    tree.update_node_params(&cycle, pixels(7.0, 11.0)).unwrap();
    let recovered = tree.solve_layout_batch(changed).unwrap();
    assert_eq!(recovered, BatchLayoutStats::default());
    matches_full(&tree, changed, |_, _, _| Xy::new_symm(0.0));
}

#[test]
fn switching_schedulers_republishes_the_cached_batch_view() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let batch_window = Xy::new(80.0, 100.0);
    capture_batch(&mut tree, batch_window);
    let expected = words(tree.layout(&root).unwrap());
    tree.solve_layout(Xy::new(92.0, 116.0));
    assert_ne!(words(tree.layout(&root).unwrap()), expected);
    let batch = tree.solve_layout_batch(batch_window).unwrap();
    assert!(!batch.rebuilt_graph && batch.computed == 0);
    assert_eq!(words(tree.layout(&root).unwrap()), expected);
}

#[test]
fn returning_viewport_reuses_only_unchanged_measurements_and_declarations() {
    let mut tree = LayoutTree::<usize>::new();
    let root = tree.root();
    tree.update_node_params(
        &root,
        LayoutParams {
            children_layout: ChildrenLayout::Stack {
                axis: Axis::Y,
                arrange: Arrange::Start,
                spacing: 1.0,
            },
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let style = LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        text: TextContent::Fixed,
        ..LayoutParams::DEFAULT
    };
    let child = tree.add_node_with_context(&root, style, 5).unwrap();
    let measure = |_: NodeId, context: Option<&mut usize>, _: Option<f32>| {
        Xy::new(6.0, context.map_or(0.0, |value| *value as f32))
    };
    let narrow = Xy::new(40.0, 100.0);
    let wide = Xy::new(90.0, 100.0);
    capture_batch_with(&mut tree, |tree| {
        tree.solve_layout_batch_with_measure(wide, measure)
    });
    tree.solve_layout_batch_with_measure(narrow, measure)
        .unwrap();
    tree.solve_layout_batch_with_measure(wide, measure).unwrap();
    let restored = tree
        .solve_layout_batch_with_measure(narrow, measure)
        .unwrap();
    assert_eq!(restored.computed, 0);
    matches_full(&tree, narrow, measure);

    tree.update_node_context(&child, Some(9)).unwrap();
    let updated = tree.solve_layout_batch_with_measure(wide, measure).unwrap();
    assert!(updated.computed > 0);
    matches_full(&tree, wide, measure);

    tree.update_node_params(
        &child,
        LayoutParams {
            padding: Xy::new([0.0; 2], [2.0, 3.0]),
            ..style
        },
    )
    .unwrap();
    let changed = tree
        .solve_layout_batch_with_measure(narrow, measure)
        .unwrap();
    assert!(changed.computed > 0 && !changed.rebuilt_graph);
    matches_full(&tree, narrow, measure);
}

#[test]
fn width_grid_memo_keeps_visibility_and_content_in_its_inputs() {
    let mut tree = LayoutTree::<usize>::new();
    let root = tree.root();
    tree.update_node_params(
        &root,
        LayoutParams {
            children_layout: ChildrenLayout::Stack {
                axis: Axis::Y,
                arrange: Arrange::Start,
                spacing: 1.25,
            },
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let banner_style = LayoutParams {
        children_layout: ChildrenLayout::Wrap {
            axis: Axis::X,
            arrange: Arrange::Start,
            spacing: 1.0,
            line_spacing: 1.0,
        },
        ..pixels(8.0, 4.0)
    };
    let banner = tree.add_node(&root, banner_style).unwrap();
    let grid = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                children_layout: ChildrenLayout::Grid {
                    main_axis: Axis::X,
                    columns: MainAxisCellSize::Width(25.0),
                    spacing_x: 2.0,
                    spacing_y: 1.0,
                    backfill: false,
                },
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    let style = LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        text: TextContent::Wrapping,
        ..LayoutParams::DEFAULT
    };
    let child = tree.add_node_with_context(&grid, style, 80).unwrap();
    for _ in 0..8 {
        tree.add_node_with_context(&grid, style, 45).unwrap();
    }
    let measure = |_: NodeId, context: Option<&mut usize>, width: Option<f32>| {
        let size = context.map_or(0.0, |value| *value as f32);
        Xy::new(size, (size / width.unwrap_or(size).max(1.0)).ceil())
    };
    let wide = Xy::new(97.0, 70.0);
    let narrow = Xy::new(54.0, 70.0);
    capture_batch_with(&mut tree, |tree| {
        tree.solve_layout_batch_with_measure(wide, measure)
    });
    let first = tree
        .solve_layout_batch_with_measure(narrow, measure)
        .unwrap();
    tree.solve_layout_batch_with_measure(wide, measure).unwrap();
    let cached = tree
        .solve_layout_batch_with_measure(narrow, measure)
        .unwrap();
    assert!(cached.computed < first.computed);
    matches_full(&tree, narrow, measure);

    // Reusing the Grid's solved dimensions must respect its current origin.
    tree.update_node_params(
        &banner,
        LayoutParams {
            size: Xy::new(Size::Pixels(8.0), Size::Pixels(9.375)),
            ..banner_style
        },
    )
    .unwrap();
    tree.solve_layout_batch_with_measure(wide, measure).unwrap();
    assert_eq!(tree.layout(&grid).unwrap().y[0], 10.625);
    matches_full(&tree, wide, measure);
    tree.set_pixel_scale(keru_layout::PixelScale::new(1.25));
    tree.solve_layout_batch_with_measure(narrow, measure)
        .unwrap();
    matches_full(&tree, narrow, measure);
    tree.set_pixel_scale(None);

    tree.update_node_params(
        &child,
        LayoutParams {
            disabled: true,
            ..style
        },
    )
    .unwrap();
    tree.solve_layout_batch_with_measure(wide, measure).unwrap();
    matches_full(&tree, wide, measure);
    tree.update_node_context(&child, Some(180)).unwrap();
    tree.update_node_params(&child, style).unwrap();
    tree.solve_layout_batch_with_measure(narrow, measure)
        .unwrap();
    matches_full(&tree, narrow, measure);
}

#[test]
fn isolated_tail_edits_reuse_the_batch_order_across_visibility_and_resizes() {
    for scale in [None, keru_layout::PixelScale::new(1.3)] {
        let mut tree = LayoutTree::<usize>::new();
        tree.set_pixel_scale(scale);
        let root = tree.root();
        tree.update_node_params(
            &root,
            LayoutParams {
                children_layout: ChildrenLayout::Stack {
                    axis: Axis::Y,
                    spacing: 1.375,
                    arrange: Arrange::Start,
                },
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
        let fixed = pixels(34.375, 19.125);
        let toggle = tree
            .add_node(
                &root,
                LayoutParams {
                    disabled: true,
                    ..fixed
                },
            )
            .unwrap();
        tree.add_node(&root, fixed).unwrap();
        let mut window = Xy::new(121.25, 74.875);
        capture_batch_with(&mut tree, |tree| {
            tree.solve_layout_batch_with_measure(window, text)
        });

        for revision in 0..3 {
            let branch = tree
                .add_node(
                    &root,
                    LayoutParams {
                        size: Xy::new(Size::Fill, Size::FitContent),
                        children_layout: ChildrenLayout::Stack {
                            axis: Axis::Y,
                            spacing: 2.875,
                            arrange: Arrange::Center,
                        },
                        ..LayoutParams::DEFAULT
                    },
                )
                .unwrap();
            let label = tree
                .add_node_with_context(
                    &branch,
                    LayoutParams {
                        size: Xy::new(Size::FitContent, Size::FitContent),
                        text: TextContent::Fixed,
                        ..LayoutParams::DEFAULT
                    },
                    revision + 12,
                )
                .unwrap();
            tree.update_node_params(&toggle, fixed).unwrap();
            let added = tree.solve_layout_batch_with_measure(window, text).unwrap();
            assert!(!added.rebuilt_graph && added.computed > 0);
            matches_full(&tree, window, text);

            window.x += 11.375;
            tree.solve_layout_batch_with_measure(window, text).unwrap();
            matches_full(&tree, window, text);
            assert!(tree.layout(&label).is_ok());

            tree.remove(&branch).unwrap();
            tree.update_node_params(
                &toggle,
                LayoutParams {
                    disabled: true,
                    ..fixed
                },
            )
            .unwrap();
            let removed = tree.solve_layout_batch_with_measure(window, text).unwrap();
            assert!(!removed.rebuilt_graph);
            assert!(tree.layout(&label).is_err());
            matches_full(&tree, window, text);
        }
    }
}

#[test]
fn localized_batch_tail_respects_cyclic_and_dependent_boundaries() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let window = Xy::new_symm(160.0);
    capture_batch(&mut tree, window);
    let previous = tree.layout(&root).unwrap();
    let branch = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new_symm(Size::AspectRatio(1.0)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    assert_eq!(
        tree.solve_layout_batch(window),
        Err(BatchLayoutError::Cycle)
    );
    assert_eq!(tree.layout(&root).unwrap(), previous);
    tree.update_node_params(&branch, pixels(23.0, 12.0))
        .unwrap();
    tree.solve_layout_batch(window).unwrap();

    tree.update_node_params(
        &root,
        LayoutParams {
            children_layout: ChildrenLayout::Stack {
                axis: Axis::Y,
                spacing: 6.0,
                arrange: Arrange::Start,
            },
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let child = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::Frac(0.5)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    tree.solve_layout_batch(window).unwrap();
    let before = tree.layout(&child).unwrap().y;
    tree.add_node(&root, pixels(8.0, 4.0)).unwrap();
    assert!(tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    assert_ne!(tree.layout(&child).unwrap().y, before);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
}

#[test]
fn removing_a_reordered_fragment_refreshes_its_actual_predecessor() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let window = Xy::new_symm(120.0);
    let first = tree.add_node(&root, pixels(30.0, 24.0)).unwrap();
    capture_batch(&mut tree, window);
    let tail = tree.add_node(&root, pixels(14.0, 12.0)).unwrap();
    assert!(!tree.solve_layout_batch(window).unwrap().rebuilt_graph);

    tree.move_node(&tail, Destination::Before(&first)).unwrap();
    assert!(!tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    tree.remove(&tail).unwrap();
    assert!(tree.solve_layout_batch(window).unwrap().rebuilt_graph);
    matches_full(&tree, window, |_, _, _| Xy::new_symm(0.0));
}
