#![cfg(feature = "incremental")]

use keru_layout::*;

const WINDOW: Xy<f32> = Xy::new(640.0, 480.0);

#[test]
fn fixed_fill_group_matches_the_general_path_on_both_axes() {
    for axis in [Axis::X, Axis::Y] {
        let make_tree = |disabled_child| {
            let mut tree = LayoutTree::<()>::new();
            let root = tree.root();
            tree.update_node_params(&root, LayoutParams {
                size: Xy::new(Size::Pixels(320.0), Size::Pixels(96.0)),
                children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: 0.0 },
                ..LayoutParams::DEFAULT
            }).unwrap();
            let children = [16_777_216.0, 1.0, 2.0, 4096.0].map(|fill_weight| {
                tree.add_node(&root, LayoutParams { fill_weight, ..LayoutParams::DEFAULT }).unwrap()
            });
            if disabled_child {
                tree.add_node(&root, LayoutParams { disabled: true, ..LayoutParams::DEFAULT }).unwrap();
            }
            (tree, children)
        };
        let (mut fast, fast_children) = make_tree(false);
        let (mut general, general_children) = make_tree(true);
        for weight in [1.0, 8.0] {
            for (tree, child) in [(&mut fast, &fast_children[1]), (&mut general, &general_children[1])] {
                tree.update_node_params(child, LayoutParams { fill_weight: weight, ..LayoutParams::DEFAULT }).unwrap();
                tree.solve_layout(WINDOW);
                assert!(tree.warnings().is_empty());
            }
            for (a, b) in fast_children.iter().zip(&general_children) {
                let a = fast.layout(a).unwrap();
                let b = general.layout(b).unwrap();
                assert_eq!(a.x.map(f32::to_bits), b.x.map(f32::to_bits));
                assert_eq!(a.y.map(f32::to_bits), b.y.map(f32::to_bits));
            }
        }
    }
}

#[test]
fn warm_unit_fill_rechecks_current_count_and_weights() {
    let make = |disabled_child| {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        tree.update_node_params(&root, LayoutParams {
            size: Xy::new(Size::Pixels(320.0), Size::Pixels(96.0)),
            children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 0.0 },
            ..LayoutParams::DEFAULT
        }).unwrap();
        let children = (0..128).map(|_| tree.add_node(&root, LayoutParams::DEFAULT).unwrap()).collect::<Vec<_>>();
        if disabled_child {
            tree.add_node(&root, LayoutParams { disabled: true, ..LayoutParams::DEFAULT }).unwrap();
        }
        (tree, root, children)
    };
    let (mut fast, fast_root, mut fast_ids) = make(false);
    let (mut general, general_root, mut general_ids) = make(true);
    for frame in 0..4 {
        for (tree, root, children) in [(&mut fast, &fast_root, &mut fast_ids), (&mut general, &general_root, &mut general_ids)] {
            if frame == 2 {
                children.push(tree.add_node(root, LayoutParams::DEFAULT).unwrap());
            }
            if frame == 3 {
                tree.update_node_params(&children[83], LayoutParams { fill_weight: 2.0, ..LayoutParams::DEFAULT }).unwrap();
            }
            tree.invalidate();
            tree.solve_layout(WINDOW);
            assert!(tree.warnings().is_empty());
        }
        for (fast_id, general_id) in fast_ids.iter().zip(&general_ids) {
            let a = fast.layout(fast_id).unwrap();
            let b = general.layout(general_id).unwrap();
            assert_eq!(a.x.map(f32::to_bits), b.x.map(f32::to_bits));
            assert_eq!(a.y.map(f32::to_bits), b.y.map(f32::to_bits));
        }
    }
}

#[test]
fn warm_fill_pair_rechecks_the_current_siblings() {
    for axis in [Axis::X, Axis::Y] {
        let make = |disabled_child| {
            let mut tree = LayoutTree::<()>::new();
            let root = tree.root();
            let panel = tree.add_node(&root, LayoutParams {
                size: Xy::new(Size::Pixels(103.25), Size::Pixels(85.5)),
                position: Xy::new_symm(Pos::Start),
                children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: 0.0 },
                ..LayoutParams::DEFAULT
            }).unwrap();
            let children = [1.0, 2.25].map(|fill_weight| {
                tree.add_node(&panel, LayoutParams {
                    fill_weight,
                    position: Xy::new_symm(Pos::Start),
                    ..LayoutParams::DEFAULT
                }).unwrap()
            });
            if disabled_child {
                tree.add_node(&panel, LayoutParams { disabled: true, ..LayoutParams::DEFAULT }).unwrap();
            }
            (tree, panel, children)
        };
        let (mut fast, fast_panel, fast_children) = make(false);
        let (mut general, general_panel, general_children) = make(true);
        for frame in 0..4 {
            for (tree, panel, children) in [(&mut fast, &fast_panel, &fast_children), (&mut general, &general_panel, &general_children)] {
                if frame == 2 {
                    tree.update_node_params(&children[1], LayoutParams {
                        fill_weight: 13.25,
                        position: Xy::new_symm(Pos::Start),
                        ..LayoutParams::DEFAULT
                    }).unwrap();
                } else if frame == 3 {
                    tree.add_node(panel, LayoutParams::DEFAULT).unwrap();
                }
                tree.invalidate();
                tree.solve_layout(WINDOW);
                assert!(tree.warnings().is_empty());
            }
            for (a, b) in fast_children.iter().zip(&general_children) {
                let a = fast.layout(a).unwrap();
                let b = general.layout(b).unwrap();
                assert_eq!(a.x.map(f32::to_bits), b.x.map(f32::to_bits));
                assert_eq!(a.y.map(f32::to_bits), b.y.map(f32::to_bits));
            }
        }
    }
}

fn row() -> LayoutParams {
    LayoutParams {
        size: Xy::new(Size::Pixels(180.0), Size::Pixels(80.0)),
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 2.0 },
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    }
}

fn label() -> LayoutParams {
    LayoutParams {
        size: Xy::new(Size::FitContent, Size::FitContent),
        content_measure: ContentMeasure::HeightForWidth,
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    }
}

fn solve(tree: &mut LayoutTree<u32>, window: Xy<f32>) -> (IncrementalRelayoutOutcome, Vec<NodeId>) {
    let mut calls = Vec::new();
    let outcome = tree.solve_layout_with_content_measure(window, |node, context, input| {
        calls.push(node);
        let width = *context.unwrap() as f32;
        let available = input.known_dimensions.x.unwrap_or(width).max(1.0);
        Xy::new(width, (width / available).ceil() * 11.0)
    });
    (outcome, calls)
}

fn compare_full(tree: &mut LayoutTree<u32>, window: Xy<f32>) -> (IncrementalRelayoutOutcome, Vec<NodeId>) {
    let mut reference = tree.clone();
    reference.invalidate();
    let (full, _) = solve(&mut reference, window);
    assert!(!matches!(full, IncrementalRelayoutOutcome::Success { .. }));
    let result = solve(tree, window);
    assert_same_view(tree, &reference);
    result
}

fn assert_same_view<T>(tree: &LayoutTree<T>, reference: &LayoutTree<T>) {
    let mut nodes = vec![(tree.root(), reference.root())];
    while let Some((id, other_id)) = nodes.pop() {
        match (tree.layout(&id), reference.layout(&other_id)) {
            (Ok(a), Ok(b)) => {
                assert_eq!(a.x.map(f32::to_bits), b.x.map(f32::to_bits), "x on {id:?}");
                assert_eq!(a.y.map(f32::to_bits), b.y.map(f32::to_bits), "y on {id:?}");
            }
            (Err(TreeError::LayoutUnavailable), Err(TreeError::LayoutUnavailable)) => {}
            (a, b) => panic!("different layout availability on {id:?}: {a:?} vs {b:?}"),
        }
        let mut children = tree.children(&id).unwrap();
        let mut other_children = reference.children(&other_id).unwrap();
        loop {
            match (children.next(), other_children.next()) {
                (Some(child), Some(other_child)) => nodes.push((child.into(), other_child.into())),
                (None, None) => break,
                _ => panic!("different child counts on {id:?}"),
            }
        }
    }
}

#[test]
fn signed_zero_aspect_ratio_edits_select_the_same_bound_as_a_full_solve() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    let mut params = LayoutParams {
        position: Xy::new_symm(Pos::Start),
        size: Xy::new(Size::Pixels(10.0), Size::AspectRatio(0.0)),
        min_size: Xy::new(None, Some(Size::Pixels(1.0))),
        max_size: Xy::new(None, Some(Size::Pixels(20.0))),
        ..LayoutParams::DEFAULT
    };
    let leaf = tree.add_node(&root, params).unwrap();
    // Keep the change under the incremental work budget.
    for _ in 0..12 { tree.add_node(&root, LayoutParams::DEFAULT).unwrap(); }
    tree.solve_layout(WINDOW);
    assert_eq!(tree.layout(&leaf).unwrap().y, [0.0, 20.0]);
    for (ratio, height) in [(-0.0, 1.0), (0.0, 20.0)] {
        params.size.y = Size::AspectRatio(ratio);
        tree.update_node_params(&leaf, params).unwrap();
        let (outcome, _) = compare_full(&mut tree, WINDOW);
        assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
        assert_eq!(tree.layout(&leaf).unwrap().y, [0.0, height]);
    }
}

#[test]
fn fixed_leaf_edits_and_host_measurements_survive_pending_full_invalidation() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    let mut pixels = LayoutParams {
        size: Xy::new_symm(Size::Pixels(10.0)),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    let box_id = tree.add_node(&root, pixels).unwrap();
    let measured = tree.add_node_with_context(&root, label(), 24).unwrap();
    solve(&mut tree, WINDOW);

    tree.invalidate();
    pixels.size.x = Size::Pixels(37.0);
    tree.update_node_params(&box_id, pixels).unwrap();
    let (outcome, calls) = solve(&mut tree, WINDOW);
    assert_eq!(outcome, IncrementalRelayoutOutcome::FallbackInvalidated);
    assert_eq!(tree.layout(&box_id).unwrap().x, [0.0, 37.0]);
    assert!(calls.contains(&measured));

    tree.invalidate();
    pixels.max_size.x = Some(Size::Pixels(9.0));
    tree.update_node_params(&box_id, pixels).unwrap();
    solve(&mut tree, WINDOW);
    assert_eq!(tree.layout(&box_id).unwrap().x, [0.0, 9.0]);
}

fn compare_structural(tree: &mut LayoutTree<u32>, window: Xy<f32>) -> Vec<NodeId> {
    let (outcome, measured) = compare_full(tree, window);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    measured
}

fn independent_panels() -> (LayoutTree<u32>, ChildId, ChildId) {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    let hot = tree.add_node(&root, row()).unwrap();
    let cold = tree.add_node(&root, row()).unwrap();
    let cold_label = tree.add_node_with_context(&cold, label(), 48).unwrap();
    for _ in 0..80 {
        tree.add_node_with_context(&cold, label(), 3).unwrap();
    }
    (tree, hot, cold_label)
}

#[test]
fn a_structural_batch_includes_content_edits_in_either_order() {
    for content_first in [true, false] {
        let (mut tree, row, other_label) = independent_panels();
        tree.add_node(&tree.root(), LayoutParams {
            children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 0.0, line_spacing: 0.0 },
            ..LayoutParams::DEFAULT
        }).unwrap();
        solve(&mut tree, WINDOW);
        if content_first { tree.update_node_context(&other_label, Some(90)).unwrap(); }
        let inserted = tree.add_node_with_context(&row, label(), 16).unwrap();
        if !content_first { tree.update_node_context(&other_label, Some(90)).unwrap(); }
        let (outcome, measured) = compare_full(&mut tree, WINDOW);
        assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }));
        assert!(measured.contains(&other_label) && measured.contains(&inserted));
    }
}

#[test]
fn insert_reorder_and_remove_preserve_unrelated_measurements() {
    let (mut tree, row, cold_label) = independent_panels();
    let left = tree.add_node_with_context(&row, label(), 27).unwrap();
    let fill = tree.add_node(&row, LayoutParams { size: Xy::new(Size::Fill, Size::Pixels(7.0)), ..LayoutParams::DEFAULT }).unwrap();
    solve(&mut tree, WINDOW);

    let right = tree.add_node_with_context(&row, label(), 42).unwrap();
    let (outcome, measured) = compare_full(&mut tree, WINDOW);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert!(measured.contains(&right));
    assert!(!measured.contains(&cold_label));
    assert_eq!(tree.layout(&fill).unwrap().x, [29.0, 136.0]);

    tree.move_node(&right, Destination::Before(&left)).unwrap();
    let (outcome, measured) = compare_full(&mut tree, WINDOW);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert!(!measured.contains(&cold_label));
    assert_eq!(tree.layout(&left).unwrap().x, [44.0, 71.0]);

    tree.remove(&left).unwrap();
    let (outcome, measured) = compare_full(&mut tree, WINDOW);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert!(!measured.contains(&cold_label));
    assert_eq!(tree.layout(&fill).unwrap().x, [44.0, 180.0]);
}

#[test]
fn reparent_and_coalesced_edits_preserve_subsequent_dependencies() {
    let (mut tree, first, cold_label) = independent_panels();
    let grid = tree.add_node(&tree.root(), LayoutParams {
        size: Xy::new(Size::Frac(0.5), Size::Pixels(45.0)),
        children_layout: ChildrenLayout::Grid {
            columns: MainAxisCellSize::Count(3), main_axis: Axis::X,
            spacing_x: 2.5, spacing_y: 3.0, backfill: true,
        },
        ..row()
    }).unwrap();
    let item = tree.add_node(&first, LayoutParams { size: Xy::new_symm(Size::Fill), ..LayoutParams::DEFAULT }).unwrap();
    let child = tree.add_node_with_context(&item, label(), 33).unwrap();
    let neighbor = tree.add_node_with_context(&grid, label(), 9).unwrap();
    tree.set_pixel_scale(Some(PixelScale::new(1.5).unwrap()));
    solve(&mut tree, WINDOW);

    tree.move_node(&item, Destination::Before(&neighbor)).unwrap();
    tree.add_node_with_context(&first, label(), 41).unwrap();
    tree.update_node_context(&child, Some(67)).unwrap();
    let measured = compare_structural(&mut tree, WINDOW);
    assert!(measured.contains(&child));

    let mut changed = *tree.params(&item).unwrap();
    changed.grid_span.x = 2;
    tree.update_node_params(&item, changed).unwrap();
    compare_full(&mut tree, WINDOW);
    tree.update_node_context(&neighbor, Some(51)).unwrap();
    compare_full(&mut tree, Xy::new(517.0, 480.0));

    tree.move_node(&item, Destination::LastChildOf(&first)).unwrap();
    let (outcome, measured) = compare_full(&mut tree, Xy::new(517.0, 480.0));
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert!(!measured.contains(&cold_label));
}

#[test]
fn pending_edits_in_a_removed_subtree_do_not_reach_reused_slots() {
    let (mut tree, panel, _) = independent_panels();
    let group = tree.add_node(&panel, row()).unwrap();
    let text = tree.add_node_with_context(&group, label(), 13).unwrap();
    solve(&mut tree, WINDOW);

    tree.update_node_context(&text, Some(28)).unwrap();
    let mut style = *tree.params(&group).unwrap();
    style.size.x = Size::Pixels(37.0);
    tree.update_node_params(&group, style).unwrap();
    tree.add_node_with_context(&group, label(), 7).unwrap();
    tree.remove(&group).unwrap();
    let replacement = tree.add_node_with_context(&panel, label(), 61).unwrap();
    assert_ne!(replacement, group);
    assert_ne!(replacement, text);
    compare_structural(&mut tree, WINDOW);
    assert_eq!(tree.layout(&replacement).unwrap().x, [0.0, 61.0]);

    tree.update_node_context(&replacement, Some(75)).unwrap();
    compare_full(&mut tree, WINDOW);
    assert_eq!(tree.layout(&replacement).unwrap().x, [0.0, 75.0]);
}

#[test]
fn a_structural_edit_can_introduce_and_remove_a_sizing_cycle() {
    let (mut tree, panel, _) = independent_panels();
    solve(&mut tree, WINDOW);
    let cyclic = tree.add_node(&panel, LayoutParams {
        size: Xy::new_symm(Size::AspectRatio(1.5)),
        ..LayoutParams::DEFAULT
    }).unwrap();
    compare_structural(&mut tree, WINDOW);
    assert!(tree.warnings().contains(&LayoutWarning::AspectRatioOnBothAxes { node: cyclic.clone().into() }));
    assert!(tree.warnings().iter().any(|warning| matches!(warning, LayoutWarning::Cycle { node, .. } if node == &*cyclic)));

    let sibling = tree.add_node_with_context(&panel, label(), 5).unwrap();
    compare_structural(&mut tree, WINDOW);
    tree.remove(&sibling).unwrap();
    tree.remove(&cyclic).unwrap();
    compare_structural(&mut tree, WINDOW);
    assert!(tree.warnings().is_empty());
    assert_eq!(solve(&mut tree, WINDOW).0, IncrementalRelayoutOutcome::Success { computed: 0 });
    let replacement = tree.add_node_with_context(&panel, label(), 25).unwrap();
    let (outcome, _) = compare_full(&mut tree, WINDOW);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert_eq!(tree.layout(&replacement).unwrap().x, [0.0, 25.0]);
}

#[test]
fn moving_a_cyclic_leaf_replays_the_full_axis_order() {
    let window = Xy::new(100.0, 80.0);
    let mut tree = LayoutTree::<()>::new();
    let fixed_parent = LayoutParams {
        size: Xy::new(Size::Pixels(31.0), Size::Pixels(18.0)),
        children_layout: ChildrenLayout::Free,
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    };
    let first = tree.add_node(&tree.root(), fixed_parent).unwrap();
    let second = tree.add_node(&tree.root(), LayoutParams {
        position: Xy::new(Pos::Pixels(43.0), Pos::Pixels(17.0)),
        ..fixed_parent
    }).unwrap();
    let leaf = tree.add_node(&first, LayoutParams {
        size: Xy::new(Size::AspectRatio(2.0), Size::AspectRatio(4.0)),
        min_size: Xy::new(Some(Size::Pixels(7.0)), Some(Size::Pixels(1.0))),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    }).unwrap();

    tree.solve_layout(window);
    assert_eq!(tree.layout(&leaf).unwrap(), Xy::new([0.0, 7.0], [0.0, 1.0]));
    tree.move_node(&leaf, Destination::LastChildOf(&second)).unwrap();
    let mut full = tree.clone();
    full.invalidate();
    full.solve_layout(window);
    assert!(matches!(
        tree.solve_layout(window),
        IncrementalRelayoutOutcome::Success { .. }
    ));
    // Starting with Y would read the completed X minimum in the ratio and
    // produce height 7/4. Starting with X sees the provisional X value in Y.
    assert_eq!(tree.layout(&leaf).unwrap(), Xy::new([43.0, 50.0], [17.0, 18.0]));
    assert_same_view(&tree, &full);
}

#[test]
fn moving_a_cyclic_subtree_uses_the_new_fixed_parent_boundary() {
    let window = Xy::new(160.0, 80.0);
    let mut tree = LayoutTree::<()>::new();
    let fixed = LayoutParams {
        size: Xy::new(Size::Pixels(30.0), Size::Pixels(18.0)),
        children_layout: ChildrenLayout::Free,
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    };
    let first = tree.add_node(&tree.root(), fixed).unwrap();
    let second = tree.add_node(&tree.root(), LayoutParams {
        size: Xy::new(Size::Pixels(60.0), Size::Pixels(18.0)),
        position: Xy::new(Pos::Pixels(43.0), Pos::Pixels(17.0)),
        ..fixed
    }).unwrap();
    let region = tree.add_node(&first, LayoutParams {
        size: Xy::new(Size::Frac(0.5), Size::FitContent),
        children_layout: ChildrenLayout::Free,
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    }).unwrap();
    tree.add_node(&region, LayoutParams {
        size: Xy::new(Size::AspectRatio(2.0), Size::AspectRatio(4.0)),
        min_size: Xy::new(Some(Size::Pixels(7.0)), Some(Size::Pixels(1.0))),
        ..LayoutParams::DEFAULT
    }).unwrap();

    tree.solve_layout(window);
    assert_eq!(tree.layout(&region).unwrap().x, [0.0, 15.0]);
    tree.move_node(&region, Destination::LastChildOf(&second)).unwrap();
    let mut full = tree.clone();
    full.invalidate();
    full.solve_layout(window);
    assert!(matches!(
        tree.solve_layout(window),
        IncrementalRelayoutOutcome::Success { .. }
    ));
    assert_eq!(tree.layout(&region).unwrap().x, [43.0, 73.0]);
    assert_same_view(&tree, &full);
}

#[test]
fn edits_below_a_disabled_parent_take_effect_when_reenabled() {
    let (mut tree, panel, _) = independent_panels();
    let child = tree.add_node_with_context(&panel, label(), 35).unwrap();
    solve(&mut tree, WINDOW);

    let mut style = *tree.params(&panel).unwrap();
    style.disabled = true;
    tree.update_node_params(&panel, style).unwrap();
    tree.update_node_context(&child, Some(51)).unwrap();
    let new = tree.add_node_with_context(&panel, label(), 23).unwrap();
    let calls = compare_structural(&mut tree, WINDOW);
    assert!(!calls.contains(&child));
    assert!(!calls.contains(&new));

    style.disabled = false;
    tree.update_node_params(&panel, style).unwrap();
    compare_structural(&mut tree, WINDOW);
    assert_eq!(tree.layout(&child).unwrap().x, [0.0, 51.0]);
    assert_eq!(tree.layout(&new).unwrap().x, [53.0, 76.0]);
}

#[test]
fn resizing_a_large_fill_group_reuses_unchanged_intrinsic_measurements() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        children_layout: ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 0.0 },
        ..*tree.params(&root).unwrap()
    }).unwrap();
    let item = LayoutParams {
        size: Xy::new(Size::FitContent, Size::Fill),
        content_measure: ContentMeasure::Independent,
        ..label()
    };
    for _ in 0..1024 {
        tree.add_node_with_context(&root, item, 15).unwrap();
    }
    solve(&mut tree, WINDOW);
    let inserted = tree.add_node_with_context(&root, item, 27).unwrap();
    let measured = compare_structural(&mut tree, WINDOW);
    assert_eq!(measured, [NodeId::from(inserted.clone())]);

    tree.remove(&inserted).unwrap();
    assert!(compare_structural(&mut tree, WINDOW).is_empty());
}

#[test]
fn stack_tail_batches_cross_the_zero_share_boundary() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    let stack = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::Pixels(80.0), Size::Pixels(10.0)),
        children_layout: ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 3.5 },
        ..row()
    }).unwrap();
    let item = LayoutParams { size: Xy::new(Size::FitContent, Size::Fill), ..label() };
    let stretch = LayoutParams { size: Xy::new_symm(Size::Fill), ..item };
    let first = tree.add_node_with_context(&stack, stretch, 12).unwrap();
    tree.add_node_with_context(&stack, item, 13).unwrap();
    let third = tree.add_node_with_context(&stack, item, 14).unwrap();
    solve(&mut tree, WINDOW);
    assert_eq!(tree.layout(&first).unwrap().y, [0.0, 1.0]);

    let fourth = tree.add_node_with_context(&stack, item, 15).unwrap();
    let fifth = tree.add_node_with_context(&stack, stretch, 16).unwrap();
    assert_eq!(compare_structural(&mut tree, WINDOW), [NodeId::from(fourth.clone())]);
    assert_eq!(tree.layout(&first).unwrap().y, [0.0, 0.0]);
    assert_eq!(tree.layout(&fifth).unwrap().y, [14.0, 14.0]);

    tree.remove(&fifth).unwrap();
    let (outcome, calls) = compare_full(&mut tree, WINDOW);
    assert_eq!(outcome, IncrementalRelayoutOutcome::Success { computed: 0 });
    assert!(calls.is_empty());

    tree.remove(&fourth).unwrap();
    tree.remove(&third).unwrap();
    let replacement = tree.add_node_with_context(&stack, LayoutParams { fill_weight: 2.0, ..item }, 17).unwrap();
    assert_eq!(compare_structural(&mut tree, WINDOW), [NodeId::from(replacement.clone())]);
    assert_eq!(tree.layout(&first).unwrap().y, [0.0, 0.75]);
    assert_eq!(tree.layout(&replacement).unwrap().y, [8.5, 10.0]);

    let old = *tree.params(&first).unwrap();
    tree.update_node_params(&first, LayoutParams { min_size: Xy::new(None, Some(Size::Pixels(2.0))), ..old }).unwrap();
    tree.remove(&replacement).unwrap();
    compare_structural(&mut tree, WINDOW);
}

#[test]
fn changing_a_stack_tail_redistributes_space_around_pixel_bounds() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        size: Xy::new_symm(Size::Pixels(100.0)),
        children_layout: ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 0.0 },
        ..row()
    }).unwrap();
    let item = LayoutParams { size: Xy::new(Size::FitContent, Size::Fill), ..label() };
    tree.add_node_with_context(&root, LayoutParams { min_size: Xy::new(None, Some(Size::Pixels(60.0))), ..item }, 1).unwrap();
    tree.add_node_with_context(&root, LayoutParams { max_size: Xy::new(None, Some(Size::Pixels(10.0))), ..item }, 2).unwrap();
    let flexible = tree.add_node_with_context(&root, item, 3).unwrap();
    solve(&mut tree, WINDOW);
    assert_eq!(tree.layout(&flexible).unwrap().y, [70.0, 100.0]);

    let added = tree.add_node_with_context(&root, item, 4).unwrap();
    assert_eq!(compare_structural(&mut tree, WINDOW), [NodeId::from(added.clone())]);
    assert_eq!(tree.layout(&flexible).unwrap().y, [70.0, 85.0]);
    tree.remove(&added).unwrap();
    assert!(compare_structural(&mut tree, WINDOW).is_empty());
    assert_eq!(tree.layout(&flexible).unwrap().y, [70.0, 100.0]);
}

#[test]
fn fit_content_root_tracks_insertions_and_removals() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams { size: Xy::new_symm(Size::FitContent), ..row() }).unwrap();
    tree.add_node_with_context(&root, label(), 21).unwrap();
    solve(&mut tree, WINDOW);

    let second = tree.add_node_with_context(&root, label(), 37).unwrap();
    assert!(compare_structural(&mut tree, WINDOW).contains(&second));
    assert_eq!(tree.layout(&root).unwrap().x, [0.0, 60.0]);
    tree.remove(&second).unwrap();
    assert!(compare_structural(&mut tree, WINDOW).is_empty());
    assert_eq!(tree.layout(&root).unwrap().x, [0.0, 21.0]);
}

#[test]
fn structural_style_and_content_edits_use_the_new_window() {
    let (mut tree, panel, cold_label) = independent_panels();
    let mut style = *tree.params(&panel).unwrap();
    style.size.x = Size::Frac(0.5);
    tree.update_node_params(&panel, style).unwrap();
    let child = tree.add_node_with_context(&panel, label(), 27).unwrap();
    solve(&mut tree, WINDOW);

    tree.update_node_context(&child, Some(45)).unwrap();
    style.children_layout = ChildrenLayout::Block;
    tree.update_node_params(&panel, style).unwrap();
    let measured = compare_structural(&mut tree, Xy::new(400.0, 300.0));
    assert!(measured.contains(&child));
    assert!(!measured.contains(&cold_label));
    let [left, right] = tree.layout(&panel).unwrap().x;
    assert_eq!(right - left, 200.0);
}

#[test]
fn coupled_edits_recheck_wrapping_measurements_at_the_resolved_width() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, row()).unwrap();
    let item = LayoutParams { size: Xy::new(Size::Fill, Size::FitContent), ..label() };
    let a = tree.add_node_with_context(&root, item, 93).unwrap();
    let b = tree.add_node_with_context(&root, item, 142).unwrap();
    solve(&mut tree, WINDOW);

    tree.move_node(&b, Destination::Before(&a)).unwrap();
    let measured = compare_structural(&mut tree, WINDOW);
    assert!(!measured.contains(&a));

    let c = tree.add_node_with_context(&root, item, 215).unwrap();
    let measured = compare_structural(&mut tree, WINDOW);
    assert!(measured.contains(&a) && measured.contains(&b) && measured.contains(&c));
    tree.update_node_context(&b, Some(44)).unwrap();
    tree.move_node(&c, Destination::Before(&b)).unwrap();
    let measured = compare_structural(&mut tree, WINDOW);
    assert!(measured.contains(&b));
    assert!(!measured.contains(&a));
}

#[test]
fn a_clean_fixed_panel_keeps_its_internal_flow_and_measurements() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, row()).unwrap();
    let panel = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::Pixels(68.0), Size::Pixels(76.0)),
        children_layout: ChildrenLayout::Block,
        ..row()
    }).unwrap();
    let container = tree.add_node_with_context(&panel, LayoutParams {
        children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 1.0, line_spacing: 2.0 },
        size: Xy::new(Size::Fill, Size::FitContent),
        ..label()
    }, 37).unwrap();
    tree.add_node_with_context(&container, label(), 41).unwrap();
    tree.add_node_with_context(&container, label(), 50).unwrap();
    let flex = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    solve(&mut tree, WINDOW);

    let added = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    assert!(compare_structural(&mut tree, WINDOW).is_empty());
    assert_eq!(tree.layout(&flex).unwrap().x[1] - tree.layout(&flex).unwrap().x[0], 54.0);

    tree.update_node_context(&container, Some(97)).unwrap();
    tree.remove(&added).unwrap();
    assert!(compare_structural(&mut tree, WINDOW).contains(&container));
    tree.add_node_with_context(&container, label(), 21).unwrap();
    compare_structural(&mut tree, WINDOW);
}

#[test]
fn reparenting_reuses_content_at_the_same_width_and_refreshes_changed_inputs() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    let mut panel = LayoutParams { children_layout: ChildrenLayout::Free, ..row() };
    let first = tree.add_node(&root, panel).unwrap();
    let second = tree.add_node(&root, panel).unwrap();
    panel.size.x = Size::Pixels(63.0);
    let narrow = tree.add_node(&root, panel).unwrap();
    let item = tree.add_node_with_context(&first, LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent), ..label()
    }, 149).unwrap();
    solve(&mut tree, WINDOW);

    tree.move_node(&item, Destination::LastChildOf(&second)).unwrap();
    assert!(compare_structural(&mut tree, WINDOW).is_empty());
    tree.move_node(&item, Destination::LastChildOf(&narrow)).unwrap();
    assert_eq!(compare_structural(&mut tree, WINDOW), [NodeId::from(item.clone())]);
    tree.move_node(&item, Destination::LastChildOf(&first)).unwrap();
    compare_structural(&mut tree, WINDOW);
    tree.update_node_context(&item, Some(215)).unwrap();
    tree.move_node(&item, Destination::LastChildOf(&second)).unwrap();
    assert_eq!(compare_structural(&mut tree, WINDOW), [NodeId::from(item.clone())]);
}

#[test]
fn cyclic_block_region_keeps_nested_margins_and_full_placement() {
    let mut tree: LayoutTree<u32> = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        size: Xy::new(Size::Pixels(200.0), Size::Pixels(130.0)),
        children_layout: ChildrenLayout::Free,
        ..LayoutParams::DEFAULT
    }).unwrap();
    let cold = tree.add_node_with_context(&root, label(), 37).unwrap();
    let parent = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::Pixels(100.0), Size::FitContent),
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    }).unwrap();
    let nested = tree.add_node(&parent, LayoutParams {
        size: Xy::new(Size::Auto, Size::Fill),
        min_size: Xy::new(None, Some(Size::Frac(0.65))),
        margin: Xy::new([Margin::ZERO; 2], [Margin::px(4.0).unwrap(), Margin::px(-3.0).unwrap()]),
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    }).unwrap();
    tree.set_pixel_scale(Some(PixelScale::new(1.25).unwrap()));
    solve(&mut tree, WINDOW);

    let cyclic = tree.add_node(&nested, LayoutParams {
        size: Xy::new(Size::AspectRatio(2.0), Size::AspectRatio(0.5)),
        min_size: Xy::new(Some(Size::Pixels(5.0)), Some(Size::Pixels(7.0))),
        margin: Xy::new([Margin::ZERO; 2], [Margin::px(8.5).unwrap(), Margin::px(-2.25).unwrap()]),
        ..LayoutParams::DEFAULT
    }).unwrap();
    let measured = compare_structural(&mut tree, WINDOW);
    assert!(!measured.contains(&cold));
    assert!(tree.warnings().iter().any(|w| matches!(w, LayoutWarning::Cycle { node, .. } if node == &*cyclic)));
    assert_eq!(tree.layout(&nested).unwrap().y[0], tree.layout(&cyclic).unwrap().y[0]);
    let before = tree.layout(&parent).unwrap().y;

    let separator = tree.add_node(&nested, LayoutParams {
        size: Xy::new(Size::Auto, Size::Pixels(6.5)),
        margin: Xy::new([Margin::ZERO; 2], [Margin::px(13.25).unwrap(), Margin::px(5.0).unwrap()]),
        ..LayoutParams::DEFAULT
    }).unwrap();
    tree.move_node(&separator, Destination::Before(&cyclic)).unwrap();
    assert!(!compare_structural(&mut tree, WINDOW).contains(&cold));
    assert_ne!(before, tree.layout(&parent).unwrap().y);

    tree.remove(&cyclic).unwrap();
    assert!(!compare_structural(&mut tree, WINDOW).contains(&cold));
    assert!(tree.warnings().iter().all(|w| !matches!(w, LayoutWarning::Cycle { .. })));
}

#[test]
fn cyclic_stack_share_replays_declared_bounds_in_document_order() {
    let mut tree: LayoutTree<u32> = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        size: Xy::new(Size::Pixels(200.0), Size::Pixels(130.0)),
        children_layout: ChildrenLayout::Free,
        ..LayoutParams::DEFAULT
    }).unwrap();
    let cold = tree.add_node_with_context(&root, label(), 37).unwrap();
    let stack = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::FitContent, Size::Pixels(20.0)),
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 2.75 },
        ..LayoutParams::DEFAULT
    }).unwrap();
    let fill = tree.add_node(&stack, LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(8.0)),
        fill_weight: 2.0,
        ..LayoutParams::DEFAULT
    }).unwrap();
    tree.set_pixel_scale(Some(PixelScale::new(1.25).unwrap()));
    solve(&mut tree, WINDOW);

    let cyclic = tree.add_node(&stack, LayoutParams {
        size: Xy::new(Size::Fill, Size::AspectRatio(0.75)),
        min_size: Xy::new(Some(Size::AspectRatio(1.5)), Some(Size::Pixels(7.0))),
        max_size: Xy::new(Some(Size::Pixels(42.0)), None),
        margin: Xy::new([Margin::px(1.25).unwrap(), Margin::px(-0.5).unwrap()], [Margin::ZERO; 2]),
        fill_weight: 1.5,
        ..LayoutParams::DEFAULT
    }).unwrap();
    assert!(!compare_structural(&mut tree, WINDOW).contains(&cold));
    assert!(tree.warnings().contains(&LayoutWarning::Cycle { node: stack.clone().into(), axis: Axis::X }));
    let previous = tree.layout(&cyclic).unwrap().x;
    tree.move_node(&cyclic, Destination::Before(&fill)).unwrap();
    assert!(!compare_structural(&mut tree, WINDOW).contains(&cold));
    assert_ne!(previous, tree.layout(&cyclic).unwrap().x);

    tree.remove(&cyclic).unwrap();
    assert!(!compare_structural(&mut tree, WINDOW).contains(&cold));
    assert!(tree.warnings().iter().all(|w| !matches!(w, LayoutWarning::Cycle { .. })));
}
