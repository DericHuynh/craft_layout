#![cfg(feature = "incremental")]

use keru_layout::{ChildrenLayout, Destination, IncrementalRelayoutOutcome, LayoutParams, LayoutTree, Size, TextContent, TreeError, Xy};

#[test]
fn invalid_edits_leave_the_tree_unchanged() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let left = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    let right = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    let nested = tree.add_node(&left, LayoutParams::DEFAULT).unwrap();
    let mut other = LayoutTree::<()>::new();
    let other_root = other.root();
    let foreign = other.add_node(&other_root, LayoutParams::DEFAULT).unwrap();

    assert!(root.as_child().is_none());
    assert_eq!(tree.move_node(&left, Destination::LastChildOf(&nested)), Err(TreeError::WouldCreateCycle));
    assert_eq!(tree.move_node(&left, Destination::Before(&nested)), Err(TreeError::WouldCreateCycle));
    assert_eq!(tree.move_node(&left, Destination::Before(&left)), Err(TreeError::BeforeSelf));
    assert_eq!(tree.move_node(&left, Destination::Before(&foreign)), Err(TreeError::ForeignNode));
    assert_eq!(tree.add_node(&other_root, LayoutParams::DEFAULT), Err(TreeError::ForeignNode));
    assert_eq!(tree.remove(&foreign), Err(TreeError::ForeignNode));
    assert!(tree.children(&root).unwrap().eq([left.clone(), right.clone()]));
    assert_eq!(tree.parent(&nested).unwrap().as_ref(), Some(&*left));

    tree.move_node(&nested, Destination::Before(&right)).unwrap();
    assert!(tree.children(&root).unwrap().eq([left, nested, right]));
}

#[test]
fn clones_and_reused_slots_cannot_resolve_another_nodes_handle() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let first = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    let mut clone = tree.clone();
    let clone_root = clone.root();
    let clone_first = clone.children(&clone_root).unwrap().next().unwrap();
    assert_eq!(clone.params(&first), Err(TreeError::ForeignNode));
    assert_eq!(tree.params(&clone_first), Err(TreeError::ForeignNode));
    clone.remove(&clone_first).unwrap();
    tree.remove(&first).unwrap();
    let replacement = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    assert_ne!(first, replacement);
    assert_eq!(tree.layout(&first), Err(TreeError::StaleNode));
    assert_eq!(tree.remove(&first), Err(TreeError::StaleNode));
    assert_eq!(tree.move_node(&first, Destination::LastChildOf(&root)), Err(TreeError::StaleNode));
    assert_eq!(tree.move_node(&replacement, Destination::Before(&first)), Err(TreeError::StaleNode));
    assert!(tree.children(&root).unwrap().eq([replacement]));
    assert_eq!(tree.update_node_params(&first, LayoutParams::DEFAULT), Err(TreeError::StaleNode));
    assert_eq!(tree.parent(&first), Err(TreeError::StaleNode));
    assert!(matches!(tree.children(&first), Err(TreeError::StaleNode)));
    assert_eq!(tree.mark_content_changed(&first), Err(TreeError::StaleNode));
    assert!(matches!(LayoutTree::<()>::with_capacity(usize::MAX), Err(TreeError::Capacity)));
}

#[test]
fn rectangles_only_become_available_after_placement() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let node = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    let window = Xy::new_symm(100.0);
    assert_eq!(tree.layout(&root), Err(TreeError::LayoutUnavailable));
    assert_eq!(tree.layout(&node), Err(TreeError::LayoutUnavailable));
    tree.solve_layout(window);
    assert_eq!(tree.layout(&node).unwrap(), Xy::new_symm([0.0, 100.0]));

    let mut params = *tree.params(&node).unwrap();
    params.disabled = true;
    tree.update_node_params(&node, params).unwrap();
    assert_eq!(tree.layout(&node), Err(TreeError::LayoutUnavailable));
    params.disabled = false;
    tree.update_node_params(&node, params).unwrap();
    assert_eq!(tree.layout(&node), Err(TreeError::LayoutUnavailable));
    tree.solve_layout(window);
    assert_eq!(tree.layout(&node).unwrap(), Xy::new_symm([0.0, 100.0]));
}

#[test]
fn idle_owned_frames_keep_geometry_until_an_input_changes() {
    use keru_layout::{PixelScale, Pos};

    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let mut params = LayoutParams {
        size: Xy::new_symm(Size::Pixels(3.25)),
        position: Xy::new_symm(Pos::Pixels(1.25)),
        ..LayoutParams::DEFAULT
    };
    let child = tree.add_node(&root, params).unwrap();
    let window = Xy::new_symm(30.0);
    tree.solve_layout(window);
    let bits = |rect: keru_layout::XyRect| Xy::new(rect.x.map(f32::to_bits), rect.y.map(f32::to_bits));
    let snapshot = |tree: &LayoutTree<()>| bits(tree.layout(&child).unwrap());
    let compare_full = |tree: &LayoutTree<()>| {
        let mut reference = tree.clone();
        let reference_child = reference.children(&reference.root()).unwrap().next().unwrap();
        reference.invalidate();
        reference.solve_layout(window);
        assert_eq!(snapshot(tree), bits(reference.layout(&reference_child).unwrap()));
    };

    for edit in 0..3 {
        let prior = snapshot(&tree);
        assert_eq!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { computed: 0 });
        assert_eq!(snapshot(&tree), prior);
        compare_full(&tree);

        match edit {
            0 => tree.set_pixel_scale(Some(PixelScale::ONE)),
            1 => {
                params.position.x = Pos::Pixels(5.25);
                tree.update_node_params(&child, params).unwrap();
            }
            _ => {
                params.size.y = Size::Pixels(12.75);
                tree.update_node_params(&child, params).unwrap();
            }
        }
        tree.solve_layout(window);
        assert_ne!(snapshot(&tree), prior);
        compare_full(&tree);
    }
}

#[test]
fn a_clone_refreshes_measurements_in_its_new_handle_namespace() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let node = tree.add_node(&root, LayoutParams {
        text: TextContent::Fixed,
        size: Xy::new_symm(Size::FitContent),
        ..LayoutParams::DEFAULT
    }).unwrap();
    let window = Xy::new_symm(100.0);
    tree.solve_layout_with_measure(window, |id, _, _| {
        assert_eq!(&id, &*node);
        Xy::new_symm(12.0)
    });

    let mut cloned = tree.clone();
    let cloned_node = cloned.children(&cloned.root()).unwrap().next().unwrap();
    assert_eq!(cloned.layout(&cloned_node), tree.layout(&node));
    let measure_clone = |id, _: Option<&mut ()>, _| {
        assert_eq!(&id, &*cloned_node);
        Xy::new_symm(24.0)
    };
    assert_eq!(
        cloned.solve_layout_with_measure(window, measure_clone),
        IncrementalRelayoutOutcome::FallbackInvalidated,
    );
    let rect = cloned.layout(&cloned_node).unwrap();
    assert_eq!(rect.x[1] - rect.x[0], 24.0);
    cloned.invalidate();
    cloned.solve_layout_with_measure(window, measure_clone);
    assert_eq!(cloned.layout(&cloned_node), Ok(rect));
}

#[test]
fn moved_descendant_remeasures_after_its_hidden_cache_expires() {
    use keru_layout::{Arrange, Axis, Pos};

    let branch = LayoutParams {
        children_layout: ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 0.0 },
        size: Xy::new(Size::Fill, Size::FitContent),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    let window = Xy::new_symm(120.0);
    for history in 0..3 {
        let mut original = LayoutTree::<()>::new();
        let root = original.root();
        let source = original.add_node(&root, branch).unwrap();
        let target = original.add_node(&root, branch).unwrap();
        let leaf = original.add_node(&source, LayoutParams {
            size: Xy::new(Size::FitContent, Size::Pixels(12.0)),
            position: Xy::new_symm(Pos::Start),
            text: TextContent::Fixed,
            ..LayoutParams::DEFAULT
        }).unwrap();
        let old_measure = |_, _: Option<&mut ()>, _| Xy::new(4.0, 12.0);
        original.solve_layout_with_measure(window, old_measure);
        assert_eq!(original.layout(&leaf).unwrap().x, [0.0, 4.0]);

        if history == 1 { original.invalidate(); }
        original.update_node_params(&source, LayoutParams { disabled: true, ..branch }).unwrap();
        if history != 1 { original.solve_layout_with_measure(window, old_measure); }
        assert_eq!(original.layout(&leaf), Err(TreeError::LayoutUnavailable));

        let (mut tree, source, target, leaf) = if history == 2 {
            let clone = original.clone();
            let [source, target]: [_; 2] = clone.children(&clone.root()).unwrap()
                .collect::<Vec<_>>().try_into().unwrap();
            let leaf = clone.children(&source).unwrap().next().unwrap();
            (clone, source, target, leaf)
        } else {
            if history == 0 { original.invalidate(); }
            (original, source, target, leaf)
        };
        let measure = |id, _: Option<&mut ()>, _| {
            assert_eq!(&id, &*leaf);
            Xy::new(11.0, 12.0)
        };
        tree.solve_layout_with_measure(window, measure);
        assert_eq!(tree.layout(&leaf), Err(TreeError::LayoutUnavailable));
        tree.update_node_params(&source, branch).unwrap();
        tree.move_node(&leaf, Destination::LastChildOf(&target)).unwrap();
        let result = tree.solve_layout_with_measure(window, measure);
        assert!(matches!(result, IncrementalRelayoutOutcome::Success { .. }));
        let actual = tree.layout(&leaf).unwrap().x.map(f32::to_bits);
        tree.invalidate();
        tree.solve_layout_with_measure(window, measure);
        let reference = tree.layout(&leaf).unwrap().x.map(f32::to_bits);
        assert_eq!(reference, [0.0f32.to_bits(), 11.0f32.to_bits()]);
        assert_eq!(actual, reference, "history {history}");
    }
}

#[test]
fn a_panicking_context_destructor_cannot_leave_detached_live_nodes() {
    struct Context;
    impl Drop for Context {
        fn drop(&mut self) { panic!("test context destructor"); }
    }

    let mut tree = LayoutTree::new();
    let root = tree.root();
    let parent = tree.add_node_with_context(&root, LayoutParams::DEFAULT, Context).unwrap();
    let descendant = tree.add_node(&parent, LayoutParams::DEFAULT).unwrap();
    let retained = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tree.remove(&parent)));
    assert!(unwind.is_err());
    assert_eq!(tree.params(&parent), Err(TreeError::StaleNode));
    assert_eq!(tree.params(&descendant), Err(TreeError::StaleNode));
    assert!(tree.children(&root).unwrap().eq([retained.clone()]));

    let leaf = tree.add_node_with_context(&root, LayoutParams::DEFAULT, Context).unwrap();
    let unwind = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| tree.remove(&leaf)));
    assert!(unwind.is_err());
    assert_eq!(tree.params(&leaf), Err(TreeError::StaleNode));
    assert!(tree.children(&root).unwrap().eq([retained.clone()]));
    tree.solve_layout(Xy::new_symm(100.0));
    assert!(tree.layout(&retained).is_ok());
}

#[test]
fn full_and_incremental_solve_handle_a_deep_tree_on_a_small_stack() {
    std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
        let mut tree = LayoutTree::<()>::new();
        let mut leaf = tree.root();
        let style = LayoutParams {
            children_layout: ChildrenLayout::Free,
            size: Xy::new_symm(Size::Pixels(8.0)),
            ..LayoutParams::DEFAULT
        };
        for _ in 0..8_192 {
            leaf = tree.add_node(&leaf, style).unwrap().into();
        }
        let window = Xy::new_symm(400.0);
        tree.solve_layout(window);
        assert_eq!(tree.layout(&leaf), Ok(Xy::new_symm([196.0, 204.0])));

        // Rebuild the deep branch using the incremental structural API.
        tree.move_node(&leaf.as_child().unwrap(), Destination::LastChildOf(&tree.root())).unwrap();
        let leaf_params = LayoutParams { size: Xy::new_symm(Size::Pixels(16.0)), ..style };
        tree.update_node_params(&leaf, leaf_params).unwrap();
        let outcome = tree.solve_layout(window);
        assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }));
        assert_eq!(tree.layout(&leaf), Ok(Xy::new_symm([192.0, 208.0])));
    }).unwrap().join().unwrap();
}

#[test]
fn reenabled_width_grid_subtree_reloads_after_late_edits() {
    use keru_layout::{Arrange, Axis, MainAxisCellSize, Pos};
    let branch = LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        children_layout: ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 1.0 },
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    let leaf = LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        text: TextContent::Wrapping,
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    for history in 0..14 {
        let run = |forced: bool| {
            let mut tree = LayoutTree::<f32>::new();
            let grid = tree.add_node(&tree.root(), LayoutParams {
                children_layout: ChildrenLayout::Grid {
                    main_axis: Axis::X, columns: MainAxisCellSize::Width(100.0),
                    spacing_x: 7.0, spacing_y: 9.0, backfill: false,
                },
                size: Xy::new(Size::Fill, Size::FitContent),
                ..LayoutParams::DEFAULT
            }).unwrap();
            let card = tree.add_node(&grid, branch).unwrap();
            let other = tree.add_node(&grid, branch).unwrap();
            let title = tree.add_node_with_context(&card, leaf, 48.0).unwrap();
            let body = tree.add_node_with_context(&card, leaf, 1000.0).unwrap();
            let other_title = tree.add_node_with_context(&other, leaf, 1100.0).unwrap();
            let mut window = Xy::new(299.0, 200.0);
            let solve = |tree: &mut LayoutTree<f32>, win| {
                if forced { tree.invalidate(); }
                tree.solve_layout_with_measure(win, |_, word, width| {
                    let w = width.unwrap_or(400.0).max(1.0);
                    Xy::new(w, (word.map_or(0.0, |width| *width) / w).ceil())
                });
            };
            solve(&mut tree, window);
            let mut hidden_style = LayoutParams { disabled: true, ..branch };
            tree.update_node_params(&card, hidden_style).unwrap();
            if history < 11 { solve(&mut tree, window); }
            assert_eq!(tree.layout(&card), Err(TreeError::LayoutUnavailable));
            if history == 1 { tree.update_node_context(&body, Some(3200.0)).unwrap(); }
            if history == 2 { window.x = 167.0; }
            if history == 3 { tree.invalidate(); }
            if history == 4 { tree.move_node(&body, Destination::LastChildOf(&other)).unwrap(); }
            let dormant_order = tree.children(&card).unwrap().count();
            assert!(dormant_order >= 1);
            if history == 8 || history == 11 { tree.mark_content_changed(&card).unwrap(); }
            if history == 9 || history == 12 {
                hidden_style.padding.y[0] = 2.5;
                tree.update_node_params(&card, hidden_style).unwrap();
            }
            if history == 10 || history == 13 { tree.remove(&body).unwrap(); }
            if (8..=10).contains(&history) { solve(&mut tree, window); }
            tree.update_node_params(&card, LayoutParams { disabled: false, ..hidden_style }).unwrap();
            if history == 5 { tree.remove(&body).unwrap(); }
            if history == 6 { tree.update_node_context(&body, Some(7500.0)).unwrap(); }
            if history == 7 { tree.move_node(&body, Destination::LastChildOf(&other)).unwrap(); }
            solve(&mut tree, window);
            [grid, card, other, title, body, other_title].map(|id| {
                tree.layout(&id).map(|rect| (rect.x.map(f32::to_bits), rect.y.map(f32::to_bits)))
            })
        };
        assert_eq!(run(false), run(true), "history {history}");
    }
}

#[test]
fn flow_replay_publishes_the_same_nan_edges_as_full_layout() {
    use keru_layout::{Arrange, Axis, NodeId, Pos};

    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let fit = LayoutParams {
        position: Xy::new_symm(Pos::End),
        size: Xy::new_symm(Size::FitContent),
        ..LayoutParams::DEFAULT
    };
    tree.update_node_params(&root, fit).unwrap();
    let wrap = tree.add_node(&root, LayoutParams {
        children_layout: ChildrenLayout::Wrap {
            axis: Axis::X,
            arrange: Arrange::SpaceBetween,
            spacing: f32::NEG_INFINITY,
            line_spacing: f32::MAX,
        },
        ..fit
    }).unwrap();
    let stack = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::Pixels(16.0), Size::FitContent),
        padding: Xy::new([0.0; 2], [0.0, f32::from_bits(0xffa2_4abc)]),
        children_layout: ChildrenLayout::Stack {
            axis: Axis::Y,
            arrange: Arrange::SpaceBetween,
            spacing: f32::NEG_INFINITY,
        },
        ..fit
    }).unwrap();
    let leaf = tree.add_node(&wrap, fit).unwrap();
    tree.add_node(&stack, LayoutParams { free_placement: true, ..fit }).unwrap();

    let window = Xy::new_symm(1.0);
    tree.solve_layout(window);
    tree.mark_content_changed(&leaf).unwrap();
    let mut full = tree.clone();
    let outcome = tree.solve_layout(window);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { computed } if computed > 0), "{outcome:?}");
    full.solve_layout(window);

    let view = |tree: &LayoutTree<()>| {
        let mut pending = vec![tree.root()];
        let mut words = Vec::new();
        while let Some(node) = pending.pop() {
            let rect = tree.layout(&node).unwrap();
            words.push([rect.x.map(f32::to_bits), rect.y.map(f32::to_bits)]);
            pending.extend(tree.children(&node).unwrap().map(NodeId::from));
        }
        words
    };
    let incremental = view(&tree);
    assert_eq!(incremental, view(&full));
    assert!(incremental.iter().flatten().flatten().any(|&word| word == 0x7fc0_0000));
}

#[test]
fn fractional_anchor_with_pixel_offset_tracks_resizes_and_flipped_origins() {
    use keru_layout::{Anchor, Pos};

    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let mut parent = LayoutParams { padding: Xy::new([10.0, 20.0], [0.0; 2]), ..LayoutParams::DEFAULT };
    tree.update_node_params(&root, parent).unwrap();
    let mut style = LayoutParams {
        size: Xy::new(Size::Pixels(12.0), Size::Pixels(4.0)),
        position: Xy::new(Pos::Offset { fraction: 0.5, pixels: 3.0 }, Pos::Start),
        anchor: Xy::new(Anchor::End, Anchor::Start),
        ..LayoutParams::DEFAULT
    };
    let child = tree.add_node(&root, style).unwrap();
    let solve = |tree: &mut LayoutTree, width, expected| {
        tree.solve_layout(Xy::new(width, 40.0));
        assert_eq!(tree.layout(&child).unwrap().x, expected);
    };
    solve(&mut tree, 130.0, [51.0, 63.0]);
    solve(&mut tree, 230.0, [101.0, 113.0]);
    style.position.x = Pos::Offset { fraction: 0.25, pixels: 3.0 };
    tree.update_node_params(&child, style).unwrap();
    solve(&mut tree, 230.0, [51.0, 63.0]);
    style.position.x = Pos::Offset { fraction: 0.25, pixels: -5.0 };
    tree.update_node_params(&child, style).unwrap();
    solve(&mut tree, 230.0, [43.0, 55.0]);
    parent.children_origin_flipped.x = true;
    tree.update_node_params(&root, parent).unwrap();
    solve(&mut tree, 230.0, [165.0, 177.0]);
}
