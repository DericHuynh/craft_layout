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
    cloned.solve_layout_with_measure(window, |id, _, _| {
        assert_eq!(&id, &*cloned_node);
        Xy::new_symm(24.0)
    });
    let rect = cloned.layout(&cloned_node).unwrap();
    assert_eq!(rect.x[1] - rect.x[0], 24.0);
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
