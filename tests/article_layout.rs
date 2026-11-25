#![cfg(feature = "incremental")]

use keru_layout::{
    measure_monospace_text, Anchor, Arrange, Axis, ChildrenLayout, IncrementalRelayoutOutcome,
    LayoutParams, LayoutTree, Pos, Size, TextContent, Xy,
};

const WINDOW: Xy<f32> = Xy::new(300.0, 200.0);

enum Frame {
    First,
    Invalidated,
    Edited,
}

/// The giraffe example from https://kekelp.github.io/keru/blog/layout2/.
fn check_giraffe_layout(mut solve: impl FnMut(&mut LayoutTree<&'static str>, Frame)) {
    let mut tree: LayoutTree<&str> = LayoutTree::new();
    let root = tree.root();
    let fit = LayoutParams {
        size: Xy::new_symm(Size::FitContent),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    };
    let stack = |axis| LayoutParams {
        children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: 0.0 },
        ..fit
    };
    let panel = tree.add_node(&root, stack(Axis::X)).unwrap();
    let image = tree.add_node(&panel, LayoutParams {
        size: Xy::new(Size::AspectRatio(0.5), Size::Fill),
        ..fit
    }).unwrap();
    let column = tree.add_node(&panel, stack(Axis::Y)).unwrap();
    let label = tree.add_node_with_context(&column, LayoutParams {
        text: TextContent::Fixed, ..fit
    }, "0123456789").unwrap();
    let paragraph = tree.add_node_with_context(&column, LayoutParams {
        text: TextContent::Wrapping,
        size: Xy::new(Size::Fill, Size::FitContent),
        ..fit
    }, "four five").unwrap();

    // Keep this five-node dependency chain inside the incremental solver's work budget.
    for _ in 0..16 {
        tree.add_node(&root, LayoutParams { size: Xy::new_symm(Size::Pixels(1.0)), ..fit }).unwrap();
    }

    let check = |tree: &LayoutTree<&str>, label_width: f32, paragraph_lines: f32| {
        let line_height = 14.4;
        let height = line_height * (1.0 + paragraph_lines);
        let image_width = height * 0.5;
        let width = image_width + label_width;
        for (name, id, expected) in [
            ("panel", &panel, [0.0, 0.0, width, height]),
            ("image", &image, [0.0, 0.0, image_width, height]),
            ("column", &column, [image_width, 0.0, width, height]),
            ("label", &label, [image_width, 0.0, width, line_height]),
            ("paragraph", &paragraph, [image_width, line_height, width, height]),
        ] {
            let rect = tree.layout(id).unwrap();
            let actual = [rect.x[0], rect.y[0], rect.x[1], rect.y[1]];
            assert!(actual.iter().zip(expected).all(|(a, e)| (a - e).abs() < 0.001),
                "{name}: expected {expected:?}, got {actual:?}");
        }
        assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
    };

    // The sample measurer uses 7.2 px per character. The nine-character paragraph
    // fits on one line below a ten-character label and wraps below an eight-character label.
    solve(&mut tree, Frame::First);
    check(&tree, 72.0, 1.0);
    // The Batch entry point delegates its first frame to the default solver.
    // Invalidate once to exercise a Batch full solve before the first edit.
    tree.invalidate();
    solve(&mut tree, Frame::Invalidated);
    check(&tree, 72.0, 1.0);
    for (text, width, lines) in [("01234567", 57.6, 2.0), ("0123456789", 72.0, 1.0)] {
        tree.update_node_context(&label, Some(text)).unwrap();
        solve(&mut tree, Frame::Edited);
        check(&tree, width, lines);

        tree.invalidate();
        solve(&mut tree, Frame::Invalidated);
        check(&tree, width, lines);
    }
}

#[test]
fn wrapping_to_label_width_determines_the_image_and_panel_size() {
    check_giraffe_layout(|tree, frame| {
        let outcome = tree.solve_layout_with_measure(WINDOW, measure_monospace_text);
        match frame {
            Frame::First => {}
            Frame::Invalidated => assert_eq!(outcome, IncrementalRelayoutOutcome::FallbackInvalidated),
            Frame::Edited => assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}"),
        }
    });
}

#[cfg(feature = "batch-pilot")]
#[test]
fn batch_propagates_label_edits_through_the_same_dependency_chain() {
    let mut captured = false;
    check_giraffe_layout(|tree, frame| {
        let stats = tree.solve_layout_batch_with_measure(WINDOW, measure_monospace_text).unwrap();
        match frame {
            Frame::First => assert_eq!(stats, keru_layout::BatchLayoutStats::default()),
            Frame::Invalidated | Frame::Edited => {
                assert!(stats.computed > 0, "{stats:?}");
                assert_eq!(stats.rebuilt_graph, !captured, "{stats:?}");
                captured = true;
            }
        }
    });
}
