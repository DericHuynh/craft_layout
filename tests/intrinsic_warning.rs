#![cfg(feature = "incremental")]

use keru_layout::*;

#[test]
fn zero_fitted_extent_only_warns_without_an_independent_source() {
    let zero = LayoutParams { size: Xy::new_symm(Size::Pixels(0.0)), ..LayoutParams::DEFAULT };
    let hidden = LayoutParams { disabled: true, ..zero };
    let free = LayoutParams { free_placement: true, ..zero };
    for axis in [Axis::X, Axis::Y] {
        for (preferred, minimum, sibling, text, should_warn) in [
            (Size::Fill, None, None, TextContent::None, true),
            (Size::Frac(0.5), Some(Size::Pixels(0.0)), None, TextContent::None, true),
            (Size::Fill, None, Some(hidden), TextContent::None, true),
            (Size::Fill, None, Some(free), TextContent::None, true),
            (Size::Fill, None, Some(zero), TextContent::None, false),
            (Size::Fill, Some(Size::FitContent), None, TextContent::None, false),
            (Size::Fill, None, None, TextContent::Fixed, false),
        ] {
            let mut tree = LayoutTree::<()>::new();
            let root = tree.root();
            let mut row = LayoutParams {
                children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: 0.0 },
                size: Xy::new_symm(Size::Pixels(20.0)), text, ..LayoutParams::DEFAULT
            };
            row.size[axis] = Size::FitContent;
            tree.update_node_params(&root, row).unwrap();
            let mut item = zero;
            item.size[axis] = preferred;
            item.min_size[axis] = minimum;
            tree.add_node(&root, item).unwrap();
            if let Some(sibling) = sibling { tree.add_node(&root, sibling).unwrap(); }
            tree.solve_layout_with_measure(Xy::new_symm(100.0), |_, _, _| Xy::new_symm(0.0));
            let edges = tree.layout(&root).unwrap()[axis];
            assert_eq!(edges[1] - edges[0], 0.0);
            let expected = if should_warn {
                vec![LayoutWarning::FitContentCollapsed { node: root, axis }]
            } else { Vec::new() };
            assert_eq!(tree.warnings(), expected);
        }
    }
}
