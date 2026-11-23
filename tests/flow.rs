#![cfg(feature = "incremental")]

use keru_layout::*;

fn px(x: f32, y: f32) -> Xy<Size> {
    Xy::new(Size::Pixels(x), Size::Pixels(y))
}

fn rect(x: [f32; 2], y: [f32; 2]) -> XyRect {
    Xy::new(x, y)
}

fn edges(start: f32, end: f32) -> [Margin; 2] {
    [Margin::px(start).unwrap(), Margin::px(end).unwrap()]
}

#[test]
fn width_grid_with_zero_track_step_uses_one_column() {
    for (width, spacing) in [(0.0, 0.0), (8.0, -8.0)] {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        tree.update_node_params(&root, LayoutParams {
            children_layout: ChildrenLayout::Grid {
                columns: MainAxisCellSize::Width(width), main_axis: Axis::X,
                spacing_x: spacing, spacing_y: 0.0, backfill: true,
            },
            ..LayoutParams::DEFAULT
        }).unwrap();
        let first = tree.add_node(&root, LayoutParams {
            grid_span: Xy::new(2, 1), ..LayoutParams::DEFAULT
        }).unwrap();
        let second = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
        tree.solve_layout(Xy::new(100.0, 40.0));
        assert_eq!(tree.layout(&first).unwrap(), rect([0.0, 100.0], [0.0, 20.0]));
        assert_eq!(tree.layout(&second).unwrap(), rect([0.0, 100.0], [20.0, 40.0]));
    }
}

#[test]
fn wrap_reflows_on_resize_and_stretches_cross_fill_to_its_line() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        size: Xy::new(Size::Fill, Size::Auto),
        children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 5.0, line_spacing: 4.0 },
        padding: Xy::new([3.0, 7.0], [5.0, 6.0]),
        ..LayoutParams::DEFAULT
    }).unwrap();
    let first = tree.add_node(&root, LayoutParams {
        size: px(30.0, 10.0),
        margin: Xy::new(edges(2.0, 3.0), edges(1.0, 2.0)),
        ..LayoutParams::DEFAULT
    }).unwrap();
    let second = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::Pixels(40.0), Size::Fill),
        margin: Xy::new(edges(0.0, 0.0), edges(2.0, 3.0)),
        ..LayoutParams::DEFAULT
    }).unwrap();
    let free = tree.add_node(&root, LayoutParams {
        size: px(1000.0, 1000.0),
        position: Xy::new_symm(Pos::Start),
        margin: Xy::new_symm(edges(9.0, 9.0)),
        free_placement: true,
        ..LayoutParams::DEFAULT
    }).unwrap();
    let third = tree.add_node(&root, LayoutParams {
        size: px(30.0, 20.0),
        ..LayoutParams::DEFAULT
    }).unwrap();

    tree.solve_layout(Xy::new(100.0, 200.0));
    assert_eq!(tree.layout(&root).unwrap(), rect([0.0, 100.0], [0.0, 48.0]));
    assert_eq!(tree.layout(&first).unwrap(), rect([5.0, 35.0], [6.0, 16.0]));
    assert_eq!(tree.layout(&second).unwrap(), rect([43.0, 83.0], [7.0, 15.0]));
    assert_eq!(tree.layout(&third).unwrap(), rect([3.0, 33.0], [22.0, 42.0]));
    assert_eq!(tree.layout(&free).unwrap(), rect([3.0, 1003.0], [5.0, 1005.0]));
    assert!(tree.warnings().is_empty());

    assert_eq!(tree.solve_layout(Xy::new(130.0, 200.0)), IncrementalRelayoutOutcome::FallbackFlow);
    assert_eq!(tree.layout(&root).unwrap().y, [0.0, 31.0]);
    assert_eq!(tree.layout(&second).unwrap().y, [7.0, 22.0]);
    assert_eq!(tree.layout(&third).unwrap().x, [88.0, 118.0]);
}

#[test]
fn vertical_wrap_places_an_oversized_item_on_the_first_flipped_line() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        size: px(50.0, 25.0),
        children_origin_flipped: Xy::new_symm(true),
        children_layout: ChildrenLayout::Wrap { axis: Axis::Y, arrange: Arrange::Start, spacing: 1.0, line_spacing: 3.0 },
        ..LayoutParams::DEFAULT
    }).unwrap();
    let first = tree.add_node(&root, LayoutParams { size: px(10.0, 30.0), ..LayoutParams::DEFAULT }).unwrap();
    let second = tree.add_node(&root, LayoutParams { size: px(20.0, 10.0), ..LayoutParams::DEFAULT }).unwrap();
    tree.solve_layout(Xy::new_symm(100.0));
    assert_eq!(tree.layout(&first).unwrap(), rect([40.0, 50.0], [-5.0, 25.0]));
    assert_eq!(tree.layout(&second).unwrap(), rect([17.0, 37.0], [15.0, 25.0]));
}

#[test]
fn weighted_fill_is_distributed_within_each_wrap_line() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        size: Xy::new(Size::Fill, Size::Auto),
        children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 2.0, line_spacing: 3.0 },
        ..LayoutParams::DEFAULT
    }).unwrap();
    let proportional = |min, weight| LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(10.0)),
        min_size: Xy::new(Some(Size::Pixels(min)), None),
        fill_weight: weight,
        ..LayoutParams::DEFAULT
    };
    let first = tree.add_node(&root, proportional(50.0, 1.0)).unwrap();
    let second = tree.add_node(&root, proportional(0.0, 3.0)).unwrap();
    let third = tree.add_node(&root, proportional(60.0, 1.0)).unwrap();
    tree.solve_layout(Xy::new_symm(100.0));
    assert_eq!(tree.layout(&first).unwrap(), rect([0.0, 50.0], [0.0, 10.0]));
    assert_eq!(tree.layout(&second).unwrap(), rect([52.0, 100.0], [0.0, 10.0]));
    assert_eq!(tree.layout(&third).unwrap(), rect([0.0, 100.0], [13.0, 23.0]));
    assert!(tree.warnings().is_empty());
}

#[test]
fn inserting_into_a_fill_stack_rebuilds_the_enclosing_wraps_main_axis_share() {
    let mut tree: LayoutTree = LayoutTree::new();
    let window = Xy::new_symm(200.0);
    let start = Xy::new_symm(Pos::Start);
    let wrap = tree.add_node(&tree.root(), LayoutParams {
        size: Xy::new(Size::Pixels(180.0), Size::FitContent),
        children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 0.0, line_spacing: 0.0 },
        position: start, ..LayoutParams::DEFAULT
    }).unwrap();
    let fill = LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(10.0)), position: start, ..LayoutParams::DEFAULT
    };
    let stack = tree.add_node(&wrap, LayoutParams {
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 0.0 }, ..fill
    }).unwrap();
    let first = tree.add_node(&stack, fill).unwrap();
    tree.add_node(&stack, fill).unwrap();
    tree.solve_layout(window);
    assert_eq!(tree.layout(&first).unwrap(), rect([0.0, 90.0], [0.0, 10.0]));

    let last = tree.add_node(&stack, fill).unwrap();
    assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
    assert_eq!(tree.layout(&stack).unwrap(), rect([0.0, 180.0], [0.0, 10.0]));
    assert_eq!(tree.layout(&first).unwrap(), rect([0.0, 60.0], [0.0, 10.0]));
    assert_eq!(tree.layout(&last).unwrap(), rect([120.0, 180.0], [0.0, 10.0]));
}

#[test]
fn stack_fill_items_follow_incremental_weight_margin_and_pixel_changes() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    let mut stack = LayoutParams {
        size: Xy::new(Size::Pixels(110.0), Size::FitContent),
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 6.0 },
        padding: Xy::new([2.0, 2.0], [0.0; 2]),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    let row = tree.add_node(&root, stack).unwrap();
    let mut item = LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(6.0)),
        margin: Xy::new(edges(1.0, 3.0), edges(0.0, 0.0)),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    let first = tree.add_node(&row, item).unwrap();
    tree.add_node(&row, LayoutParams { disabled: true, ..LayoutParams::DEFAULT }).unwrap();
    let second = tree.add_node(&row, LayoutParams {
        size: Xy::new(Size::Fill, Size::Pixels(9.0)), fill_weight: 2.0,
        position: Xy::new_symm(Pos::Start), ..LayoutParams::DEFAULT
    }).unwrap();
    // The fixed descendants also leave room in the incremental solver's work budget.
    for _ in 0..64 {
        tree.add_node(&first, LayoutParams { size: px(2.0, 3.0), ..LayoutParams::DEFAULT }).unwrap();
    }
    let window = Xy::new_symm(250.0);
    tree.solve_layout(window);
    assert_eq!(tree.layout(&first).unwrap(), rect([3.0, 35.0], [0.0, 6.0]));
    assert_eq!(tree.layout(&second).unwrap(), rect([44.0, 108.0], [0.0, 9.0]));

    stack.size.x = Size::Pixels(126.0);
    tree.update_node_params(&row, stack).unwrap();
    item.size.y = Size::Pixels(15.0);
    item.margin.x = edges(3.0, 5.0);
    item.fill_weight = 2.0;
    tree.update_node_params(&first, item).unwrap();
    assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
    assert_eq!(tree.layout(&row).unwrap(), rect([0.0, 126.0], [0.0, 15.0]));
    assert_eq!(tree.layout(&first).unwrap(), rect([5.0, 59.0], [0.0, 15.0]));
    assert_eq!(tree.layout(&second).unwrap(), rect([70.0, 124.0], [0.0, 9.0]));
    assert!(tree.warnings().is_empty());
}

#[test]
fn margins_consume_stack_fill_and_grid_cell_space() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    let stack = tree.add_node(&root, LayoutParams {
        size: px(100.0, 40.0),
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 4.0 },
        ..LayoutParams::DEFAULT
    }).unwrap();
    let first = tree.add_node(&stack, LayoutParams { margin: Xy::new(edges(2.0, 6.0), edges(3.0, 5.0)), ..LayoutParams::DEFAULT }).unwrap();
    let second = tree.add_node(&stack, LayoutParams::DEFAULT).unwrap();
    let grid = tree.add_node(&root, LayoutParams {
        size: px(100.0, 40.0),
        children_layout: ChildrenLayout::Grid {
            columns: MainAxisCellSize::Count(2), spacing_x: 4.0, spacing_y: 0.0, main_axis: Axis::X, backfill: false,
        },
        ..LayoutParams::DEFAULT
    }).unwrap();
    let cell = tree.add_node(&grid, LayoutParams { margin: Xy::new(edges(3.0, 5.0), edges(1.0, 2.0)), ..LayoutParams::DEFAULT }).unwrap();
    tree.solve_layout(Xy::new(100.0, 40.0));
    assert_eq!(tree.layout(&first).unwrap(), rect([2.0, 46.0], [3.0, 35.0]));
    assert_eq!(tree.layout(&second).unwrap(), rect([56.0, 100.0], [0.0, 40.0]));
    assert_eq!(tree.layout(&cell).unwrap(), rect([3.0, 43.0], [1.0, 38.0]));
    assert!(tree.warnings().is_empty());
}

#[test]
fn block_auto_width_and_collapsing_positive_negative_and_empty_margins() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        size: Xy::new(Size::Fill, Size::Auto),
        children_layout: ChildrenLayout::Block,
        padding: Xy::new([5.0, 5.0], [0.0; 2]),
        ..LayoutParams::DEFAULT
    }).unwrap();
    let first = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::Auto, Size::Pixels(10.0)),
        margin: Xy::new(edges(2.0, 3.0), edges(12.0, 20.0)),
        ..LayoutParams::DEFAULT
    }).unwrap();
    tree.add_node(&root, LayoutParams { size: px(0.0, 0.0), margin: Xy::new(edges(0.0, 0.0), edges(-8.0, -15.0)), ..LayoutParams::DEFAULT }).unwrap();
    let centered = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::Pixels(30.0), Size::Frac(1.0)),
        margin: Xy::new([Margin::AUTO; 2], edges(7.0, 9.0)),
        image: Some(Xy::new(0.0, 5.0)),
        ..LayoutParams::DEFAULT
    }).unwrap();

    tree.solve_layout(Xy::new_symm(100.0));
    assert_eq!(tree.layout(&first).unwrap(), rect([7.0, 92.0], [12.0, 22.0]));
    assert_eq!(tree.layout(&centered).unwrap(), rect([35.0, 65.0], [27.0, 32.0]));
    assert_eq!(tree.layout(&root).unwrap().y, [0.0, 41.0]);
    assert!(tree.warnings().is_empty());
}

#[test]
fn nested_block_margins_collapse_with_parent_unless_padding_separates_them() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    let block = LayoutParams { size: Xy::new_symm(Size::Auto), children_layout: ChildrenLayout::Block, ..LayoutParams::DEFAULT };
    tree.update_node_params(&root, LayoutParams { size: Xy::new(Size::Fill, Size::Auto), ..block }).unwrap();
    let parent = tree.add_node(&root, LayoutParams { margin: Xy::new(edges(0.0, 0.0), edges(7.0, 8.0)), ..block }).unwrap();
    let child = tree.add_node(&parent, LayoutParams {
        size: Xy::new(Size::Auto, Size::Pixels(10.0)),
        margin: Xy::new(edges(0.0, 0.0), edges(12.0, 18.0)),
        ..LayoutParams::DEFAULT
    }).unwrap();

    tree.solve_layout(Xy::new_symm(100.0));
    assert_eq!(tree.layout(&parent).unwrap().y, [12.0, 22.0]);
    assert_eq!(tree.layout(&child).unwrap().y, [12.0, 22.0]);
    assert_eq!(tree.layout(&root).unwrap().y, [0.0, 40.0]);
    let mut params = *tree.params(&parent).unwrap();
    params.padding.y = [2.0, 3.0];
    tree.update_node_params(&parent, params).unwrap();

    assert_eq!(tree.solve_layout(Xy::new_symm(100.0)), IncrementalRelayoutOutcome::FallbackFlow);
    assert_eq!(tree.layout(&parent).unwrap().y, [7.0, 52.0]);
    assert_eq!(tree.layout(&child).unwrap().y, [21.0, 31.0]);
    assert_eq!(tree.layout(&root).unwrap().y, [0.0, 60.0]);
}

#[test]
fn custom_content_receives_inner_dimensions_and_remeasures_incrementally() {
    let mut tree = LayoutTree::<f32>::with_capacity(40).unwrap();
    let root = tree.root();
    for _ in 0..32 {
        tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    }
    let child = tree.add_node_with_context(&root, LayoutParams {
        size: Xy::new(Size::Pixels(32.0), Size::FitContent),
        padding: Xy::new([1.0; 2], [2.0; 2]),
        max_size: Xy::new(None, Some(Size::Pixels(55.0))),
        content_measure: ContentMeasure::HeightForWidth,
        ..LayoutParams::DEFAULT
    }, 2.0).unwrap();
    let measure = |_, factor: Option<&mut f32>, input: ContentMeasureInput| {
        assert_eq!(input.axis, Axis::Y);
        assert_eq!(input.known_dimensions.y, None);
        assert_eq!(input.max_size.y, Some(51.0));
        Xy::new(0.0, input.known_dimensions.x.unwrap() / *factor.unwrap())
    };

    tree.solve_layout_with_content_measure(Xy::new_symm(100.0), measure);
    assert_eq!(tree.layout(&child).unwrap().y, [40.5, 59.5]);
    let mut params = *tree.params(&child).unwrap();
    params.size.x = Size::Pixels(42.0);
    tree.update_node_params(&child, params).unwrap();
    tree.update_node_context(&child, Some(4.0)).unwrap();
    let outcome = tree.solve_layout_with_content_measure(Xy::new_symm(100.0), measure);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { computed: 1.. }));
    assert_eq!(tree.layout(&child).unwrap().y, [43.0, 57.0]);
}

#[test]
fn custom_content_can_use_a_resolved_height_without_replacing_text_measurement() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let child = tree.add_node(&root, LayoutParams {
        size: Xy::new(Size::Auto, Size::Frac(0.5)),
        padding: Xy::new([2.0, 3.0], [4.0, 6.0]),
        content_measure: ContentMeasure::WidthForHeight,
        text: TextContent::Fixed,
        ..LayoutParams::DEFAULT
    }).unwrap();
    tree.solve_layout_with_measurers(
        Xy::new_symm(100.0),
        |_, _, _| Xy::new(30.0, 0.0),
        |_, _, input| {
            assert_eq!(input.axis, Axis::X);
            assert_eq!(input.known_dimensions, Xy::new(None, Some(40.0)));
            Xy::new(20.0, 0.0)
        },
    );
    assert_eq!(tree.layout(&child).unwrap(), rect([32.5, 67.5], [25.0, 75.0]));
}

#[test]
fn pixel_rounding_tiles_nested_fractional_rectangles_and_can_be_disabled() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    let row = tree.add_node(&root, LayoutParams {
        size: px(10.0, 3.0),
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 0.0 },
        position: Xy::new_symm(Pos::Pixels(0.3)),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }).unwrap();
    let children = std::array::from_fn::<_, 3, _>(|_| tree.add_node(&row, LayoutParams::DEFAULT).unwrap());
    tree.set_pixel_scale(Some(PixelScale::new(2.0).unwrap()));
    tree.solve_layout(Xy::new_symm(100.0));
    let [first, second, third] = children.map(|child| tree.layout(&child).unwrap());
    assert_eq!(tree.layout(&row).unwrap().x, [0.5, 10.5]);
    assert_eq!(first.x, [0.5, 3.5]);
    assert_eq!(second.x, [3.5, 7.0]);
    assert_eq!(third.x, [7.0, 10.5]);
    tree.set_pixel_scale(None);
    assert_eq!(tree.solve_layout(Xy::new_symm(100.0)), IncrementalRelayoutOutcome::Success { computed: 0 });
    assert_eq!(tree.layout(&row).unwrap().x, [0.3, 10.3]);
}

#[test]
fn wrap_reuses_measured_lines_for_arrangement_edits() {
    let mut tree: LayoutTree = LayoutTree::new();
    let root = tree.root();
    let flow = |arrange, spacing, line_spacing| LayoutParams {
        size: Xy::new(Size::Fill, Size::Auto),
        children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange, spacing, line_spacing },
        ..LayoutParams::DEFAULT
    };
    let window = Xy::new_symm(100.0);
    tree.update_node_params(&root, flow(Arrange::Start, 0.0, 0.0)).unwrap();
    let [first, _, last] = std::array::from_fn(|_| {
        tree.add_node(&root, LayoutParams { size: px(45.0, 10.0), ..LayoutParams::DEFAULT }).unwrap()
    });
    tree.solve_layout(window);

    tree.update_node_params(&root, flow(Arrange::End, 0.0, 0.0)).unwrap();
    assert_eq!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { computed: 0 });
    assert_eq!(tree.layout(&first).unwrap(), rect([10.0, 55.0], [0.0, 10.0]));
    assert_eq!(tree.layout(&last).unwrap(), rect([55.0, 100.0], [10.0, 20.0]));

    tree.update_node_params(&root, flow(Arrange::End, 15.0, 0.0)).unwrap();
    assert_eq!(tree.solve_layout(window), IncrementalRelayoutOutcome::FallbackFlow);
    assert_eq!(tree.layout(&last).unwrap().y, [20.0, 30.0]);
    tree.update_node_params(&root, flow(Arrange::End, 15.0, 3.0)).unwrap();
    assert_eq!(tree.solve_layout(window), IncrementalRelayoutOutcome::FallbackFlow);
    assert_eq!(tree.layout(&last).unwrap().y, [26.0, 36.0]);
}
