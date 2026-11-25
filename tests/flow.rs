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
fn fit_stack_resolves_a_fraction_just_below_one_and_its_aspect_dependent() {
    let mut tree = LayoutTree::<()>::new();
    let start = Xy::new_symm(Pos::Start);
    let row = tree.add_node(&tree.root(), LayoutParams {
        position: start,
        size: Xy::new(Size::FitContent, Size::AspectRatio(2.0)),
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 2.0 },
        padding: Xy::new([3.0, 5.0], [0.0; 2]),
        ..LayoutParams::DEFAULT
    }).unwrap();
    let mut fixed = LayoutParams { position: start, size: px(1.0, 1.0), ..LayoutParams::DEFAULT };
    let first = tree.add_node(&row, fixed).unwrap();
    let last = tree.add_node(&row, LayoutParams {
        position: start, size: Xy::new(Size::Frac(1023.0 / 1024.0), Size::Pixels(1.0)),
        ..LayoutParams::DEFAULT
    }).unwrap();

    // Make the edited row a small enough share of the tree to use the retained solve.
    for _ in 0..32 {
        tree.add_node(&tree.root(), LayoutParams { size: px(1.0, 1.0), ..LayoutParams::DEFAULT }).unwrap();
    }
    for fixed_width in [1.0, 2.0] {
        fixed.size.x = Size::Pixels(fixed_width);
        tree.update_node_params(&first, fixed).unwrap();
        let outcome = tree.solve_layout(Xy::new_symm(3000.0));
        if fixed_width == 2.0 {
            assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
        }
        // After padding and the gap, W = fixed_width + (1023/1024) * W.
        let width = fixed_width * 1024.0 + 10.0;
        assert_eq!(tree.layout(&row).unwrap(), rect([0.0, width], [0.0, width / 2.0]));
        assert_eq!(tree.layout(&last).unwrap().x, [5.0 + fixed_width, width - 5.0]);
        assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
    }
}

fn horizontal_fit_stack() -> (LayoutTree<()>, NodeId) {
    let mut tree = LayoutTree::<()>::new();
    let row = tree.root();
    tree.update_node_params(&row, LayoutParams {
        position: Xy::new_symm(Pos::Start), size: Xy::new(Size::FitContent, Size::Pixels(1.0)),
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 0.0 },
        ..LayoutParams::DEFAULT
    }).unwrap();
    (tree, row)
}

#[test]
fn fit_stack_resolves_overcommitted_fractions_when_a_child_maximum_binds() {
    let (mut tree, row) = horizontal_fit_stack();
    tree.add_node(&row, LayoutParams { size: px(1.0, 4.0), ..LayoutParams::DEFAULT }).unwrap();
    let style = LayoutParams {
        size: Xy::new(Size::Frac(0.75), Size::Pixels(4.0)), ..LayoutParams::DEFAULT
    };
    let mut capped = style;
    capped.max_size.x = Some(Size::Pixels(12.0));
    let first = tree.add_node(&row, capped).unwrap();
    let second = tree.add_node(&row, style).unwrap();
    let viewport = Xy::new_symm(300.0);

    for cap in [12.0, 15.0] {
        capped.max_size.x = Some(Size::Pixels(cap));
        tree.update_node_params(&first, capped).unwrap();
        tree.solve_layout(viewport);
        // W = 1 + cap + 3/4 W once the first item reaches its limit.
        let width = (1.0 + cap) * 4.0;
        assert_eq!(tree.layout(&row).unwrap().x, [0.0, width]);
        assert_eq!(tree.layout(&first).unwrap().x, [1.0, 1.0 + cap]);
        assert_eq!(tree.layout(&second).unwrap().x, [1.0 + cap, width]);
        assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
    }

    tree.update_node_params(&first, style).unwrap();
    tree.solve_layout(viewport);
    assert!(tree.warnings().iter().any(|warning| matches!(warning,
        LayoutWarning::ImpossibleFracChildren { node, axis: Axis::X } if *node == row)));
}

#[test]
fn fit_stack_honors_the_minimum_that_supplies_its_intrinsic_size() {
    let (mut tree, row) = horizontal_fit_stack();
    let mut style = LayoutParams {
        size: Xy::new(Size::Frac(1.0), Size::Pixels(1.0)),
        min_size: Xy::new(Some(Size::Pixels(10.0)), None),
        max_size: Xy::new(Some(Size::Pixels(30.0)), None),
        ..LayoutParams::DEFAULT
    };
    let child = tree.add_node(&row, style).unwrap();
    for (fraction, width) in [(1.0, 10.0), (1.5, 30.0)] {
        style.size.x = Size::Frac(fraction);
        tree.update_node_params(&child, style).unwrap();
        tree.solve_layout(Xy::new_symm(100.0));
        assert_eq!(tree.layout(&row).unwrap().x, [0.0, width]);
        assert_eq!(tree.layout(&child).unwrap().x, [0.0, width]);
        assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
    }
}

#[test]
fn fit_stack_crosses_many_caps_without_truncating_the_solution() {
    let (mut tree, row) = horizontal_fit_stack();
    tree.add_node(&row, LayoutParams { size: px(1.0, 1.0), ..LayoutParams::DEFAULT }).unwrap();
    let mut items = Vec::new();
    for cap in 1..=100 {
        let item = tree.add_node(&row, LayoutParams {
            size: Xy::new(Size::Frac(1.0), Size::Pixels(1.0)),
            max_size: Xy::new(Some(Size::Pixels(cap as f32)), None),
            ..LayoutParams::DEFAULT
        }).unwrap();
        items.push(item);
    }
    tree.solve_layout(Xy::new_symm(6000.0));
    let mut x = 1.0;
    for (index, item) in items.iter().enumerate() {
        let end = x + (index + 1) as f32;
        assert_eq!(tree.layout(item).unwrap().x, [x, end]);
        x = end;
    }
    assert_eq!(tree.layout(&row).unwrap().x, [0.0, 5051.0]);
    assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
}

#[test]
fn fit_stack_caps_a_fraction_before_its_uncapped_extrapolation_overflows() {
    let (mut tree, row) = horizontal_fit_stack();
    let fixed = 2f32.powi(120);
    let cap = fixed / 4.0;
    tree.add_node(&row, LayoutParams { size: px(fixed, 1.0), ..LayoutParams::DEFAULT }).unwrap();
    let child = tree.add_node(&row, LayoutParams {
        size: Xy::new(Size::Frac(1023.0 / 1024.0), Size::Pixels(1.0)),
        max_size: Xy::new(Some(Size::Pixels(cap)), None),
        ..LayoutParams::DEFAULT
    }).unwrap();
    tree.solve_layout(Xy::new_symm(1.0));
    assert_eq!(tree.layout(&row).unwrap().x, [0.0, fixed + cap]);
    assert_eq!(tree.layout(&child).unwrap().x, [fixed, fixed + cap]);
    assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
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

    assert!(matches!(tree.solve_layout(Xy::new(130.0, 200.0)), IncrementalRelayoutOutcome::Success { .. }));
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

    assert!(matches!(tree.solve_layout(Xy::new_symm(100.0)), IncrementalRelayoutOutcome::Success { .. }));
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
    assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
    assert_eq!(tree.layout(&last).unwrap().y, [20.0, 30.0]);
    tree.update_node_params(&root, flow(Arrange::End, 15.0, 3.0)).unwrap();
    assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
    assert_eq!(tree.layout(&last).unwrap().y, [26.0, 36.0]);
}

#[test]
fn explicit_invalidation_remeasures_every_leaf_after_content_flow_replay() {
    let mut tree = LayoutTree::<f32>::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    }).unwrap();
    let text = LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        text: TextContent::Wrapping,
        ..LayoutParams::DEFAULT
    };
    let edited = tree.add_node_with_context(&root, text, 4.5).unwrap();
    let retained = tree.add_node_with_context(&root, text, 2.75).unwrap();
    let window = Xy::new_symm(40.0);
    let mut calls = 0;
    let mut measure = |_: NodeId, content: Option<&mut f32>, _: Option<f32>| {
        calls += 1;
        Xy::new(0.0, content.copied().unwrap_or(0.0))
    };
    tree.solve_layout_with_measure(window, &mut measure);
    tree.update_node_context(&edited, Some(7.0)).unwrap();
    assert!(matches!(tree.solve_layout_with_measure(window, &mut measure), IncrementalRelayoutOutcome::Success { .. }));
    tree.update_node_context(&edited, Some(8.0)).unwrap();
    tree.invalidate();
    assert_eq!(tree.solve_layout_with_measure(window, &mut measure), IncrementalRelayoutOutcome::FallbackInvalidated);
    assert_eq!(calls, 5);
    assert_eq!(tree.layout(&retained).unwrap().y, [8.0, 10.75]);
}

#[test]
fn ordinary_block_root_replay_matches_a_fresh_reflow() {
    let mut tree = LayoutTree::<f32>::new();
    let root = tree.root();
    tree.update_node_params(&root, LayoutParams {
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    }).unwrap();
    let section = LayoutParams {
        size: Xy::new_symm(Size::Auto),
        max_size: Xy::new(Some(Size::Pixels(55.25)), None),
        margin: Xy::new([Margin::AUTO; 2], edges(5.0, -2.75)),
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    };
    let page = tree.add_node(&root, section).unwrap();
    let nested = tree.add_node(&page, section).unwrap();
    let text = LayoutParams {
        size: Xy::new(Size::Auto, Size::FitContent),
        text: TextContent::Wrapping,
        padding: Xy::new([1.25, 0.5], [0.75, 0.0]),
        margin: Xy::new([Margin::ZERO; 2], edges(-2.0, 4.75)),
        ..LayoutParams::DEFAULT
    };
    let edit = tree.add_node_with_context(&nested, text, 11.0).unwrap();
    tree.add_node(&nested, LayoutParams {
        size: Xy::new(Size::Pixels(-0.0), Size::Pixels(-0.0)),
        margin: Xy::new([Margin::ZERO; 2], edges(2.25, -0.75)),
        ..LayoutParams::DEFAULT
    }).unwrap();
    tree.add_node(&page, section).unwrap();
    tree.add_node_with_context(&page, text, 13.25).unwrap();
    let mut section_with_padding = section;
    section_with_padding.padding.x = [1.25, 2.0];
    let scale = PixelScale::new(1.25).unwrap();
    tree.set_pixel_scale(Some(scale));
    let measure = |_: NodeId, value: Option<&mut f32>, width: Option<f32>| {
        Xy::new(0.0, value.copied().unwrap_or(0.0) + width.unwrap_or(0.0) * 0.125)
    };
    let view = |tree: &LayoutTree<f32>| {
        let mut output = Vec::new();
        let mut next = vec![tree.root()];
        while let Some(node) = next.pop() {
            let rectangle = tree.layout(&node).unwrap();
            output.push([rectangle.x.map(f32::to_bits), rectangle.y.map(f32::to_bits)]);
            let mut children: Vec<_> = tree.children(&node).unwrap().map(NodeId::from).collect();
            children.reverse();
            next.extend(children);
        }
        output
    };
    tree.solve_layout_with_measure(Xy::new(72.0, 96.0), measure);
    for (i, width) in [75.75, 41.125, 41.125, 81.25, 23.75].into_iter().enumerate() {
        tree.update_node_context(&edit, Some(5.75 + i as f32)).unwrap();
        if i == 2 { tree.update_node_params(&page, section_with_padding).unwrap(); }
        let window = Xy::new(width, 96.0 + i as f32);
        let mut fresh = tree.clone();
        fresh.invalidate();
        fresh.solve_layout_with_measure(window, measure);
        assert!(matches!(tree.solve_layout_with_measure(window, measure), IncrementalRelayoutOutcome::Success { .. }));
        assert_eq!(view(&tree), view(&fresh));
        assert!(tree.warnings().is_empty());
        assert!(fresh.warnings().is_empty());
    }
}

#[test]
fn intrinsic_block_width_includes_the_childs_padding_floor() {
    let window = Xy::new_symm(200.0);
    check_block_padding_floor(|tree| { tree.solve_layout(window); });
    #[cfg(feature = "batch-pilot")]
    check_block_padding_floor(|tree| { tree.solve_layout_batch(window).unwrap(); });
}

fn check_block_padding_floor(mut solve: impl FnMut(&mut LayoutTree<()>)) {
    let mut tree = LayoutTree::<()>::new();
    let outer = tree.add_node(&tree.root(), LayoutParams {
        size: Xy::new(Size::FitContent, Size::FitContent),
        position: Xy::new_symm(Pos::Start),
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    }).unwrap();
    let mut params = LayoutParams {
        size: Xy::new(Size::Auto, Size::Pixels(10.0)),
        max_size: Xy::new(Some(Size::Pixels(12.0)), None),
        padding: Xy::new([15.0, 7.0], [0.0; 2]),
        margin: Xy::new(edges(2.0, 3.0), [Margin::ZERO; 2]),
        ..LayoutParams::DEFAULT
    };
    let item = tree.add_node(&outer, params).unwrap();
    for right in [7.0, 11.0, 3.0] {
        params.padding.x[1] = right;
        tree.update_node_params(&item, params).unwrap();
        solve(&mut tree);
        assert_eq!(tree.layout(&item).unwrap().x, [2.0, 17.0 + right]);
        assert_eq!(tree.layout(&outer).unwrap().x, [0.0, 20.0 + right]);
        assert!(tree.warnings().is_empty());
    }
}

#[test]
fn block_minimum_only_keeps_a_childs_bottom_margin_inside_when_it_binds() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let block = LayoutParams {
        children_layout: ChildrenLayout::Block,
        size: Xy::new(Size::Auto, Size::FitContent),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    tree.update_node_params(&root, LayoutParams {
        size: Xy::new(Size::Pixels(50.0), Size::FitContent), ..block
    }).unwrap();
    let mut section = LayoutParams { margin: Xy::new([Margin::ZERO; 2], edges(0.0, 10.0)), ..block };
    let parent = tree.add_node(&root, section).unwrap();
    tree.add_node(&parent, LayoutParams {
        size: px(50.0, 20.0), margin: Xy::new([Margin::ZERO; 2], edges(0.0, 30.0)), ..block
    }).unwrap();
    let next = tree.add_node(&root, LayoutParams { size: px(50.0, 10.0), ..block }).unwrap();
    for (minimum, height, next_y) in [(10.0, 20.0, 50.0), (60.0, 60.0, 70.0), (20.0, 20.0, 50.0)] {
        section.min_size.y = Some(Size::Pixels(minimum));
        tree.update_node_params(&parent, section).unwrap();
        tree.solve_layout(Xy::new_symm(100.0));
        assert_eq!(tree.layout(&parent).unwrap().y, [0.0, height]);
        assert_eq!(tree.layout(&next).unwrap().y, [next_y, next_y + 10.0]);
        assert!(tree.warnings().is_empty());
    }
}

#[test]
fn empty_formatting_context_separates_margins_inside_an_auto_height_block() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let block = LayoutParams {
        children_layout: ChildrenLayout::Block,
        position: Xy::new_symm(Pos::Start),
        size: Xy::new(Size::Pixels(50.0), Size::FitContent),
        ..LayoutParams::DEFAULT
    };
    tree.update_node_params(&root, block).unwrap();
    let fixed = LayoutParams { size: px(50.0, 10.0), ..block };
    tree.add_node(&root, LayoutParams { margin: Xy::new([Margin::ZERO; 2], edges(0.0, 10.0)), ..fixed }).unwrap();
    let mut spacer = LayoutParams {
        min_size: Xy::new(None, Some(Size::Frac(0.1))),
        margin: Xy::new([Margin::ZERO; 2], edges(10.0, 10.0)), ..block
    };
    let divider = tree.add_node(&root, spacer).unwrap();
    let next = tree.add_node(&root, LayoutParams { margin: Xy::new([Margin::ZERO; 2], edges(10.0, 0.0)), ..fixed }).unwrap();
    let stack = ChildrenLayout::Stack { axis: Axis::X, spacing: 0.0, arrange: Arrange::Start };
    for (mode, next_y) in [(ChildrenLayout::Block, 20.0), (stack, 30.0), (ChildrenLayout::Block, 20.0)] {
        spacer.children_layout = mode;
        tree.update_node_params(&divider, spacer).unwrap();
        tree.solve_layout(Xy::new_symm(100.0));
        assert_eq!(tree.layout(&divider).unwrap().y, [20.0; 2]);
        assert_eq!(tree.layout(&next).unwrap().y, [next_y, next_y + 10.0]);
        assert!(tree.warnings().is_empty());
    }
}

#[test]
fn empty_managed_formatting_context_separates_sibling_margins() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::flex::FlexLayout;
    use keru_layout::tracks::TrackGrid;

    for batch in [false, true] {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        tree.update_node_params(&root, LayoutParams {
            children_layout: ChildrenLayout::Block,
            size: Xy::new(Size::Pixels(50.), Size::FitContent),
            position: Xy::new_symm(Pos::Start),
            ..LayoutParams::DEFAULT
        }).unwrap();
        let child = |height, before, after| LayoutParams {
            size: Xy::new(Size::Auto, height),
            margin: Xy::new([Margin::ZERO; 2], edges(before, after)),
            children_layout: ChildrenLayout::Block,
            ..LayoutParams::DEFAULT
        };
        tree.add_node(&root, child(Size::Pixels(10.), 0., 10.)).unwrap();
        let middle = tree.add_node(&root, child(Size::Auto, 10., 10.)).unwrap();
        let last = tree.add_node(&root, child(Size::Pixels(10.), 10., 0.)).unwrap();
        for (rules, last_y) in [
            (NodeRules { grid: Some(TrackGrid::default()), ..Default::default() }, 30.),
            (NodeRules::default(), 20.),
            (NodeRules { flex: Some(FlexLayout::default()), ..Default::default() }, 30.),
        ] {
            tree.set_rules(&middle, rules).unwrap();
            let window = Xy::new_symm(100.);
            if batch {
                #[cfg(feature = "batch-pilot")]
                tree.solve_layout_batch(window).unwrap();
                #[cfg(not(feature = "batch-pilot"))]
                continue;
            } else {
                tree.solve_layout(window);
            }
            assert_eq!(tree.layout(&middle).unwrap().y, [20., 20.]);
            assert_eq!(tree.layout(&last).unwrap().y, [last_y, last_y + 10.]);
            assert_eq!(tree.layout(&root).unwrap().y, [0., last_y + 10.]);
            assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
        }
    }
}

#[test]
fn authored_block_margin_boundary_keeps_child_margins_inside_the_container() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let block = LayoutParams {
        children_layout: ChildrenLayout::Block,
        size: Xy::new(Size::Auto, Size::FitContent),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    tree.update_node_params(&root, LayoutParams { size: Xy::new(Size::Fill, Size::FitContent), ..block }).unwrap();
    let mut group = LayoutParams { margin: Xy::new([Margin::ZERO; 2], edges(3., 5.)), ..block };
    let container = tree.add_node(&root, group).unwrap();
    let child = tree.add_node(&container, LayoutParams {
        margin: Xy::new([Margin::ZERO; 2], edges(7., 11.)),
        size: Xy::new(Size::Auto, Size::Pixels(13.)),
        ..LayoutParams::DEFAULT
    }).unwrap();
    for (isolate, parent_y, child_y, height) in [
        (false, [7., 20.], [7., 20.], 31.),
        (true, [3., 34.], [10., 23.], 39.),
        (false, [7., 20.], [7., 20.], 31.),
    ] {
        group.isolate_block_margins = isolate;
        tree.update_node_params(&container, group).unwrap();
        for width in [50., 75.] {
            tree.solve_layout(Xy::new(width, 100.));
            assert_eq!(tree.layout(&root).unwrap().y, [0., height]);
            assert_eq!(tree.layout(&container).unwrap().y, parent_y);
            assert_eq!(tree.layout(&child).unwrap().y, child_y);
        }
    }
}
