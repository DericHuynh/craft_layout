use keru_layout::flex::{
    FlexAlign, FlexBasis, FlexItem, FlexLayout, FlexMetrics, FlexWrap, LineAlign,
};
use keru_layout::{Arrange, Axis, Margin, Xy};

fn button(width: f32, height: f32) -> FlexMetrics {
    FlexMetrics {
        preferred: Xy::new(width, height),
        stretch_cross: false,
        ..Default::default()
    }
}

#[test]
fn toolbar_shrinks_only_with_permission_and_redistributes_at_a_limit() {
    let layout = FlexLayout {
        gap: 10.0,
        ..Default::default()
    };
    let mut items = [button(160.0, 20.0), button(120.0, 20.0)];
    let available = Xy::new(220.0, 40.0);
    let fixed = layout.resolve(available, &items);
    assert_eq!(fixed[0].x, [0.0, 160.0]);
    assert_eq!(fixed[1].x, [170.0, 290.0]);
    for item in &mut items {
        item.item = FlexItem::css();
    }
    let compressed = layout.resolve(available, &items);
    assert_eq!(compressed[0].x, [0.0, 120.0]);
    assert_eq!(compressed[1].x, [130.0, 220.0]);
    items[1].min.x = 110.0;
    let bounded = layout.resolve(available, &items);
    assert_eq!(bounded[0].x, [0.0, 100.0]);
    assert_eq!(bounded[1].x, [110.0, 220.0]);
}

#[test]
fn mixed_min_max_violations_freeze_the_correct_side_first() {
    let mut items = [button(50.0, 10.0); 3];
    for item in &mut items {
        item.item.grow = 1.0;
    }
    items[0].min.x = 90.0;
    items[1].max.x = 65.0;
    let rects = FlexLayout::default().resolve(Xy::new(210.0, 10.0), &items);
    assert_eq!(rects[0].x, [0.0, 90.0]);
    assert_eq!(rects[1].x, [90.0, 150.0]);
    assert_eq!(rects[2].x, [150.0, 210.0]);
}

#[test]
fn fractional_growth_can_leave_room_for_an_auto_margin() {
    let mut items = [button(40.0, 10.0); 2];
    items[0].item = FlexItem {
        basis: FlexBasis::Pixels(0.0),
        grow: 0.25,
        ..Default::default()
    };
    items[1].item = items[0].item;
    items[1].margin.x[0] = Margin::AUTO;
    let layout = FlexLayout {
        justify: Arrange::Center,
        ..Default::default()
    };
    let rects = layout.resolve(Xy::new(100.0, 10.0), &items);
    assert_eq!(rects[0].x, [0.0, 25.0]);
    assert_eq!(rects[1].x, [75.0, 100.0]);
}

#[test]
fn content_basis_and_padding_affect_shrink_independently_of_preferred() {
    let mut items = [button(150.0, 10.0); 2];
    for it in &mut items {
        it.item = FlexItem {
            basis: FlexBasis::Content,
            ..FlexItem::css()
        };
    }
    items[0].content_main = 100.0;
    items[0].padding.x = [10.0; 2];
    items[1].content_main = 20.0;
    // The inner bases are 80 and 20. The 20px deficit is divided 16:4.
    let rects = FlexLayout::default().resolve(Xy::new(100.0, 10.0), &items);
    assert_eq!(rects[0].x, [0.0, 84.0]);
    assert_eq!(rects[1].x, [84.0, 100.0]);
}

#[test]
fn reverse_wrap_aligns_lines_and_keeps_indices_in_source_order() {
    let layout = FlexLayout {
        gap: 2.0,
        line_gap: 5.0,
        wrap: FlexWrap::WrapReverse,
        reverse: true,
        align_content: LineAlign::SpaceBetween,
        ..Default::default()
    };
    let mut items = [button(35.0, 20.0); 3];
    items[1].item.order = -1;
    items[2].preferred.y = 10.0;
    let rects = layout.resolve(Xy::new(72.0, 50.0), &items);
    assert_eq!(rects[1], Xy::new([37.0, 72.0], [30.0, 50.0]));
    assert_eq!(rects[0], Xy::new([0.0, 35.0], [30.0, 50.0]));
    assert_eq!(rects[2], Xy::new([37.0, 72.0], [0.0, 10.0]));
    let three_lines = layout.resolve(Xy::new(71.0, 60.0), &items);
    assert_eq!(three_lines[1].y, [40.0, 60.0]);
    assert_eq!(three_lines[0].y, [15.0, 35.0]);
    assert_eq!(three_lines[2].y, [0.0, 10.0]);
}

#[test]
fn distributed_line_stretch_and_baseline_groups_respect_metrics() {
    let mut items = [button(30.0, 12.0), button(30.0, 22.0), button(40.0, 10.0)];
    items[0].first_baseline = Some(9.0);
    items[1].first_baseline = Some(16.0);
    items[2].item.align_self = Some(FlexAlign::Stretch);
    items[2].stretch_cross = true;
    let layout = FlexLayout {
        wrap: FlexWrap::Wrap,
        align_items: FlexAlign::FirstBaseline,
        line_gap: 4.0,
        ..Default::default()
    };
    let rects = layout.resolve(Xy::new(60.0, 60.0), &items);
    assert_eq!(rects[0].y, [7.0, 19.0]);
    assert_eq!(rects[1].y, [0.0, 22.0]);
    assert_eq!(rects[2].y, [38.0, 60.0]);
    let last = FlexLayout {
        align_items: FlexAlign::LastBaseline,
        ..Default::default()
    };
    items[0].last_baseline = Some(8.0);
    items[1].last_baseline = Some(18.0);
    let rects = last.resolve(Xy::new(60.0, 40.0), &items[..2]);
    assert_eq!(rects[0].y, [28.0, 40.0]);
    assert_eq!(rects[1].y, [18.0, 40.0]);
}

#[test]
fn column_on_a_reversed_cross_axis_handles_safe_center_and_auto_margins() {
    let layout = FlexLayout {
        axis: Axis::Y,
        cross_reverse: true,
        align_items: FlexAlign::SafeCenter,
        ..Default::default()
    };
    let mut items = [button(60.0, 10.0), button(20.0, 10.0)];
    items[1].margin.x[0] = Margin::AUTO;
    let rects = layout.resolve(Xy::new(40.0, 100.0), &items);
    assert_eq!(rects[0], Xy::new([-20.0, 40.0], [0.0, 10.0]));
    assert_eq!(rects[1], Xy::new([20.0, 40.0], [10.0, 20.0]));
}

#[cfg(feature = "incremental")]
#[test]
fn managed_toolbar_resize_and_width_conditioned_cross_size() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{LayoutParams, LayoutTree, Pos, Size, TextContent};
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let bar = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                position: Xy::new_symm(Pos::Start),
                padding: Xy::new([4.; 2], [2.; 2]),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &bar,
        NodeRules {
            flex: Some(FlexLayout {
                gap: 10.,
                align_items: FlexAlign::Start,
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let label = tree
        .add_node(
            &bar,
            LayoutParams {
                size: Xy::new(Size::Pixels(160.), Size::FitContent),
                text: TextContent::Wrapping,
                ..Default::default()
            },
        )
        .unwrap();
    let control = tree
        .add_node(
            &bar,
            LayoutParams {
                size: Xy::new(Size::Pixels(120.), Size::Pixels(16.)),
                min_size: Xy::new(Some(Size::Pixels(110.)), None),
                ..Default::default()
            },
        )
        .unwrap();
    for id in [&label, &control] {
        tree.set_rules(
            id,
            NodeRules {
                flex_item: FlexItem::css(),
                ..Default::default()
            },
        )
        .unwrap();
    }
    for (width, label_w, bar_h) in [(228., 100., 44.), (298., 160., 24.), (228., 100., 44.)] {
        let win = Xy::new(width, 120.);
        let measure = |_, _: Option<&mut ()>, w: Option<f32>| {
            Xy::new(
                160.,
                if w.is_some_and(|px| px < 160.) {
                    40.
                } else {
                    20.
                },
            )
        };
        tree.solve_layout_with_measure(win, measure);
        assert_eq!(tree.rule_issues(), &[]);
        assert_eq!(
            tree.layout(&bar).unwrap(),
            Xy::new([0., width], [0., bar_h])
        );
        assert_eq!(
            tree.layout(&label).unwrap(),
            Xy::new([4., 4. + label_w], [2., bar_h - 2.])
        );
        assert_eq!(
            tree.layout(&control).unwrap().x,
            [14. + label_w, width - 4.]
        );
        #[cfg(feature = "batch-pilot")]
        {
            tree.solve_layout_batch_with_measure(win, measure).unwrap();
            assert_eq!(tree.layout(&bar).unwrap().y, [0., bar_h]);
        }
    }
}

#[test]
fn a_negative_cross_margin_can_pull_a_baseline_above_line_start() {
    let mut item = button(20., 20.);
    item.first_baseline = Some(5.);
    item.margin.y[0] = Margin::px(-10.).unwrap();
    let layout = FlexLayout {
        align_items: FlexAlign::FirstBaseline,
        ..Default::default()
    };
    let (rects, height) = layout.resolve_and_measure(Xy::new(50., 40.), &[item]);
    assert_eq!(rects[0].y, [-10., 10.]);
    assert_eq!(height, 10.);
}
