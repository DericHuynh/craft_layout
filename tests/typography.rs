#![cfg(feature = "incremental")]
use keru_layout::*;

#[derive(Clone, Copy)]
struct Label {
    word: f32,
    width: f32,
    line_height: f32,
    ascent: f32,
}

#[derive(Default)]
struct Font {
    width_calls: usize,
    line_calls: usize,
}

impl InlineMeasurer<Label> for Font {
    fn intrinsic_widths(&mut self, _: &NodeId, content: Option<&Label>) -> IntrinsicWidths {
        self.width_calls += 1;
        let c = content.expect("only text is measured");
        IntrinsicWidths::new(c.word, c.width).unwrap()
    }
    fn measure_lines(
        &mut self,
        _: &NodeId,
        content: Option<&Label>,
        width: Option<f32>,
    ) -> InlineMetrics {
        self.line_calls += 1;
        let c = content.expect("only text is measured");
        let lines = width.map_or(1.0, |w| (c.width / w.max(c.word)).ceil().max(1.0));
        InlineMetrics::new(
            c.line_height * lines,
            c.ascent,
            c.line_height * (lines - 1.0) + c.ascent,
        )
        .unwrap()
    }
}

fn row(width: Size, wrap: bool) -> LayoutParams {
    let children_layout = if wrap {
        ChildrenLayout::Wrap {
            axis: Axis::X,
            arrange: Arrange::Start,
            spacing: 4.0,
            line_spacing: 5.0,
        }
    } else {
        ChildrenLayout::Stack {
            axis: Axis::X,
            arrange: Arrange::Start,
            spacing: 4.0,
        }
    };
    LayoutParams {
        size: Xy::new(width, Size::FitContent),
        position: Xy::new_symm(Pos::Start),
        children_layout,
        ..LayoutParams::DEFAULT
    }
}
fn label(width: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(width, Size::FitContent),
        text: TextContent::Wrapping,
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    }
}
fn text(ascent: f32, height: f32) -> Label {
    Label {
        word: 10.0,
        width: 20.0,
        ascent,
        line_height: height,
    }
}

#[test]
fn content_bounds_apply_padding_once_and_remeasure_at_the_effective_width() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, row(Size::Fill, false))
        .unwrap();
    let mut authored = label(Size::Pixels(200.0));
    authored.padding = Xy::new([3.0, 7.0], [1.0, 2.0]);
    let content = Label {
        word: 30.0,
        width: 120.0,
        ascent: 8.0,
        line_height: 10.0,
    };
    let child = tree
        .add_node_with_context(&root, authored, content)
        .unwrap();
    let mut font = Font::default();
    for (preferred, expected_width, expected_height) in [
        (IntrinsicWidth::MinContent, 40.0, 43.0),
        (IntrinsicWidth::MaxContent, 130.0, 13.0),
        (IntrinsicWidth::FitContent(5.0), 40.0, 43.0),
        (IntrinsicWidth::FitContent(65.0), 75.0, 23.0),
        (IntrinsicWidth::FitContent(180.0), 130.0, 13.0),
    ] {
        tree.set_intrinsic_sizing(
            &child,
            IntrinsicSizing {
                preferred: Some(preferred),
                ..Default::default()
            },
        )
        .unwrap();
        tree.solve_layout_with_typography(Xy::new(300.0, 200.0), &mut font)
            .unwrap();
        let r = tree.layout(&child).unwrap();
        assert_eq!((r.x, r.y), ([0.0, expected_width], [0.0, expected_height]));
        assert_eq!(tree.params(&child).unwrap().size, authored.size);
    }
    assert_eq!(font.width_calls, 1);
    tree.set_intrinsic_sizing(
        &child,
        IntrinsicSizing {
            maximum: Some(IntrinsicWidth::MaxContent),
            ..Default::default()
        },
    )
    .unwrap();
    tree.update_node_context(
        &child,
        Some(Label {
            width: 60.0,
            ..content
        }),
    )
    .unwrap();
    tree.solve_layout_with_typography(Xy::new(300.0, 200.0), &mut font)
        .unwrap();
    assert_eq!(tree.layout(&child).unwrap().x, [0.0, 70.0]);
    assert_eq!(
        tree.measured_widths(&child).unwrap().unwrap().max_content(),
        60.0
    );
    tree.set_intrinsic_sizing(&child, IntrinsicSizing::default())
        .unwrap();
    tree.solve_layout_with_typography(Xy::new(300.0, 200.0), &mut font)
        .unwrap();
    assert_eq!(tree.layout(&child).unwrap().x, [0.0, 200.0]);
}

#[test]
fn first_and_last_baselines_change_row_height_and_ignore_hidden_and_free_children() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, row(Size::Fill, false))
        .unwrap();
    let tall = tree
        .add_node_with_context(&root, label(Size::Pixels(20.0)), text(17.0, 20.0))
        .unwrap();
    let multi = tree
        .add_node_with_context(&root, label(Size::Pixels(10.0)), text(3.0, 10.0))
        .unwrap();
    tree.add_node(
        &root,
        LayoutParams {
            disabled: true,
            size: Xy::new_symm(Size::Pixels(200.0)),
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    tree.add_node(
        &root,
        LayoutParams {
            free_placement: true,
            size: Xy::new_symm(Size::Pixels(200.0)),
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let icon = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new_symm(Size::Pixels(12.0)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    let mut font = Font::default();
    let win = Xy::new(200.0, 100.0);

    tree.set_baseline_alignment(&root, Some(Baseline::First))
        .unwrap();
    tree.solve_layout_with_typography(win, &mut font).unwrap();
    assert_eq!(tree.layout(&tall).unwrap().y, [0.0, 20.0]);
    assert_eq!(tree.layout(&multi).unwrap().y, [14.0, 34.0]);
    assert_eq!(tree.layout(&icon).unwrap().y, [5.0, 17.0]);
    assert_eq!(tree.layout(&root).unwrap().y, [0.0, 34.0]);

    tree.set_baseline_alignment(&root, Some(Baseline::Last))
        .unwrap();
    tree.solve_layout_with_typography(win, &mut font).unwrap();
    assert_eq!(tree.layout(&tall).unwrap().y, [0.0, 20.0]);
    assert_eq!(tree.layout(&multi).unwrap().y, [4.0, 24.0]);
    assert_eq!(tree.layout(&icon).unwrap().y, [5.0, 17.0]);
    assert_eq!(tree.layout(&root).unwrap().y, [0.0, 24.0]);
    let calls = (font.width_calls, font.line_calls);
    tree.solve_layout_with_typography(win, &mut font).unwrap();
    assert_eq!(calls, (font.width_calls, font.line_calls));

    let mut clone = tree.clone();
    let cr = clone.root();
    clone
        .solve_layout_with_typography(win, &mut Font::default())
        .unwrap();
    assert_eq!(tree.layout(&root).unwrap(), clone.layout(&cr).unwrap());
    tree.set_baseline_alignment(&root, None).unwrap();
    tree.solve_layout_with_typography(win, &mut font).unwrap();
    assert_eq!(tree.layout(&multi).unwrap().y, [0.0, 20.0]);
    assert_eq!(tree.layout(&root).unwrap().y, [0.0, 20.0]);
}

#[test]
fn wrap_aligns_baselines_per_line_and_rebuilds_groups_on_resize() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, row(Size::Fill, true))
        .unwrap();
    let mut ids = Vec::new();
    for ascent in [15.0, 5.0, 8.0, 8.0] {
        ids.push(
            tree.add_node_with_context(&root, label(Size::Pixels(20.0)), text(ascent, 20.0))
                .unwrap(),
        );
    }
    tree.set_baseline_alignment(&root, Some(Baseline::First))
        .unwrap();
    let mut font = Font::default();
    for (width, expected) in [
        (44.0, [0.0, 10.0, 35.0, 35.0]),
        (92.0, [0.0, 10.0, 7.0, 7.0]),
        (44.0, [0.0, 10.0, 35.0, 35.0]),
    ] {
        tree.solve_layout_with_typography(Xy::new(width, 100.0), &mut font)
            .unwrap();
        assert_eq!(
            ids.iter()
                .map(|i| tree.layout(i).unwrap().y[0])
                .collect::<Vec<_>>(),
            expected
        );
    }
}

#[test]
fn flex_reads_wrapped_control_baselines_without_manual_offsets() {
    use keru_layout::flex::{FlexAlign, FlexLayout};
    use keru_layout::layout_rules::NodeRules;
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, row(Size::Fill, false))
        .unwrap();
    let tall = tree
        .add_node_with_context(&root, label(Size::Pixels(20.0)), text(17.0, 20.0))
        .unwrap();
    let multi = tree
        .add_node_with_context(&root, label(Size::Pixels(10.0)), text(3.0, 10.0))
        .unwrap();
    let mut font = Font::default();
    for (alignment, expected, height) in [
        (FlexAlign::FirstBaseline, [14.0, 34.0], 34.0),
        (FlexAlign::LastBaseline, [4.0, 24.0], 24.0),
    ] {
        tree.set_rules(
            &root,
            NodeRules {
                flex: Some(FlexLayout {
                    align_items: alignment,
                    ..Default::default()
                }),
                ..Default::default()
            },
        )
        .unwrap();
        tree.solve_layout_with_typography(Xy::new(100.0, 100.0), &mut font)
            .unwrap();
        assert_eq!(tree.rule_issues(), &[]);
        assert_eq!(tree.layout(&tall).unwrap().y, [0.0, 20.0]);
        assert_eq!(tree.layout(&multi).unwrap().y, expected);
        assert_eq!(tree.layout(&root).unwrap().y, [0.0, height]);
    }
}

#[test]
fn baseline_metrics_follow_a_query_selected_flex_row() {
    use keru_layout::flex::{FlexAlign, FlexLayout};
    use keru_layout::layout_rules::{
        Container, ContainerQuery, NodeRules, QueryLayout, QueryStyle,
    };
    let mut tree = LayoutTree::new();
    let root = tree.root();
    let panel = tree
        .add_node(&root, row(Size::Pixels(160.), false))
        .unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            container: Some(Container::axis(Axis::X)),
            ..Default::default()
        },
    )
    .unwrap();
    let group = tree.add_node(&panel, row(Size::Fill, false)).unwrap();
    tree.set_rules(
        &group,
        NodeRules {
            queries: vec![ContainerQuery {
                name: None,
                axis: LogicalAxis::Inline,
                min: None,
                max: Some(100.),
                style: QueryStyle {
                    layout: Some(QueryLayout::Flex(FlexLayout {
                        align_items: FlexAlign::FirstBaseline,
                        ..Default::default()
                    })),
                    ..Default::default()
                },
            }],
            ..Default::default()
        },
    )
    .unwrap();
    let tall = tree
        .add_node_with_context(&group, label(Size::Pixels(20.)), text(17., 20.))
        .unwrap();
    let short = tree
        .add_node_with_context(&group, label(Size::Pixels(10.)), text(3., 10.))
        .unwrap();
    let mut font = Font::default();
    for (width, top) in [(160., 0.), (100., 14.), (160., 0.), (80., 14.)] {
        tree.update_node_params(&panel, row(Size::Pixels(width), false))
            .unwrap();
        tree.solve_layout_with_typography(Xy::new(300., 100.), &mut font)
            .unwrap();
        assert_eq!(tree.layout(&tall).unwrap().y[0], 0.);
        assert_eq!(tree.layout(&short).unwrap().y[0], top);
    }
}
