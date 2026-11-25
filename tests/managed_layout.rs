#![cfg(feature = "incremental")]
use keru_layout::{
    flex::{FlexItem, FlexLayout},
    layout_rules::*,
    *,
};

fn box_params(w: Size, h: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(w, h),
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    }
}
fn fixed(w: f32, h: f32) -> LayoutParams {
    box_params(Size::Pixels(w), Size::Pixels(h))
}
fn layout_row() -> ChildrenLayout {
    ChildrenLayout::Stack {
        axis: Axis::X,
        arrange: Arrange::Start,
        spacing: 0.,
    }
}
fn solve(tree: &mut LayoutTree, width: f32) {
    tree.solve_layout(Xy::new(width, 300.));
    assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
}

#[test]
fn admitted_breakpoint_depends_on_nearest_named_panel_and_restores_authored_style() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let panel = tree.add_node(&root, fixed(170., 100.)).unwrap();
    let nested = tree
        .add_node(&panel, box_params(Size::Fill, Size::Fill))
        .unwrap();
    let field = tree.add_node(&nested, fixed(40., 25.)).unwrap();
    let mut scope = Container::axis(Axis::X);
    scope.name = Some("panel".into());
    tree.set_rules(
        &panel,
        NodeRules {
            container: Some(scope),
            ..Default::default()
        },
    )
    .unwrap();
    tree.set_rules(
        &nested,
        NodeRules {
            container: Some(Container::axis(Axis::X)),
            ..Default::default()
        },
    )
    .unwrap();
    tree.set_rules(
        &field,
        NodeRules {
            queries: vec![ContainerQuery {
                name: Some("panel".into()),
                axis: LogicalAxis::Inline,
                min: Some(160.),
                max: None,
                style: QueryStyle {
                    size: Xy::new(Some(Size::Pixels(90.)), None),
                    ..Default::default()
                },
            }],
            ..Default::default()
        },
    )
    .unwrap();
    for (w, expected) in [(170., 90.), (135., 40.), (160., 90.)] {
        tree.update_node_params(&panel, fixed(w, 100.)).unwrap();
        solve(&mut tree, 640.);
        assert_eq!(tree.layout(&field).unwrap().x, [0., expected]);
        assert_eq!(tree.params(&field).unwrap().size.x, Size::Pixels(40.));
    }
    tree.set_rules(&field, NodeRules::default()).unwrap();
    solve(&mut tree, 640.);
    assert_eq!(tree.layout(&field).unwrap().x, [0., 40.]);
}
#[test]
fn contained_fit_uses_placeholder_plus_padding_and_breakpoint_is_content_box() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let p = tree
        .add_node(
            &root,
            LayoutParams {
                padding: Xy::new([7., 3.], [0.; 2]),
                ..box_params(Size::FitContent, Size::Fill)
            },
        )
        .unwrap();
    let child = tree.add_node(&p, fixed(200., 20.)).unwrap();
    let mut scope = Container::axis(Axis::X);
    scope.placeholder.x = 56.;
    tree.set_rules(
        &p,
        NodeRules {
            container: Some(scope),
            ..Default::default()
        },
    )
    .unwrap();
    tree.set_rules(
        &child,
        NodeRules {
            queries: vec![ContainerQuery {
                name: None,
                axis: LogicalAxis::Inline,
                min: None,
                max: Some(56.),
                style: QueryStyle {
                    size: Xy::new(None, Some(Size::Pixels(36.))),
                    ..Default::default()
                },
            }],
            ..Default::default()
        },
    )
    .unwrap();
    solve(&mut tree, 800.);
    assert_eq!(tree.layout(&p).unwrap().x, [0., 66.]);
    assert_eq!(tree.layout(&child).unwrap().y, [0., 36.]);
}
#[test]
fn edits_hiding_reparenting_and_rule_removal_preserve_original_inputs() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let rtl = tree
        .add_node(
            &root,
            LayoutParams {
                children_layout: layout_row(),
                ..fixed(100., 40.)
            },
        )
        .unwrap();
    let ltr = tree
        .add_node(
            &root,
            LayoutParams {
                children_layout: layout_row(),
                ..fixed(100., 40.)
            },
        )
        .unwrap();
    let item = tree.add_node(&rtl, fixed(17., 10.)).unwrap();
    tree.set_rules(
        &rtl,
        NodeRules {
            logical: LogicalStyle {
                direction: Some(Direction::Rtl),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    tree.set_rules(
        &item,
        NodeRules {
            logical: LogicalStyle {
                size: Logical::new(Some(Size::Pixels(25.)), None),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    solve(&mut tree, 120.);
    assert_eq!(tree.layout(&item).unwrap().x, [75., 100.]);
    tree.update_node_params(&item, fixed(22., 10.)).unwrap();
    tree.update_node_params(
        &rtl,
        LayoutParams {
            disabled: true,
            ..*tree.params(&rtl).unwrap()
        },
    )
    .unwrap();
    solve(&mut tree, 120.);
    assert!(tree.layout(&item).is_err());
    tree.update_node_params(
        &rtl,
        LayoutParams {
            disabled: false,
            ..*tree.params(&rtl).unwrap()
        },
    )
    .unwrap();
    tree.move_node(&item, Destination::LastChildOf(&ltr))
        .unwrap();
    solve(&mut tree, 120.);
    assert_eq!(tree.layout(&item).unwrap().x, [0., 25.]);
    tree.set_rules(&item, Default::default()).unwrap();
    solve(&mut tree, 120.);
    assert_eq!(tree.layout(&item).unwrap().x, [0., 22.]);
    tree.remove(&item).unwrap();
    solve(&mut tree, 120.);
    assert_eq!(tree.rules(&item), Err(TreeError::StaleNode));
}
#[test]
fn logical_wrap_and_shrink_use_real_width_for_multiline_measurement() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.set_rules(
        &root,
        NodeRules {
            flex: Some(FlexLayout::default()),
            ..Default::default()
        },
    )
    .unwrap();
    let label = tree
        .add_node(
            &root,
            LayoutParams {
                text: TextContent::Wrapping,
                ..box_params(Size::Pixels(100.), Size::FitContent)
            },
        )
        .unwrap();
    tree.set_rules(
        &label,
        NodeRules {
            flex_item: FlexItem {
                shrink: 1.,
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    tree.add_node(&root, fixed(40., 14.)).unwrap();
    for (w, h) in [(90., 20.), (140., 10.), (65., 40.)] {
        tree.solve_layout_with_measure(Xy::new(w, 90.), |_, _, width| {
            Xy::new(100., width.map_or(10., |v| (100. / v.max(1.)).ceil() * 10.))
        });
        let r = tree.layout(&label).unwrap();
        assert_eq!(r.x, [0., w - 40.]);
        assert_eq!(r.y, [0., h]);
    }
}
#[cfg(feature = "batch-pilot")]
#[test]
fn opted_in_batch_matches_canonical_after_resize_and_loss_of_rules() {
    let mut a = LayoutTree::<()>::new();
    let root = a.root();
    a.set_rules(
        &root,
        NodeRules {
            flex: Some(FlexLayout {
                gap: 10.,
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    for w in [160., 120.] {
        let child = a.add_node(&root, fixed(w, 20.)).unwrap();
        a.set_rules(
            &child,
            NodeRules {
                flex_item: FlexItem::css(),
                ..Default::default()
            },
        )
        .unwrap();
    }
    let mut b = a.clone();
    let br = b.root();
    for w in [220., 300., 170., 220.] {
        let window = Xy::new(w, 60.);
        a.solve_layout(window);
        b.solve_layout_batch(window).unwrap();
        let boxes = |tree: &LayoutTree, root: &NodeId| {
            tree.children(root)
                .unwrap()
                .map(|n| tree.layout(&n).unwrap())
                .collect::<Vec<_>>()
        };
        assert_eq!(boxes(&a, &root), boxes(&b, &br));
        if w == 220. {
            assert_eq!(boxes(&a, &root)[0].x, [0., 120.]);
        }
    }
    a.set_rules(&root, Default::default()).unwrap();
    b.set_rules(&br, Default::default()).unwrap();
    a.solve_layout(Xy::new(220., 60.));
    b.solve_layout_batch(Xy::new(220., 60.)).unwrap();
    assert_eq!(
        b.layout(&b.children(&br).unwrap().next().unwrap())
            .unwrap()
            .x,
        [0., 160.]
    );
}
#[cfg(feature = "batch-pilot")]
#[test]
fn rejected_managed_frame_preserves_publication_and_can_be_retried() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let field = tree.add_node(&root, fixed(45., 20.)).unwrap();
    tree.set_rules(
        &root,
        NodeRules {
            scroll: ScrollStyle {
                overflow: Xy::new(Overflow::Clip, Overflow::Auto),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let window = Xy::new(200., 80.);
    tree.solve_layout_batch(window).unwrap();
    let previous = (
        tree.layout(&field).unwrap(),
        tree.view_geometry(&root).unwrap(),
    );
    tree.update_node_params(
        &field,
        box_params(Size::AspectRatio(1.), Size::AspectRatio(1.)),
    )
    .unwrap();
    assert_eq!(
        tree.solve_layout_batch(Xy::new(260., 80.)),
        Err(BatchLayoutError::Cycle)
    );
    assert_eq!(
        previous,
        (
            tree.layout(&field).unwrap(),
            tree.view_geometry(&root).unwrap()
        )
    );
    tree.update_node_params(&field, fixed(31., 26.)).unwrap();
    tree.solve_layout_batch(Xy::new(260., 80.)).unwrap();
    assert_eq!(tree.layout(&field).unwrap().x, [0., 31.]);
    assert_eq!(tree.view_geometry(&root).unwrap().rect.x, [0., 260.]);
}
#[test]
fn diagnostics_clear_after_last_rule_is_removed() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.set_rules(
        &root,
        NodeRules {
            queries: vec![ContainerQuery {
                name: None,
                axis: LogicalAxis::Inline,
                min: None,
                max: None,
                style: Default::default(),
            }],
            ..Default::default()
        },
    )
    .unwrap();
    let window = Xy::new(80., 30.);
    tree.solve_layout(window);
    assert_eq!(
        tree.rule_issues(),
        [RuleIssue::MissingContainer(root.clone())]
    );
    tree.set_rules(&root, Default::default()).unwrap();
    tree.solve_layout(window);
    assert!(tree.rule_issues().is_empty());
}
#[test]
fn idle_and_scroll_only_updates_reuse_measurements_and_canonical_rectangles() {
    let mut tree = LayoutTree::<()>::new();
    let panel = tree.root();
    tree.update_node_params(
        &panel,
        LayoutParams {
            children_layout: ChildrenLayout::Stack {
                axis: Axis::Y,
                arrange: Arrange::Start,
                spacing: 0.,
            },
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            scroll: ScrollStyle {
                overflow: Xy::new(Overflow::Clip, Overflow::Auto),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let label = tree
        .add_node(
            &panel,
            LayoutParams {
                text: TextContent::Wrapping,
                ..box_params(Size::Fill, Size::FitContent)
            },
        )
        .unwrap();
    let calls = std::cell::Cell::new(0);
    let mut measure = |_: NodeId, _: Option<&mut ()>, _: Option<f32>| {
        calls.set(calls.get() + 1);
        Xy::new(90., 120.)
    };
    let window = Xy::new(80., 40.);
    tree.solve_layout_with_measure(window, &mut measure);
    let n = calls.get();
    assert!(n > 0);
    let before = tree.layout(&label).unwrap();
    tree.solve_layout_with_measure(window, &mut measure);
    tree.set_scroll_offset(&panel, Xy::new(0., 30.)).unwrap();
    tree.solve_layout_with_measure(window, &mut measure);
    assert_eq!(calls.get(), n);
    assert_eq!(tree.layout(&label).unwrap(), before);
    assert_eq!(
        tree.view_geometry(&label).unwrap().rect.y,
        [before.y[0] - 30., before.y[1] - 30.]
    );
}

#[test]
fn scroll_only_publication_keeps_query_width_of_fixed_control() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let panel = tree.add_node(&root, fixed(100., 100.)).unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            container: Some(Container::axis(Axis::X)),
            scroll: ScrollStyle {
                overflow: Xy::new(Overflow::Clip, Overflow::Auto),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    tree.add_node(&panel, fixed(90., 220.)).unwrap();
    let fixed_control = tree.add_node(&panel, fixed(40., 20.)).unwrap();
    tree.set_rules(
        &fixed_control,
        NodeRules {
            placement: Placement::Fixed(Default::default()),
            queries: vec![ContainerQuery {
                name: None,
                axis: LogicalAxis::Inline,
                min: None,
                max: Some(120.),
                style: QueryStyle {
                    size: Xy::new(Some(Size::Pixels(80.)), None),
                    ..Default::default()
                },
            }],
            ..Default::default()
        },
    )
    .unwrap();
    for scroll in [0., 30., 0.] {
        tree.set_scroll_offset(&panel, Xy::new(0., scroll)).unwrap();
        solve(&mut tree, 600.);
        let direct = tree.view_geometry(&fixed_control).unwrap();
        assert_eq!(direct.rect.x, [0., 80.], "scroll {scroll}");
        tree.invalidate();
        solve(&mut tree, 600.);
        assert_eq!(
            direct,
            tree.view_geometry(&fixed_control).unwrap(),
            "forced layout at {scroll}"
        );
    }
}

#[test]
fn managed_bounds_keep_the_minimum_and_publish_the_contradiction() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.set_rules(
        &root,
        NodeRules {
            flex: Some(FlexLayout::default()),
            ..Default::default()
        },
    )
    .unwrap();
    let child = tree
        .add_node(
            &root,
            LayoutParams {
                min_size: Xy::new(Some(Size::Pixels(60.)), None),
                max_size: Xy::new(Some(Size::Pixels(30.)), None),
                ..fixed(45., 10.)
            },
        )
        .unwrap();
    solve(&mut tree, 120.);
    assert_eq!(tree.layout(&child).unwrap().x, [0., 60.]);
    assert!(
        tree.warnings()
            .iter()
            .any(|w| matches!(w, LayoutWarning::MinAboveMax {node,axis:Axis::X} if node==&*child))
    );
}

#[test]
fn bounded_flexible_rows_conserve_the_requested_budget_and_mirror_every_item() {
    use keru_layout::flex::FlexMetrics;
    let mut seed = 15u32;
    let mut draw = |limit: u32| {
        seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
        (seed >> 8) % limit
    };
    for _ in 0..160 {
        let count = 2 + draw(8) as usize;
        let gap = draw(6) as f32;
        let mut items = Vec::new();
        let mut low = gap * (count - 1) as f32;
        let mut high = low;
        for _ in 0..count {
            let min = draw(33) as f32;
            let pref = min + draw(45) as f32;
            let max = pref + draw(50) as f32 + 1.;
            // A zero inner basis has no share of a shrink deficit. It also
            // cannot shrink farther here, because its minimum is zero.
            let item = FlexMetrics {
                preferred: Xy::new(pref, 18.),
                min: Xy::new(min, 0.),
                max: Xy::new(max, 40.),
                item: FlexItem {
                    grow: 1. + draw(4) as f32,
                    shrink: 1. + draw(4) as f32,
                    ..Default::default()
                },
                ..Default::default()
            };
            items.push(item);
            low += min;
            high += max;
        }
        let width = (low - 12.) + (high - low + 24.) * (draw(101) as f32 / 100.);
        let size = Xy::new(width, 40.);
        let ltr = FlexLayout {
            gap,
            ..Default::default()
        }
        .resolve(size, &items);
        let rtl = FlexLayout {
            gap,
            reverse: true,
            ..Default::default()
        }
        .resolve(size, &items);
        let used = ltr.last().unwrap().x[1] - ltr[0].x[0];
        assert!(
            (used - width.clamp(low, high)).abs() < 0.001,
            "used={used}, requested={width}, possible={low}..{high}"
        );
        for ((l, r), m) in ltr.iter().zip(&rtl).zip(&items) {
            let w = l.x[1] - l.x[0];
            assert!(w + 0.001 >= m.min.x && w <= m.max.x + 0.001);
            assert!(
                (width - l.x[1] - r.x[0]).abs() < 0.001 && (width - l.x[0] - r.x[1]).abs() < 0.001
            );
        }
    }
}

#[test]
fn width_query_uses_flex_allocation_when_a_sibling_resizes() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.set_rules(
        &root,
        NodeRules {
            flex: Some(FlexLayout::default()),
            ..Default::default()
        },
    )
    .unwrap();
    let sidebar = tree.add_node(&root, fixed(180., 60.)).unwrap();
    let panel = tree.add_node(&root, fixed(300., 60.)).unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            flex_item: FlexItem {
                shrink: 1.,
                ..Default::default()
            },
            container: Some(Container::axis(Axis::X)),
            ..Default::default()
        },
    )
    .unwrap();
    let control = tree.add_node(&panel, fixed(50., 20.)).unwrap();
    tree.set_rules(
        &control,
        NodeRules {
            queries: vec![ContainerQuery {
                name: None,
                axis: LogicalAxis::Inline,
                min: None,
                max: Some(200.),
                style: QueryStyle {
                    size: Xy::new(Some(Size::Pixels(32.)), None),
                    ..Default::default()
                },
            }],
            ..Default::default()
        },
    )
    .unwrap();
    for (sidebar_width, panel_width, control_width) in
        [(180., 300., 50.), (320., 160., 32.), (180., 300., 50.)]
    {
        tree.update_node_params(&sidebar, fixed(sidebar_width, 60.))
            .unwrap();
        solve(&mut tree, 480.);
        let panel = tree.layout(&panel).unwrap().x;
        let control = tree.layout(&control).unwrap().x;
        assert_eq!(panel[1] - panel[0], panel_width);
        assert_eq!(
            control[1] - control[0],
            control_width,
            "allocated panel width {panel_width}"
        );
    }
}

#[test]
fn dormant_rules_report_missing_dependencies_when_the_component_is_shown() {
    let mut tree = LayoutTree::new();
    let root = tree.root();
    let item = tree
        .add_node(
            &root,
            LayoutParams {
                disabled: true,
                ..fixed(10., 10.)
            },
        )
        .unwrap();
    let anchor = tree.add_node(&root, fixed(20., 20.)).unwrap();
    tree.set_rules(
        &item,
        NodeRules {
            placement: Placement::Anchor {
                target: (*anchor).clone(),
                sides: vec![Side::Below],
                gap: 0.,
            },
            queries: vec![ContainerQuery {
                name: Some("missing".into()),
                axis: LogicalAxis::Inline,
                min: None,
                max: None,
                style: Default::default(),
            }],
            ..Default::default()
        },
    )
    .unwrap();
    tree.remove(&anchor).unwrap();
    solve(&mut tree, 100.);
    tree.update_node_params(&item, fixed(10., 10.)).unwrap();
    tree.solve_layout(Xy::new(100., 300.));
    assert!(
        tree.rule_issues()
            .contains(&RuleIssue::MissingReference((*item).clone()))
    );
    assert!(
        tree.rule_issues()
            .contains(&RuleIssue::MissingContainer((*item).clone()))
    );
}
