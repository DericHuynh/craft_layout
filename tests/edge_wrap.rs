#![cfg(feature = "incremental")]

use keru_layout::flex::{FlexLayout, FlexWrap, LineAlign};
use keru_layout::layout_rules::NodeRules;
use keru_layout::tracks::{Track, TrackAxis, TrackGrid};
use keru_layout::{
    Anchor, Arrange, ChildId, LayoutParams, LayoutTree, Margin, Pos, Size, Xy, XyRect,
};

fn at_start(width: Size, height: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(width, height),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}

fn flex(justify: Arrange, gap: f32, line_gap: f32) -> NodeRules {
    NodeRules {
        flex: Some(FlexLayout {
            wrap: FlexWrap::Wrap,
            justify,
            gap,
            line_gap,
            align_content: LineAlign::Start,
            ..Default::default()
        }),
        ..Default::default()
    }
}

fn solve(tree: &mut LayoutTree<()>, width: f32) {
    tree.solve_layout(Xy::new(width, 100.));
    assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
    assert!(tree.rule_issues().is_empty(), "{:?}", tree.rule_issues());
}

#[derive(Clone, Copy)]
enum Shelf {
    Grid,
    Flex,
    FlexWithSpacer,
}

impl Shelf {
    fn build(self, count: usize) -> (LayoutTree<()>, ChildId, Vec<ChildId>) {
        let mut tree = LayoutTree::new();
        let shelf = tree
            .add_node(&tree.root(), at_start(Size::Fill, Size::FitContent))
            .unwrap();
        let rules = match self {
            Self::Grid => NodeRules {
                grid: Some(TrackGrid {
                    tracks: Xy::new(
                        TrackAxis::AutoFill {
                            minimum: 40.,
                            track: Track::Pixels(40.),
                        },
                        TrackAxis::default(),
                    ),
                    justify: Xy::new(Arrange::SpaceBetween, Arrange::Start),
                    gap: Xy::new(4., 6.),
                    ..Default::default()
                }),
                ..Default::default()
            },
            Self::Flex | Self::FlexWithSpacer => flex(Arrange::SpaceBetween, 4., 6.),
        };
        tree.set_rules(&shelf, rules).unwrap();
        let cards = (0..count)
            .map(|_| {
                tree.add_node(&shelf, at_start(Size::Pixels(40.), Size::Pixels(20.)))
                    .unwrap()
            })
            .collect();
        if matches!(self, Self::FlexWithSpacer) {
            tree.add_node(&shelf, at_start(Size::Pixels(40.), Size::Pixels(0.)))
                .unwrap();
        }
        (tree, shelf, cards)
    }
}

// https://travishorn.com/some-ways-to-align-the-last-row-in-a-flexbox-grid/
#[test]
fn incomplete_catalog_rows_keep_shared_columns_without_a_phantom_card() {
    for mode in [Shelf::Grid, Shelf::Flex, Shelf::FlexWithSpacer] {
        let (mut tree, shelf, cards) = mode.build(8);
        for (width, count) in [(184., 6), (184., 7), (184., 8), (171., 6), (184., 6)] {
            for (i, id) in cards.iter().enumerate() {
                let mut params = *tree.params(id).unwrap();
                params.disabled = i >= count;
                tree.update_node_params(id, params).unwrap();
            }
            let (mut fresh, fresh_shelf, fresh_cards) = mode.build(count);
            solve(&mut tree, width);
            solve(&mut fresh, width);
            let capacity = if width == 184. { 4 } else { 3 };
            let total = count + usize::from(matches!(mode, Shelf::FlexWithSpacer));
            let lines = total.div_ceil(capacity);
            let expected_height = 20. * count.div_ceil(capacity) as f32 + 6. * (lines - 1) as f32;
            let bounds = tree.layout(&shelf).unwrap();
            assert_eq!(bounds.y, [0., expected_height]);
            assert_eq!(bounds, fresh.layout(&fresh_shelf).unwrap());
            for (i, (id, fresh_id)) in cards.iter().zip(&fresh_cards).enumerate() {
                let row = i / capacity;
                let occupied = match mode {
                    Shelf::Grid => capacity,
                    _ => (total - row * capacity).min(capacity),
                };
                let pitch = if occupied > 1 {
                    (width - 40.) / (occupied - 1) as f32
                } else {
                    0.
                };
                let x = (i % capacity) as f32 * pitch;
                let y = 26. * row as f32;
                let expected = Xy::new([x, x + 40.], [y, y + 20.]);
                assert_eq!(tree.layout(id).unwrap(), expected);
                assert_eq!(fresh.layout(fresh_id).unwrap(), expected);
            }
        }
    }
}

#[derive(Clone, Copy)]
enum Gutters {
    Gap,
    Margin,
    CompensatedMargin,
}

// https://coryrylan.com/blog/css-gap-space-with-flexbox
#[test]
fn a_pill_gutter_has_no_outer_edge_at_the_exact_wrap_threshold() {
    for gutters in [Gutters::Gap, Gutters::Margin, Gutters::CompensatedMargin] {
        let build = || {
            let mut tree = LayoutTree::<()>::new();
            let panel = tree
                .add_node(&tree.root(), at_start(Size::Fill, Size::FitContent))
                .unwrap();
            let gap = if matches!(gutters, Gutters::Gap) {
                6.
            } else {
                0.
            };
            tree.set_rules(&panel, flex(Arrange::Start, gap, 4.))
                .unwrap();
            let ids = [25., 31., 26.].map(|width| {
                let mut pill = at_start(Size::Pixels(width), Size::Pixels(10.));
                if !matches!(gutters, Gutters::Gap) {
                    pill.margin.x[0] = Margin::px(6.).unwrap();
                }
                tree.add_node(&panel, pill).unwrap()
            });
            (tree, panel, ids)
        };
        let (mut retained, panel, ids) = build();
        for width in [100., 94., 93., 94., 100.] {
            let (mut fresh, fresh_panel, fresh_ids) = build();
            for (tree, panel, ids) in [
                (&mut retained, &panel, &ids),
                (&mut fresh, &fresh_panel, &fresh_ids),
            ] {
                if matches!(gutters, Gutters::CompensatedMargin) {
                    // An explicitly widened box shifted left by the leading margin.
                    let mut style = at_start(Size::Pixels(width + 6.), Size::FitContent);
                    style.position.x = Pos::Pixels(-6.);
                    tree.update_node_params(panel, style).unwrap();
                }
                solve(tree, width);
                let naive = matches!(gutters, Gutters::Margin);
                let left = if naive { 6. } else { 0. };
                let wraps = width < if naive { 100. } else { 94. };
                for ((node, length), (x, y)) in ids.iter().zip([25., 31., 26.]).zip([
                    (left, 0.),
                    (left + 31., 0.),
                    if wraps { (left, 14.) } else { (left + 68., 0.) },
                ]) {
                    assert_eq!(
                        tree.layout(node).unwrap(),
                        Xy::new([x, x + length], [y, y + 10.])
                    );
                }
                assert_eq!(
                    tree.layout(panel).unwrap().y,
                    [0., if wraps { 24. } else { 10. }]
                );
            }
        }
    }
}

#[test]
fn an_action_auto_margin_uses_only_the_space_on_its_current_line() {
    let build = || {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        tree.set_rules(&root, flex(Arrange::Start, 6., 4.)).unwrap();
        let controls = [34., 34., 20.].map(|width| {
            tree.add_node(&root, at_start(Size::Pixels(width), Size::Pixels(10.)))
                .unwrap()
        });
        (tree, controls)
    };
    let (mut retained, controls) = build();
    for (width, label, action, origins) in [
        (106., 34., 20., [(0., 0.), (40., 0.), (86., 0.)]),
        (100., 34., 20., [(0., 0.), (40., 0.), (80., 0.)]),
        (99., 34., 20., [(0., 0.), (40., 0.), (79., 14.)]),
        (99., 68., 20., [(0., 0.), (0., 14.), (79., 14.)]),
        (99., 34., 110., [(0., 0.), (40., 0.), (0., 14.)]),
        (106., 34., 20., [(0., 0.), (40., 0.), (86., 0.)]),
    ] {
        let (mut fresh, fresh_controls) = build();
        for (tree, controls) in [(&mut retained, &controls), (&mut fresh, &fresh_controls)] {
            for (index, (id, size)) in controls.iter().zip([34., label, action]).enumerate() {
                let mut params = at_start(Size::Pixels(size), Size::Pixels(10.));
                if index == 2 {
                    params.margin.x[0] = Margin::AUTO;
                }
                tree.update_node_params(id, params).unwrap();
            }
            solve(tree, width);
            for ((id, size), (x, y)) in controls.iter().zip([34., label, action]).zip(origins) {
                let expected: XyRect = Xy::new([x, x + size], [y, y + 10.]);
                assert_eq!(tree.layout(id).unwrap(), expected);
            }
        }
    }
}

#[test]
fn a_trailing_action_stays_at_the_edge_when_switching_between_simple_and_managed_wrap() {
    let mut tree = LayoutTree::<()>::new();
    let mut style = at_start(Size::Fill, Size::FitContent);
    style.children_layout = keru_layout::ChildrenLayout::Wrap {
        axis: keru_layout::Axis::X,
        arrange: Arrange::Start,
        spacing: 6.,
        line_spacing: 4.,
    };
    let bar = tree.add_node(&tree.root(), style).unwrap();
    for _ in 0..2 {
        tree.add_node(&bar, at_start(Size::Pixels(34.), Size::Pixels(10.)))
            .unwrap();
    }
    let mut action = at_start(Size::Pixels(20.), Size::Pixels(10.));
    action.margin.x[0] = Margin::AUTO;
    let action = tree.add_node(&bar, action).unwrap();
    for managed in [false, true, false] {
        tree.set_rules(
            &bar,
            if managed {
                flex(Arrange::Start, 6., 4.)
            } else {
                NodeRules::default()
            },
        )
        .unwrap();
        for (window, x, y) in [(106., 86., 0.), (99., 79., 14.)] {
            solve(&mut tree, window);
            assert_eq!(
                tree.layout(&action).unwrap(),
                Xy::new([x, x + 20.], [y, y + 10.])
            );
        }
    }
}

#[test]
fn a_toolbar_resolves_fill_before_automatic_margins() {
    let mut tree = LayoutTree::<()>::new();
    let bar = tree.root();
    let stack = keru_layout::ChildrenLayout::Stack {
        axis: keru_layout::Axis::X, arrange: Arrange::Center, spacing: 4.,
    };
    tree.update_node_params(&bar, LayoutParams {
        children_layout: stack, ..LayoutParams::DEFAULT
    }).unwrap();
    let body = tree.add_node(&bar, at_start(Size::Fill, Size::Pixels(10.))).unwrap();
    let mut action = at_start(Size::Pixels(20.), Size::Pixels(10.));
    action.margin.x[0] = Margin::AUTO;
    let action = tree.add_node(&bar, action).unwrap();
    for (maximum, body_end) in [(None, 76.), (Some(Size::Pixels(30.)), 30.), (None, 76.)] {
        let mut style = *tree.params(&body).unwrap();
        style.max_size.x = maximum;
        tree.update_node_params(&body, style).unwrap();
        solve(&mut tree, 100.);
        assert_eq!(tree.layout(&body).unwrap().x, [0., body_end]);
        assert_eq!(tree.layout(&action).unwrap().x, [80., 100.]);
    }
}

#[cfg(feature = "batch-pilot")]
#[test]
fn appending_or_removing_a_tail_repositions_preceding_automatic_margins() {
    for batch in [false, true] {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        tree.update_node_params(&root, LayoutParams {
            children_layout: keru_layout::ChildrenLayout::Stack {
                axis: keru_layout::Axis::Y, arrange: Arrange::Start, spacing: 5.,
            },
            ..LayoutParams::DEFAULT
        }).unwrap();
        tree.add_node(&root, at_start(Size::Pixels(12.), Size::Pixels(18.))).unwrap();
        let mut chip = at_start(Size::Pixels(12.), Size::Pixels(20.));
        chip.margin.y = [Margin::AUTO; 2];
        let chip = tree.add_node(&root, chip).unwrap();
        let mut tail = None;
        for (include_tail, y) in [(false, 45.5), (true, 38.), (false, 45.5), (true, 38.)] {
            if include_tail {
                tail = Some(tree.add_node(&root, at_start(Size::Pixels(12.), Size::Pixels(10.))).unwrap());
            } else if let Some(node) = tail.take() {
                tree.remove(&node).unwrap();
            }
            let view = Xy::new(50., 88.);
            if batch { tree.solve_layout_batch(view).unwrap(); } else { tree.solve_layout(view); }
            assert_eq!(tree.layout(&chip).unwrap().y, [y, y + 20.]);
            if let Some(node) = &tail {
                assert_eq!(tree.layout(node).unwrap().y, [78., 88.]);
            }
        }
    }
}
