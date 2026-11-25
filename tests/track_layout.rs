use keru_layout::tracks::*;
use keru_layout::{Axis, Xy};
fn measure(tracks: std::ops::Range<usize>, min: f32, pref: f32) -> TrackContribution {
    TrackContribution {
        tracks,
        minimum: min,
        preferred: pref,
    }
}
#[test]
fn tracks_allocate_remaining_width_after_content_gaps_and_bounds() {
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::Tracks(vec![
                Track::Content,
                Track::MinMax(TrackMin::Pixels(80.), TrackMax::Fr(1.)),
                Track::Fr(2.),
                Track::Pixels(30.),
            ]),
            TrackAxis::default(),
        ),
        gap: Xy::new(10., 0.),
        ..Default::default()
    };
    let (edges, _) = grid.resolve_axis(Axis::X, Some(300.), 4, &[measure(0..1, 45., 75.)]);
    // 300 - 30 in gaps - 75 label - 30 action leaves 165 for the fields.
    // A third would be 55; bind the 80 minimum and assign the second field 85.
    assert_eq!(
        edges,
        vec![[0., 75.], [85., 165.], [175., 260.], [270., 300.]]
    );
    let (_, natural) = grid.resolve_axis(
        Axis::X,
        None,
        4,
        &[measure(0..1, 45., 75.), measure(2..3, 0., 210.)],
    );
    assert_eq!(natural, 75. + 105. + 210. + 30. + 30.);
}
#[test]
fn tall_overlapping_spans_allow_explicit_overlap_and_bound_implicit_tracks() {
    let grid = TrackGrid::default();
    let tall = GridItem {
        span: Xy::new(1, u16::MAX),
        ..Default::default()
    };
    let (n, slots) = grid.place_cells(Xy::new_symm(10.), &[tall; 5], Xy::new_symm(None));
    assert_eq!(n.y, 65_536);
    assert_eq!(slots[4].y, 1..65_536);
    let pinned = GridItem {
        start: Xy::new_symm(Some(u16::MAX)),
        span: Xy::new_symm(u16::MAX),
        ..Default::default()
    };
    let (n, slots) = grid.place_cells(Xy::new_symm(0.), &[pinned; 2], Xy::new_symm(None));
    assert_eq!(n, Xy::new_symm(65_536));
    assert_eq!(slots[0], slots[1]);
}
#[test]
fn dense_placement_backfills_holes_while_sparse_preserves_cursor() {
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::repeat(3, Track::Pixels(10.)),
            TrackAxis::default(),
        ),
        ..Default::default()
    };
    let wide = GridItem {
        span: Xy::new(2, 1),
        ..Default::default()
    };
    let items = [
        wide,
        wide,
        GridItem::default(),
        GridItem {
            start: Xy::new(Some(0), Some(0)),
            ..Default::default()
        },
    ];
    let (_, sparse) = grid.place_cells(Xy::new_symm(90.), &items, Xy::new_symm(None));
    assert_eq!(sparse[0], Xy::new(1..3, 0..1));
    assert_eq!(sparse[1], Xy::new(0..2, 1..2));
    assert_eq!(sparse[2], Xy::new(2..3, 1..2));
    let items = [wide, wide, GridItem::default()];
    let (n, sparse) = grid.place_cells(Xy::new_symm(90.), &items, Xy::new_symm(None));
    let (_, dense) = TrackGrid {
        dense: true,
        ..grid
    }
    .place_cells(Xy::new_symm(90.), &items, Xy::new_symm(None));
    assert_eq!(n, Xy::new(3, 2));
    assert_eq!(sparse[2], Xy::new(2..3, 1..2));
    assert_eq!(dense[2], Xy::new(2..3, 0..1));
}
#[test]
fn auto_fit_collapses_empty_tracks_and_gutters_while_auto_fill_preserves_them() {
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::AutoFit {
                minimum: 60.,
                track: Track::Fr(1.),
            },
            TrackAxis::default(),
        ),
        gap: Xy::new(10., 0.),
        ..Default::default()
    };
    let inner = Xy::new(270., 20.);
    let items = [GridItem::default(); 2];
    let (n, _) = grid.place_cells(inner, &items, Xy::new_symm(None));
    assert_eq!(n.x, 4);
    let demand = [measure(0..1, 0., 0.), measure(1..2, 0., 0.)];
    let (edges, _) = grid.resolve_axis(Axis::X, Some(inner.x), n.x, &demand);
    assert_eq!(
        edges,
        [[0., 130.], [140., 270.], [270., 270.], [270., 270.]]
    );
    let fill = TrackGrid {
        tracks: Xy::new(
            TrackAxis::AutoFill {
                minimum: 60.,
                track: Track::Fr(1.),
            },
            TrackAxis::default(),
        ),
        ..grid
    };
    let (edges, _) = fill.resolve_axis(Axis::X, Some(inner.x), 4, &demand);
    assert_eq!(edges, [[0., 60.], [70., 130.], [140., 200.], [210., 270.]]);
}
#[test]
fn spanning_intrinsic_requirements_are_independent_of_source_order() {
    let grid = TrackGrid {
        tracks: Xy::new(TrackAxis::repeat(3, Track::Content), TrackAxis::default()),
        ..Default::default()
    };
    let mut demand = [
        measure(0..2, 0., 100.),
        measure(1..3, 0., 100.),
        measure(0..1, 0., 20.),
    ];
    let expected = vec![[0., 60.], [60., 110.], [110., 160.]];
    assert_eq!(
        grid.resolve_axis(Axis::X, Some(200.), 3, &demand).0,
        expected
    );
    demand.reverse();
    assert_eq!(
        grid.resolve_axis(Axis::X, Some(200.), 3, &demand).0,
        expected
    );
}
#[cfg(feature = "incremental")]
#[test]
fn nested_form_rows_share_actual_columns_and_recompute_after_a_label_edit() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{LayoutParams, LayoutTree, Pos, Size};
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.set_rules(
        &root,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::Tracks(vec![Track::Content, Track::Fr(1.), Track::Pixels(30.)]),
                    TrackAxis::default(),
                ),
                gap: Xy::new(8., 4.),
                implicit: Xy::new(Track::Content, Track::Pixels(24.)),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let mut fields = Vec::new();
    let mut labels = Vec::new();
    let mut actions = Vec::new();
    for width in [46., 72.] {
        let row = tree
            .add_node(
                &root,
                LayoutParams {
                    position: Xy::new_symm(Pos::Start),
                    ..Default::default()
                },
            )
            .unwrap();
        tree.set_rules(
            &row,
            NodeRules {
                grid_item: GridItem {
                    span: Xy::new(3, 1),
                    ..Default::default()
                },
                grid: Some(TrackGrid {
                    tracks: Xy::new(TrackAxis::Subgrid, TrackAxis::repeat(1, Track::Fr(1.))),
                    ..Default::default()
                }),
                ..Default::default()
            },
        )
        .unwrap();
        labels.push(
            tree.add_node(
                &row,
                LayoutParams {
                    size: Xy::new(Size::Pixels(width), Size::Fill),
                    ..Default::default()
                },
            )
            .unwrap(),
        );
        fields.push(tree.add_node(&row, Default::default()).unwrap());
        actions.push(tree.add_node(&row, Default::default()).unwrap());
    }
    for (width, expected, edit) in [
        (220., [80., 182.], false),
        (300., [80., 262.], false),
        (300., [100., 262.], true),
    ] {
        if edit {
            let mut p = *tree.params(&labels[0]).unwrap();
            p.size.x = Size::Pixels(92.);
            tree.update_node_params(&labels[0], p).unwrap();
        }
        let window = Xy::new(width, 100.);
        tree.solve_layout(window);
        assert_eq!(tree.rule_issues(), &[]);
        for (i, field) in fields.iter().enumerate() {
            let y = 28. * i as f32;
            assert_eq!(tree.layout(field).unwrap(), Xy::new(expected, [y, y + 24.]));
            assert_eq!(tree.layout(&actions[i]).unwrap().x, [width - 30., width]);
        }
        #[cfg(feature = "batch-pilot")]
        {
            tree.solve_layout_batch(window).unwrap();
            assert_eq!(tree.layout(&fields[0]).unwrap().x, expected);
        }
        let mut reference = tree.clone();
        reference.invalidate();
        reference.solve_layout(window);
        let rows: Vec<_> = reference.children(&reference.root()).unwrap().collect();
        for (row, field) in rows.iter().zip(&fields) {
            let r = reference.children(row).unwrap().nth(1).unwrap();
            assert_eq!(reference.layout(&r), tree.layout(field));
        }
    }
}

#[cfg(feature = "incremental")]
#[test]
fn shared_tracks_preserve_padded_edges_across_opposite_directions() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{Direction, LayoutParams, LayoutTree, LogicalStyle, Pos, Size};
    let mut t = LayoutTree::<()>::new();
    let root = t.root();
    t.set_rules(
        &root,
        NodeRules {
            logical: LogicalStyle {
                direction: Some(Direction::Rtl),
                ..Default::default()
            },
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::Tracks(vec![Track::Pixels(30.), Track::Content, Track::Fr(1.)]),
                    TrackAxis::repeat(1, Track::Pixels(24.)),
                ),
                gap: Xy::new(7., 0.),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let row = t
        .add_node(
            &root,
            LayoutParams {
                padding: Xy::new([3., 5.], [0., 0.]),
                ..Default::default()
            },
        )
        .unwrap();
    t.set_rules(
        &row,
        NodeRules {
            logical: LogicalStyle {
                direction: Some(Direction::Ltr),
                ..Default::default()
            },
            grid_item: GridItem {
                span: Xy::new(3, 1),
                ..Default::default()
            },
            grid: Some(TrackGrid {
                tracks: Xy::new(TrackAxis::Subgrid, TrackAxis::repeat(1, Track::Fr(1.))),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let field = t.add_node(&row, LayoutParams::DEFAULT).unwrap();
    let label = t
        .add_node(
            &row,
            LayoutParams {
                size: Xy::new(Size::Pixels(50.), Size::Fill),
                position: Xy::new_symm(Pos::Start),
                ..Default::default()
            },
        )
        .unwrap();
    let action = t.add_node(&row, LayoutParams::DEFAULT).unwrap();
    t.solve_layout(Xy::new(200., 70.));
    assert_eq!(t.rule_issues(), &[]);
    assert_eq!(t.layout(&field).unwrap().x, [3., 106.]);
    assert_eq!(t.layout(&label).unwrap().x, [113., 163.]);
    assert_eq!(t.layout(&action).unwrap().x, [170., 195.]);
}
#[cfg(feature = "incremental")]
#[test]
fn fractional_track_width_drives_media_aspect_and_a_content_row() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{LayoutParams, LayoutTree, Size};
    let mut t = LayoutTree::<()>::new();
    let root = t.root();
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::Tracks(vec![Track::Pixels(40.), Track::Fr(1.)]),
            TrackAxis::Tracks(vec![Track::Content]),
        ),
        ..Default::default()
    };
    t.set_rules(
        &root,
        NodeRules {
            grid: Some(grid),
            ..Default::default()
        },
    )
    .unwrap();
    let media = t
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::AspectRatio(2.)),
                ..Default::default()
            },
        )
        .unwrap();
    t.set_rules(
        &media,
        NodeRules {
            grid_item: GridItem {
                start: Xy::new(Some(1), Some(0)),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    for w in [140., 230.] {
        t.solve_layout(Xy::new(w, 140.));
        assert_eq!(t.rule_issues(), &[]);
        assert_eq!(
            t.layout(&media).unwrap(),
            Xy::new([40., w], [0., (w - 40.) / 2.])
        );
    }
}

#[cfg(feature = "incremental")]
#[test]
fn first_and_last_baselines_share_parent_rows_through_a_padded_subgrid() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{LayoutParams, LayoutTree, Size};
    for (alignment, first_y, nested_y, row_height) in [
        (GridAlign::FirstBaseline, 13., 3., 33.),
        (GridAlign::LastBaseline, 9., 3., 29.),
    ] {
        let mut t = LayoutTree::<()>::new();
        let root = t.root();
        let cols = TrackAxis::repeat(2, Track::Fr(1.));
        let grid = TrackGrid {
            tracks: Xy::new(cols, TrackAxis::repeat(1, Track::Content)),
            align_items: Xy::new(GridAlign::Stretch, alignment),
            ..Default::default()
        };
        t.set_rules(
            &root,
            NodeRules {
                grid: Some(grid),
                ..Default::default()
            },
        )
        .unwrap();
        let p = LayoutParams {
            size: Xy::new(Size::Fill, Size::Pixels(20.)),
            ..Default::default()
        };
        let first = t.add_node(&root, p).unwrap();
        t.set_rules(
            &first,
            NodeRules {
                baselines: Xy::new(Some(5.), Some(12.)),
                ..Default::default()
            },
        )
        .unwrap();
        let shared = t
            .add_node(
                &root,
                LayoutParams {
                    padding: Xy::new([0.; 2], [3., 1.]),
                    ..Default::default()
                },
            )
            .unwrap();
        t.set_rules(
            &shared,
            NodeRules {
                grid: Some(TrackGrid {
                    tracks: Xy::new(TrackAxis::repeat(1, Track::Fr(1.)), TrackAxis::Subgrid),
                    align_items: Xy::new(GridAlign::Stretch, alignment),
                    ..Default::default()
                }),
                ..Default::default()
            },
        )
        .unwrap();
        let child = t.add_node(&shared, p).unwrap();
        t.set_rules(
            &child,
            NodeRules {
                baselines: Xy::new(Some(15.), Some(18.)),
                ..Default::default()
            },
        )
        .unwrap();
        t.solve_layout(Xy::new(180., 100.));
        assert_eq!(t.rule_issues(), &[]);
        assert_eq!(t.layout(&shared).unwrap().y, [0., row_height]);
        assert_eq!(t.layout(&first).unwrap().y, [first_y, first_y + 20.]);
        assert_eq!(t.layout(&child).unwrap().y, [nested_y, nested_y + 20.]);
    }
}

#[cfg(feature = "incremental")]
#[test]
fn text_grid_shares_the_measured_last_baseline_after_line_wrap() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{
        InlineMeasurer, InlineMetrics, IntrinsicWidths, LayoutParams, LayoutTree, NodeId, Size,
        TextContent,
    };
    struct Font;
    impl InlineMeasurer<f32> for Font {
        fn intrinsic_widths(&mut self, _: &NodeId, _: Option<&f32>) -> IntrinsicWidths {
            IntrinsicWidths::new(20., 80.).unwrap()
        }
        fn measure_lines(
            &mut self,
            _: &NodeId,
            ascent: Option<&f32>,
            width: Option<f32>,
        ) -> InlineMetrics {
            let ascent = *ascent.unwrap();
            let lines = if width.is_some_and(|w| w < 80.) {
                2.
            } else {
                1.
            };
            InlineMetrics::new(lines * 16., ascent, ascent + (lines - 1.) * 16.).unwrap()
        }
    }
    let mut t = LayoutTree::<f32>::new();
    let root = t.root();
    t.set_rules(
        &root,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(
                    TrackAxis::Tracks(vec![Track::Fr(1.), Track::Pixels(80.)]),
                    TrackAxis::repeat(1, Track::Content),
                ),
                align_items: Xy::new(GridAlign::Stretch, GridAlign::LastBaseline),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let p = LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        text: TextContent::Wrapping,
        ..Default::default()
    };
    let a = t.add_node_with_context(&root, p, 9.).unwrap();
    let b = t.add_node_with_context(&root, p, 12.).unwrap();
    for (w, aa, bb) in [
        (140., [0., 32.], [13., 29.]),
        (180., [3., 19.], [0., 16.]),
        (140., [0., 32.], [13., 29.]),
    ] {
        t.solve_layout_with_typography(Xy::new(w, 100.), &mut Font)
            .unwrap();
        assert_eq!(t.rule_issues(), &[]);
        assert_eq!(t.layout(&a).unwrap().y, aa);
        assert_eq!(t.layout(&b).unwrap().y, bb);
    }
}
