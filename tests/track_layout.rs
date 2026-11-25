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

#[test]
fn auto_tracks_share_leftover_equally_after_intrinsic_and_fractional_sizing() {
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::Tracks(vec![
                Track::Auto,
                Track::Content,
                Track::MinMax(TrackMin::Pixels(10.), TrackMax::Auto),
                Track::Fr(0.5),
            ]),
            TrackAxis::default(),
        ),
        gap: Xy::new(2., 0.),
        ..Default::default()
    };
    let items = [measure(0..1, 20., 30.), measure(1..2, 40., 40.)];
    // At 286, gaps and preferred track sizes consume 86. Half an fr takes 100.
    // The two auto maxima split the remaining 100 equally, despite different bases.
    let (edges, total) = grid.resolve_axis(Axis::X, Some(286.), 4, &items);
    assert_eq!(edges, [[0., 80.], [82., 122.], [124., 184.], [186., 286.]]);
    assert_eq!(total, 286.);
    assert_eq!(grid.resolve_axis(Axis::X, None, 4, &items).1, 86.);
    assert_eq!(grid.resolve_axis(Axis::X, Some(50.), 4, &items).1, 76.);
}

#[test]
fn collapsed_auto_fit_slots_never_receive_stretch_space() {
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::AutoFit {
                minimum: 20.,
                track: Track::Auto,
            },
            TrackAxis::default(),
        ),
        gap: Xy::new(5., 0.),
        ..Default::default()
    };
    let (n, _) = grid.place_cells(
        Xy::new(100., 30.),
        &[GridItem::default()],
        Xy::new_symm(None),
    );
    let (edges, _) = grid.resolve_axis(Axis::X, Some(100.), n.x, &[measure(0..1, 10., 12.)]);
    assert_eq!(
        edges,
        [[0., 100.], [100., 100.], [100., 100.], [100., 100.]]
    );
}

#[cfg(feature = "incremental")]
#[test]
fn published_track_edges_keep_subpixels_empty_axes_and_rtl_template_order() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{Direction, LayoutParams, LayoutTree, LogicalStyle, PixelScale, TreeError};

    fn scene() -> LayoutTree<()> {
        let mut tree = LayoutTree::new();
        let root = tree.root();
        tree.update_node_params(
            &root,
            LayoutParams {
                padding: Xy::new([7., 3.], [0., 0.]),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
        tree.set_rules(
            &root,
            NodeRules {
                logical: LogicalStyle {
                    direction: Some(Direction::Rtl),
                    ..Default::default()
                },
                grid: Some(TrackGrid {
                    tracks: Xy::new(
                        TrackAxis::Tracks(vec![Track::Pixels(20.25), Track::Fr(1.)]),
                        TrackAxis::default(),
                    ),
                    gap: Xy::new(2.5, 0.),
                    ..Default::default()
                }),
                ..Default::default()
            },
        )
        .unwrap();
        tree.set_pixel_scale(Some(PixelScale::ONE));
        tree
    }

    let mut tree = scene();
    let root = tree.root();
    assert_eq!(
        tree.resolved_grid_tracks(&root, Axis::X),
        Err(TreeError::LayoutUnavailable)
    );
    for width in [96.5, 121.5, 96.5] {
        let window = Xy::new(width, 40.);
        tree.solve_layout(window);
        let inner = width - 10.;
        let expected = [[inner - 20.25, inner], [0., inner - 22.75]];
        assert_eq!(
            tree.resolved_grid_tracks(&root, Axis::X).unwrap(),
            Some(expected.as_slice())
        );
        assert_eq!(
            tree.resolved_grid_tracks(&root, Axis::Y).unwrap(),
            Some([].as_slice())
        );

        let mut fresh = scene();
        fresh.solve_layout(window);
        assert_eq!(
            fresh.resolved_grid_tracks(&fresh.root(), Axis::X).unwrap(),
            Some(expected.as_slice())
        );
        assert_eq!(
            tree.resolved_grid_tracks(&fresh.root(), Axis::X),
            Err(TreeError::ForeignNode)
        );
        tree.set_scroll_offset(&root, Xy::new(2., 3.)).unwrap();
        tree.solve_layout(window);
        assert_eq!(
            tree.resolved_grid_tracks(&root, Axis::X).unwrap(),
            Some(expected.as_slice())
        );
    }

    let copy = tree.clone();
    assert_eq!(
        copy.resolved_grid_tracks(&copy.root(), Axis::X).unwrap(),
        tree.resolved_grid_tracks(&root, Axis::X).unwrap()
    );
    tree.set_rules(&root, NodeRules::default()).unwrap();
    tree.solve_layout(Xy::new(110., 40.));
    assert_eq!(tree.resolved_grid_tracks(&root, Axis::X).unwrap(), None);

    let child = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    tree.set_rules(
        &child,
        NodeRules {
            grid: Some(TrackGrid::default()),
            ..Default::default()
        },
    )
    .unwrap();
    tree.solve_layout(Xy::new(110., 40.));
    assert_eq!(
        tree.resolved_grid_tracks(&child, Axis::X).unwrap(),
        Some([].as_slice())
    );
    tree.update_node_params(
        &child,
        LayoutParams {
            disabled: true,
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    tree.solve_layout(Xy::new(110., 40.));
    assert_eq!(
        tree.resolved_grid_tracks(&child, Axis::X),
        Err(TreeError::LayoutUnavailable)
    );
    tree.remove(&child).unwrap();
    assert_eq!(
        tree.resolved_grid_tracks(&child, Axis::X),
        Err(TreeError::StaleNode)
    );
}

#[cfg(feature = "batch-pilot")]
#[test]
fn rejected_batch_retains_track_lists_until_the_corrected_frame_publishes() {
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{BatchLayoutError, LayoutParams, LayoutTree, Size};

    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    tree.set_rules(
        &root,
        NodeRules {
            grid: Some(TrackGrid {
                tracks: Xy::new(TrackAxis::repeat(2, Track::Fr(1.)), TrackAxis::default()),
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let field = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
    tree.solve_layout_batch(Xy::new(120., 40.)).unwrap();
    let initial = [[0., 60.], [60., 120.]];
    assert_eq!(
        tree.resolved_grid_tracks(&root, Axis::X).unwrap(),
        Some(initial.as_slice())
    );
    tree.update_node_params(
        &field,
        LayoutParams {
            size: Xy::new_symm(Size::AspectRatio(1.)),
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    let resized = Xy::new(240., 40.);
    assert_eq!(
        tree.solve_layout_batch(resized),
        Err(BatchLayoutError::Cycle)
    );
    assert_eq!(
        tree.resolved_grid_tracks(&root, Axis::X).unwrap(),
        Some(initial.as_slice())
    );
    tree.update_node_params(&field, LayoutParams::DEFAULT)
        .unwrap();
    tree.solve_layout_batch(resized).unwrap();
    assert_eq!(
        tree.resolved_grid_tracks(&root, Axis::X).unwrap(),
        Some([[0., 120.], [120., 240.]].as_slice())
    );
}

#[test]
fn fractional_floors_share_each_items_demand_by_weight_from_one_snapshot() {
    let flex = |weight| Track::MinMax(TrackMin::Content, TrackMax::Fr(weight));
    for (weights, expected) in [
        ([1., 3.], [25., 75.]),
        ([0., 1.], [0., 100.]),
        ([0., 0.], [50., 50.]),
        ([0.2, 0.3], [40., 60.]),
    ] {
        let grid = TrackGrid {
            tracks: Xy::new(
                TrackAxis::Tracks(weights.map(flex).to_vec()),
                TrackAxis::default(),
            ),
            ..Default::default()
        };
        let (tracks, _) = grid.resolve_axis(Axis::X, Some(40.), 2, &[measure(0..2, 100., 100.)]);
        assert!((tracks[0][1] - expected[0]).abs() < 0.001);
        assert!((tracks[1][1] - tracks[1][0] - expected[1]).abs() < 0.001);
    }
    let grid = TrackGrid {
        tracks: Xy::new(TrackAxis::repeat(4, flex(1.)), TrackAxis::default()),
        ..Default::default()
    };
    for (mut demands, expected) in [
        (
            [measure(0..2, 60., 60.), measure(1..4, 150., 150.)],
            [30., 50., 50., 50.],
        ),
        (
            [measure(0..1, 60., 60.), measure(0..3, 150., 150.)],
            [60., 50., 50., 0.],
        ),
    ] {
        for _ in 0..2 {
            let (edges, _) = grid.resolve_axis(Axis::X, Some(40.), 4, &demands);
            assert_eq!(
                edges.iter().map(|e| e[1] - e[0]).collect::<Vec<_>>(),
                expected
            );
            demands.reverse();
        }
    }
}

#[test]
fn natural_fractional_sizes_respect_hard_floors_and_partial_factors() {
    let axis = |tracks: Vec<Track>| TrackGrid {
        tracks: Xy::new(TrackAxis::Tracks(tracks), TrackAxis::default()),
        ..Default::default()
    };
    let grid = axis(vec![Track::Pixels(50.), Track::Fr(0.5)]);
    let demand = [measure(0..2, 0., 100.)];
    assert_eq!(
        grid.resolve_axis(Axis::X, None, 2, &demand).0,
        [[0., 50.], [50., 75.]]
    );
    assert_eq!(
        grid.resolve_axis(Axis::X, Some(75.), 2, &demand).0,
        [[0., 50.], [50., 62.5]]
    );
    let grid = axis(vec![
        Track::MinMax(TrackMin::Content, TrackMax::Fr(0.)),
        Track::Fr(1.),
    ]);
    assert_eq!(
        grid.resolve_axis(Axis::X, None, 2, &[measure(0..1, 100., 100.)])
            .1,
        200.
    );
    let grid = axis(vec![Track::MinMax(
        TrackMin::Content,
        TrackMax::Pixels(10.),
    )]);
    assert_eq!(grid.resolve_axis(Axis::X, None, 1, &[]).1, 10.);
}

#[test]
fn spanning_labels_use_available_content_tracks_before_enlarging_a_fitted_neighbor() {
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::Tracks(vec![Track::FitContent(110.), Track::FitContent(40.)]),
            TrackAxis::default(),
        ),
        gap: Xy::new(5., 0.),
        ..Default::default()
    };
    let (_, total) = grid.resolve_axis(Axis::X, None, 2, &[measure(0..1, 125., 140.)]);
    assert_eq!(total, 130.);
    let demand = [measure(1..2, 20., 20.), measure(0..2, 30., 70.)];
    assert_eq!(
        grid.resolve_axis(Axis::X, Some(100.), 2, &demand).0,
        [[0., 45.], [50., 70.]]
    );
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::Tracks(vec![Track::Content, Track::Content, Track::Fr(1.)]),
            TrackAxis::default(),
        ),
        ..Default::default()
    };
    let demand = [measure(0..1, 100., 100.), measure(0..2, 120., 120.)];
    assert_eq!(
        grid.resolve_axis(Axis::X, Some(320.), 3, &demand).0,
        [[0., 100.], [100., 120.], [120., 320.]]
    );
}

#[test]
fn fractional_budgets_match_the_largest_feasible_unit_for_two_tracks() {
    // Independently enumerate every subset of binding floors. With partial
    // factors a smaller feasible unit can also leave unused space. The largest
    // feasible unit gives the declared fractional tracks their full share.
    for a in [0., 0.25, 1., 2.] {
        for b in [0., 0.5, 1., 3.] {
            for floors in [[0., 0.], [12., 0.], [0., 21.], [12., 21.]] {
                let tracks = [a, b]
                    .into_iter()
                    .zip(floors)
                    .map(|(weight, floor)| {
                        Track::MinMax(TrackMin::Pixels(floor), TrackMax::Fr(weight))
                    })
                    .collect();
                let grid = TrackGrid {
                    tracks: Xy::new(TrackAxis::Tracks(tracks), TrackAxis::default()),
                    gap: Xy::new(4., 0.),
                    ..Default::default()
                };
                for width in [0., 4., 19., 37., 80., 129.] {
                    let budget: f32 = width - 4.;
                    let mut best = 0.0f32;
                    for active in [[false, false], [true, false], [false, true], [true, true]] {
                        let mut fixed = 0.;
                        let mut weight: f32 = 0.;
                        for (i, factor) in [a, b].into_iter().enumerate() {
                            if active[i] && factor > 0. {
                                weight += factor;
                            } else {
                                fixed += floors[i];
                            }
                        }
                        let unit = (budget - fixed).max(0.) / weight.max(1.);
                        let sizes = [floors[0].max(a * unit), floors[1].max(b * unit)];
                        let unused = (1. - weight).max(0.) * unit;
                        if sizes[0] + sizes[1] + unused <= budget + 0.00001 {
                            best = best.max(unit);
                        }
                    }
                    let edges = grid.resolve_axis(Axis::X, Some(width), 2, &[]).0;
                    for (i, factor) in [a, b].into_iter().enumerate() {
                        let expected = floors[i].max(best * factor);
                        assert!(
                            (edges[i][1] - edges[i][0] - expected).abs() < 0.0002,
                            "width {width} factors {a},{b} floors {floors:?} edges {edges:?} unit {best}"
                        );
                    }
                }
            }
        }
    }
}
