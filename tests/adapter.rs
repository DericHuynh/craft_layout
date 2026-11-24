use keru_layout::*;

#[derive(Clone)]
struct Adapter<const N: usize = 4> {
    root: usize,
    parent: [Option<usize>; N],
    first: [Option<usize>; N],
    next: [Option<usize>; N],
    params: [LayoutParams; N],
    data: [NodeLayoutData; N],
    layout: LayoutData<usize>,
    output: [Option<(XyRect, XyRect)>; N],
    measurements: usize,
    writes: [usize; N],
    write_order: Vec<usize>,
    #[cfg(feature = "incremental")]
    retained: bool,
}

impl Default for Adapter {
    fn default() -> Self {
        Self {
            root: 0,
            parent: [None, Some(0), Some(1), None],
            first: [Some(1), Some(2), None, None],
            next: [None; 4],
            params: [LayoutParams::DEFAULT; 4],
            data: [NodeLayoutData::new(); 4],
            layout: LayoutData::new(),
            output: [None; 4],
            measurements: 0,
            writes: [0; 4],
            write_order: Vec::new(),
            #[cfg(feature = "incremental")]
            retained: false,
        }
    }
}

impl<const N: usize> TreeAdapter for Adapter<N> {
    type NodeId = usize;

    fn root(&self) -> usize { self.root }
    fn parent(&self, node: usize) -> Option<usize> { self.parent[node] }
    fn first_child(&self, node: usize) -> Option<usize> { self.first[node] }
    fn next_sibling(&self, node: usize) -> Option<usize> { self.next[node] }
    fn node_layout_params(&self, node: usize) -> &LayoutParams { &self.params[node] }
    fn node_layout_data(&self, node: usize) -> &NodeLayoutData { &self.data[node] }
    fn node_layout_data_mut(&mut self, node: usize) -> &mut NodeLayoutData { &mut self.data[node] }
    fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }

    fn measure_content(&mut self, node: usize, input: ContentMeasureInput) -> Xy<f32> {
        self.measurements += 1;
        assert_eq!(node, 2);
        assert_eq!(input.axis, Axis::Y);
        assert_eq!(input.known_dimensions.x, Some(10.25));
        Xy::new(0.0, 2.4)
    }

    fn write_output_rect(&mut self, node: usize, absolute: XyRect, local: XyRect) {
        self.output[node] = Some((absolute, local));
        self.writes[node] += 1;
        self.write_order.push(node);
    }

    #[cfg(feature = "incremental")]
    fn retains_output_rects(&self) -> bool { self.retained }
}

#[test]
fn rounded_stack_and_grid_keep_preorder_and_parent_local_bits() {
    const BRANCH_CHILD: usize = 23;
    const N: usize = BRANCH_CHILD + 1;
    let mut tree = Adapter::<N> {
        root: 0,
        parent: std::array::from_fn(|node| match node { 0 => None, BRANCH_CHILD => Some(17), _ => Some(0) }),
        first: std::array::from_fn(|node| match node { 0 => Some(1), 17 => Some(BRANCH_CHILD), _ => None }),
        next: std::array::from_fn(|node| (1..BRANCH_CHILD - 1).contains(&node).then_some(node + 1)),
        params: [LayoutParams::DEFAULT; N],
        data: [NodeLayoutData::new(); N],
        layout: LayoutData::new(),
        output: [None; N],
        measurements: 0,
        writes: [0; N],
        write_order: Vec::new(),
        #[cfg(feature = "incremental")]
        retained: false,
    };
    tree.params[0].padding = Xy::new([0.2, 0.0], [0.125, 0.0]);
    for (node, params) in tree.params.iter_mut().enumerate().skip(1) {
        params.size = Xy::new(Size::Pixels(2.4 + node as f32 * 0.025), Size::Pixels(3.25));
        params.position = Xy::new_symm(Pos::Start);
    }
    tree.params[4].disabled = true;
    tree.params[6].grid_span = Xy::new(3, 2);
    tree.params[12].free_placement = true;
    tree.params[17].children_layout = ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 0.0 };
    tree.params[17].padding.x[0] = 0.225;
    let window = Xy::new(120.0, 10.0);
    let scale = 1.25_f64;
    let expected_order: Vec<_> = (0..BRANCH_CHILD).filter(|&node| node != 4)
        .flat_map(|node| [Some(node), (node == 17).then_some(BRANCH_CHILD)].into_iter().flatten())
        .collect();
    let snap = |edge: f32| ((f64::from(edge) * scale).round() / scale) as f32;
    let bits = |rect: XyRect| Xy::new(rect.x.map(f32::to_bits), rect.y.map(f32::to_bits));
    for mode in [
        ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 0.05 },
        ChildrenLayout::Grid { columns: MainAxisCellSize::Count(7), main_axis: Axis::X, spacing_x: 0.05, spacing_y: 0.15, backfill: false },
    ] {
        tree.params[0].children_layout = mode;
        let (mut raw_tree, mut rounded) = (tree.clone(), tree.clone());
        raw_tree.solve_layout(window);
        rounded.layout.set_pixel_scale(Some(PixelScale::new(scale as f32).unwrap()));
        rounded.solve_layout(window);
        assert_eq!(raw_tree.write_order, expected_order);
        assert_eq!(rounded.write_order, expected_order);
        assert!(rounded.output[4].is_none());
        if matches!(mode, ChildrenLayout::Stack { .. }) {
            let mut general = tree.clone();
            // This resolves to zero after bypassing the plain Start prefix.
            general.params[1].margin.x[1] = Margin::AUTO;
            general.solve_layout(window);
            assert_eq!(general.write_order, expected_order);
            for &node in &expected_order {
                let (absolute, local) = raw_tree.output[node].unwrap();
                let (general_absolute, general_local) = general.output[node].unwrap();
                assert_eq!(bits(absolute), bits(general_absolute));
                assert_eq!(bits(local), bits(general_local));
            }
        }
        let general_grid = matches!(mode, ChildrenLayout::Grid { .. }).then(|| {
            let mut general = tree.clone();
            for params in &mut general.params[1..] {
                // Grid resolves an auto margin to zero, through the general position resolver.
                params.margin.x[1] = Margin::AUTO;
            }
            general.layout.set_pixel_scale(Some(PixelScale::new(scale as f32).unwrap()));
            general.solve_layout(window);
            assert_eq!(general.write_order, expected_order);
            general
        });
        for &node in &expected_order {
            let raw = raw_tree.output[node].unwrap().0;
            let absolute = Xy::new(raw.x.map(snap), raw.y.map(snap));
            let origin = tree.parent[node].map_or(Xy::new_symm(0.0), |parent| {
                let raw = raw_tree.output[parent].unwrap().0;
                Xy::new(snap(raw.x[0]), snap(raw.y[0]))
            });
            let local = Xy::new(absolute.x.map(|x| x - origin.x), absolute.y.map(|y| y - origin.y));
            let (actual_absolute, actual_local) = rounded.output[node].unwrap();
            assert_eq!(bits(actual_absolute), bits(absolute), "{mode:?} absolute for node {node}");
            assert_eq!(bits(actual_local), bits(local), "{mode:?} local for node {node}");
            if let Some(general) = &general_grid {
                let (general_absolute, general_local) = general.output[node].unwrap();
                assert_eq!(bits(actual_absolute), bits(general_absolute));
                assert_eq!(bits(actual_local), bits(general_local));
            }
        }
    }
}

#[test]
fn measurement_requests_and_results_preserve_binary32_words() {
    use keru_layout::measurement::{Axis as MeasurementAxis, Request, SizeBits};

    const NEGATIVE_ZERO: u32 = 0x8000_0000;
    const NAN: u32 = 0xffc1_2345;
    let negative_zero = f32::from_bits(NEGATIVE_ZERO);
    let nan = f32::from_bits(NAN);
    assert!(matches!(Request::text_height(None), Request::TextHeight { wrap_width: None }));
    assert!(matches!(Request::text_height(Some(negative_zero)),
        Request::TextHeight { wrap_width: Some(NEGATIVE_ZERO) }));
    assert!(matches!(Request::text_height(Some(nan)),
        Request::TextHeight { wrap_width: Some(NAN) }));

    let horizontal = Request::from(ContentMeasureInput {
        axis: Axis::X,
        known_dimensions: Xy::new(None, Some(negative_zero)),
        max_size: Xy::new(Some(nan), Some(0.0)),
    });
    assert!(matches!(horizontal, Request::Content {
        axis: MeasurementAxis::X,
        known_dimensions: [None, Some(NEGATIVE_ZERO)],
        max_size: [Some(NAN), Some(0)],
    }));

    let vertical = Request::from(ContentMeasureInput {
        axis: Axis::Y,
        known_dimensions: Xy::new(Some(nan), None),
        max_size: Xy::new(None, Some(negative_zero)),
    });
    assert!(matches!(vertical, Request::Content {
        axis: MeasurementAxis::Y,
        known_dimensions: [Some(NAN), None],
        max_size: [None, Some(NEGATIVE_ZERO)],
    }));

    let size = SizeBits { x: NAN, y: NEGATIVE_ZERO }.to_size();
    assert_eq!(size.x.to_bits(), NAN);
    assert_eq!(size.y.to_bits(), NEGATIVE_ZERO);
}

#[cfg(feature = "incremental")]
#[test]
fn a_retained_width_grid_supplies_a_nonzero_cell_to_a_rebuilt_subtree() {
    let window = Xy::new(60.0, 80.0);
    let mut tree = Adapter {
        retained: true,
        parent: [None, Some(0), Some(0), None],
        first: [Some(1), None, None, None],
        next: [None, Some(2), None, None],
        ..Adapter::default()
    };
    tree.params[0] = LayoutParams {
        size: Xy::new(Size::Pixels(60.0), Size::Pixels(80.0)),
        children_layout: ChildrenLayout::Grid {
            columns: MainAxisCellSize::Width(30.0), main_axis: Axis::X,
            spacing_x: 0.0, spacing_y: 0.0, backfill: true,
        },
        ..LayoutParams::DEFAULT
    };
    tree.params[2] = LayoutParams {
        children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 0.0 },
        ..LayoutParams::DEFAULT
    };
    tree.solve_layout(window);
    let writes = tree.writes;
    tree.first[2] = Some(3);
    tree.parent[3] = Some(2);
    tree.register_child_attached(3).unwrap();
    assert!(matches!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { .. }));

    // The grid and first cell were skipped. The far cell's container and its
    // new child must receive the same absolute and parent-local coordinates.
    assert_eq!(tree.writes[0], writes[0]);
    assert_eq!(tree.writes[1], writes[1]);
    assert_eq!(tree.writes[2], writes[2] + 1);
    assert_eq!(tree.writes[3], 1);
    assert_eq!(tree.output[2].unwrap().0.x, [30.0, 60.0]);
    assert_eq!(tree.output[3].unwrap().0.x, [30.0, 60.0]);
    assert_eq!(tree.output[3].unwrap().1.x, [0.0, 30.0]);
    let mut fresh = Adapter {
        parent: tree.parent, first: tree.first, next: tree.next, params: tree.params,
        ..Adapter::default()
    };
    fresh.solve_layout(window);
    let bits = |r: XyRect| (r.x.map(f32::to_bits), r.y.map(f32::to_bits));
    assert_eq!(
        tree.output.map(|entry| entry.map(|(absolute, local)| (bits(absolute), bits(local)))),
        fresh.output.map(|entry| entry.map(|(absolute, local)| (bits(absolute), bits(local)))),
    );
}

#[cfg(feature = "incremental")]
#[test]
fn grid_replay_keeps_the_clean_spanned_cell_and_publishes_the_edited_subtree() {
    let viewport = Xy::new(94.25, 82.5);
    let scale = PixelScale::new(1.25).unwrap();
    let bits = |rect: XyRect| (rect.x.map(f32::to_bits), rect.y.map(f32::to_bits));
    for retained in [false, true] {
        let mut tree = Adapter {
            retained,
            parent: [None, Some(0), Some(0), None],
            first: [Some(1), None, None, None],
            next: [None, Some(2), None, None],
            ..Adapter::default()
        };
        tree.params[0] = LayoutParams {
            size: Xy::new(Size::Pixels(94.25), Size::Pixels(82.5)),
            children_layout: ChildrenLayout::Grid {
                columns: MainAxisCellSize::Width(30.0), main_axis: Axis::X,
                spacing_x: 1.25, spacing_y: 2.25, backfill: true,
            },
            ..LayoutParams::DEFAULT
        };
        tree.params[1] = LayoutParams {
            size: Xy::new(Size::Pixels(49.5), Size::Pixels(17.75)),
            grid_span: Xy::new(2, 1),
            position: Xy::new(Pos::Frac(0.375), Pos::End),
            margin: Xy::new([Margin::px(1.25).unwrap(), Margin::ZERO], [Margin::ZERO; 2]),
            ..LayoutParams::DEFAULT
        };
        tree.params[2] = LayoutParams {
            grid_span: Xy::new(1, 2),
            padding: Xy::new([1.75, 1.25], [2.5, 2.0]),
            children_layout: ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Center, spacing: 1.25 },
            ..LayoutParams::DEFAULT
        };
        tree.params[3].size = Xy::new(Size::Pixels(11.5), Size::Pixels(12.25));
        tree.layout.set_pixel_scale(Some(scale));
        tree.solve_layout(viewport);
        let clean_output = tree.output[1].map(|(absolute, local)| (bits(absolute), bits(local)));
        tree.write_order.clear();

        tree.first[2] = Some(3);
        tree.parent[3] = Some(2);
        tree.register_child_attached(3).unwrap();
        assert!(matches!(tree.solve_layout_incremental(viewport), IncrementalRelayoutOutcome::Success { .. }));
        let expected_order: &[usize] = if retained { &[2, 3] } else { &[0, 1, 2, 3] };
        assert_eq!(tree.write_order, expected_order);
        assert_eq!(tree.output[1].map(|(absolute, local)| (bits(absolute), bits(local))), clean_output);
        assert!(tree.output[2].unwrap().0.x[0] > 0.0);

        let mut fresh = Adapter {
            parent: tree.parent, first: tree.first, next: tree.next, params: tree.params,
            ..Adapter::default()
        };
        fresh.layout.set_pixel_scale(Some(scale));
        fresh.solve_layout(viewport);
        assert_eq!(
            tree.output.map(|entry| entry.map(|(absolute, local)| (bits(absolute), bits(local)))),
            fresh.output.map(|entry| entry.map(|(absolute, local)| (bits(absolute), bits(local)))),
        );
    }
}

#[cfg(feature = "incremental")]
#[test]
fn a_retained_fractional_parent_supplies_its_size_to_a_rebuilt_subtree() {
    let window = Xy::new(80.5, 64.5);
    let mut tree = Adapter { retained: true, ..Adapter::default() };
    tree.params[1] = LayoutParams {
        size: Xy::new(Size::Frac(0.5), Size::Frac(0.25)),
        position: Xy::new_symm(Pos::Pixels(0.375)),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    };
    tree.params[2] = LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        children_layout: ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 0.0 },
        ..LayoutParams::DEFAULT
    };
    tree.layout.set_pixel_scale(Some(PixelScale::new(2.0).unwrap()));
    tree.solve_layout(window);
    let writes = tree.writes;

    tree.first[2] = Some(3);
    tree.parent[3] = Some(2);
    tree.params[3].size = Xy::new(Size::Fill, Size::Pixels(7.75));
    tree.register_child_attached(3).unwrap();
    assert!(matches!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { .. }));
    assert_eq!(tree.writes, [writes[0], writes[1], writes[2] + 1, 1]);

    let mut fresh = Adapter {
        parent: tree.parent, first: tree.first, params: tree.params,
        ..Adapter::default()
    };
    fresh.layout.set_pixel_scale(Some(PixelScale::new(2.0).unwrap()));
    fresh.solve_layout(window);
    let bits = |r: XyRect| (r.x.map(f32::to_bits), r.y.map(f32::to_bits));
    assert_eq!(
        tree.output.map(|entry| entry.map(|(absolute, local)| (bits(absolute), bits(local)))),
        fresh.output.map(|entry| entry.map(|(absolute, local)| (bits(absolute), bits(local)))),
    );
}

#[test]
fn partial_placement_rejects_ineligible_nodes_before_writing() {
    let mut tree = Adapter::default();
    tree.params[0].children_layout = ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 1.0 };
    tree.solve_layout(Xy::new_symm(100.0));
    let rect = Xy::new([4.0, 84.0], [7.0, 87.0]);
    let output = tree.output;
    let writes = tree.writes;
    tree.write_order.clear();

    assert_eq!(tree.place_free_placed_subtree(0, rect), Err(FreePlacementError::Root));
    assert_eq!(tree.place_free_placed_subtree(1, rect), Err(FreePlacementError::InFlow));
    assert_eq!(tree.place_free_placed_subtree(3, rect), Err(FreePlacementError::Detached));
    tree.params[2].disabled = true;
    assert_eq!(tree.place_free_placed_subtree(2, rect), Err(FreePlacementError::Disabled));
    tree.params[2].disabled = false;
    tree.params[0].disabled = true;
    assert_eq!(tree.place_free_placed_subtree(2, rect), Err(FreePlacementError::Disabled));
    tree.params[0].disabled = false;
    tree.parent[2] = Some(3);
    tree.first[3] = Some(2);
    tree.first[1] = None;
    assert_eq!(tree.place_free_placed_subtree(2, rect), Err(FreePlacementError::Detached));
    assert_eq!(tree.output, output);
    assert_eq!(tree.writes, writes);
    assert!(tree.write_order.is_empty());
}

#[test]
fn partial_placement_requires_solved_sizes_throughout_the_visible_subtree() {
    let mut tree = Adapter::default();
    let rect = Xy::new_symm([10.0, 50.0]);
    assert_eq!(tree.place_free_placed_subtree(1, rect), Err(FreePlacementError::Unsolved));
    assert!(tree.write_order.is_empty());

    tree.solve_layout(Xy::new_symm(100.0));
    tree.write_order.clear();
    let output = tree.output;
    tree.parent[3] = Some(2);
    tree.first[2] = Some(3);
    assert_eq!(tree.place_free_placed_subtree(1, rect), Err(FreePlacementError::Unsolved));
    assert_eq!(tree.output, output);
    assert!(tree.write_order.is_empty());

    tree.params[2].disabled = true;
    assert_eq!(tree.place_free_placed_subtree(1, rect), Ok(()));
    assert_eq!(tree.write_order, [1]);
    tree.params[2].disabled = false;
    tree.solve_layout(Xy::new_symm(100.0));
    tree.write_order.clear();
    assert_eq!(tree.place_free_placed_subtree(1, rect), Ok(()));
    assert_eq!(tree.write_order, [1, 2, 3]);
}

#[test]
fn partial_placement_rejects_a_new_wrap_bound_until_it_is_solved() {
    let mut tree = Adapter::default();
    tree.params[1].children_layout = ChildrenLayout::Wrap {
        axis: Axis::X, arrange: Arrange::Start, spacing: 0.0, line_spacing: 0.0,
    };
    let window = Xy::new_symm(100.0);
    let rect = Xy::new_symm([10.0, 50.0]);
    tree.solve_layout(window);
    tree.write_order.clear();

    #[cfg(feature = "incremental")]
    let old = tree.params[2];
    tree.params[2].min_size.y = Some(Size::Pixels(20.0));
    #[cfg(feature = "incremental")]
    tree.register_node_change(2, &old);

    assert_eq!(tree.place_free_placed_subtree(1, rect), Err(FreePlacementError::Unsolved));
    assert!(tree.write_order.is_empty());

    tree.solve_layout(window);
    tree.write_order.clear();
    assert_eq!(tree.place_free_placed_subtree(1, rect), Ok(()));
    assert_eq!(tree.write_order, [1, 2]);
}

#[test]
fn partial_placement_writes_an_explicitly_free_child_and_its_descendants() {
    let mut tree = Adapter::default();
    tree.params[0].children_layout = ChildrenLayout::Block;
    tree.params[1].free_placement = true;
    for params in &mut tree.params[1..=2] {
        params.size = Xy::new_symm(Size::Pixels(5.0));
        params.position = Xy::new_symm(Pos::Start);
    }
    tree.solve_layout(Xy::new_symm(100.0));
    tree.write_order.clear();
    assert_eq!(tree.place_free_placed_subtree(1, Xy::new([4.0, 84.0], [7.0, 87.0])), Ok(()));
    assert_eq!(tree.write_order, [1, 2]);
    assert_eq!(tree.output[2], Some((Xy::new([4.0, 9.0], [7.0, 12.0]), Xy::new_symm([0.0, 5.0]))));
}

#[test]
fn rounded_local_coordinates_share_the_absolute_edges() {
    let mut tree = Adapter::default();
    tree.params[1] = LayoutParams {
        size: Xy::new(Size::Pixels(10.25), Size::Pixels(5.0)),
        position: Xy::new_symm(Pos::Pixels(0.3)),
        anchor: Xy::new_symm(Anchor::Start),
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    };
    tree.params[2] = LayoutParams {
        size: Xy::new_symm(Size::Auto),
        content_measure: ContentMeasure::HeightForWidth,
        ..LayoutParams::DEFAULT
    };
    tree.layout.set_pixel_scale(Some(PixelScale::new(2.0).unwrap()));
    tree.solve_layout(Xy::new_symm(100.0));
    assert_eq!(
        tree.output[2],
        Some((Xy::new([0.5, 10.5], [0.5, 2.5]), Xy::new([0.0, 10.0], [0.0, 2.0]))),
    );

    tree.place_free_placed_subtree(1, Xy::new([0.4, 100.4], [-0.1, 99.9])).unwrap();
    assert_eq!(
        tree.output[2],
        Some((Xy::new([0.5, 11.0], [0.0, 2.5]), Xy::new([0.0, 10.5], [0.0, 2.5]))),
    );
}

#[cfg(feature = "incremental")]
#[test]
fn incremental_layout_restores_a_manually_placed_free_subtree() {
    let window = Xy::new_symm(100.0);
    let mut tree = Adapter::<5> {
        root: 0,
        parent: [None, Some(0), Some(1), Some(0), None],
        first: [Some(1), Some(2), None, None, None],
        next: [None, Some(3), None, None, None],
        params: [LayoutParams::DEFAULT; 5],
        data: [NodeLayoutData::new(); 5],
        layout: LayoutData::new(),
        output: [None; 5],
        measurements: 0,
        writes: [0; 5],
        write_order: Vec::new(),
        retained: true,
    };
    tree.params[1].size = Xy::new_symm(Size::Pixels(20.0));
    tree.params[2].size = Xy::new_symm(Size::Pixels(5.0));
    tree.params[2].position = Xy::new_symm(Pos::Start);
    tree.params[3].size = Xy::new_symm(Size::Pixels(30.0));
    tree.params[4].size = Xy::new_symm(Size::Pixels(10.0));
    tree.solve_layout(window);
    let alternate_parent = Xy::new([8.0, 108.0], [16.0, 116.0]);
    tree.place_free_placed_subtree(2, alternate_parent).unwrap();
    let manually_placed = tree.output[2];

    tree.first[3] = Some(4);
    tree.parent[4] = Some(3);
    tree.register_child_attached(4).unwrap();

    let mut fresh = Adapter::<5> {
        data: [NodeLayoutData::new(); 5],
        layout: LayoutData::new(),
        output: [None; 5],
        ..tree.clone()
    };
    fresh.solve_layout(window);
    assert_ne!(manually_placed, fresh.output[2]);
    let outcome = tree.solve_layout_incremental(window);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    let bits = |rect: XyRect| [rect.x.map(f32::to_bits), rect.y.map(f32::to_bits)];
    let view = |tree: &Adapter<5>| tree.output.map(|row| row.map(|(absolute, local)| (bits(absolute), bits(local))));
    assert_eq!(view(&tree), view(&fresh));
}

#[cfg(feature = "incremental")]
#[test]
fn signed_zero_edits_match_full_layout_for_registered_and_unlocalized_changes() {
    let window = Xy::new_symm(100.0);
    for localized in [true, false] {
        let mut tree = Adapter { retained: true, ..Adapter::default() };
        tree.first[1] = None;
        tree.parent[2] = Some(0);
        tree.next[1] = Some(2);
        for (id, ratio) in [(1, 0.0), (2, -0.0)] {
            tree.params[id] = LayoutParams {
                position: Xy::new_symm(Pos::Start),
                size: Xy::new(Size::Pixels(10.0), Size::AspectRatio(ratio)),
                min_size: Xy::new(None, Some(Size::Pixels(1.0))),
                max_size: Xy::new(None, Some(Size::Pixels(20.0))),
                ..LayoutParams::DEFAULT
            };
        }
        tree.solve_layout(window);
        assert_eq!(tree.output[1].unwrap().0.y, [0.0, 20.0]);
        assert_eq!(tree.output[2].unwrap().0.y, [0.0, 1.0]);

        // These adjacent declarations have different bit patterns in a shared-style snapshot.
        for (id, ratio) in [(1, -0.0), (2, 0.0)] {
            let old = tree.params[id];
            tree.params[id].size.y = Size::AspectRatio(ratio);
            if localized { tree.register_node_change(id, &old); }
        }
        if !localized { tree.register_structural_change(); }
        tree.solve_layout_incremental(window);
        let incremental = tree.output;
        tree.solve_layout(window);
        assert_eq!(incremental, tree.output);
        assert_eq!(incremental[1].unwrap().0.y, [0.0, 1.0]);
        assert_eq!(incremental[2].unwrap().0.y, [0.0, 20.0]);
    }
}

#[cfg(feature = "incremental")]
#[test]
fn a_signed_zero_viewport_change_reaches_the_root() {
    let mut tree = Adapter { retained: true, ..Adapter::default() };
    tree.solve_layout(Xy::new(0.0, 10.0));
    let window = Xy::new(-0.0, 10.0);
    tree.solve_layout_incremental(window);
    let incremental = tree.output[0].unwrap().0.x.map(f32::to_bits);
    tree.solve_layout(window);
    assert_eq!(incremental, tree.output[0].unwrap().0.x.map(f32::to_bits));
    assert_eq!(incremental[1], (-0.0f32).to_bits());
}

#[cfg(feature = "incremental")]
#[test]
fn numeric_width_grid_reuses_cells_only_while_columns_agree() {
    const N: usize = 32;
    for main in [Axis::X, Axis::Y] {
        let window = |extent| match main {
            Axis::X => Xy::new(extent, 110.25),
            Axis::Y => Xy::new(110.25, extent),
        };
        let mut template = Adapter::<N> {
            root: 0,
            parent: std::array::from_fn(|id| (id != 0).then_some(0)),
            first: std::array::from_fn(|id| (id == 0).then_some(1)),
            next: std::array::from_fn(|id| (1..N - 1).contains(&id).then_some(id + 1)),
            params: std::array::from_fn(|id| LayoutParams {
                size: Xy::new(Size::Pixels(3.25), Size::Pixels(7.75)),
                grid_span: Xy::new(1 + (id % 3) as u16, 1 + (id % 2) as u16),
                ..LayoutParams::DEFAULT
            }),
            data: [NodeLayoutData::new(); N],
            layout: LayoutData::new(),
            output: [None; N],
            measurements: 0,
            writes: [0; N],
            write_order: Vec::new(),
            retained: true,
        };
        template.params[0] = LayoutParams {
            children_layout: ChildrenLayout::Grid {
                columns: MainAxisCellSize::Width(22.5), main_axis: main,
                spacing_x: 0.375, spacing_y: 0.25, backfill: true,
            },
            ..LayoutParams::DEFAULT
        };
        template.layout.set_pixel_scale(Some(PixelScale::new(1.25).unwrap()));
        let mut incremental = template.clone();
        incremental.solve_layout(window(200.0));
        for width in [204.0, 165.0, 164.0, 216.0, 200.0] {
            let mut full = template.clone();
            full.solve_layout(window(width));
            assert!(matches!(incremental.solve_layout_incremental(window(width)),
                IncrementalRelayoutOutcome::Success { .. }));
            let bits = |(a, l): (XyRect, XyRect)| [a.x, a.y, l.x, l.y].map(|edges| edges.map(f32::to_bits));
            for id in 0..N {
                assert_eq!(incremental.output[id].map(bits), full.output[id].map(bits), "{main:?} {width} node {id}");
            }
        }
    }
}

#[cfg(feature = "incremental")]
#[test]
fn checked_solve_recovers_after_an_unregistered_edit() {
    let mut tree = Adapter::default();
    let window = Xy::new_symm(100.0);
    tree.params[2].size = Xy::new_symm(Size::Pixels(10.0));
    tree.solve_layout(window);
    let unchanged = IncrementalRelayoutOutcome::Success { computed: 0 };
    assert_eq!(tree.solve_layout_incremental_checked(window), unchanged);

    tree.params[2].size.x = Size::Pixels(25.0);
    assert_eq!(tree.solve_layout_incremental_checked(window),
        IncrementalRelayoutOutcome::CheckedIncrementalRelayoutMismatch);
    let [left, right] = tree.output[2].unwrap().0.x;
    assert_eq!(right - left, 25.0);
    assert_eq!(tree.solve_layout_incremental_checked(window), unchanged);
}

#[cfg(feature = "incremental")]
#[test]
fn checked_initial_fallback_publishes_the_engine_reference() {
    #[derive(Default)]
    struct OverridingAdapter {
        inner: Adapter,
        full_calls: usize,
    }

    impl TreeAdapter for OverridingAdapter {
        type NodeId = usize;

        fn root(&self) -> usize { self.inner.root() }
        fn parent(&self, id: usize) -> Option<usize> { self.inner.parent(id) }
        fn first_child(&self, id: usize) -> Option<usize> { self.inner.first_child(id) }
        fn next_sibling(&self, id: usize) -> Option<usize> { self.inner.next_sibling(id) }
        fn node_layout_params(&self, id: usize) -> &LayoutParams { self.inner.node_layout_params(id) }
        fn node_layout_data(&self, id: usize) -> &NodeLayoutData { self.inner.node_layout_data(id) }
        fn node_layout_data_mut(&mut self, id: usize) -> &mut NodeLayoutData { self.inner.node_layout_data_mut(id) }
        fn layout_data(&mut self) -> &mut LayoutData<usize> { self.inner.layout_data() }
        fn write_output_rect(&mut self, id: usize, rect: XyRect, local: XyRect) {
            self.inner.write_output_rect(id, rect, local);
        }
        fn solve_layout(&mut self, window: Xy<f32>) {
            self.full_calls += 1;
            self.inner.solve_layout(window);
        }
    }

    let window = Xy::new(100.25, 80.75);
    let mut reference = Adapter::default();
    reference.solve_layout(window);
    let mut checked = OverridingAdapter::default();
    assert_eq!(checked.solve_layout_incremental_checked(window), IncrementalRelayoutOutcome::FallbackNeverSolved);
    assert_eq!(checked.full_calls, 0);
    assert_eq!(checked.inner.write_order, reference.write_order);
    assert_eq!(checked.inner.output, reference.output);

    checked.inner.write_order.clear();
    assert_eq!(
        checked.solve_layout_incremental_checked(window),
        IncrementalRelayoutOutcome::Success { computed: 0 },
    );
    assert_eq!(checked.full_calls, 0);
    assert_eq!(checked.inner.write_order, reference.write_order);
    assert_eq!(checked.inner.output, reference.output);

    let mut ordinary = OverridingAdapter::default();
    assert_eq!(ordinary.solve_layout_incremental(window), IncrementalRelayoutOutcome::FallbackNeverSolved);
    assert_eq!(ordinary.full_calls, 1);
}

#[cfg(feature = "incremental")]
#[test]
fn checked_solve_compares_placement_even_when_every_size_agrees() {
    let mut tree = Adapter::default();
    let window = Xy::new_symm(100.0);
    tree.parent[2] = Some(0);
    tree.first[1] = None;
    tree.next[1] = Some(2);
    tree.params[0].children_layout = ChildrenLayout::Grid {
        columns: MainAxisCellSize::Count(2), main_axis: Axis::X,
        spacing_x: 0.0, spacing_y: 0.0, backfill: true,
    };
    for node in [1, 2] {
        tree.params[node].size = Xy::new_symm(Size::Pixels(10.0));
        tree.params[node].position = Xy::new_symm(Pos::Start);
        tree.params[node].anchor = Xy::new_symm(Anchor::Start);
    }
    tree.solve_layout(window);
    assert_eq!(tree.output[1].unwrap().0.x, [0.0, 10.0]);
    assert_eq!(tree.output[2].unwrap().0.x, [50.0, 60.0]);

    // Swap equal-size nodes while leaving the old grid cell assignments cached.
    tree.first[0] = Some(2);
    tree.next[1] = None;
    tree.next[2] = Some(1);
    tree.writes = [0; 4];
    assert_eq!(
        tree.solve_layout_incremental_checked(window),
        IncrementalRelayoutOutcome::CheckedIncrementalRelayoutMismatch
    );
    assert_eq!(tree.output[1].unwrap().0.x, [50.0, 60.0]);
    assert_eq!(tree.output[2].unwrap().0.x, [0.0, 10.0]);
    assert_eq!(tree.writes, [1, 1, 1, 0]);
}

#[cfg(feature = "incremental")]
#[test]
fn attachment_rejects_the_root_and_detached_subtrees() {
    let mut tree = Adapter { retained: true, ..Adapter::default() };
    tree.first[1] = None;
    tree.parent[2] = Some(3);
    tree.first[3] = Some(2);
    let window = Xy::new_symm(100.0);
    tree.solve_layout(window);
    assert_eq!(tree.register_child_attached(0), Err(AttachmentError::Root));
    assert_eq!(tree.register_child_attached(3), Err(AttachmentError::Detached));
    assert_eq!(tree.register_child_attached(2), Err(AttachmentError::Detached));
    assert_eq!(tree.solve_layout_incremental_checked(window), IncrementalRelayoutOutcome::Success { computed: 0 });
}

#[cfg(feature = "incremental")]
#[test]
fn localized_reparent_and_unspecified_structure_notifications() {
    let mut tree = Adapter::default();
    let window = Xy::new(100.0, 60.0);
    tree.params[1].size = Xy::new_symm(Size::Pixels(40.0));
    tree.solve_layout(window);
    assert_eq!(tree.output[2].unwrap().1.x, [0.0, 40.0]);

    tree.parent[2] = Some(0);
    tree.first[1] = None;
    tree.next[1] = Some(2);
    tree.register_children_change(1);
    tree.register_child_attached(2).unwrap();
    let outcome = tree.solve_layout_incremental_checked(window);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    let expected = Xy::new([0.0, 100.0], [0.0, 60.0]);
    assert_eq!(tree.output[2], Some((expected, expected)));

    tree.parent[2] = Some(1);
    tree.first[1] = Some(2);
    tree.next[1] = None;
    tree.register_structural_change();
    let outcome = tree.solve_layout_incremental_checked(window);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert_eq!(tree.output[2].unwrap().1.x, [0.0, 40.0]);
}

#[cfg(feature = "incremental")]
#[test]
fn unspecified_child_list_edits_handle_reorder_removal_and_reused_ids() {
    let mut tree = Adapter::default();
    let window = Xy::new_symm(100.0);
    tree.first[1] = None;
    tree.next[1] = Some(2);
    tree.parent[2] = Some(0);
    tree.params[0].children_layout = ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 3.0 };
    tree.params[1].size.x = Size::Pixels(15.0);
    tree.params[2].size.x = Size::Fill;
    tree.solve_layout(window);
    assert_eq!(tree.output[2].unwrap().1.x, [18.0, 100.0]);

    let solve_unknown = |tree: &mut Adapter| {
        tree.register_structural_change();
        let outcome = tree.solve_layout_incremental(window);
        assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
        let incremental = tree.output;
        tree.solve_layout(window);
        assert_eq!(incremental, tree.output);
    };

    tree.first[0] = Some(2);
    tree.next[2] = Some(1);
    tree.next[1] = None;
    solve_unknown(&mut tree);
    assert_eq!(tree.output[2].unwrap().1.x, [0.0, 82.0]);

    tree.next[2] = None;
    tree.parent[1] = None;
    tree.output[1] = None;
    solve_unknown(&mut tree);
    assert!(tree.output[1].is_none());
    assert_eq!(tree.output[2].unwrap().1.x, [0.0, 100.0]);

    tree.data[1] = NodeLayoutData::new();
    tree.params[1].size.x = Size::Pixels(26.0);
    tree.next[2] = Some(1);
    tree.parent[1] = Some(0);
    solve_unknown(&mut tree);
    assert_eq!(tree.output[1].unwrap().1.x, [74.0, 100.0]);

    // The host replaces this node between frames and reuses its integer ID.
    tree.data[1] = NodeLayoutData::new();
    tree.output[1] = None;
    solve_unknown(&mut tree);
    assert_eq!(tree.output[1].unwrap().1.x, [74.0, 100.0]);

    tree.params[1].size.x = Size::Frac(0.5);
    solve_unknown(&mut tree);
    assert_eq!(tree.output[1].unwrap().1.x, [51.5, 100.0]);
}

#[cfg(feature = "incremental")]
#[test]
fn an_existing_subtree_can_become_the_adapter_root() {
    let mut tree = Adapter::default();
    let window = Xy::new(120.0, 80.0);
    tree.params[1].size.x = Size::Frac(0.5);
    tree.params[2].size.x = Size::Frac(0.5);
    for params in &mut tree.params {
        params.position = Xy::new_symm(Pos::Start);
    }
    tree.solve_layout(window);
    assert_eq!(tree.output[2].unwrap().1.x, [0.0, 30.0]);

    tree.root = 2;
    tree.parent = [Some(1), Some(2), None, None];
    tree.first = [None, Some(0), Some(1), None];
    tree.register_structural_change();
    let outcome = tree.solve_layout_incremental_checked(window);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert_eq!(tree.output[2].unwrap().1.x, [0.0, 60.0]);
    assert_eq!(tree.output[0].unwrap().1.x, [0.0, 30.0]);
}

#[cfg(feature = "incremental")]
#[test]
fn retained_rectangles_refresh_on_placement_edits_resize_and_scale() {
    let mut tree = Adapter { retained: true, ..Adapter::default() };
    tree.parent[2] = Some(0);
    tree.first[1] = None;
    tree.next[1] = Some(2);
    tree.params[1].size = Xy::new_symm(Size::Pixels(15.0));
    tree.params[2].size = Xy::new_symm(Size::Pixels(10.25));
    let initial = Xy::new_symm(100.25);
    tree.solve_layout(initial);
    assert_eq!(tree.writes, [1, 1, 1, 0]);

    let check = |tree: &mut Adapter, window| {
        let mut oracle = tree.clone();
        oracle.solve_layout(window);
        let outcome = tree.solve_layout_incremental(window);
        assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
        assert_eq!(tree.output, oracle.output);
    };
    let detach_first = |tree: &mut Adapter| {
        tree.first[0] = Some(2);
        tree.next[1] = None;
        tree.parent[1] = None;
        tree.register_children_change(0);
    };
    let attach_first = |tree: &mut Adapter| {
        tree.first[0] = Some(1);
        tree.next[1] = Some(2);
        tree.parent[1] = Some(0);
        tree.register_child_attached(1).unwrap();
    };
    detach_first(&mut tree);
    check(&mut tree, initial);
    assert_eq!(tree.writes[2], 1);

    let old = tree.params[2];
    tree.params[2].position.x = Pos::End;
    tree.register_node_change(2, &old);
    attach_first(&mut tree);
    check(&mut tree, initial);
    assert_eq!(tree.writes[2], 2);

    let larger = Xy::new_symm(200.25);
    detach_first(&mut tree);
    check(&mut tree, larger);
    assert_eq!(tree.writes[2], 3);
    assert_eq!(tree.output[2].unwrap().0.x, [190.0, 200.25]);

    tree.layout.set_pixel_scale(Some(PixelScale::new(2.0).unwrap()));
    attach_first(&mut tree);
    check(&mut tree, larger);
    assert_eq!(tree.writes[2], 4);
    assert_eq!(tree.output[2].unwrap().0.x, [190.0, 200.5]);
}

#[cfg(feature = "incremental")]
#[test]
fn leaving_a_stack_flow_repositions_retained_siblings() {
    let mut tree = Adapter { retained: true, ..Adapter::default() };
    tree.parent[2] = Some(0);
    tree.first[1] = None;
    tree.next[1] = Some(2);
    tree.params[0].children_layout = ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 3.0 };
    tree.params[1].size = Xy::new_symm(Size::Pixels(14.0));
    tree.params[2].size = Xy::new_symm(Size::Pixels(21.0));
    let window = Xy::new_symm(100.0);
    tree.solve_layout(window);
    assert_eq!(tree.output[2].unwrap().0.x, [17.0, 38.0]);

    tree.params[1].free_placement = true;
    tree.register_structural_change();
    let outcome = tree.solve_layout_incremental(window);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert_eq!(tree.output[2].unwrap().0.x, [0.0, 21.0]);
}

#[cfg(feature = "incremental")]
#[test]
fn reenabled_subtrees_measure_changes_made_while_hidden() {
    for localized in [false, true] {
        let mut tree = Adapter::default();
        let window = Xy::new_symm(100.0);
        tree.params[2].position = Xy::new_symm(Pos::Start);
        tree.params[2].size = Xy::new_symm(Size::FitContent);
        tree.params[2].image = Some(Xy::new(12.0, 5.0));
        tree.solve_layout(window);
        assert_eq!(tree.output[2].unwrap().1.x, [0.0, 12.0]);

        tree.params[1].disabled = true;
        tree.params[2].disabled = true;
        tree.register_structural_change();
        assert!(matches!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { .. }));
        tree.params[2].image = Some(Xy::new(32.0, 7.0));
        tree.register_structural_change();
        assert_eq!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { computed: 0 });

        let old = tree.params[1];
        tree.params[1].disabled = false;
        tree.params[2].disabled = false;
        if localized {
            tree.register_node_change(1, &old);
        } else {
            tree.register_structural_change();
        }
        assert!(matches!(tree.solve_layout_incremental_checked(window), IncrementalRelayoutOutcome::Success { .. }));
        assert_eq!(tree.output[2].unwrap().1.x, [0.0, 32.0]);
    }
}

#[cfg(feature = "incremental")]
#[test]
fn reattaching_a_detached_subtree_rebuilds_its_block_and_descendant_caches() {
    let mut tree = Adapter::default();
    let window = Xy::new_symm(100.0);
    tree.first[2] = Some(3);
    tree.parent[3] = Some(2);
    tree.params[1].size = Xy::new_symm(Size::Pixels(80.0));
    tree.params[2].size = Xy::new_symm(Size::Pixels(60.0));
    tree.params[2].children_layout = ChildrenLayout::Block;
    tree.params[3].size = Xy::new_symm(Size::FitContent);
    tree.params[3].image = Some(Xy::new(21.0, 8.0));
    tree.solve_layout(window);
    let [top, bottom] = tree.output[3].unwrap().1.y;
    assert_eq!(bottom - top, 8.0);

    tree.first[0] = None;
    tree.parent[1] = None;
    tree.register_children_change(0);
    assert!(matches!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { .. }));

    tree.params[3].image = Some(Xy::new(21.0, 32.0));
    tree.first[0] = Some(1);
    tree.parent[1] = Some(0);
    tree.register_child_attached(1).unwrap();
    assert!(matches!(tree.solve_layout_incremental_checked(window), IncrementalRelayoutOutcome::Success { .. }));
    let [top, bottom] = tree.output[3].unwrap().1.y;
    assert_eq!(bottom - top, 32.0);
}

#[cfg(feature = "incremental")]
#[test]
fn reparenting_a_live_leaf_reuses_its_intrinsic_measurement() {
    for localized in [false, true] {
        let mut tree = Adapter::default();
        let window = Xy::new_symm(100.0);
        tree.next[1] = Some(3);
        tree.parent[3] = Some(0);
        tree.params[1].size = Xy::new_symm(Size::Pixels(60.0));
        tree.params[3].size = Xy::new_symm(Size::Pixels(40.0));
        tree.params[2].size = Xy::new(Size::Pixels(10.25), Size::FitContent);
        tree.params[2].content_measure = ContentMeasure::HeightForWidth;
        tree.solve_layout(window);
        assert_eq!(tree.measurements, 1);

        tree.first[1] = None;
        tree.first[3] = Some(2);
        tree.parent[2] = Some(3);
        if localized {
            tree.register_children_change(1);
            tree.register_child_attached(2).unwrap();
        } else {
            tree.register_structural_change();
        }
        assert!(matches!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { .. }));
        assert_eq!(tree.measurements, 1);
        let moved = tree.output[2];
        tree.solve_layout(window);
        assert_eq!(moved, tree.output[2]);
    }
}

#[cfg(feature = "incremental")]
#[test]
fn localized_parameter_registration_preserves_an_unlocalized_edit() {
    let mut tree = Adapter::default();
    let window = Xy::new_symm(100.0);
    tree.solve_layout(window);
    tree.params[2].size.x = Size::Pixels(24.0);
    tree.register_structural_change();
    let old = tree.params[2];
    tree.params[2].position.x = Pos::Start;
    tree.register_node_change(2, &old);
    assert!(matches!(tree.solve_layout_incremental_checked(window), IncrementalRelayoutOutcome::Success { .. }));
    assert_eq!(tree.output[2].unwrap().1.x, [0.0, 24.0]);
}

#[cfg(feature = "incremental")]
#[test]
fn first_unlocalized_edit_after_full_solves_reuses_unchanged_pixel_sizes() {
    let mut tree = Adapter::default();
    tree.first[1] = None;
    tree.next[1] = Some(2);
    tree.parent[2] = Some(0);
    tree.params[0].size = Xy::new_symm(Size::Pixels(80.0));
    tree.params[0].children_layout = ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 2.0 };
    tree.params[1].size = Xy::new_symm(Size::Pixels(11.0));
    tree.params[2].size = Xy::new_symm(Size::Pixels(14.0));
    let window = Xy::new_symm(80.0);
    tree.solve_layout(window);
    tree.solve_layout(window);

    tree.first[0] = Some(2);
    tree.next[2] = Some(1);
    tree.next[1] = None;
    tree.params[2].size.x = Size::Pixels(19.0);
    tree.register_structural_change();
    assert_eq!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { computed: 4 });
    assert_eq!(tree.output[1].unwrap().0.x, [21.0, 32.0]);
    assert_eq!(tree.output[2].unwrap().0.x, [0.0, 19.0]);
    let incremental = tree.output;
    tree.solve_layout(window);
    assert_eq!(incremental, tree.output);
}

#[cfg(feature = "incremental")]
#[test]
fn reordering_fixed_root_stack_children_only_repositions_them() {
    let mut tree = Adapter::default();
    tree.parent[2] = Some(0);
    tree.first[1] = None;
    tree.next[1] = Some(2);
    tree.params[0].children_layout = ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 2.0 };
    tree.params[1].size = Xy::new_symm(Size::Pixels(12.0));
    tree.params[2].size = Xy::new(Size::Pixels(10.25), Size::FitContent);
    tree.params[2].content_measure = ContentMeasure::HeightForWidth;
    let window = Xy::new_symm(100.0);
    tree.solve_layout(window);
    assert_eq!(tree.output[2].unwrap().1.x, [14.0, 24.25]);
    assert_eq!(tree.measurements, 1);

    tree.first[0] = Some(2);
    tree.next[2] = Some(1);
    tree.next[1] = None;
    tree.register_children_change(0);
    assert_eq!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { computed: 0 });
    assert_eq!(tree.output[2].unwrap().1.x, [0.0, 10.25]);
    assert_eq!(tree.output[1].unwrap().0.x, [12.25, 24.25]);
    assert_eq!(tree.measurements, 1);

    tree.first[0] = Some(1);
    tree.next[1] = Some(2);
    tree.next[2] = None;
    tree.register_structural_change();
    let outcome = tree.solve_layout_incremental(window);
    assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
    assert_eq!(tree.output[2].unwrap().1.x, [14.0, 24.25]);
    assert_eq!(tree.measurements, 1);
}

#[cfg(feature = "incremental")]
#[test]
fn retained_view_matches_a_fresh_full_build_across_edits() {
    fn bits((absolute, local): (XyRect, XyRect)) -> [[u32; 2]; 4] {
        [absolute.x, absolute.y, local.x, local.y].map(|edge| edge.map(f32::to_bits))
    }

    fn visible_view(tree: &Adapter, node: usize, output: &mut Vec<(usize, [[u32; 2]; 4])>) {
        if tree.params[node].disabled { return; }
        output.push((node, bits(tree.output[node].expect("missing visible rectangle"))));
        let mut next = tree.first_child(node);
        while let Some(child) = next {
            visible_view(tree, child, output);
            next = tree.next_sibling(child);
        }
    }

    fn check(tree: &mut Adapter, window: Xy<f32>, scale: Option<PixelScale>, order: &[usize]) {
        // Copy only the host's live declarations and links. The reference gets fresh
        // node data, output storage, and a fresh solver with the same pixel scale.
        let mut fresh = Adapter {
            root: tree.root, parent: tree.parent, first: tree.first, next: tree.next,
            params: tree.params, ..Adapter::default()
        };
        fresh.layout.set_pixel_scale(scale);
        fresh.solve_layout(window);
        tree.layout.set_pixel_scale(scale);
        let outcome = tree.solve_layout_incremental(window);
        assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{outcome:?}");
        let mut incremental = Vec::new();
        visible_view(tree, tree.root(), &mut incremental);
        let expected: Vec<_> = order.iter().map(|&id| (id, bits(fresh.output[id].unwrap()))).collect();
        assert_eq!(incremental, expected);
        for (node, output) in fresh.output.iter().enumerate() {
            assert_eq!(output.is_some(), order.contains(&node));
        }
    }

    let window = Xy::new(100.25, 81.75);
    let mut tree = Adapter { retained: true, ..Adapter::default() };
    tree.parent[3] = Some(0);
    tree.next[1] = Some(3);
    for (panel, left, width) in [(1, 8.25, 40.0), (3, 24.25, 24.0)] {
        tree.params[panel] = LayoutParams {
            position: Xy::new(Pos::Pixels(left), Pos::Start),
            anchor: Xy::new_symm(Anchor::Start),
            size: Xy::new(Size::Pixels(width), Size::Pixels(30.5)),
            ..LayoutParams::DEFAULT
        };
    }
    tree.params[2].size = Xy::new(Size::Pixels(7.25), Size::Pixels(5.5));
    tree.params[2].position = Xy::new(Pos::End, Pos::Center);
    tree.solve_layout(window);
    check(&mut tree, window, None, &[0, 1, 2, 3]);

    // Both panels have the same right edge. Reparenting changes only the leaf's
    // local horizontal coordinates, which an absolute-only comparison would miss.
    let before = bits(tree.output[2].unwrap());
    tree.first[1] = None;
    tree.first[3] = Some(2);
    tree.parent[2] = Some(3);
    tree.register_children_change(1);
    tree.register_child_attached(2).unwrap();
    check(&mut tree, window, None, &[0, 1, 3, 2]);
    let after = bits(tree.output[2].unwrap());
    assert_eq!(&before[..2], &after[..2]);
    assert_ne!(before[2], after[2]);

    tree.first[0] = Some(3);
    tree.next[3] = Some(1);
    tree.next[1] = None;
    tree.register_structural_change();
    check(&mut tree, window, None, &[0, 3, 2, 1]);

    let writes_before = tree.writes[1];
    tree.first[3] = None;
    tree.parent[2] = None;
    tree.register_children_change(3);
    check(&mut tree, window, None, &[0, 3, 1]);
    assert_eq!(tree.writes[1], writes_before, "the independent panel should retain its output");

    // Replace the detached node with a new instance using the same host ID.
    tree.data[2] = NodeLayoutData::new();
    tree.output[2] = None;
    tree.params[2].size.x = Size::Frac(0.75);
    tree.first[3] = Some(2);
    tree.parent[2] = Some(3);
    tree.register_structural_change();
    check(&mut tree, window, Some(PixelScale::new(1.5).unwrap()), &[0, 3, 2, 1]);

    tree.params[3].disabled = true;
    tree.params[2].disabled = true;
    tree.register_structural_change();
    check(&mut tree, window, Some(PixelScale::new(1.5).unwrap()), &[0, 1]);
    tree.params[2].size.y = Size::Pixels(13.75);
    tree.params[2].disabled = false;
    tree.params[3].disabled = false;
    tree.register_structural_change();
    check(&mut tree, Xy::new(120.625, 60.25), Some(PixelScale::new(2.0).unwrap()), &[0, 3, 2, 1]);
}

#[cfg(feature = "incremental")]
#[test]
fn a_disabled_root_publishes_no_rectangles_and_can_be_shown_again() {
    let window = Xy::new_symm(100.0);
    let mut tree = Adapter { retained: true, ..Adapter::default() };
    tree.solve_layout(window);
    for disabled in [true, false] {
        tree.writes.fill(0);
        for params in &mut tree.params { params.disabled = disabled; }
        tree.register_structural_change();
        tree.solve_layout_incremental(window);

        let mut fresh = Adapter { params: tree.params, ..Adapter::default() };
        fresh.solve_layout(window);
        if disabled {
            assert_eq!(fresh.writes, [0; 4]);
            assert_eq!(tree.writes, [0; 4]);
        } else {
            assert_eq!(fresh.writes, [1, 1, 1, 0]);
            assert_eq!(tree.writes, fresh.writes);
            assert_eq!(tree.output, fresh.output);
        }
    }
}

#[test]
fn full_stack_rechecks_a_prior_fill_leaf_count() {
    for (main, cross) in [(Axis::X, Axis::Y), (Axis::Y, Axis::X)] {
        check_fill_leaf_count(main, cross);
    }
}

fn check_fill_leaf_count(main: Axis, cross: Axis) {
    const N: usize = 9;
    let mut tree = Adapter::<N> {
        parent: std::array::from_fn(|id| match id { 0 | 8 => None, 1 => Some(0), _ => Some(1) }),
        first: std::array::from_fn(|id| match id { 0 => Some(1), 1 => Some(2), _ => None }),
        next: std::array::from_fn(|id| (2..7).contains(&id).then_some(id + 1)),
        root: 0,
        params: [LayoutParams::DEFAULT; N],
        data: [NodeLayoutData::new(); N],
        layout: LayoutData::new(),
        output: [None; N],
        measurements: 0,
        writes: [0; N],
        write_order: Vec::new(),
        #[cfg(feature = "incremental")]
        retained: false,
    };
    let window = Xy::new(100.0, 100.0);
    for (index, params) in tree.params.iter_mut().enumerate() {
        params.position = Xy::new_symm(Pos::Start);
        params.size[main] = if index == 0 { Size::Pixels(100.0) } else { Size::Fill };
        params.size[cross] = if index < 2 { Size::FitContent } else { Size::Pixels(2.25 + index as f32) };
        if index < 2 {
            params.children_layout = ChildrenLayout::Stack {
                axis: if index == 0 { cross } else { main },
                arrange: Arrange::Start,
                spacing: 0.35,
            };
        }
    }
    tree.params[2].margin[cross] = [Margin::px(-0.75).unwrap(), Margin::px(1.25).unwrap()];
    let rect_bits = |(rect, local): (XyRect, XyRect)| {
        [rect.x, rect.y, local.x, local.y].map(|edges| edges.map(f32::to_bits))
    };
    let check = |tree: &mut Adapter<N>| {
        let mut cold = tree.clone();
        cold.layout = LayoutData::new();
        cold.data = [NodeLayoutData::new(); N];
        cold.output = [None; N];
        cold.write_order.clear();
        tree.output = [None; N];
        tree.write_order.clear();
        cold.solve_layout(window);
        tree.solve_layout(window);
        assert_eq!(tree.write_order, cold.write_order);
        assert_eq!(tree.output.map(|rect| rect.map(rect_bits)), cold.output.map(|rect| rect.map(rect_bits)));
    };

    check(&mut tree);
    check(&mut tree);

    // A matching hint still uses the current parent extent.
    let old_right = tree.output[7].unwrap().0[main][1];
    tree.params[0].size[main] = Size::Pixels(123.5);
    check(&mut tree);
    assert_ne!(tree.output[7].unwrap().0[main][1].to_bits(), old_right.to_bits());

    // A longer sibling list may reject after provisionally preparing a prefix.
    tree.parent[8] = Some(1);
    tree.next[7] = Some(8);
    check(&mut tree);
    check(&mut tree);

    // A shorter list rejects when its actual count does not match the hint.
    tree.next[6] = None;
    tree.next[7] = None;
    tree.parent[7] = None;
    tree.parent[8] = None;
    check(&mut tree);

    // Width bounds and non-unit weights reject the shape even at the old count.
    tree.params[5].max_size[main] = Some(Size::Pixels(12.75));
    check(&mut tree);
    tree.params[5].max_size[main] = None;
    tree.params[6].fill_weight = 2.25;
    check(&mut tree);
}

#[test]
fn cross_fill_line_matches_late_fallback() {
    const N: usize = 8;
    let margin = |value| Margin::px(value).unwrap();
    for (cross, main) in [(Axis::X, Axis::Y), (Axis::Y, Axis::X)] {
        let mut tree = Adapter::<N> {
            root: 0,
            parent: std::array::from_fn(|id| (1..7).contains(&id).then_some(0)),
            first: std::array::from_fn(|id| (id == 0).then_some(1)),
            next: std::array::from_fn(|id| (1..6).contains(&id).then_some(id + 1)),
            params: [LayoutParams::DEFAULT; N],
            data: [NodeLayoutData::new(); N],
            layout: LayoutData::new(),
            output: [None; N],
            measurements: 0,
            writes: [0; N],
            write_order: Vec::new(),
            #[cfg(feature = "incremental")]
            retained: false,
        };
        tree.params[0].size[cross] = Size::Pixels(37.625);
        tree.params[0].size[main] = Size::FitContent;
        tree.params[0].padding[cross] = [5.75, 0.5];
        tree.params[0].padding[main] = [1.25, 2.75];
        tree.params[0].children_layout = ChildrenLayout::Stack {
            axis: main, arrange: Arrange::Start, spacing: 0.1875,
        };
        let cross_margins = [
            [Margin::ZERO, Margin::ZERO],
            [margin(0.75), margin(-0.25)],
            [margin(28.5), margin(17.0)],
            [Margin::AUTO, margin(-3.0)],
            [margin(-6.5), margin(0.25)],
            [margin(-2.5), margin(2.5)],
        ];
        for (offset, pixels) in [-0.0, 2.75, 8.125, 0.5, 13.375, 3.625].into_iter().enumerate() {
            let params = &mut tree.params[offset + 1];
            params.size[main] = Size::Pixels(pixels);
            params.margin[cross] = cross_margins[offset];
            params.margin[main] = [margin(offset as f32 * 0.1), margin(-0.25)];
            params.position = Xy::new_symm(Pos::Start);
        }
        let mut fallback = tree.clone();
        fallback.next[6] = Some(7);
        fallback.parent[7] = Some(0);
        fallback.params[7].disabled = true;
        let bits = |(rect, local): (XyRect, XyRect)| {
            [rect.x, rect.y, local.x, local.y].map(|edges| edges.map(f32::to_bits))
        };
        let window = Xy::new_symm(100.0);
        for iteration in 0..4 {
            if iteration == 2 {
                tree.params[4].position[cross] = Pos::Center;
                fallback.params[4].position[cross] = Pos::Center;
            }
            if iteration == 3 {
                tree.params[4].position[cross] = Pos::Start;
                fallback.params[4].position[cross] = Pos::Start;
                let scale = Some(PixelScale::new(1.25).unwrap());
                tree.layout.set_pixel_scale(scale);
                fallback.layout.set_pixel_scale(scale);
            }
            tree.write_order.clear();
            fallback.write_order.clear();
            tree.solve_layout(window);
            fallback.solve_layout(window);
            assert_eq!(tree.write_order, fallback.write_order);
            assert_eq!(tree.output.map(|rect| rect.map(bits)), fallback.output.map(|rect| rect.map(bits)));
        }
    }
}

#[test]
fn prepared_stack_rows_are_separate_from_enclosing_grid_and_wrap_metrics() {
    const N: usize = 11;
    let modes = [
        ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 4.0, line_spacing: 0.5 },
        ChildrenLayout::Grid {
            columns: MainAxisCellSize::Count(2), main_axis: Axis::X, spacing_x: 1.25, spacing_y: 0.5, backfill: false,
        },
    ];
    for parent_mode in modes {
        let mut tree = Adapter::<N> {
            root: 0,
            parent: [None, Some(0), Some(0), Some(1), Some(1), Some(1), Some(2), Some(2), Some(2), None, None],
            first: [Some(1), Some(3), Some(6), None, None, None, None, None, None, None, None],
            next: [None, Some(2), None, Some(4), Some(5), None, Some(7), Some(8), None, None, None],
            params: [LayoutParams::DEFAULT; N],
            data: [NodeLayoutData::new(); N],
            layout: LayoutData::new(),
            output: [None; N],
            measurements: 0,
            writes: [0; N],
            write_order: Vec::new(),
            #[cfg(feature = "incremental")]
            retained: false,
        };
        tree.params[0].children_layout = parent_mode;
        for id in 1..=2 {
            tree.params[id].size = Xy::new(Size::Pixels(32.0 + id as f32 * 3.5), Size::FitContent);
            tree.params[id].padding = Xy::new([0.25, 0.75], [0.125, 1.375]);
            tree.params[id].position = Xy::new_symm(Pos::Start);
            tree.params[id].children_layout = ChildrenLayout::Stack {
                axis: Axis::Y, arrange: Arrange::Start, spacing: 0.15,
            };
        }
        for id in 3..=8 {
            tree.params[id].size.y = Size::Pixels(2.5 + id as f32);
            tree.params[id].margin.y[1] = Margin::px(0.125 * id as f32).unwrap();
            tree.params[id].position = Xy::new_symm(Pos::Start);
        }
        let mut fallback = tree.clone();
        fallback.parent[9] = Some(1);
        fallback.parent[10] = Some(2);
        fallback.next[5] = Some(9);
        fallback.next[8] = Some(10);
        fallback.params[9].disabled = true;
        fallback.params[10].disabled = true;
        let bits = |(absolute, local): (XyRect, XyRect)| {
            [absolute.x, absolute.y, local.x, local.y].map(|edges| edges.map(f32::to_bits))
        };
        for width in [105.0, 105.0, 73.0] {
            let window = Xy::new(width, 100.0);
            tree.write_order.clear();
            fallback.write_order.clear();
            tree.solve_layout(window);
            fallback.solve_layout(window);
            assert_eq!(tree.write_order, fallback.write_order);
            assert_eq!(tree.output.map(|rect| rect.map(bits)), fallback.output.map(|rect| rect.map(bits)));
        }
    }
}

#[test]
fn fixed_fraction_ratio_run_preserves_nested_output_and_fallback() {
    const SENTINEL: usize = 9;
    const N: usize = SENTINEL + 1;
    let bits = |rect: XyRect| Xy::new(rect.x.map(f32::to_bits), rect.y.map(f32::to_bits));
    let window = Xy::new(210.25, 175.125);
    for outer in [
        ChildrenLayout::Grid {
            columns: MainAxisCellSize::Count(2), main_axis: Axis::X,
            spacing_x: 0.375, spacing_y: 0.625, backfill: false,
        },
        ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 0.125, line_spacing: 0.5 },
    ] {
        for axis in [Axis::X, Axis::Y] {
            let mut fast = Adapter::<N> {
                root: 0,
                parent: std::array::from_fn(|id| match id {
                    0 | SENTINEL => None, 1 | 2 => Some(0), _ => Some(1),
                }),
                first: std::array::from_fn(|id| match id { 0 => Some(1), 1 => Some(3), _ => None }),
                next: std::array::from_fn(|id| (id == 1 || (3..SENTINEL - 1).contains(&id)).then_some(id + 1)),
                params: [LayoutParams::DEFAULT; N],
                data: [NodeLayoutData::new(); N],
                layout: LayoutData::new(),
                output: [None; N],
                measurements: 0,
                writes: [0; N],
                write_order: Vec::new(),
                #[cfg(feature = "incremental")]
                retained: false,
            };
            fast.params[0].children_layout = outer;
            fast.params[0].padding = Xy::new([1.375, 2.625], [4.75, 2.125]);
            fast.params[1] = LayoutParams {
                size: Xy::new(Size::Pixels(113.25), Size::Pixels(89.125)),
                position: Xy::new_symm(Pos::Start),
                padding: Xy::new([0.375, 0.5], [0.625, -0.125]),
                children_layout: ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: 0.375 },
                ..LayoutParams::DEFAULT
            };
            fast.params[2] = LayoutParams {
                size: Xy::new(Size::Pixels(23.125), Size::Pixels(31.25)),
                position: Xy::new_symm(Pos::Start),
                ..LayoutParams::DEFAULT
            };
            for (offset, (fraction, ratio)) in [
                (0.5, 1.25), (-0.0, -1.5), (0.625, 3.25),
                (-0.25, 2.75), (0.0, 1.5), (0.125, -1.25),
            ].into_iter().enumerate() {
                let size = if axis == Axis::X {
                    Xy::new(Size::AspectRatio(ratio), Size::Frac(fraction))
                } else {
                    Xy::new(Size::Frac(fraction), Size::AspectRatio(ratio))
                };
                fast.params[offset + 3] = LayoutParams {
                    size,
                    position: Xy::new_symm(Pos::Start),
                    margin: if offset % 2 == 0 {
                        Xy::new([Margin::px(0.375).unwrap(), Margin::AUTO], [Margin::ZERO, Margin::px(-0.5).unwrap()])
                    } else { Xy::new_symm([Margin::ZERO; 2]) },
                    ..LayoutParams::DEFAULT
                };
            }
            let mut general = fast.clone();
            // Reject the packed run after its otherwise compatible live prefix.
            general.params[SENTINEL].disabled = true;
            general.parent[SENTINEL] = Some(1);
            general.next[SENTINEL - 1] = Some(SENTINEL);
            for frame in 0..4 {
                for tree in [&mut fast, &mut general] {
                    if frame == 2 {
                        tree.params[6].position[if axis == Axis::X { Axis::Y } else { Axis::X }] = Pos::Center;
                    }
                    if frame == 3 {
                        tree.params[4].min_size[axis] = Some(Size::Pixels(1.0));
                    }
                    tree.write_order.clear();
                    tree.solve_layout(window);
                    assert_eq!(tree.write_order, [0, 1, 3, 4, 5, 6, 7, 8, 2]);
                }
                for id in 0..SENTINEL {
                    let (a, b) = fast.output[id].unwrap();
                    let (c, d) = general.output[id].unwrap();
                    assert_eq!(bits(a), bits(c), "absolute {outer:?} {axis:?} frame {frame} node {id}");
                    assert_eq!(bits(b), bits(d), "local {outer:?} {axis:?} frame {frame} node {id}");
                }
            }
        }
    }
}

#[cfg(feature = "incremental")]
#[test]
fn warm_wrap_rows_keep_preorder_and_exact_edges_after_fallback() {
    const LEAVES: usize = 20;
    const HORIZONTAL: usize = 1;
    const GRID: usize = HORIZONTAL + LEAVES + 1;
    const STACK: usize = GRID + 1;
    const VERTICAL: usize = STACK + LEAVES + 1;
    const N: usize = VERTICAL + LEAVES + 1;
    let mut tree = Adapter::<N> {
        root: 0,
        parent: std::array::from_fn(|id| match id {
            0 => None,
            HORIZONTAL | GRID => Some(0),
            STACK | VERTICAL => Some(GRID),
            id if id < GRID => Some(HORIZONTAL),
            id if id < VERTICAL => Some(STACK),
            _ => Some(VERTICAL),
        }),
        first: std::array::from_fn(|id| match id {
            0 => Some(HORIZONTAL),
            HORIZONTAL | GRID | STACK | VERTICAL => Some(id + 1),
            _ => None,
        }),
        next: std::array::from_fn(|id| match id {
            HORIZONTAL => Some(GRID),
            STACK => Some(VERTICAL),
            0 | GRID | VERTICAL => None,
            id if id + 1 == GRID || id + 1 == VERTICAL || id + 1 == N => None,
            _ => Some(id + 1),
        }),
        params: [LayoutParams::DEFAULT; N],
        data: [NodeLayoutData::new(); N],
        layout: LayoutData::new(),
        output: [None; N],
        measurements: 0,
        writes: [0; N],
        write_order: Vec::new(),
        retained: false,
    };
    tree.params[0].children_layout = ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 1.25 };
    tree.params[GRID].children_layout = ChildrenLayout::Grid {
        columns: MainAxisCellSize::Count(2), main_axis: Axis::X, spacing_x: 0.125, spacing_y: 0.5, backfill: false,
    };
    tree.params[GRID].size = Xy::new(Size::Pixels(40.0), Size::FitContent);
    tree.params[STACK].children_layout = ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 0.25 };
    tree.params[STACK].size = Xy::new(Size::Pixels(10.0), Size::FitContent);
    for child in &mut tree.params[STACK + 1..VERTICAL] {
        child.size = Xy::new(Size::Fill, Size::Pixels(1.625));
        child.position = Xy::new_symm(Pos::Start);
    }
    for (wrap, axis) in [(HORIZONTAL, Axis::X), (VERTICAL, Axis::Y)] {
        tree.params[wrap].children_layout = ChildrenLayout::Wrap { axis, arrange: Arrange::Start, spacing: 0.125, line_spacing: 0.625 };
        tree.params[wrap].size = Xy::new_symm(Size::FitContent);
        tree.params[wrap].size[axis] = Size::Pixels(12.0);
        for (offset, child) in tree.params[wrap + 1..wrap + LEAVES + 1].iter_mut().enumerate() {
            child.size[axis] = Size::Pixels(1.25 + (offset % 4) as f32);
            child.size[if axis == Axis::X { Axis::Y } else { Axis::X }] = if offset % 3 == 1 {
                Size::Fill
            } else {
                Size::Pixels(2.0 + (offset % 5) as f32 / 8.0)
            };
            child.position = Xy::new_symm(Pos::Start);
        }
    }
    let bits = |rect: XyRect| Xy::new(rect.x.map(f32::to_bits), rect.y.map(f32::to_bits));
    for frame in 0..6 {
        let disabled = HORIZONTAL + LEAVES - 1;
        tree.params[disabled].disabled = frame == 2;
        let window = Xy::new(100.0 - 0.25 * frame as f32, 175.25);
        let scale = (frame == 4).then(|| PixelScale::new(1.25).unwrap());
        tree.params[VERTICAL + 1].size.y = if frame == 3 { Size::Pixels(-0.0) } else { Size::Pixels(2.0) };
        let mut fresh = tree.clone();
        fresh.layout = LayoutData::new();
        fresh.data = [NodeLayoutData::new(); N];
        for current in [&mut tree, &mut fresh] {
            current.output = [None; N];
            current.write_order.clear();
            current.layout.set_pixel_scale(scale);
            current.solve_layout(window);
        }
        let expected: Vec<_> = (0..N).filter(|&id| frame != 2 || id != disabled).collect();
        assert_eq!(fresh.write_order, expected);
        assert_eq!(tree.write_order, expected, "frame {frame}");
        assert_eq!(
            tree.output.map(|rect| rect.map(|(absolute, local)| (bits(absolute), bits(local)))),
            fresh.output.map(|rect| rect.map(|(absolute, local)| (bits(absolute), bits(local)))),
            "frame {frame}",
        );
    }
}

#[cfg(feature = "incremental")]
#[test]
fn checked_flow_replay_matches_the_full_adapter_view() {
    #[derive(Clone)]
    struct Measured {
        tree: Adapter,
        height: [f32; 4],
        calls: [u32; 4],
    }
    impl TreeAdapter for Measured {
        type NodeId = usize;
        fn root(&self) -> usize { self.tree.root() }
        fn parent(&self, node: usize) -> Option<usize> { self.tree.parent(node) }
        fn first_child(&self, node: usize) -> Option<usize> { self.tree.first_child(node) }
        fn next_sibling(&self, node: usize) -> Option<usize> { self.tree.next_sibling(node) }
        fn node_layout_params(&self, node: usize) -> &LayoutParams { self.tree.node_layout_params(node) }
        fn node_layout_data(&self, node: usize) -> &NodeLayoutData { self.tree.node_layout_data(node) }
        fn node_layout_data_mut(&mut self, node: usize) -> &mut NodeLayoutData { self.tree.node_layout_data_mut(node) }
        fn layout_data(&mut self) -> &mut LayoutData<usize> { self.tree.layout_data() }
        fn measure_text_height(&mut self, node: usize, width: Option<f32>) -> f32 {
            self.calls[node] += 1;
            self.height[node] + width.unwrap_or(0.0) * 0.125
        }
        fn write_output_rect(&mut self, node: usize, absolute: XyRect, local: XyRect) {
            self.tree.write_output_rect(node, absolute, local);
        }
        fn retains_output_rects(&self) -> bool { true }
    }

    let bits = |r: XyRect| [r.x.map(f32::to_bits), r.y.map(f32::to_bits)];
    let compare_full = |tree: &Measured, window| {
        let mut full = tree.clone();
        full.tree.layout = LayoutData::new();
        full.tree.data = [NodeLayoutData::new(); 4];
        full.tree.output = [None; 4];
        full.tree.write_order.clear();
        full.solve_layout(window);
        assert_eq!(tree.tree.write_order, full.tree.write_order);
        let rectangles = |tree: &Measured| tree.tree.output.map(|r| r.map(|(a, b)| (bits(a), bits(b))));
        assert_eq!(rectangles(tree), rectangles(&full));
    };
    for mode in [
        ChildrenLayout::Block,
        ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 0.75, line_spacing: 1.0 },
    ] {
        let window = Xy::new(41.0, 0.0);
        let mut tree = Measured {
            tree: Adapter {
                parent: [None, Some(0), Some(0), None],
                first: [Some(1), None, None, None],
                next: [None, Some(2), None, None],
                ..Adapter::default()
            },
            height: [0.0, 7.25, 12.5, 4.0],
            calls: [0; 4],
        };
        tree.tree.params[0] = LayoutParams {
            size: Xy::new(Size::Fill, Size::FitContent),
            children_layout: mode,
            ..LayoutParams::DEFAULT
        };
        for leaf in &mut tree.tree.params[1..] {
            leaf.size = Xy::new(Size::Pixels(10.25), Size::FitContent);
            leaf.text = TextContent::Wrapping;
        }
        tree.solve_layout(window);

        tree.calls = [0; 4];
        tree.tree.write_order.clear();
        tree.height[1] = 11.5;
        tree.register_content_change(1);
        assert!(matches!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { .. }), "{mode:?}");
        assert_eq!(tree.calls, [0, 1, 0, 0], "{mode:?}");
        compare_full(&tree, window);

        tree.tree.write_order.clear();
        tree.height[1] = 3.0;
        tree.register_content_change(1);
        tree.register_content_change(1);
        assert!(matches!(tree.solve_layout_incremental_checked(window), IncrementalRelayoutOutcome::Success { .. }), "{mode:?}");
        compare_full(&tree, window);

        let negative_zero = Xy::new(41.0, -0.0);
        tree.tree.write_order.clear();
        tree.height[1] = 8.25;
        tree.register_content_change(1);
        assert!(matches!(tree.solve_layout_incremental_checked(negative_zero), IncrementalRelayoutOutcome::Success { .. }), "{mode:?}");
        compare_full(&tree, negative_zero);

        tree.tree.write_order.clear();
        tree.tree.parent[3] = Some(0);
        tree.tree.next[2] = Some(3);
        tree.register_child_attached(3).unwrap();
        assert!(matches!(tree.solve_layout_incremental_checked(negative_zero), IncrementalRelayoutOutcome::Success { .. }), "{mode:?}");
        compare_full(&tree, negative_zero);
    }

    // A Stack root can contain flowing rows. A resize must remeasure the leaf
    // with a new width, while a fixed-width neighbor can keep its measurement.
    let mut tree = Measured {
        tree: Adapter {
            parent: [None, Some(0), Some(1), Some(1)],
            first: [Some(1), Some(2), None, None],
            next: [None, None, Some(3), None],
            ..Adapter::default()
        },
        height: [0.0, 0.0, 7.25, 12.5],
        calls: [0; 4],
    };
    tree.tree.params[0].children_layout = ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 0.0 };
    tree.tree.params[1] = LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 0.75, line_spacing: 1.0 },
        ..LayoutParams::DEFAULT
    };
    tree.tree.params[2].size = Xy::new(Size::Frac(0.5), Size::FitContent);
    tree.tree.params[3].size = Xy::new(Size::Pixels(14.5), Size::FitContent);
    tree.tree.params[2].text = TextContent::Wrapping;
    tree.tree.params[3].text = TextContent::Wrapping;
    tree.solve_layout(Xy::new(41.0, 120.0));
    for width in [23.5, 75.0, 23.5] {
        let window = Xy::new(width, 120.0);
        tree.calls = [0; 4];
        tree.tree.write_order.clear();
        assert!(matches!(tree.solve_layout_incremental(window), IncrementalRelayoutOutcome::Success { .. }));
        assert_eq!(tree.calls, [0, 0, 1, 0]);
        compare_full(&tree, window);
    }
}

#[cfg(feature = "incremental")]
#[test]
fn flow_replay_publishes_exact_rounded_rectangles_in_document_order() {
    let scale = PixelScale::new(1.25).unwrap();
    let bits = |r: XyRect| [r.x.map(f32::to_bits), r.y.map(f32::to_bits)];
    let modes = [
        ChildrenLayout::Block,
        ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::SpaceAround, spacing: 0.75, line_spacing: 2.125 },
    ];
    for mode in modes {
        for retained in [false, true] {
            let mut tree = Adapter::<7> {
                root: 0, retained,
                parent: [None, Some(0), Some(0), Some(1), Some(1), Some(1), Some(1)],
                first: [Some(1), Some(3), None, None, None, None, None],
                next: [None, Some(2), None, Some(4), Some(5), Some(6), None],
                params: [LayoutParams::DEFAULT; 7], data: [NodeLayoutData::new(); 7],
                layout: LayoutData::new(), output: [None; 7], measurements: 0,
                writes: [0; 7], write_order: Vec::new(),
            };
            tree.params[1] = LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                children_layout: mode,
                position: Xy::new(Pos::Pixels(3.25), Pos::Pixels(5.75)),
                anchor: Xy::new_symm(Anchor::Start),
                padding: Xy::new([0.125; 2], [0.0; 2]),
                children_origin_flipped: Xy::new(true, false),
                ..LayoutParams::DEFAULT
            };
            tree.params[2].size = Xy::new_symm(Size::Pixels(9.25));
            for (id, width, height) in [(3, 13.25, 0.0), (4, 11.5, 7.25), (5, 15.25, 12.5)] {
                tree.params[id].size = Xy::new(Size::Pixels(width), Size::Pixels(height));
                tree.params[id].margin.y = [Margin::px(id as f32 * 0.5).unwrap(), Margin::px(-0.75).unwrap()];
            }
            tree.params[6].size = Xy::new_symm(Size::Pixels(2.75));
            tree.params[6].free_placement = true;
            tree.layout.set_pixel_scale(Some(scale));
            let mut window = Xy::new(42.25, 90.0);
            tree.solve_layout(window);

            for frame in 0..3 {
                let previous = tree.output;
                tree.write_order.clear();
                match frame {
                    0 => {
                        let old = tree.params[4];
                        match mode {
                            ChildrenLayout::Block => tree.params[4].size.y = Size::Pixels(16.5),
                            _ => tree.params[4].size.x = Size::Pixels(16.5),
                        }
                        tree.register_node_change(4, &old);
                    }
                    1 => window.x = 28.75,
                    _ => {
                        tree.first[1] = Some(4);
                        tree.next[4] = Some(3);
                        tree.next[3] = Some(5);
                        tree.register_children_change(1);
                    }
                }
                let outcome = tree.solve_layout_incremental(window);
                assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { .. }), "{mode:?} {frame}: {outcome:?}");
                assert_ne!(tree.output, previous);

                let mut fresh = tree.clone();
                fresh.layout = LayoutData::new();
                fresh.layout.set_pixel_scale(Some(scale));
                fresh.data = [NodeLayoutData::new(); 7];
                fresh.output = [None; 7];
                fresh.write_order.clear();
                fresh.solve_layout(window);
                let expected_order: &[usize] = if frame == 2 && retained { &[1, 4, 3, 5, 6] } else { &fresh.write_order };
                assert_eq!(tree.write_order, expected_order, "{mode:?} {retained} {frame}");
                let rectangles = |tree: &Adapter<7>| tree.output.map(|r| r.map(|(absolute, local)| (bits(absolute), bits(local))));
                assert_eq!(rectangles(&tree), rectangles(&fresh), "{mode:?} {retained} {frame}");
            }
        }
    }
}

#[cfg(feature = "incremental")]
#[test]
fn width_grid_updates_a_fixed_cross_stack_around_ready_intrinsic_leaves() {
    const N: usize = 6;
    let mut params = [LayoutParams::DEFAULT; N];
    params[0].children_layout = ChildrenLayout::Stack {
        axis: Axis::Y, arrange: Arrange::Start, spacing: 2.25,
    };
    params[0].padding.x = [3.5, 1.25];
    params[1].children_layout = ChildrenLayout::Grid {
        main_axis: Axis::X, columns: MainAxisCellSize::Width(20.0),
        spacing_x: 3.25, spacing_y: 4.0, backfill: false,
    };
    params[1].size.y = Size::FitContent;
    params[1].padding.x = [0.5, 1.75];
    params[2].size.y = Size::Pixels(10.0);
    params[2].children_layout = ChildrenLayout::Stack {
        axis: Axis::X, arrange: Arrange::SpaceBetween, spacing: 1.375,
    };
    params[3].size = Xy::new(Size::FitContent, Size::Pixels(3.5));
    params[3].image = Some(Xy::new(6.25, 0.0));
    params[4].size.y = Size::Pixels(8.0);
    params[4].children_layout = ChildrenLayout::Wrap {
        axis: Axis::X, arrange: Arrange::Start, spacing: 2.0, line_spacing: 1.0,
    };
    params[5].size = Xy::new(Size::FitContent, Size::Pixels(4.25));
    params[5].image = Some(Xy::new(4.125, 0.0));
    let mut tree = Adapter::<N> {
        root: 0,
        parent: [None, Some(0), Some(1), Some(2), Some(0), Some(2)],
        first: [Some(1), Some(2), Some(3), None, None, None],
        next: [None, Some(4), None, Some(5), None, None],
        params,
        data: [NodeLayoutData::new(); N],
        layout: LayoutData::new(),
        output: [None; N],
        measurements: 0,
        writes: [0; N],
        write_order: Vec::new(),
        retained: true,
    };
    tree.solve_layout(Xy::new(94.5, 100.0));
    for (width, changed_image) in [
        (88.25, false), (56.0, false), (94.5, true), (88.25, false),
    ] {
        if changed_image {
            let old = tree.params[5];
            tree.params[5].image = Some(Xy::new(2.75, 0.0));
            tree.register_node_change(5, &old);
        }
        let before = tree.output[2].unwrap().0;
        let outcome = tree.solve_layout_incremental_checked(Xy::new(width, 100.0));
        assert!(matches!(outcome, IncrementalRelayoutOutcome::Success { computed: 1.. }), "{outcome:?}");
        assert_ne!(tree.output[2].unwrap().0, before);
    }
}
