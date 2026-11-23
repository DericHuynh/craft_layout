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
    tree.params[2].disabled = true;
    tree.params[6].grid_span = Xy::new(3, 2);
    tree.params[12].free_placement = true;
    tree.params[17].children_layout = ChildrenLayout::Stack { axis: Axis::Y, arrange: Arrange::Start, spacing: 0.0 };
    tree.params[17].padding.x[0] = 0.225;
    let window = Xy::new(120.0, 10.0);
    let scale = 1.25_f64;
    let expected_order: Vec<_> = (0..BRANCH_CHILD).filter(|&node| node != 2)
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
        assert!(rounded.output[2].is_none());
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
