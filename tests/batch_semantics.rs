#![cfg(feature = "batch-pilot")]
//! Checks that the Batch solver produces the geometry a layout author would
//! expect, using hand-computed rectangles rather than comparing against the
//! default solver. Every scenario runs the Batch scheduler itself: the first
//! `solve_layout_batch*` call is served by the default solver, so `solve`
//! invalidates and solves again, and asserts that the Batch graph did the work.

use keru_layout::{
    measure_monospace_text, Anchor, Arrange, Axis, BatchLayoutStats, ChildId, ChildrenLayout,
    Destination, LayoutParams, LayoutTree, MainAxisCellSize, Margin, NodeId, Pos, Size,
    TextContent, Xy,
};

type Tree = LayoutTree<&'static str>;

const WINDOW: Xy<f32> = Xy { x: 800.0, y: 600.0 };
const CHAR: f32 = 7.2;
const LINE: f32 = 14.4;

/// Solves with the Batch API until the Batch graph has computed the frame.
fn solve(tree: &mut Tree, window: Xy<f32>) -> BatchLayoutStats {
    let mut stats = tree.solve_layout_batch_with_measure(window, measure_monospace_text).unwrap();
    if stats == BatchLayoutStats::default() {
        tree.invalidate();
        stats = tree.solve_layout_batch_with_measure(window, measure_monospace_text).unwrap();
        assert!(stats.rebuilt_graph && stats.computed > 0, "Batch graph did not run: {stats:?}");
    }
    assert!(tree.warnings().is_empty(), "unexpected warnings: {:?}", tree.warnings());
    stats
}

/// Solves an edited frame. It must stay on the Batch path.
fn resolve(tree: &mut Tree, window: Xy<f32>) -> BatchLayoutStats {
    let stats = tree.solve_layout_batch_with_measure(window, measure_monospace_text).unwrap();
    assert!(tree.warnings().is_empty(), "unexpected warnings: {:?}", tree.warnings());
    stats
}

/// `[x0, y0, x1, y1]` in absolute coordinates.
fn rect(tree: &Tree, node: &NodeId) -> [f32; 4] {
    let r = tree.layout(node).unwrap();
    [r.x[0], r.y[0], r.x[1], r.y[1]]
}

#[track_caller]
fn assert_rect(tree: &Tree, node: &NodeId, expected: [f32; 4]) {
    let actual = rect(tree, node);
    let close = actual.iter().zip(expected).all(|(a, e)| (a - e).abs() < 1e-3);
    assert!(close, "expected {expected:?}, got {actual:?}");
}

fn px(w: f32, h: f32) -> LayoutParams {
    LayoutParams { size: Xy::new(Size::Pixels(w), Size::Pixels(h)), ..LayoutParams::DEFAULT }
}

/// Pins a root child to the window's top-left corner.
fn top_left(params: LayoutParams) -> LayoutParams {
    LayoutParams {
        position: Xy::new(Pos::Start, Pos::Start),
        anchor: Xy::new(Anchor::Start, Anchor::Start),
        ..params
    }
}

fn stack(axis: Axis, arrange: Arrange, spacing: f32, size: Xy<Size>) -> LayoutParams {
    LayoutParams {
        size,
        children_layout: ChildrenLayout::Stack { axis, arrange, spacing },
        ..LayoutParams::DEFAULT
    }
}

fn pad(params: LayoutParams, all: f32) -> LayoutParams {
    LayoutParams { padding: Xy::new([all; 2], [all; 2]), ..params }
}

fn child(tree: &mut Tree, parent: &NodeId, params: LayoutParams) -> ChildId {
    tree.add_node(parent, params).unwrap()
}

#[test]
fn root_fills_window_and_default_child_is_centered() {
    let mut tree = Tree::new();
    let root = tree.root();
    let boxed = child(&mut tree, &root, px(200.0, 100.0));
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &root, [0.0, 0.0, 800.0, 600.0]);
    // Default position and anchor are Center.
    assert_rect(&tree, &boxed, [300.0, 250.0, 500.0, 350.0]);
}

#[test]
fn free_placement_positions_and_anchors() {
    let mut tree = Tree::new();
    let root = tree.root();
    let at = |x, y, ax, ay| LayoutParams {
        position: Xy::new(x, y),
        anchor: Xy::new(ax, ay),
        ..px(100.0, 50.0)
    };
    let tl = child(&mut tree, &root, at(Pos::Start, Pos::Start, Anchor::Start, Anchor::Start));
    let br = child(&mut tree, &root, at(Pos::End, Pos::End, Anchor::End, Anchor::End));
    let pixel = child(&mut tree, &root, at(Pos::Pixels(40.0), Pos::Pixels(30.0), Anchor::Start, Anchor::Start));
    let frac = child(&mut tree, &root, at(Pos::Frac(0.25), Pos::Frac(0.5), Anchor::Start, Anchor::Center));
    let offset = child(&mut tree, &root, at(
        Pos::Offset { fraction: 1.0, pixels: -12.0 }, Pos::Offset { fraction: 0.5, pixels: 8.0 },
        Anchor::End, Anchor::Center,
    ));
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &tl, [0.0, 0.0, 100.0, 50.0]);
    assert_rect(&tree, &br, [700.0, 550.0, 800.0, 600.0]);
    assert_rect(&tree, &pixel, [40.0, 30.0, 140.0, 80.0]);
    assert_rect(&tree, &frac, [200.0, 275.0, 300.0, 325.0]);
    assert_rect(&tree, &offset, [688.0, 283.0, 788.0, 333.0]);
}

#[test]
fn row_divides_free_space_by_fill_weight() {
    let mut tree = Tree::new();
    let root = tree.root();
    let row = child(
        &mut tree,
        &root,
        top_left(pad(stack(Axis::X, Arrange::Start, 10.0, Xy::new(Size::Pixels(500.0), Size::Pixels(100.0))), 20.0)),
    );
    let row_id: NodeId = (*row).clone();
    let a = child(&mut tree, &row_id, LayoutParams { size: Xy::new(Size::Pixels(50.0), Size::Fill), ..LayoutParams::DEFAULT });
    let b = child(&mut tree, &row_id, LayoutParams::DEFAULT);
    let c = child(&mut tree, &row_id, LayoutParams { fill_weight: 3.0, ..LayoutParams::DEFAULT });
    let d = child(&mut tree, &row_id, LayoutParams { size: Xy::new(Size::Pixels(30.0), Size::Fill), ..LayoutParams::DEFAULT });
    solve(&mut tree, WINDOW);
    // Inner width 460, three gaps of 10, fixed 80: 350 free, split 1:3.
    assert_rect(&tree, &row, [0.0, 0.0, 500.0, 100.0]);
    assert_rect(&tree, &a, [20.0, 20.0, 70.0, 80.0]);
    assert_rect(&tree, &b, [80.0, 20.0, 167.5, 80.0]);
    assert_rect(&tree, &c, [177.5, 20.0, 440.0, 80.0]);
    assert_rect(&tree, &d, [450.0, 20.0, 480.0, 80.0]);
}

#[test]
fn arrange_modes_distribute_free_space() {
    // A 300 px row with three 50 px children leaves 150 px free.
    let cases = [
        (Arrange::Start, [0.0, 50.0, 100.0]),
        (Arrange::End, [150.0, 200.0, 250.0]),
        (Arrange::Center, [75.0, 125.0, 175.0]),
        (Arrange::SpaceBetween, [0.0, 125.0, 250.0]),
        (Arrange::SpaceAround, [25.0, 125.0, 225.0]),
        (Arrange::SpaceEvenly, [37.5, 125.0, 212.5]),
    ];
    for (arrange, starts) in cases {
        let mut tree = Tree::new();
        let root = tree.root();
        let row = child(&mut tree, &root, top_left(stack(Axis::X, arrange, 0.0, Xy::new(Size::Pixels(300.0), Size::Pixels(40.0)))));
        let row_id: NodeId = (*row).clone();
        let kids: Vec<_> = (0..3).map(|_| child(&mut tree, &row_id, px(50.0, 40.0))).collect();
        solve(&mut tree, WINDOW);
        for (kid, start) in kids.iter().zip(starts) {
            let r = rect(&tree, kid);
            assert!((r[0] - start).abs() < 1e-3, "{arrange:?}: expected x {start}, got {r:?}");
        }
    }
}

#[test]
fn fit_content_column_wraps_children_and_centers_cross_axis() {
    let mut tree = Tree::new();
    let root = tree.root();
    let col = child(
        &mut tree,
        &root,
        top_left(pad(stack(Axis::Y, Arrange::Start, 5.0, Xy::new(Size::FitContent, Size::FitContent)), 10.0)),
    );
    let col_id: NodeId = (*col).clone();
    let wide = child(&mut tree, &col_id, px(100.0, 20.0));
    let narrow = child(&mut tree, &col_id, px(60.0, 30.0));
    let left = child(&mut tree, &col_id, LayoutParams { position: Xy::new(Pos::Start, Pos::Center), anchor: Xy::new(Anchor::Start, Anchor::Center), ..px(40.0, 10.0) });
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &col, [0.0, 0.0, 120.0, 90.0]);
    assert_rect(&tree, &wide, [10.0, 10.0, 110.0, 30.0]);
    assert_rect(&tree, &narrow, [30.0, 35.0, 90.0, 65.0]);
    assert_rect(&tree, &left, [10.0, 70.0, 50.0, 80.0]);
}

#[test]
fn frac_is_a_fraction_of_the_parent_content_box() {
    let mut tree = Tree::new();
    let root = tree.root();
    let panel = child(&mut tree, &root, top_left(pad(px(400.0, 200.0), 20.0)));
    let panel_id: NodeId = (*panel).clone();
    let quarter = child(&mut tree, &panel_id, LayoutParams {
        size: Xy::new(Size::Frac(0.25), Size::Frac(0.5)),
        position: Xy::new(Pos::Start, Pos::Start),
        anchor: Xy::new(Anchor::Start, Anchor::Start),
        ..LayoutParams::DEFAULT
    });
    solve(&mut tree, WINDOW);
    // Fractions apply to the parent's content box (360x160), placed inside the padding.
    assert_rect(&tree, &quarter, [20.0, 20.0, 110.0, 100.0]);
}

#[test]
fn max_size_caps_fill_and_redistributes() {
    let mut tree = Tree::new();
    let root = tree.root();
    let row = child(&mut tree, &root, top_left(stack(Axis::X, Arrange::Start, 0.0, Xy::new(Size::Pixels(400.0), Size::Pixels(40.0)))));
    let row_id: NodeId = (*row).clone();
    let capped = child(&mut tree, &row_id, LayoutParams { max_size: Xy::new(Some(Size::Pixels(100.0)), None), ..LayoutParams::DEFAULT });
    let rest = child(&mut tree, &row_id, LayoutParams::DEFAULT);
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &capped, [0.0, 0.0, 100.0, 40.0]);
    assert_rect(&tree, &rest, [100.0, 0.0, 400.0, 40.0]);
}

#[test]
fn min_size_floors_fill() {
    let mut tree = Tree::new();
    let root = tree.root();
    let row = child(&mut tree, &root, top_left(stack(Axis::X, Arrange::Start, 0.0, Xy::new(Size::Pixels(400.0), Size::Pixels(40.0)))));
    let row_id: NodeId = (*row).clone();
    let floored = child(&mut tree, &row_id, LayoutParams { min_size: Xy::new(Some(Size::Pixels(300.0)), None), ..LayoutParams::DEFAULT });
    let rest = child(&mut tree, &row_id, LayoutParams::DEFAULT);
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &floored, [0.0, 0.0, 300.0, 40.0]);
    assert_rect(&tree, &rest, [300.0, 0.0, 400.0, 40.0]);
}

#[test]
fn aspect_ratio_follows_other_axis() {
    let mut tree = Tree::new();
    let root = tree.root();
    let row = child(&mut tree, &root, top_left(stack(Axis::X, Arrange::Start, 0.0, Xy::new(Size::FitContent, Size::Pixels(120.0)))));
    let row_id: NodeId = (*row).clone();
    let thumb = child(&mut tree, &row_id, LayoutParams { size: Xy::new(Size::AspectRatio(1.5), Size::Fill), ..LayoutParams::DEFAULT });
    solve(&mut tree, WINDOW);
    let r = rect(&tree, &thumb);
    assert_eq!(r[3] - r[1], 120.0);
    // Width / height = 1.5 is the conventional reading.
    assert!((r[2] - r[0] - 180.0).abs() < 1e-3, "aspect width {}", r[2] - r[0]);
    assert_rect(&tree, &row, [0.0, 0.0, 180.0, 120.0]);
}

#[test]
fn wrapping_text_reflows_with_width() {
    // 10 words of 4 letters: "word word ..." is 49 chars on one line.
    const TEXT: &str = "word word word word word word word word word word";
    let mut tree = Tree::new();
    let root = tree.root();
    let col = child(&mut tree, &root, top_left(stack(Axis::Y, Arrange::Start, 0.0, Xy::new(Size::Pixels(200.0), Size::FitContent))));
    let col_id: NodeId = (*col).clone();
    let para = tree.add_node_with_context(&col_id, LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        text: TextContent::Wrapping,
        ..LayoutParams::DEFAULT
    }, TEXT).unwrap();
    solve(&mut tree, WINDOW);
    // 200 / 7.2 = 27 chars per line: 5 words (24 chars) per line, 2 lines.
    assert_rect(&tree, &para, [0.0, 0.0, 200.0, 2.0 * LINE]);
    assert_rect(&tree, &col, [0.0, 0.0, 200.0, 2.0 * LINE]);

    // Narrow the column: 100 / 7.2 = 13 chars, 2 words (9 chars) per line, 5 lines.
    tree.update_node_params(&col_id, top_left(stack(Axis::Y, Arrange::Start, 0.0, Xy::new(Size::Pixels(100.0), Size::FitContent)))).unwrap();
    resolve(&mut tree, WINDOW);
    assert_rect(&tree, &para, [0.0, 0.0, 100.0, 5.0 * LINE]);
    assert_rect(&tree, &col, [0.0, 0.0, 100.0, 5.0 * LINE]);
}

#[test]
fn fixed_text_sizes_to_its_content() {
    let mut tree = Tree::new();
    let root = tree.root();
    let label = tree.add_node_with_context(&root, top_left(LayoutParams {
        size: Xy::new(Size::FitContent, Size::FitContent),
        text: TextContent::Fixed,
        padding: Xy::new([4.0; 2], [2.0; 2]),
        ..LayoutParams::DEFAULT
    }), "Save file").unwrap();
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &label, [0.0, 0.0, 9.0 * CHAR + 8.0, LINE + 4.0]);
}

#[test]
fn wrap_breaks_lines_on_overflow() {
    let mut tree = Tree::new();
    let root = tree.root();
    let wrap = child(&mut tree, &root, top_left(LayoutParams {
        size: Xy::new(Size::Pixels(300.0), Size::FitContent),
        children_layout: ChildrenLayout::Wrap { axis: Axis::X, arrange: Arrange::Start, spacing: 10.0, line_spacing: 5.0 },
        ..LayoutParams::DEFAULT
    }));
    let wrap_id: NodeId = (*wrap).clone();
    let kids: Vec<_> = (0..7).map(|_| child(&mut tree, &wrap_id, px(80.0, 20.0))).collect();
    solve(&mut tree, WINDOW);
    // 3 per line (260 px), lines at y = 0, 25, 50.
    for (i, kid) in kids.iter().enumerate() {
        let (line, col) = ((i / 3) as f32, (i % 3) as f32);
        assert_rect(&tree, kid, [col * 90.0, line * 25.0, col * 90.0 + 80.0, line * 25.0 + 20.0]);
    }
    assert_rect(&tree, &wrap, [0.0, 0.0, 300.0, 70.0]);
}

#[test]
fn grid_count_divides_width_into_equal_cells() {
    let mut tree = Tree::new();
    let root = tree.root();
    let grid = child(&mut tree, &root, top_left(LayoutParams {
        size: Xy::new(Size::Pixels(320.0), Size::FitContent),
        children_layout: ChildrenLayout::Grid {
            columns: MainAxisCellSize::Count(3),
            spacing_x: 10.0,
            spacing_y: 10.0,
            main_axis: Axis::X,
            backfill: false,
        },
        ..LayoutParams::DEFAULT
    }));
    let grid_id: NodeId = (*grid).clone();
    let cells: Vec<_> = (0..5).map(|_| child(&mut tree, &grid_id, LayoutParams { size: Xy::new(Size::Fill, Size::Pixels(40.0)), ..LayoutParams::DEFAULT })).collect();
    solve(&mut tree, WINDOW);
    for (i, cell) in cells.iter().enumerate() {
        let (row, col) = ((i / 3) as f32, (i % 3) as f32);
        assert_rect(&tree, cell, [col * 110.0, row * 50.0, col * 110.0 + 100.0, row * 50.0 + 40.0]);
    }
    assert_rect(&tree, &grid, [0.0, 0.0, 320.0, 90.0]);
}

#[test]
fn block_collapses_vertical_margins_and_centers_with_auto() {
    let m = |v: f32| Margin::px(v).unwrap();
    let mut tree = Tree::new();
    let root = tree.root();
    let page = child(&mut tree, &root, top_left(LayoutParams {
        size: Xy::new(Size::Pixels(400.0), Size::FitContent),
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    }));
    let page_id: NodeId = (*page).clone();
    let first = child(&mut tree, &page_id, LayoutParams {
        size: Xy::new(Size::Auto, Size::Pixels(50.0)),
        margin: Xy::new([Margin::ZERO; 2], [Margin::ZERO, m(20.0)]),
        ..LayoutParams::DEFAULT
    });
    let second = child(&mut tree, &page_id, LayoutParams {
        size: Xy::new(Size::Pixels(200.0), Size::Pixels(50.0)),
        margin: Xy::new([Margin::AUTO; 2], [m(30.0), Margin::ZERO]),
        ..LayoutParams::DEFAULT
    });
    solve(&mut tree, WINDOW);
    // Auto width fills the containing block; 20 and 30 collapse to 30.
    assert_rect(&tree, &first, [0.0, 0.0, 400.0, 50.0]);
    assert_rect(&tree, &second, [100.0, 80.0, 300.0, 130.0]);
    assert_rect(&tree, &page, [0.0, 0.0, 400.0, 130.0]);
}

#[test]
fn edits_update_geometry_on_the_batch_path() {
    let mut tree = Tree::new();
    let root = tree.root();
    // A full-window app shell: header, body row (sidebar + content), footer.
    let shell = child(&mut tree, &root, stack(Axis::Y, Arrange::Start, 0.0, Xy::new(Size::Fill, Size::Fill)));
    let shell_id: NodeId = (*shell).clone();
    let header = child(&mut tree, &shell_id, LayoutParams { size: Xy::new(Size::Fill, Size::Pixels(40.0)), ..LayoutParams::DEFAULT });
    let body = child(&mut tree, &shell_id, stack(Axis::X, Arrange::Start, 0.0, Xy::new(Size::Fill, Size::Fill)));
    let footer = child(&mut tree, &shell_id, LayoutParams { size: Xy::new(Size::Fill, Size::Pixels(20.0)), ..LayoutParams::DEFAULT });
    let body_id: NodeId = (*body).clone();
    let sidebar = child(&mut tree, &body_id, LayoutParams { size: Xy::new(Size::Pixels(200.0), Size::Fill), ..LayoutParams::DEFAULT });
    let content = child(&mut tree, &body_id, LayoutParams::DEFAULT);
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &header, [0.0, 0.0, 800.0, 40.0]);
    assert_rect(&tree, &sidebar, [0.0, 40.0, 200.0, 580.0]);
    assert_rect(&tree, &content, [200.0, 40.0, 800.0, 580.0]);
    assert_rect(&tree, &footer, [0.0, 580.0, 800.0, 600.0]);

    // Resize the window.
    resolve(&mut tree, Xy::new(1000.0, 500.0));
    assert_rect(&tree, &content, [200.0, 40.0, 1000.0, 480.0]);
    assert_rect(&tree, &footer, [0.0, 480.0, 1000.0, 500.0]);

    // Widen the sidebar.
    let sidebar_id: NodeId = (*sidebar).clone();
    tree.update_node_params(&sidebar_id, LayoutParams { size: Xy::new(Size::Pixels(300.0), Size::Fill), ..LayoutParams::DEFAULT }).unwrap();
    resolve(&mut tree, Xy::new(1000.0, 500.0));
    assert_rect(&tree, &sidebar, [0.0, 40.0, 300.0, 480.0]);
    assert_rect(&tree, &content, [300.0, 40.0, 1000.0, 480.0]);

    // Move the sidebar to the right of the content.
    tree.move_node(&sidebar, Destination::LastChildOf(&body_id)).unwrap();
    resolve(&mut tree, Xy::new(1000.0, 500.0));
    assert_rect(&tree, &content, [0.0, 40.0, 700.0, 480.0]);
    assert_rect(&tree, &sidebar, [700.0, 40.0, 1000.0, 480.0]);

    // Hide the sidebar: content takes the whole row.
    tree.update_node_params(&sidebar_id, LayoutParams { size: Xy::new(Size::Pixels(300.0), Size::Fill), disabled: true, ..LayoutParams::DEFAULT }).unwrap();
    resolve(&mut tree, Xy::new(1000.0, 500.0));
    assert_rect(&tree, &content, [0.0, 40.0, 1000.0, 480.0]);

    // Show it again.
    tree.update_node_params(&sidebar_id, LayoutParams { size: Xy::new(Size::Pixels(300.0), Size::Fill), ..LayoutParams::DEFAULT }).unwrap();
    resolve(&mut tree, Xy::new(1000.0, 500.0));
    assert_rect(&tree, &content, [0.0, 40.0, 700.0, 480.0]);
    assert_rect(&tree, &sidebar, [700.0, 40.0, 1000.0, 480.0]);

    // Remove the footer: the body grows down.
    tree.remove(&footer).unwrap();
    resolve(&mut tree, Xy::new(1000.0, 500.0));
    assert_rect(&tree, &content, [0.0, 40.0, 700.0, 500.0]);

    // Insert a toolbar between the header and the body.
    let toolbar = tree.add_node(&shell_id, LayoutParams { size: Xy::new(Size::Fill, Size::Pixels(30.0)), ..LayoutParams::DEFAULT }).unwrap();
    tree.move_node(&toolbar, Destination::Before(&body)).unwrap();
    resolve(&mut tree, Xy::new(1000.0, 500.0));
    assert_rect(&tree, &toolbar, [0.0, 40.0, 1000.0, 70.0]);
    assert_rect(&tree, &content, [0.0, 70.0, 700.0, 500.0]);
}

#[test]
fn text_edit_grows_fit_content_parents() {
    let mut tree = Tree::new();
    let root = tree.root();
    let card = child(&mut tree, &root, top_left(pad(stack(Axis::Y, Arrange::Start, 0.0, Xy::new(Size::Pixels(160.0), Size::FitContent)), 8.0)));
    let card_id: NodeId = (*card).clone();
    let body = tree.add_node_with_context(&card_id, LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        text: TextContent::Wrapping,
        ..LayoutParams::DEFAULT
    }, "short").unwrap();
    let below = child(&mut tree, &root, LayoutParams {
        position: Xy::new(Pos::Start, Pos::Start),
        anchor: Xy::new(Anchor::Start, Anchor::Start),
        ..px(10.0, 10.0)
    });
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &card, [0.0, 0.0, 160.0, LINE + 16.0]);
    assert_rect(&tree, &below, [0.0, 0.0, 10.0, 10.0]);

    // 144 / 7.2 = 20 chars per line; "aaaa " x 8 wraps into 4 words per line, 2 lines.
    let body_id: NodeId = (*body).clone();
    tree.update_node_context(&body_id, Some("aaaa aaaa aaaa aaaa aaaa aaaa aaaa aaaa")).unwrap();
    resolve(&mut tree, WINDOW);
    assert_rect(&tree, &body, [8.0, 8.0, 152.0, 8.0 + 2.0 * LINE]);
    assert_rect(&tree, &card, [0.0, 0.0, 160.0, 2.0 * LINE + 16.0]);
}

#[test]
fn hidden_child_leaves_no_extra_gap() {
    let mut tree = Tree::new();
    let root = tree.root();
    let row = child(&mut tree, &root, top_left(stack(Axis::X, Arrange::Start, 10.0, Xy::new(Size::FitContent, Size::Pixels(20.0)))));
    let row_id: NodeId = (*row).clone();
    let a = child(&mut tree, &row_id, px(50.0, 20.0));
    let b = child(&mut tree, &row_id, px(50.0, 20.0));
    let c = child(&mut tree, &row_id, px(50.0, 20.0));
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &row, [0.0, 0.0, 170.0, 20.0]);
    assert_rect(&tree, &c, [120.0, 0.0, 170.0, 20.0]);

    tree.update_node_params(&b, LayoutParams { disabled: true, ..px(50.0, 20.0) }).unwrap();
    resolve(&mut tree, WINDOW);
    assert_rect(&tree, &a, [0.0, 0.0, 50.0, 20.0]);
    assert_rect(&tree, &c, [60.0, 0.0, 110.0, 20.0]);
    assert_rect(&tree, &row, [0.0, 0.0, 110.0, 20.0]);
}

#[test]
fn fill_never_goes_negative_when_fixed_children_overflow() {
    let mut tree = Tree::new();
    let root = tree.root();
    let row = child(&mut tree, &root, top_left(stack(Axis::X, Arrange::Start, 0.0, Xy::new(Size::Pixels(400.0), Size::Pixels(20.0)))));
    let row_id: NodeId = (*row).clone();
    let a = child(&mut tree, &row_id, px(300.0, 20.0));
    let fill = child(&mut tree, &row_id, LayoutParams::DEFAULT);
    let b = child(&mut tree, &row_id, px(300.0, 20.0));
    solve(&mut tree, WINDOW);
    // Fill collapses to zero and fixed children keep their size, overflowing the row.
    assert_rect(&tree, &a, [0.0, 0.0, 300.0, 20.0]);
    assert_rect(&tree, &fill, [300.0, 0.0, 300.0, 20.0]);
    assert_rect(&tree, &b, [300.0, 0.0, 600.0, 20.0]);
}

#[test]
fn fill_in_fit_content_parent_takes_sibling_extent() {
    // A FitContent column whose width comes from its widest fixed child:
    // a Fill-width divider should stretch to match, not collapse.
    let mut tree = Tree::new();
    let root = tree.root();
    let col = child(&mut tree, &root, top_left(stack(Axis::Y, Arrange::Start, 0.0, Xy::new(Size::FitContent, Size::FitContent))));
    let col_id: NodeId = (*col).clone();
    child(&mut tree, &col_id, px(120.0, 20.0));
    let divider = child(&mut tree, &col_id, LayoutParams { size: Xy::new(Size::Fill, Size::Pixels(1.0)), ..LayoutParams::DEFAULT });
    child(&mut tree, &col_id, px(80.0, 20.0));
    solve(&mut tree, WINDOW);
    assert_rect(&tree, &col, [0.0, 0.0, 120.0, 41.0]);
    assert_rect(&tree, &divider, [0.0, 20.0, 120.0, 21.0]);
}

/// Builds a wrapping card in a Fill column: resizing the window changes the
/// text's wrap width without touching the card's own parameters.
fn reflow_tree() -> (Tree, ChildId) {
    let mut tree = Tree::new();
    let root = tree.root();
    let col = child(&mut tree, &root, top_left(stack(Axis::Y, Arrange::Start, 0.0, Xy::new(Size::Fill, Size::FitContent))));
    let col_id: NodeId = (*col).clone();
    let para = tree.add_node_with_context(&col_id, LayoutParams {
        size: Xy::new(Size::Fill, Size::FitContent),
        text: TextContent::Wrapping,
        ..LayoutParams::DEFAULT
    }, "word word word word word word word word word word").unwrap();
    (tree, para)
}

fn full_svg(tree: &Tree, window: Xy<f32>) -> String {
    let mut full = tree.clone();
    full.invalidate();
    full.solve_layout_with_measure(window, measure_monospace_text);
    full.to_svg_with_text()
}

#[test]
fn svg_after_batch_resize_uses_the_new_window_and_wrap_width() {
    let (mut tree, para) = reflow_tree();
    solve(&mut tree, Xy::new(400.0, 300.0));
    let narrow = Xy::new(100.0, 200.0);
    let stats = resolve(&mut tree, narrow);
    assert!(stats.computed > 0, "resize stayed off the Batch path: {stats:?}");
    // 100 / 7.2 = 13 chars per line: 5 lines.
    assert_rect(&tree, &para, [0.0, 0.0, 100.0, 5.0 * LINE]);
    let svg = tree.to_svg_with_text();
    assert!(svg.contains("width=\"100\" height=\"200\""), "stale SVG canvas");
    assert_eq!(svg, full_svg(&tree, narrow));
}

#[test]
fn clone_of_batch_tree_draws_the_batch_layout() {
    let (mut tree, _) = reflow_tree();
    solve(&mut tree, Xy::new(400.0, 300.0));
    let narrow = Xy::new(100.0, 200.0);
    resolve(&mut tree, narrow);
    let cloned = tree.clone();
    assert_eq!(cloned.to_svg_with_text(), tree.to_svg_with_text());
    assert_eq!(cloned.to_svg_with_text(), full_svg(&tree, narrow));
}

#[test]
fn default_solver_after_batch_frames_matches_a_full_solve() {
    let (mut tree, para) = reflow_tree();
    solve(&mut tree, Xy::new(400.0, 300.0));
    resolve(&mut tree, Xy::new(100.0, 200.0));
    // Return to the original window with the default solver.
    tree.solve_layout_with_measure(Xy::new(400.0, 300.0), measure_monospace_text);
    // 400 / 7.2 = 55 chars: the 49-char text fits on one line.
    assert_rect(&tree, &para, [0.0, 0.0, 400.0, LINE]);
    assert_eq!(tree.to_svg_with_text(), full_svg(&tree, Xy::new(400.0, 300.0)));
}
