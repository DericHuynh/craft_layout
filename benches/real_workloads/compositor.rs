use keru_layout::{
    Anchor, Arrange, Axis, ChildId, ChildrenLayout, Destination, LayoutParams, LayoutTree, NodeId,
    PixelScale, Pos, Size, TextContent, WindowOverflow, Xy,
};

use super::Case;

pub(super) fn cases() -> Vec<Case> {
    vec![tiled_workspace(), floating_workspace()]
}

fn stack(axis: Axis, spacing: f32, padding: f32) -> LayoutParams {
    LayoutParams {
        position: Xy::new_symm(Pos::Start),
        padding: Xy::new_symm([padding, padding]),
        children_layout: ChildrenLayout::Stack {
            axis,
            spacing,
            arrange: Arrange::Start,
        },
        ..LayoutParams::DEFAULT
    }
}

fn add(tree: &mut LayoutTree<String>, parent: &NodeId, params: LayoutParams) -> ChildId {
    tree.add_node(parent, params)
        .expect("valid compositor fixture")
}

fn label(tree: &mut LayoutTree<String>, parent: &NodeId, text: impl Into<String>) {
    let params = LayoutParams {
        size: Xy::new_symm(Size::FitContent),
        text: TextContent::Fixed,
        ..LayoutParams::DEFAULT
    };
    tree.add_node_with_context(parent, params, text.into())
        .expect("valid compositor label");
}

fn panel(tree: &mut LayoutTree<String>, parent: &NodeId) {
    let bar = add(
        tree,
        parent,
        LayoutParams {
            size: Xy::new(Size::Fill, Size::Pixels(34.0)),
            ..stack(Axis::X, 9.0, 7.0)
        },
    );
    for workspace in 1..=6 {
        label(tree, &bar, format!("[{workspace}]"));
    }
    add(tree, &bar, LayoutParams::DEFAULT);
    for status in ["Ethernet", "Battery 84%", "14:25"] {
        label(tree, &bar, status);
    }
}

fn decorate(tree: &mut LayoutTree<String>, window: &NodeId, title: String) {
    let bar = add(
        tree,
        window,
        LayoutParams {
            size: Xy::new(Size::Fill, Size::Pixels(24.0)),
            ..stack(Axis::X, 5.0, 4.0)
        },
    );
    label(tree, &bar, title);
    add(tree, &bar, LayoutParams::DEFAULT);
    for _ in 0..3 {
        add(
            tree,
            &bar,
            LayoutParams {
                size: Xy::new_symm(Size::Pixels(9.0)),
                ..LayoutParams::DEFAULT
            },
        );
    }
    // The client content is a single surface from the compositor's perspective.
    add(tree, window, LayoutParams::DEFAULT);
}

fn set_position(params: &mut LayoutParams, x: f32, y: f32) {
    params.position = Xy::new(Pos::Pixels(x), Pos::Pixels(y));
}

fn tiled_workspace() -> Case {
    const WEIGHTS: [f32; 6] = [1.20, 1.45, 1.25, 0.95, 1.15, 1.0];
    let mut tree = LayoutTree::new();
    tree.set_pixel_scale(Some(
        PixelScale::try_from(1.25).expect("valid fractional scale"),
    ));
    let root = tree.root();
    tree.update_node_params(&root, stack(Axis::Y, 0.0, 0.0))
        .expect("live compositor root");
    panel(&mut tree, &root);

    let workspace = add(&mut tree, &root, stack(Axis::X, 7.5, 6.5));
    let columns: [ChildId; 4] =
        std::array::from_fn(|_| add(&mut tree, &workspace, stack(Axis::Y, 5.5, 0.0)));
    let apps = [
        "Terminal", "Editor", "Browser", "Files", "Preview", "Monitor",
    ];
    let windows: [[ChildId; 6]; 4] = std::array::from_fn(|column| {
        std::array::from_fn(|row| {
            let window = add(&mut tree, &columns[column], stack(Axis::Y, 0.0, 0.0));
            decorate(&mut tree, &window, format!("{} {}", apps[row], column + 1));
            window
        })
    });

    let dock = add(
        &mut tree,
        &root,
        LayoutParams {
            size: Xy::new(Size::Fill, Size::Pixels(34.0)),
            children_layout: ChildrenLayout::Stack {
                axis: Axis::X,
                spacing: 7.0,
                arrange: Arrange::Center,
            },
            ..LayoutParams::DEFAULT
        },
    );
    for _ in 0..8 {
        add(
            &mut tree,
            &dock,
            LayoutParams {
                size: Xy::new_symm(Size::Pixels(24.0)),
                ..LayoutParams::DEFAULT
            },
        );
    }

    let viewport = Xy::new(1600.5, 900.25);
    let split = windows[0][0].clone();
    Case {
        name: "compositor/tiled_split_resize",
        period: WEIGHTS.len(),
        tree,
        viewport,
        edit: Box::new(move |tree, frame| {
            let phase = frame % WEIGHTS.len();
            let mut params = *tree.params(&split).expect("live tiling split");
            params.fill_weight = WEIGHTS[phase];
            tree.update_node_params(&split, params)
                .expect("resize tiling split");
            if phase < 3 {
                Xy::new(1440.25, 900.25)
            } else {
                viewport
            }
        }),
    }
}

fn floating_workspace() -> Case {
    const DRAG: [(f32, f32); 8] = [
        (464.25, 229.5),
        (575.5, 280.25),
        (737.25, 352.75),
        (1035.5, 529.25),
        (1052.75, 605.5),
        (897.25, 474.25),
        (644.75, 321.5),
        (436.25, 201.5),
    ];
    let mut tree = LayoutTree::new();
    tree.set_pixel_scale(Some(
        PixelScale::try_from(1.5).expect("valid fractional scale"),
    ));
    let root = tree.root();
    let surface_layer = add(&mut tree, &root, LayoutParams::DEFAULT);
    let windows: [ChildId; 18] = std::array::from_fn(|index| {
        let mut params = LayoutParams {
            size: Xy::new(
                Size::Pixels(420.0 + (index % 3) as f32 * 36.25),
                Size::Pixels(280.0 + (index % 4) as f32 * 18.5),
            ),
            anchor: Xy::new_symm(Anchor::Start),
            window_overflow: Xy::new_symm(WindowOverflow::Clamp),
            ..stack(Axis::Y, 0.0, 0.0)
        };
        set_position(
            &mut params,
            90.25 + (index * 173 % 850) as f32,
            55.5 + (index * 73 % 475) as f32,
        );
        let window = add(&mut tree, &surface_layer, params);
        decorate(&mut tree, &window, format!("Client {}", index + 1));
        window
    });

    let overlay = add(&mut tree, &root, LayoutParams::DEFAULT);
    panel(&mut tree, &overlay);
    let popup = add(
        &mut tree,
        &overlay,
        LayoutParams {
            size: Xy::new(Size::Pixels(210.0), Size::Pixels(105.0)),
            anchor: Xy::new_symm(Anchor::Start),
            window_overflow: Xy::new_symm(WindowOverflow::Flip),
            disabled: true,
            ..stack(Axis::Y, 5.0, 8.0)
        },
    );
    for item in ["Move to workspace", "Always on top", "Close window"] {
        label(&mut tree, &popup, item);
    }

    let viewport = Xy::new(1440.0, 900.0);
    let dragged = windows[2].clone();
    let following = windows[3].clone();
    Case {
        name: "compositor/floating_drag_and_raise",
        period: DRAG.len(),
        tree,
        viewport,
        edit: Box::new(move |tree, frame| {
            let phase = frame % DRAG.len();
            let (x, y) = DRAG[phase];
            let mut params = *tree.params(&dragged).expect("live dragged surface");
            set_position(&mut params, x, y);
            tree.update_node_params(&dragged, params)
                .expect("move floating surface");

            if phase == 0 {
                tree.move_node(&dragged, Destination::LastChildOf(&surface_layer))
                    .expect("raise surface");
            } else if phase == 4 {
                tree.move_node(&dragged, Destination::Before(&following))
                    .expect("restore surface order");
            }

            let show_popup = (1..6).contains(&phase);
            let mut params = *tree.params(&popup).expect("live compositor menu");
            if show_popup || !params.disabled {
                params.disabled = !show_popup;
                if show_popup {
                    set_position(&mut params, x + 205.25, y + 194.5);
                }
                tree.update_node_params(&popup, params)
                    .expect("update compositor menu");
            }
            viewport
        }),
    }
}
