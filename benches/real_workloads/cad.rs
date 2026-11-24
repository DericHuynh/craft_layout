use keru_layout::{
    Anchor, Arrange, Axis, ChildId, ChildrenLayout, Destination, LayoutParams, LayoutTree, NodeId,
    Pos, Size, TextContent, Xy,
};

use super::Case;

const FILL: Xy<Size> = Xy::new_symm(Size::Fill);
const FIT: Xy<Size> = Xy::new_symm(Size::FitContent);

pub(super) fn cases() -> Vec<Case> {
    vec![docked_viewport(), assembly_inspector()]
}

fn stack(axis: Axis, size: Xy<Size>, spacing: f32, padding: f32) -> LayoutParams {
    LayoutParams {
        size,
        position: Xy::new_symm(Pos::Start),
        padding: Xy::new_symm([padding; 2]),
        children_layout: ChildrenLayout::Stack {
            axis,
            arrange: Arrange::Start,
            spacing,
        },
        ..LayoutParams::DEFAULT
    }
}

fn label(tree: &mut LayoutTree<String>, parent: &NodeId, content: impl Into<String>) -> ChildId {
    text(tree, parent, FIT, TextContent::Fixed, content)
}

fn text(
    tree: &mut LayoutTree<String>,
    parent: &NodeId,
    size: Xy<Size>,
    mode: TextContent,
    content: impl Into<String>,
) -> ChildId {
    tree.add_node_with_context(
        parent,
        LayoutParams {
            size,
            position: Xy::new_symm(Pos::Start),
            text: mode,
            ..LayoutParams::DEFAULT
        },
        content.into(),
    )
    .expect("add CAD text")
}

fn container(
    tree: &mut LayoutTree<String>,
    parent: &NodeId,
    axis: Axis,
    size: Xy<Size>,
    spacing: f32,
    padding: f32,
) -> ChildId {
    tree.add_node(parent, stack(axis, size, spacing, padding))
        .expect("add CAD panel")
}

fn toolbar(tree: &mut LayoutTree<String>, parent: &NodeId, labels: &[&str]) {
    let bar = container(
        tree,
        parent,
        Axis::X,
        Xy::new(Size::Fill, Size::FitContent),
        14.0,
        7.0,
    );
    for &title in labels {
        label(tree, &bar, title);
    }
}

fn property_row(
    tree: &mut LayoutTree<String>,
    parent: &NodeId,
    name: &str,
    value: impl Into<String>,
) {
    let row = container(
        tree,
        parent,
        Axis::X,
        Xy::new(Size::Fill, Size::FitContent),
        8.0,
        2.0,
    );
    text(
        tree,
        &row,
        Xy::new(Size::Pixels(106.0), Size::FitContent),
        TextContent::Fixed,
        name,
    );
    text(
        tree,
        &row,
        Xy::new(Size::Fill, Size::FitContent),
        TextContent::Wrapping,
        value,
    );
}

fn viewport_overlay(
    tree: &mut LayoutTree<String>,
    viewport: &NodeId,
    position: Xy<Pos>,
    content: &str,
) -> ChildId {
    tree.add_node_with_context(
        viewport,
        LayoutParams {
            size: FIT,
            position,
            anchor: Xy::new_symm(Anchor::Start),
            padding: Xy::new_symm([4.0; 2]),
            text: TextContent::Fixed,
            free_placement: true,
            ..LayoutParams::DEFAULT
        },
        content.into(),
    )
    .expect("add viewport overlay")
}

fn drawing_view(
    tree: &mut LayoutTree<String>,
    parent: &NodeId,
    orientation: &str,
    weight: f32,
) -> ChildId {
    let view = tree
        .add_node(
            parent,
            LayoutParams {
                size: FILL,
                position: Xy::new_symm(Pos::Start),
                fill_weight: weight,
                ..LayoutParams::DEFAULT
            },
        )
        .expect("add drawing viewport");
    let title = viewport_overlay(
        tree,
        &view,
        Xy::new(Pos::Pixels(8.0), Pos::Pixels(8.0)),
        orientation,
    );
    viewport_overlay(
        tree,
        &view,
        Xy::new(Pos::Start, Pos::End),
        "0     25     50 mm",
    );
    viewport_overlay(
        tree,
        &view,
        Xy::new(Pos::End, Pos::Start),
        "X +   Y +   Z +",
    );
    title
}

fn docked_viewport() -> Case {
    const RESIZES: [(Xy<f32>, f32, &str); 4] = [
        (Xy::new(1440.0, 960.0), 246.0, "Perspective · 1:2"),
        (Xy::new(1584.0, 960.0), 318.0, "Front projection · 1:1"),
        (Xy::new(1336.0, 856.0), 278.0, "Isometric · 1:4"),
        (Xy::new(1520.0, 912.0), 344.0, "Section B–B · 2:1"),
    ];

    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, stack(Axis::Y, FILL, 4.0, 6.0))
        .expect("set workspace root");
    toolbar(
        &mut tree,
        &root,
        &[
            "File", "Edit", "View", "Sketch", "Part", "Assembly", "Inspect", "Window",
        ],
    );

    let ribbon = tree
        .add_node(
            &root,
            LayoutParams {
                children_layout: ChildrenLayout::Wrap {
                    axis: Axis::X,
                    arrange: Arrange::Start,
                    spacing: 8.0,
                    line_spacing: 4.0,
                },
                ..stack(Axis::X, Xy::new(Size::Fill, Size::FitContent), 8.0, 4.0)
            },
        )
        .expect("add command ribbon");
    for command in [
        "New sketch",
        "Construction plane",
        "Extrude",
        "Revolve",
        "Shell",
        "Fillet",
        "Chamfer",
        "Pattern",
        "Mirror",
        "Section view",
        "Measure angle",
        "Inspect interference",
        "Toggle constraints",
        "Align workplane",
        "Export drawing",
        "Recompute assembly",
    ] {
        let button = container(&mut tree, &ribbon, Axis::X, FIT, 0.0, 4.0);
        label(&mut tree, &button, command);
    }

    let workbench = container(&mut tree, &root, Axis::X, FILL, 8.0, 0.0);
    let mut dock = stack(
        Axis::Y,
        Xy::new(Size::Pixels(RESIZES[0].1), Size::Fill),
        5.0,
        8.0,
    );
    let sidebar = tree.add_node(&workbench, dock).expect("add model browser");
    label(&mut tree, &sidebar, "Model browser");
    let browser = container(&mut tree, &sidebar, Axis::Y, FILL, 3.0, 0.0);
    for (index, name) in [
        "Base plate",
        "Mounting bracket",
        "Guide rail, left",
        "Guide rail, right",
        "Lead screw",
        "Drive pulley",
        "Belt tensioner",
        "Motor housing",
        "Bearing cap",
        "Coupling",
        "Shield plate",
        "Cable support",
        "Datum plane",
        "Section curve",
    ]
    .into_iter()
    .enumerate()
    {
        property_row(
            &mut tree,
            &browser,
            if index < 12 { "Part" } else { "Reference" },
            name,
        );
    }

    let views = container(&mut tree, &workbench, Axis::Y, FILL, 6.0, 0.0);
    let active_view = drawing_view(&mut tree, &views, RESIZES[0].2, 2.0);
    drawing_view(&mut tree, &views, "Right projection", 1.0);

    let inspector = container(
        &mut tree,
        &workbench,
        Axis::Y,
        Xy::new(Size::Pixels(286.0), Size::Fill),
        6.0,
        8.0,
    );
    label(&mut tree, &inspector, "Measure and inspect");
    for (name, value) in [
        ("Selection", "Guide rail, left"),
        ("Reference", "Drive housing datum"),
        ("Edge length", "148.00 mm"),
        ("Hole diameter", "Ø 8.50 mm"),
        ("Center gap", "22.75 mm"),
        ("Angle", "90.00°"),
        ("Flatness", "± 0.03 mm"),
        ("Material", "6061-T6 anodized aluminium"),
        ("Clearance", "0.80 mm at the rear bearing cap"),
    ] {
        property_row(&mut tree, &inspector, name, value);
    }
    toolbar(
        &mut tree,
        &root,
        &[
            "Millimeters",
            "Grid snap 0.25 mm",
            "Rev. C",
            "No pending solves",
        ],
    );

    Case {
        name: "cad/docked_viewport",
        tree,
        viewport: RESIZES[0].0,
        edit: Box::new(move |tree, frame| {
            let (viewport, width, title) = RESIZES[(frame % RESIZES.len() + 1) % RESIZES.len()];
            dock.size.x = Size::Pixels(width);
            tree.update_node_params(&sidebar, dock)
                .expect("resize CAD dock");
            tree.update_node_context(&active_view, Some(title.into()))
                .expect("change active projection");
            viewport
        }),
    }
}

const ASSEMBLIES: &[(&str, &[&str])] = &[
    (
        "Chassis",
        &[
            "Bed casting",
            "Front brace",
            "Back plate",
            "Leveling foot",
            "Access panel",
        ],
    ),
    (
        "X-axis guide",
        &[
            "Left rail",
            "Right rail",
            "Carriage block",
            "Stop screw",
            "Scale strip",
        ],
    ),
    (
        "Y-axis guide",
        &["Cross slide", "Guide block", "Wiper", "Hard stop"],
    ),
    (
        "Spindle head",
        &[
            "Spindle shaft",
            "Bearing race",
            "Collet",
            "Clamp nut",
            "Drive gear",
        ],
    ),
    (
        "Feed drive",
        &[
            "Lead screw",
            "Ball nut",
            "Coupler",
            "Encoder",
            "Drive motor",
            "Belt cover",
        ],
    ),
    (
        "Workholding",
        &[
            "Fixture plate",
            "Locating pin",
            "Jaw, fixed",
            "Jaw, sliding",
        ],
    ),
    (
        "Coolant loop",
        &["Return tray", "Pump", "Spray nozzle", "Hose clamp"],
    ),
    (
        "Electrical cabinet",
        &[
            "DIN rail",
            "Motor driver",
            "Terminal block",
            "Fuse",
            "Cable gland",
        ],
    ),
    (
        "Guard frame",
        &["Side frame", "Interlock", "Handle", "Viewing panel"],
    ),
    (
        "Probe mount",
        &["Probe body", "Support arm", "Stylus", "Shield"],
    ),
    (
        "Fasteners",
        &["M8 socket screw", "M6 flange nut", "Spring washer", "Dowel"],
    ),
    (
        "Reference geometry",
        &["Top datum", "Center axis", "Travel envelope"],
    ),
];

#[derive(Clone, Copy)]
struct InspectorState {
    expanded: u16,
    move_front: bool,
    inspection: bool,
}

const INSPECTOR_STATES: [InspectorState; 6] = [
    InspectorState {
        expanded: (1 << 0) | (1 << 2),
        move_front: false,
        inspection: false,
    },
    InspectorState {
        expanded: (1 << 0) | (1 << 2) | (1 << 4),
        move_front: false,
        inspection: false,
    },
    InspectorState {
        expanded: (1 << 0) | (1 << 4),
        move_front: false,
        inspection: true,
    },
    InspectorState {
        expanded: (1 << 0) | (1 << 4) | (1 << 7),
        move_front: true,
        inspection: true,
    },
    InspectorState {
        expanded: (1 << 0) | (1 << 7),
        move_front: true,
        inspection: false,
    },
    InspectorState {
        expanded: (1 << 0) | (1 << 2) | (1 << 3),
        move_front: false,
        inspection: false,
    },
];

fn inspection_details(tree: &mut LayoutTree<String>, inspector: &NodeId) -> ChildId {
    let group = container(
        tree,
        inspector,
        Axis::Y,
        Xy::new(Size::Fill, Size::FitContent),
        3.0,
        6.0,
    );
    label(tree, &group, "Interference check");
    property_row(tree, &group, "Pair", "Lead screw / guard frame");
    property_row(tree, &group, "Result", "No overlap in nominal travel");
    property_row(tree, &group, "Min. clearance", "0.62 mm at +X stop");
    group
}

fn assembly_inspector() -> Case {
    let viewport = Xy::new(1500.0, 1000.0);
    let mut tree = LayoutTree::new();
    let root = tree.root();
    tree.update_node_params(&root, stack(Axis::Y, FILL, 5.0, 8.0))
        .expect("set assembly editor root");
    toolbar(
        &mut tree,
        &root,
        &["Projects", "Mill head", "Revision C", "Assembly editor"],
    );

    let body = container(&mut tree, &root, Axis::X, FILL, 8.0, 0.0);
    let browser = container(
        &mut tree,
        &body,
        Axis::Y,
        Xy::new(Size::Pixels(352.0), Size::Fill),
        4.0,
        6.0,
    );
    label(&mut tree, &browser, "Assembly tree");

    let mut sections = Vec::new();
    let mut chassis_rows = Vec::new();
    for (index, &(name, parts)) in ASSEMBLIES.iter().enumerate() {
        let header = container(
            &mut tree,
            &browser,
            Axis::X,
            Xy::new(Size::Fill, Size::FitContent),
            8.0,
            2.0,
        );
        label(&mut tree, &header, name);
        label(&mut tree, &header, format!("{} components", parts.len()));

        let mut parameters = stack(Axis::Y, Xy::new(Size::Fill, Size::FitContent), 1.0, 0.0);
        parameters.padding.x = [18.0, 2.0];
        let list = tree
            .add_node(&browser, parameters)
            .expect("add subassembly parts");
        for (part, name) in parts.iter().enumerate() {
            let row = container(
                &mut tree,
                &list,
                Axis::X,
                Xy::new(Size::Fill, Size::FitContent),
                9.0,
                1.0,
            );
            label(
                &mut tree,
                &row,
                format!("P-{:02}{:02}", index + 1, part + 1),
            );
            label(&mut tree, &row, *name);
            if index == 0 {
                chassis_rows.push(row);
            }
        }
        parameters.disabled = INSPECTOR_STATES[0].expanded & (1 << index) == 0;
        tree.update_node_params(&list, parameters)
            .expect("set initial branch visibility");
        sections.push((list, parameters));
    }
    let chassis = sections[0].0.clone();
    let first = chassis_rows
        .first()
        .expect("chassis starts with the bed casting")
        .clone();
    let access_panel = chassis_rows
        .pop()
        .expect("chassis ends with the access panel");

    drawing_view(&mut tree, &body, "Mill head assembly · exploded view", 1.0);
    let inspector = container(
        &mut tree,
        &body,
        Axis::Y,
        Xy::new(Size::Pixels(320.0), Size::Fill),
        5.0,
        8.0,
    );
    for (heading, fields) in [
        (
            "Identification",
            [
                ("Part", "Chassis / bed casting"),
                ("Document", "MH-ASSY-017"),
                ("Revision", "C.08"),
            ],
        ),
        (
            "Transform",
            [
                ("Translation", "X 0.00   Y 25.00   Z 64.50 mm"),
                ("Rotation", "90.00° about Z"),
                ("Reference", "Machine datum"),
            ],
        ),
        (
            "Physical",
            [
                ("Material", "Cast iron, ASTM A48 Class 35"),
                ("Mass", "18.42 kg"),
                ("Centre of mass", "X −5.2   Y 18.0   Z 8.6 mm"),
            ],
        ),
        (
            "Constraints",
            [
                ("Mate", "Bed face to chassis base"),
                ("Lock", "Rotation about spindle axis"),
                ("Tolerance", "± 0.02 mm on front mounting face"),
            ],
        ),
    ] {
        label(&mut tree, &inspector, heading);
        for (name, value) in fields {
            property_row(&mut tree, &inspector, name, value);
        }
    }
    toolbar(
        &mut tree,
        &root,
        &[
            "Assembly valid",
            "Units mm",
            "Orthographic",
            "34 constraints",
        ],
    );

    let mut last = INSPECTOR_STATES[0];
    let mut detail = None;
    Case {
        name: "cad/assembly_inspector",
        tree,
        viewport,
        edit: Box::new(move |tree, frame| {
            let state =
                INSPECTOR_STATES[(frame % INSPECTOR_STATES.len() + 1) % INSPECTOR_STATES.len()];
            for (index, (section, params)) in sections.iter_mut().enumerate() {
                let disabled = state.expanded & (1 << index) == 0;
                if params.disabled != disabled {
                    params.disabled = disabled;
                    tree.update_node_params(section, *params)
                        .expect("change subassembly visibility");
                }
            }

            if state.move_front != last.move_front {
                let destination = if state.move_front {
                    Destination::Before(&first)
                } else {
                    Destination::LastChildOf(&chassis)
                };
                tree.move_node(&access_panel, destination)
                    .expect("reorder chassis component");
            }

            match (state.inspection, detail.take()) {
                (true, None) => detail = Some(inspection_details(tree, &inspector)),
                (false, Some(panel)) => tree.remove(&panel).expect("remove transient inspection"),
                (_, panel) => detail = panel,
            }
            last = state;
            viewport
        }),
    }
}
