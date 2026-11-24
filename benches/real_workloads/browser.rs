use keru_layout::{
    Arrange, Axis, ChildId, ChildrenLayout, LayoutParams, LayoutTree, MainAxisCellSize, Margin,
    NodeId, Pos, Size, TextContent, Xy,
};

use super::Case;

pub(super) fn cases() -> Vec<Case> {
    vec![article(), catalog()]
}

fn wrapping_text(width: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(width, Size::FitContent),
        position: Xy::new_symm(Pos::Start),
        text: TextContent::Wrapping,
        ..LayoutParams::DEFAULT
    }
}

fn stack(axis: Axis, spacing: f32, size: Xy<Size>) -> LayoutParams {
    LayoutParams {
        size,
        position: Xy::new_symm(Pos::Start),
        children_layout: ChildrenLayout::Stack {
            axis,
            arrange: Arrange::Start,
            spacing,
        },
        ..LayoutParams::DEFAULT
    }
}

fn add_text(
    tree: &mut LayoutTree<String>,
    parent: &NodeId,
    params: LayoutParams,
    text: String,
) -> ChildId {
    tree.add_node_with_context(parent, params, text).unwrap()
}

fn margin(value: f32) -> Margin {
    Margin::px(value).unwrap()
}

fn article() -> Case {
    const SECTIONS: &[&str] = &[
        "The route before reconstruction",
        "A five-minute transfer",
        "A missing link at the river",
        "What the ridership counts showed",
        "The station in winter",
        "The café beside the works",
        "Access by bicycle",
        "Changing the signal sequence",
        "Testing the passenger information",
        "The first weekend closure",
        "Loading bays and deliveries",
        "What changed for commuters",
        "The quieter crossing",
        "The cost of the temporary stops",
        "Measuring the new timetable",
        "Following the late train",
        "Lessons from the pilot",
        "What opens next spring",
    ];
    const PARAGRAPHS: &[&str] = &[
        "The project team spent a week watching riders cross the street between platforms. A transfer looked straightforward on the map, but a delayed bus meant that passengers could miss the next train by the time they reached the signal.",
        "The published timetable included recovery time at the terminal. On busy afternoons that time disappeared before the vehicle reached the river, leaving little room for a wheelchair boarding or a queue at the temporary crossing.",
        "Engineers kept the existing brick shelter and moved the ticket machine closer to the entrance. That left a wider path through the station without taking away the bench that riders used while waiting for the evening service.",
        "During the final weekend of work, volunteers placed signs at street corners and met the first arriving buses. The revised route was marked on a different colour so riders could tell a detour from a permanent change.",
        "Near the station, the café moved its outdoor tables while contractors cleared the loading bay. A sign reading “entrée côté rue” helped visitors find the door during the work, and the early deliveries continued through the side entrance.",
        "The trial added two minutes to the scheduled journey, but the drivers reported fewer queues at the junction. The city will publish a fresh count after the school term begins, when it can compare the same weeks in both years.",
        "People who relied on the earlier stop asked for a shelter and better lighting. The temporary platform could accommodate those changes without moving the boarding point again, preserving the directions already printed on the local map.",
        "The team separated the footpath and cycle lane with a low divider rather than a raised curb. At the market crossing the divider stops early, leaving room for riders to slow down before turning into the bicycle parking area.",
        "One resident brought notes from trips taken at three different times of day. Her records showed that the delay came from the signal at the end of the bridge, where people arriving on foot had to wait through a full cycle.",
    ];
    const ORIGINAL: &str = "The first station count covered three workdays. A second count will follow once the market reopens.";
    const UPDATED: &str = "The first station count covered three workdays. Since then, the team added a weekend count and compared the boarding totals with the last full month before construction. The Saturday figures showed that most visitors arrived between ten and noon, while weekday arrivals were spread across both directions of travel. The city will repeat the count when the market reopens and publish a separate table for riders using the accessible entrance. That will help distinguish a change in the service from the shorter route to the platform.";
    const FRAMES: [(f32, bool); 6] = [
        (1080.0, true),
        (1080.0, false),
        (412.0, false),
        (412.0, true),
        (768.0, true),
        (1080.0, false),
    ];

    let mut tree = LayoutTree::with_capacity(1 + 6 + SECTIONS.len() * 5).unwrap();
    let root = tree.root();
    tree.update_node_params(
        &root,
        LayoutParams {
            children_layout: ChildrenLayout::Block,
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();
    add_text(
        &mut tree,
        &root,
        LayoutParams {
            padding: Xy::new([20.0; 2], [14.0; 2]),
            ..wrapping_text(Size::Auto)
        },
        "City transport journal  /  Local reporting".into(),
    );
    let article = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new_symm(Size::Auto),
                max_size: Xy::new(Some(Size::Pixels(760.0)), None),
                margin: Xy::new([Margin::AUTO; 2], [margin(18.0), margin(32.0)]),
                padding: Xy::new([24.0; 2], [16.0; 2]),
                children_layout: ChildrenLayout::Block,
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    add_text(
        &mut tree,
        &article,
        LayoutParams {
            padding: Xy::new([0.0; 2], [8.0; 2]),
            ..wrapping_text(Size::Auto)
        },
        "How a new crossing changed the journey across town".into(),
    );
    add_text(
        &mut tree,
        &article,
        wrapping_text(Size::Auto),
        "A field report on the station rebuild and the small changes that made daily trips easier."
            .into(),
    );
    tree.add_node(
        &article,
        LayoutParams {
            size: Xy::new(Size::Auto, Size::Pixels(220.0)),
            margin: Xy::new([Margin::ZERO; 2], [margin(16.0); 2]),
            ..LayoutParams::DEFAULT
        },
    )
    .unwrap();

    let mut editable = None;
    for (index, heading) in SECTIONS.iter().enumerate() {
        let section = tree
            .add_node(
                &article,
                LayoutParams {
                    size: Xy::new_symm(Size::Auto),
                    margin: Xy::new([Margin::ZERO; 2], [margin(15.0), margin(10.0)]),
                    children_layout: ChildrenLayout::Block,
                    ..LayoutParams::DEFAULT
                },
            )
            .unwrap();
        add_text(
            &mut tree,
            &section,
            LayoutParams {
                padding: Xy::new([0.0; 2], [5.0; 2]),
                ..wrapping_text(Size::Auto)
            },
            (*heading).into(),
        );
        for paragraph in 0..3 {
            let is_editable = index == 8 && paragraph == 1;
            let text = if is_editable {
                ORIGINAL
            } else {
                PARAGRAPHS[(index * 3 + paragraph) % PARAGRAPHS.len()]
            };
            let node = add_text(
                &mut tree,
                &section,
                LayoutParams {
                    margin: Xy::new([Margin::ZERO; 2], [margin(8.0), margin(10.0)]),
                    ..wrapping_text(Size::Auto)
                },
                text.into(),
            );
            if is_editable {
                editable = Some(node);
            }
        }
    }
    add_text(
        &mut tree,
        &article,
        LayoutParams {
            margin: Xy::new([Margin::ZERO; 2], [margin(18.0), Margin::ZERO]),
            ..wrapping_text(Size::Auto)
        },
        "The next passenger count will appear in the June edition.".into(),
    );
    let editable = editable.unwrap();
    let mut revised = false;

    Case {
        name: "browser/article_reflow",
        tree,
        viewport: Xy::new(1080.0, 900.0),
        edit: Box::new(move |tree, frame| {
            let (width, next_revision) = FRAMES[frame % FRAMES.len()];
            if revised != next_revision {
                let text = if next_revision { UPDATED } else { ORIGINAL };
                tree.update_node_context(&editable, Some(text.into()))
                    .unwrap();
                revised = next_revision;
            }
            Xy::new(width, 900.0)
        }),
    }
}

fn catalog() -> Case {
    const PRODUCT_COUNT: usize = 72;
    const FILTERS: &[&str] = &[
        "New arrivals",
        "Desk lamps",
        "Wall shelves",
        "Textiles",
        "Storage boxes",
        "For small rooms",
        "Natural materials",
        "In stock",
        "Under $50",
        "Made locally",
        "Low energy",
        "Shop all",
    ];
    const PRODUCTS: [(&str, &str); 12] = [
        (
            "Oak desk lamp",
            "A shaded task lamp with an adjustable arm and warm light for late evenings.",
        ),
        (
            "Linen cushion",
            "A woven linen cover with a hidden zipper. Available in three muted colours.",
        ),
        (
            "Birch wall shelf",
            "A shallow shelf for books, plants and small objects. Mounting hardware included.",
        ),
        (
            "Braided floor basket",
            "A soft-sided basket with two handles for blankets or laundry.",
        ),
        (
            "Ceramic reading light",
            "A low-profile lamp with a broad base and a directional shade.",
        ),
        (
            "Cedar storage tray",
            "A slim tray with a removable divider for keys and other small items.",
        ),
        (
            "Cotton throw",
            "A lightweight checked throw with a finished edge on all four sides.",
        ),
        (
            "Steel file rack",
            "A powder-coated rack with three slots for notebooks and other desk papers.",
        ),
        (
            "Felt desk mat",
            "A quiet surface for a keyboard and a mouse, with a non-slip backing.",
        ),
        (
            "Glass table light",
            "A softly frosted globe on a weighted base with an inline dimmer.",
        ),
        (
            "Canvas magazine bin",
            "A foldable bin with a hard bottom panel and stitched handles.",
        ),
        (
            "Porcelain catchall",
            "A shallow glazed dish for jewellery, coins or a set of spare keys.",
        ),
    ];
    const FRAMES: [(f32, bool); 6] = [
        (1280.0, true),
        (1280.0, false),
        (768.0, false),
        (768.0, true),
        (412.0, true),
        (1280.0, false),
    ];

    let mut tree = LayoutTree::with_capacity(5 + FILTERS.len() + PRODUCT_COUNT * 7).unwrap();
    let root = tree.root();
    tree.update_node_params(
        &root,
        LayoutParams {
            padding: Xy::new([24.0; 2], [16.0; 2]),
            ..stack(Axis::Y, 16.0, Xy::new_symm(Size::Fill))
        },
    )
    .unwrap();
    add_text(
        &mut tree,
        &root,
        LayoutParams {
            padding: Xy::new([0.0; 2], [10.0; 2]),
            ..wrapping_text(Size::Fill)
        },
        "Birch & Clay  /  Home and desk collection".into(),
    );
    let filters = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                children_layout: ChildrenLayout::Wrap {
                    axis: Axis::X,
                    arrange: Arrange::Start,
                    spacing: 8.0,
                    line_spacing: 8.0,
                },
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    let badge = LayoutParams {
        size: Xy::new(Size::FitContent, Size::Pixels(30.0)),
        padding: Xy::new([9.0; 2], [0.0; 2]),
        text: TextContent::Fixed,
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    };
    for title in FILTERS {
        add_text(&mut tree, &filters, badge, (*title).into());
    }
    let result_count = add_text(
        &mut tree,
        &root,
        wrapping_text(Size::Fill),
        "72 products".into(),
    );
    let grid = tree
        .add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                children_layout: ChildrenLayout::Grid {
                    main_axis: Axis::X,
                    columns: MainAxisCellSize::Width(214.0),
                    spacing_x: 14.0,
                    spacing_y: 14.0,
                    backfill: false,
                },
                position: Xy::new_symm(Pos::Start),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    let card_style = LayoutParams {
        padding: Xy::new([12.0; 2], [12.0; 2]),
        ..stack(Axis::Y, 8.0, Xy::new(Size::Fill, Size::FitContent))
    };
    let mut unavailable = Vec::with_capacity(PRODUCT_COUNT / 3);
    for index in 0..PRODUCT_COUNT {
        let (title, description) = PRODUCTS[index % PRODUCTS.len()];
        let card = tree.add_node(&grid, card_style).unwrap();
        tree.add_node(
            &card,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::Pixels(126.0 + (index % 3) as f32 * 12.0)),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
        add_text(&mut tree, &card, wrapping_text(Size::Fill), title.into());
        add_text(
            &mut tree,
            &card,
            wrapping_text(Size::Fill),
            description.into(),
        );
        let price_row = tree
            .add_node(
                &card,
                LayoutParams {
                    size: Xy::new(Size::Fill, Size::Pixels(22.0)),
                    position: Xy::new_symm(Pos::Start),
                    children_layout: ChildrenLayout::Stack {
                        axis: Axis::X,
                        arrange: Arrange::SpaceBetween,
                        spacing: 8.0,
                    },
                    ..LayoutParams::DEFAULT
                },
            )
            .unwrap();
        let price_style = LayoutParams {
            size: Xy::new(Size::FitContent, Size::Pixels(22.0)),
            text: TextContent::Fixed,
            ..LayoutParams::DEFAULT
        };
        add_text(
            &mut tree,
            &price_row,
            price_style,
            format!("${}.00", 18 + index % 27 * 3),
        );
        let in_stock = index % 3 != 1;
        add_text(
            &mut tree,
            &price_row,
            price_style,
            if in_stock { "In stock" } else { "Backorder" }.into(),
        );
        if !in_stock {
            unavailable.push(card);
        }
    }
    let mut filtered = false;

    Case {
        name: "browser/product_catalog",
        tree,
        viewport: Xy::new(1280.0, 840.0),
        edit: Box::new(move |tree, frame| {
            let (width, in_stock_only) = FRAMES[frame % FRAMES.len()];
            if filtered != in_stock_only {
                for card in &unavailable {
                    tree.update_node_params(
                        card,
                        LayoutParams {
                            disabled: in_stock_only,
                            ..card_style
                        },
                    )
                    .unwrap();
                }
                let label = if in_stock_only {
                    "48 products in stock"
                } else {
                    "72 products"
                };
                tree.update_node_context(&result_count, Some(label.into()))
                    .unwrap();
                filtered = in_stock_only;
            }
            Xy::new(width, 840.0)
        }),
    }
}
