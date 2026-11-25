//! Runtime geometry from the upstream Taffy checkout used for the fixture corpus.
//! Run from the Craft repository root after `benchmarks/conformance/fetch.sh`:
//! `cargo run --locked --manifest-path benchmarks/author-intent/taffy/Cargo.toml`.
use taffy::{geometry::Point, prelude::*, style::Overflow, TaffyError};

type Tree = TaffyTree<()>;

fn flexible() -> Style {
    Style {
        flex_grow: 1.0,
        flex_shrink: 1.0,
        flex_basis: percent(0.0),
        ..Default::default()
    }
}

fn fixed_width(width: f32) -> Style {
    Style {
        size: Size {
            width: length(width),
            height: auto(),
        },
        flex_shrink: 0.0,
        ..Default::default()
    }
}

fn solve(tree: &mut Tree, root: NodeId, width: f32, height: f32) -> Result<(), TaffyError> {
    let mut style = tree.style(root)?.clone();
    style.size = Size {
        width: length(width),
        height: length(height),
    };
    tree.set_style(root, style)?;
    tree.compute_layout(
        root,
        Size {
            width: AvailableSpace::Definite(width),
            height: AvailableSpace::Definite(height),
        },
    )
}

fn title(zero_min: bool) -> Result<(), TaffyError> {
    let mut tree = Tree::new();
    let title = tree.new_leaf(fixed_width(288.0))?;
    let mut slot_style = flexible();
    if zero_min {
        slot_style.min_size.width = length(0.0);
    }
    let slot = tree.new_with_children(slot_style, &[title])?;
    let action = tree.new_leaf(fixed_width(40.0))?;
    let root = tree.new_with_children(
        Style {
            gap: Size {
                width: length(8.0),
                height: zero(),
            },
            ..Default::default()
        },
        &[slot, action],
    )?;
    for width in [224.0, 144.0] {
        solve(&mut tree, root, width, 32.0)?;
        println!(
            "title width={width} min0={zero_min} slot={} action_x={} title={}",
            tree.layout(slot)?.size.width,
            tree.layout(action)?.location.x,
            tree.layout(title)?.size.width
        );
    }
    Ok(())
}

fn cards(box_sizing: BoxSizing, inner_padding: bool) -> Result<(), TaffyError> {
    let mut tree = Tree::new();
    let mut cards = Vec::new();
    let mut inners = Vec::new();
    for index in 0..3 {
        let mut card = Style {
            box_sizing,
            ..flexible()
        };
        let mut inner = Style {
            box_sizing,
            ..flexible()
        };
        if index == 1 {
            let padding = if inner_padding {
                &mut inner.padding
            } else {
                &mut card.padding
            };
            padding.left = length(18.0);
            padding.right = length(18.0);
        }
        let child = tree.new_leaf(inner)?;
        inners.push(child);
        cards.push(tree.new_with_children(card, &[child])?);
    }
    let root = tree.new_with_children(Style::default(), &cards)?;
    for width in [300.0, 240.0] {
        solve(&mut tree, root, width, 40.0)?;
        let widths: Vec<_> = cards
            .iter()
            .map(|&node| tree.layout(node).map(|l| l.size.width))
            .collect::<Result<_, _>>()?;
        println!("cards width={width} sizing={box_sizing:?} inner_padding={inner_padding} outer={widths:?} middle_inner_content={}",
            tree.layout(inners[1])?.content_box_width());
    }
    Ok(())
}

fn list(zero_min: bool) -> Result<(), TaffyError> {
    let mut tree = Tree::new();
    let mut rows = Vec::new();
    for _ in 0..8 {
        rows.push(tree.new_leaf(Style {
            size: Size {
                width: auto(),
                height: length(30.0),
            },
            flex_shrink: 0.0,
            ..Default::default()
        })?);
    }
    let list = tree.new_with_children(
        Style {
            flex_direction: FlexDirection::Column,
            overflow: Point {
                x: Overflow::Hidden,
                y: Overflow::Scroll,
            },
            scrollbar_width: 0.0,
            ..flexible()
        },
        &rows,
    )?;
    let mut pane_style = Style {
        flex_direction: FlexDirection::Column,
        ..flexible()
    };
    if zero_min {
        pane_style.min_size.height = length(0.0);
    }
    let pane = tree.new_with_children(pane_style, &[list])?;
    let header = tree.new_leaf(Style {
        size: Size {
            width: auto(),
            height: length(36.0),
        },
        flex_shrink: 0.0,
        ..Default::default()
    })?;
    let root = tree.new_with_children(
        Style {
            flex_direction: FlexDirection::Column,
            ..Default::default()
        },
        &[header, pane],
    )?;
    for height in [160.0, 112.0] {
        solve(&mut tree, root, 224.0, height)?;
        let layout = tree.layout(list)?;
        println!("list height={height} min0={zero_min} pane={} list={} scroll_distance={} last_row_bottom={}",
            tree.layout(pane)?.size.height, layout.size.height, layout.scroll_height(),
            tree.layout(rows[7])?.location.y + tree.layout(rows[7])?.size.height);
    }
    Ok(())
}

fn wrap() -> Result<(), TaffyError> {
    let mut tree = Tree::new();
    let mut items = Vec::new();
    for (index, width) in [34.0, 34.0, 20.0].into_iter().enumerate() {
        let mut style = fixed_width(width);
        style.size.height = length(10.0);
        if index == 2 {
            style.margin.left = auto();
        }
        items.push(tree.new_leaf(style)?);
    }
    let root = tree.new_with_children(
        Style {
            flex_wrap: FlexWrap::Wrap,
            align_content: AlignContent::FLEX_START,
            gap: Size {
                width: length(6.0),
                height: length(4.0),
            },
            ..Default::default()
        },
        &items,
    )?;
    for width in [106.0, 100.0, 99.0] {
        solve(&mut tree, root, width, 40.0)?;
        let action = tree.layout(items[2])?;
        println!(
            "wrap width={width} action_x={} y={}",
            action.location.x, action.location.y
        );
    }
    Ok(())
}

fn grid(zero_track: bool) -> Result<(), TaffyError> {
    let mut tree = Tree::new();
    let rigid = tree.new_leaf(fixed_width(320.0))?;
    let main = tree.new_with_children(Style::default(), &[rigid])?;
    let rail = tree.new_leaf(Style::default())?;
    let root = tree.new_with_children(
        Style {
            display: Display::Grid,
            grid_template_columns: vec![if zero_track { flex(1.0) } else { fr(1.0) }, length(40.0)],
            ..Default::default()
        },
        &[main, rail],
    )?;
    solve(&mut tree, root, 240.0, 40.0)?;
    println!(
        "grid width=240 zero_track={zero_track} main={} rail_x={} child={}",
        tree.layout(main)?.size.width,
        tree.layout(rail)?.location.x,
        tree.layout(rigid)?.size.width
    );
    Ok(())
}

fn responsive_cards() -> Result<(), TaffyError> {
    let mut tree = Tree::new();
    tree.disable_rounding();
    let mut cards = Vec::new();
    for _ in 0..3 {
        cards.push(tree.new_leaf(Style {
            size: Size {
                width: auto(),
                height: length(20.0),
            },
            ..Default::default()
        })?);
    }
    let root = tree.new_with_children(
        Style {
            display: Display::Grid,
            grid_template_columns: vec![repeat("auto-fit", vec![minmax(length(120.0), fr(1.0))])],
            gap: Size {
                width: length(10.0),
                height: zero(),
            },
            align_content: AlignContent::START,
            ..Default::default()
        },
        &cards,
    )?;
    for width in [380.0, 379.0, 250.0, 249.0, 120.0, 90.0, 0.0] {
        solve(&mut tree, root, width, 100.0)?;
        let first = tree.layout(cards[0])?;
        let mut columns = 0;
        for &card in &cards {
            if tree.layout(card)?.location.y == 0.0 {
                columns += 1;
            }
        }
        println!(
            "auto_fit width={width} min=120 columns={columns} card_width={}",
            first.size.width
        );
    }
    Ok(())
}

fn main() -> Result<(), TaffyError> {
    for reset in [false, true] {
        title(reset)?;
        list(reset)?;
    }
    for sizing in [BoxSizing::BorderBox, BoxSizing::ContentBox] {
        for inner in [false, true] {
            cards(sizing, inner)?;
        }
    }
    wrap()?;
    for zero_track in [false, true] {
        grid(zero_track)?;
    }
    responsive_cards()?;
    Ok(())
}
