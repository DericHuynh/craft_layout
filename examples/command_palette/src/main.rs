use keru_layout::{
    Anchor, Arrange, Axis, ChildId, ChildrenLayout, LayoutParams, LayoutTree, NodeId, Pos, Size,
    TextContent, TreeError, WindowOverflow, Xy, XyRect,
};

type Tree = LayoutTree<&'static str>;
type Result<T> = std::result::Result<T, TreeError>;

fn stack(axis: Axis, gap: f32) -> ChildrenLayout {
    ChildrenLayout::Stack {
        axis,
        arrange: Arrange::Start,
        spacing: gap,
    }
}

fn intrinsic() -> LayoutParams {
    LayoutParams {
        size: Xy::new_symm(Size::FitContent),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}

fn label(tree: &mut Tree, parent: &NodeId, text: &'static str) -> Result<ChildId> {
    tree.add_node_with_context(
        parent,
        LayoutParams {
            text: TextContent::Fixed,
            ..intrinsic()
        },
        text,
    )
}

fn solve(tree: &mut Tree, window: Xy<f32>) {
    tree.solve_layout_with_measure(window, |_, content, _| {
        let text = content.expect("every text leaf has content");
        Xy::new(text.chars().count() as f32 * 8.0, 16.0)
    });
    assert!(tree.warnings().is_empty(), "{:?}", tree.warnings());
}

struct Menu {
    panel: ChildId,
    rename: ChildId,
}

impl Menu {
    fn open(tree: &mut Tree, canvas: &ChildId, overflow: WindowOverflow) -> Result<Self> {
        let panel = tree.add_node(
            canvas,
            LayoutParams {
                children_layout: stack(Axis::Y, 6.0),
                padding: Xy::new([10.0; 2], [8.0; 2]),
                window_overflow: Xy::new_symm(overflow),
                free_placement: true,
                ..intrinsic()
            },
        )?;
        label(tree, &panel, "Commands")?;
        let results = tree.add_node(
            &panel,
            LayoutParams {
                children_layout: stack(Axis::Y, 4.0),
                ..intrinsic()
            },
        )?;
        let rename = Self::action(tree, &results, "Rename", "R")?;
        Self::action(tree, &results, "Duplicate", "D")?;
        label(tree, &panel, "2 matches")?;
        Ok(Self { panel, rename })
    }

    fn action(
        tree: &mut Tree,
        parent: &NodeId,
        name: &'static str,
        shortcut: &'static str,
    ) -> Result<ChildId> {
        let row = tree.add_node(
            parent,
            LayoutParams {
                children_layout: stack(Axis::X, 8.0),
                ..intrinsic()
            },
        )?;
        tree.add_node(
            &row,
            LayoutParams {
                size: Xy::new_symm(Size::Pixels(12.0)),
                ..intrinsic()
            },
        )?;
        let name = label(tree, &row, name)?;
        label(tree, &row, shortcut)?;
        Ok(name)
    }
}

struct Canvas {
    tree: Tree,
    body: ChildId,
}

impl Canvas {
    fn new() -> Result<Self> {
        let mut tree = Tree::new();
        let root = tree.root();
        tree.update_node_params(
            &root,
            LayoutParams {
                children_layout: stack(Axis::Y, 0.0),
                padding: Xy::new([10.0; 2], [0.0; 2]),
                ..LayoutParams::DEFAULT
            },
        )?;
        let toolbar = tree.add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::Pixels(28.0)),
                ..LayoutParams::DEFAULT
            },
        )?;
        label(&mut tree, &toolbar, "Document tools")?;
        let body = tree.add_node(&root, LayoutParams::DEFAULT)?;
        label(&mut tree, &body, "Canvas")?;
        let status = tree.add_node(
            &root,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::Pixels(20.0)),
                ..LayoutParams::DEFAULT
            },
        )?;
        label(&mut tree, &status, "Ready")?;
        Ok(Self { tree, body })
    }

    fn frame(
        &mut self,
        menu: &Menu,
        window: Xy<f32>,
        point: Xy<f32>,
        manual: bool,
    ) -> Result<XyRect> {
        self.position(&menu.panel, point)?;
        solve(&mut self.tree, window);
        if manual {
            // Read the menu measured at the pointer, then place its top-left in canvas coordinates.
            let canvas = self.tree.layout(&self.body)?;
            let menu_rect = self.tree.layout(&menu.panel)?;
            let local_start = |range: [f32; 2], edge: f32, parent_start: f32| {
                let extent = range[1] - range[0];
                let proposed = if range[1] > edge {
                    range[0] - extent
                } else {
                    range[0]
                };
                proposed.clamp(0.0, (edge - extent).max(0.0)) - parent_start
            };
            self.position(
                &menu.panel,
                Xy::new(
                    local_start(menu_rect.x, window.x, canvas.x[0]),
                    local_start(menu_rect.y, window.y, canvas.y[0]),
                ),
            )?;
            solve(&mut self.tree, window);
        }
        self.tree.layout(&menu.panel)
    }

    fn position(&mut self, panel: &ChildId, point: Xy<f32>) -> Result<()> {
        let mut params = *self.tree.params(panel)?;
        params.position = Xy::new(Pos::Pixels(point.x), Pos::Pixels(point.y));
        self.tree.update_node_params(panel, params)
    }
}

fn rectangles(tree: &Tree, node: &NodeId, output: &mut Vec<XyRect>) -> Result<()> {
    output.push(tree.layout(node)?);
    for child in tree.children(node)? {
        rectangles(tree, &child, output)?;
    }
    Ok(())
}

struct Snapshot {
    panel: XyRect,
    all: Vec<XyRect>,
}

fn replay(manual: bool) -> Result<Vec<Snapshot>> {
    let mut app = Canvas::new()?;
    let large = Xy::new(400.0, 240.0);
    solve(&mut app.tree, large);
    let original_body = app.tree.layout(&app.body)?;
    assert_eq!(original_body, Xy::new([10.0, 390.0], [28.0, 220.0]));
    let overflow = if manual {
        WindowOverflow::Ignore
    } else {
        WindowOverflow::Flip
    };
    let menu = Menu::open(&mut app.tree, &app.body, overflow)?;
    let mut frames = Vec::new();
    for (index, (event, window, point)) in [
        ("right click", large, Xy::new(362.0, 188.0)),
        ("rename selection", large, Xy::new(362.0, 188.0)),
        ("reinvoke at top left", large, Xy::new(22.0, 12.0)),
        (
            "resize and invoke",
            Xy::new(256.0, 160.0),
            Xy::new(110.0, 62.0),
        ),
    ]
    .into_iter()
    .enumerate()
    {
        if index == 1 {
            app.tree
                .update_node_context(&menu.rename, Some("Rename selection"))?;
        }
        let panel = app.frame(&menu, window, point, manual)?;
        println!(
            "{} / {event}: {:?} {:?}",
            if manual { "manual" } else { "native" },
            panel.x,
            panel.y
        );
        let width = if index == 0 { 128.0 } else { 184.0 };
        assert_eq!(panel.x[1] - panel.x[0], width);
        assert_eq!(panel.y[1] - panel.y[0], 96.0);
        assert!(
            panel.x[0] >= 0.0
                && panel.x[1] <= window.x
                && panel.y[0] >= 0.0
                && panel.y[1] <= window.y
        );
        if index < 3 {
            assert_eq!(app.tree.layout(&app.body)?, original_body);
            let expected = match index {
                0 => Xy::new([244.0, 372.0], [120.0, 216.0]),
                1 => Xy::new([188.0, 372.0], [120.0, 216.0]),
                _ => Xy::new([32.0, 216.0], [40.0, 136.0]),
            };
            assert_eq!(panel, expected);
        }
        let mut all = Vec::new();
        rectangles(&app.tree, &app.tree.root(), &mut all)?;
        assert_eq!(all.len(), 19);
        frames.push(Snapshot { panel, all });
    }
    let before_dismiss = app.tree.layout(&app.body)?;
    app.tree.remove(&menu.panel)?;
    solve(&mut app.tree, Xy::new(256.0, 160.0));
    assert_eq!(app.tree.layout(&app.body)?, before_dismiss);
    assert_eq!(app.tree.layout(&menu.rename), Err(TreeError::StaleNode));
    let mut closed = Vec::new();
    rectangles(&app.tree, &app.tree.root(), &mut closed)?;
    assert_eq!(closed.len(), 7);
    Ok(frames)
}

fn main() -> Result<()> {
    let direct = replay(false)?;
    let manual = replay(true)?;
    for (left, right) in direct[..3].iter().zip(&manual[..3]) {
        assert_eq!(left.all, right.all);
    }
    // Follow-up characterization. The initial product requirement here was window containment.
    assert_eq!(direct[3].panel, Xy::new([72.0, 256.0], [64.0, 160.0]));
    assert_eq!(manual[3].panel, Xy::new([0.0, 184.0], [0.0, 96.0]));
    println!(
        "All 19 rectangles match on the first three open frames. Both menus fit on the fourth."
    );
    Ok(())
}
