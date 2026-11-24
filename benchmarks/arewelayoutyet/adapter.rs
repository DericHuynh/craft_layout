//! PanGUI template adapter for the local `keru_layout` crate.
//!
//! Based on arewelayoutyet's MIT-licensed `keru_layout_helpers.rs`.

use crate::pangui_template::{BenchmarkSize, FlowDirection, LayoutNode, SizeMode, WrapMode};
use keru_layout::{
    Arrange, Axis, ChildrenLayout, LayoutData, LayoutParams, Margin, NodeLayoutData, Pos, Size,
    TreeAdapter, Xy, XyRect,
};

fn size(value: Option<BenchmarkSize>, axis: Axis) -> Size {
    match value {
        None | Some(BenchmarkSize { mode: SizeMode::Fit, .. }) => Size::FitContent,
        Some(BenchmarkSize { mode: SizeMode::Pixels, value }) => Size::Pixels(value),
        Some(BenchmarkSize { mode: SizeMode::Percentage, value }) => Size::Frac(value),
        Some(BenchmarkSize { mode: SizeMode::Expand, .. }) => Size::Fill,
        Some(BenchmarkSize { mode: SizeMode::Ratio, value }) => match axis {
            Axis::X => Size::AspectRatio(value),
            Axis::Y => Size::AspectRatio(1.0 / value),
        },
    }
}

fn weight(value: Option<BenchmarkSize>) -> Option<f32> {
    value.filter(|value| value.mode == SizeMode::Expand).map(|value| value.value)
}

fn axis(node: &LayoutNode) -> Axis {
    if node.flow_direction == Some(FlowDirection::Horizontal) {
        Axis::X
    } else {
        Axis::Y
    }
}

fn params(node: &LayoutNode, parent_axis: Option<Axis>) -> Option<LayoutParams> {
    let padding = |value: Option<f32>| value.unwrap_or(0.0);
    let margin = |value: Option<f32>| Margin::px(value.unwrap_or(0.0));
    let width = [node.width, node.max_width, node.min_width];
    let height = [node.height, node.max_height, node.min_height];
    let fill_weight = match parent_axis {
        Some(Axis::X) => width.into_iter().find_map(weight),
        Some(Axis::Y) => height.into_iter().find_map(weight),
        None => None,
    }.unwrap_or(1.0);
    let axis = axis(node);
    let spacing = node.gap.unwrap_or(0.0);
    let children_layout = match node.wrap {
        Some(WrapMode::Auto) => ChildrenLayout::Wrap {
            axis, spacing, line_spacing: spacing, arrange: Arrange::Start,
        },
        _ => ChildrenLayout::Stack { axis, spacing, arrange: Arrange::Start },
    };
    Some(LayoutParams {
        size: Xy::new(size(node.width, Axis::X), size(node.height, Axis::Y)),
        min_size: Xy::new(
            node.min_width.map(|value| size(Some(value), Axis::X)),
            node.min_height.map(|value| size(Some(value), Axis::Y)),
        ),
        max_size: Xy::new(
            node.max_width.map(|value| size(Some(value), Axis::X)),
            node.max_height.map(|value| size(Some(value), Axis::Y)),
        ),
        fill_weight,
        padding: Xy::new(
            [padding(node.padding_left), padding(node.padding_right)],
            [padding(node.padding_top), padding(node.padding_bottom)],
        ),
        margin: Xy::new(
            [margin(node.margin_left)?, margin(node.margin_right)?],
            [margin(node.margin_top)?, margin(node.margin_bottom)?],
        ),
        children_layout,
        position: Xy::new_symm(Pos::Start),
        ..LayoutParams::DEFAULT
    })
}

fn count(node: &LayoutNode) -> usize {
    1 + node.children.iter().map(count).sum::<usize>()
}

struct Node {
    parent: u32,
    first_child: Option<u32>,
    last_child: Option<u32>,
    next_sibling: Option<u32>,
    params: LayoutParams,
    layout: NodeLayoutData,
    rect: XyRect,
}

struct Tree {
    nodes: Vec<Node>,
    layout: LayoutData<u32>,
}

impl Tree {
    fn push(&mut self, parent: u32, params: LayoutParams) -> Option<u32> {
        let id = u32::try_from(self.nodes.len()).ok()?;
        self.nodes.push(Node {
            parent,
            first_child: None,
            last_child: None,
            next_sibling: None,
            params,
            layout: NodeLayoutData::new(),
            rect: Xy::new_symm([0.0; 2]),
        });
        Some(id)
    }

    fn add(&mut self, parent: u32, template: &LayoutNode, parent_axis: Option<Axis>) -> Option<()> {
        let id = self.push(parent, params(template, parent_axis)?)?;
        let parent = parent as usize;
        if let Some(previous) = self.nodes[parent].last_child {
            self.nodes[previous as usize].next_sibling = Some(id);
        } else {
            self.nodes[parent].first_child = Some(id);
        }
        self.nodes[parent].last_child = Some(id);

        let axis = axis(template);
        for child in &template.children {
            self.add(id, child, Some(axis))?;
        }
        Some(())
    }
}

impl TreeAdapter for Tree {
    type NodeId = u32;

    fn root(&self) -> u32 { 0 }

    fn parent(&self, node: u32) -> Option<u32> {
        (node != 0).then(|| self.nodes[node as usize].parent)
    }

    fn first_child(&self, node: u32) -> Option<u32> { self.nodes[node as usize].first_child }
    fn next_sibling(&self, node: u32) -> Option<u32> { self.nodes[node as usize].next_sibling }
    fn node_layout_params(&self, node: u32) -> &LayoutParams { &self.nodes[node as usize].params }
    fn node_layout_data(&self, node: u32) -> &NodeLayoutData { &self.nodes[node as usize].layout }
    fn node_layout_data_mut(&mut self, node: u32) -> &mut NodeLayoutData { &mut self.nodes[node as usize].layout }
    fn layout_data(&mut self) -> &mut LayoutData<u32> { &mut self.layout }

    fn write_output_rect(&mut self, node: u32, rect: XyRect, _local: XyRect) {
        self.nodes[node as usize].rect = rect;
    }
}

pub struct KeruLayoutTree {
    tree: Tree,
    window: Xy<f32>,
}

impl KeruLayoutTree {
    pub fn new(template: &LayoutNode, width: f32, height: f32) -> Option<Self> {
        let mut tree = Tree { nodes: Vec::with_capacity(count(template) + 1), layout: LayoutData::new() };
        tree.push(0, LayoutParams::DEFAULT)?;
        tree.add(0, template, None)?;
        Some(Self { tree, window: Xy::new(width, height) })
    }

    /// The full solve prepares all sizing records on every invocation.
    pub fn mark_all_dirty(&mut self) {}

    pub fn compute_layout(&mut self) {
        self.tree.solve_layout(self.window);
        std::hint::black_box(&self.tree.nodes);
    }

    pub fn node_count(&self) -> usize { self.tree.nodes.len() - 1 }

    /// Check every absolute edge word, including signed zero, outside the timer.
    pub fn geometry_hash(&self) -> u64 {
        let mut hash = 0xcbf2_9ce4_8422_2325_u64;
        for node in &self.tree.nodes {
            for edge in node.rect.x.into_iter().chain(node.rect.y) {
                hash ^= u64::from(edge.to_bits());
                hash = hash.wrapping_mul(0x100_0000_01b3);
            }
        }
        hash
    }
}
