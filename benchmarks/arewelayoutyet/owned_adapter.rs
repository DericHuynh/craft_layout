//! Owned Keru backend for the same PanGUI declarations as the dense adapter.

use crate::keru_layout_helpers::{axis, count, params, KeruLayoutTree};
use crate::pangui_template::LayoutNode;
use keru_layout::{
    Axis, BatchLayoutError, BatchLayoutStats, IncrementalRelayoutOutcome, LayoutTree, NodeId, Xy,
};
use std::hint::black_box;

pub struct OwnedKeruLayoutTree {
    tree: LayoutTree,
    window: Xy<f32>,
    node_count: usize,
}

impl OwnedKeruLayoutTree {
    pub fn new(template: &LayoutNode, width: f32, height: f32) -> Option<Self> {
        let node_count = count(template);
        let mut tree = LayoutTree::with_capacity(node_count.checked_add(1)?).ok()?;
        let root = tree.root();
        add(&mut tree, &root, template, None)?;
        Some(Self {
            tree,
            window: Xy::new(width, height),
            node_count,
        })
    }

    /// Require every sizing value and output rectangle to be computed again.
    /// The batch scheduler can retain its dependency graph.
    pub fn mark_all_dirty(&mut self) {
        self.tree.invalidate();
    }

    pub fn compute_default(&mut self) -> IncrementalRelayoutOutcome {
        let result = self.tree.solve_layout(self.window);
        black_box(&self.tree);
        result
    }

    pub fn compute_batch(&mut self) -> Result<BatchLayoutStats, BatchLayoutError> {
        let result = self.tree.solve_layout_batch(self.window);
        black_box(&self.tree);
        result
    }

    /// The template node count excludes the synthetic viewport.
    pub fn node_count(&self) -> usize {
        self.node_count
    }

    /// The viewport first, followed by the template in document order.
    pub fn rectangle_bits(&self) -> Vec<[u32; 4]> {
        let mut result = Vec::with_capacity(self.node_count + 1);
        let mut pending = vec![self.tree.root()];
        while let Some(node) = pending.pop() {
            let rect = self.tree.layout(&node).expect("missing template rectangle");
            result.push([rect.x[0], rect.x[1], rect.y[0], rect.y[1]].map(f32::to_bits));
            let first_child = pending.len();
            pending.extend(
                self.tree
                    .children(&node)
                    .expect("missing template node")
                    .map(NodeId::from),
            );
            pending[first_child..].reverse();
        }
        result
    }

    pub fn assert_matches_dense(&self, dense: &KeruLayoutTree) {
        assert_eq!(self.node_count(), dense.node_count(), "template node count");
        let owned = self.rectangle_bits();
        assert_eq!(owned.len(), self.node_count + 1, "published node count");
        let mut dense = dense.rectangle_bits();
        for (index, actual) in owned.into_iter().enumerate() {
            assert_eq!(
                Some(actual),
                dense.next(),
                "absolute rectangle at preorder index {index}"
            );
        }
        assert!(dense.next().is_none(), "unexpected extra rectangle");
    }
}

fn add(
    tree: &mut LayoutTree,
    parent: &NodeId,
    template: &LayoutNode,
    parent_axis: Option<Axis>,
) -> Option<()> {
    let child = tree.add_node(parent, params(template, parent_axis)?).ok()?;
    let parent_axis = Some(axis(template));
    for template_child in &template.children {
        add(tree, &child, template_child, parent_axis)?;
    }
    Some(())
}
