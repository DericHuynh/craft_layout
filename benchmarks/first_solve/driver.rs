#![allow(dead_code)]

mod browser;
mod cad;
mod compositor;
mod keru_layout_helpers;
mod owned_adapter;

use harness_common::pangui_template::{self, LayoutNode};
use harness_common::{NodeOutput, Solver, extent};
use keru_layout::{
    BatchLayoutStats, IncrementalRelayoutOutcome, LayoutTree, NodeId, TreeError, Xy,
    measure_monospace_text,
};
use keru_layout_helpers::KeruLayoutTree;
use owned_adapter::OwnedKeruLayoutTree;

struct Dense(KeruLayoutTree);
struct Owned(OwnedKeruLayoutTree, bool);
struct Real(Case, bool);

fn output(edges: impl IntoIterator<Item = [u32; 4]>) -> Vec<NodeOutput> {
    edges
        .into_iter()
        .map(|bits| NodeOutput(Some(bits), 0))
        .collect()
}

impl Solver for Dense {
    fn solve(&mut self) {
        self.0.compute_layout();
    }

    fn output(&self) -> Vec<NodeOutput> {
        output(self.0.rectangle_bits())
    }
}

impl Solver for Owned {
    fn solve(&mut self) {
        if self.1 {
            let stats = self.0.compute_batch().unwrap();
            assert_eq!(
                stats,
                BatchLayoutStats::default(),
                "unexpected first Batch statistics"
            );
        } else {
            std::hint::black_box(self.0.compute_default());
        }
    }

    fn output(&self) -> Vec<NodeOutput> {
        output(self.0.rectangle_bits())
    }
}

impl Solver for Real {
    fn solve(&mut self) {
        if self.1 {
            let stats = self.0.layout_batch();
            assert_eq!(
                stats,
                BatchLayoutStats::default(),
                "unexpected first Batch statistics"
            );
        } else {
            std::hint::black_box(self.0.layout(false));
        }
    }

    fn output(&self) -> Vec<NodeOutput> {
        assert!(
            self.0.tree.warnings().is_empty(),
            "{} warnings",
            self.0.name
        );
        let mut result = Vec::new();
        let mut pending = vec![self.0.tree.root()];
        while let Some(id) = pending.pop() {
            let rect = match self.0.tree.layout(&id) {
                Ok(rect) => {
                    let edges = [rect.x[0], rect.x[1], rect.y[0], rect.y[1]];
                    assert!(edges.iter().all(|edge| edge.is_finite()));
                    Some(edges.map(f32::to_bits))
                }
                Err(TreeError::LayoutUnavailable) => None,
                Err(error) => panic!("{id:?}: {error}"),
            };
            let first = pending.len();
            pending.extend(self.0.tree.children(&id).unwrap().map(NodeId::from));
            pending[first..].reverse();
            result.push(NodeOutput(rect, pending.len() - first));
        }
        result
    }
}

pub fn owned(template: &LayoutNode, mode: bool) -> Box<dyn Solver> {
    let tree = OwnedKeruLayoutTree::new(template, extent(template.width), extent(template.height))
        .unwrap();
    Box::new(Owned(tree, mode))
}

pub fn dense(template: &LayoutNode) -> Box<dyn Solver> {
    let tree =
        KeruLayoutTree::new(template, extent(template.width), extent(template.height)).unwrap();
    Box::new(Dense(tree))
}

fn cases() -> impl Iterator<Item = Case> {
    browser::cases()
        .into_iter()
        .chain(cad::cases())
        .chain(compositor::cases())
}

pub fn real(name: &str, batch: bool) -> Box<dyn Solver> {
    Box::new(Real(cases().find(|case| case.name == name).unwrap(), batch))
}

pub fn names() -> Vec<&'static str> {
    cases().map(|case| case.name).collect()
}

type Edit = dyn FnMut(&mut LayoutTree<String>, usize) -> Xy<f32>;

struct Case {
    name: &'static str,
    period: usize,
    tree: LayoutTree<String>,
    viewport: Xy<f32>,
    edit: Box<Edit>,
}

impl Case {
    fn layout_batch(&mut self) -> keru_layout::BatchLayoutStats {
        self.tree
            .solve_layout_batch_with_measure(self.viewport, measure_monospace_text)
            .unwrap_or_else(|error| panic!("{} batch layout: {error}", self.name))
    }

    fn layout(&mut self, batch: bool) -> IncrementalRelayoutOutcome {
        if batch {
            let result = self.layout_batch();
            let computed = u32::try_from(result.computed).unwrap_or(u32::MAX);
            return IncrementalRelayoutOutcome::Success { computed };
        }
        self.tree
            .solve_layout_with_measure(self.viewport, measure_monospace_text)
    }
}
