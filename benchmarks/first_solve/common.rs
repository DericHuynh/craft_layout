pub mod pangui_template;

use pangui_template::{BenchmarkSize, SizeMode};

pub trait Solver {
    fn solve(&mut self);
    fn output(&self) -> Vec<NodeOutput>;
}

#[derive(Debug, PartialEq, Eq)]
pub struct NodeOutput(pub Option<[u32; 4]>, pub usize);

pub fn extent(size: Option<BenchmarkSize>) -> f32 {
    match size {
        Some(BenchmarkSize {
            mode: SizeMode::Pixels,
            value,
        }) => value,
        _ => 1_000.0,
    }
}
