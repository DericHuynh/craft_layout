//! Exercise placement directly, including suspension at every level of a deep tree.
use super::*;

// Each branch has a first child continuing the chain and a trailing leaf.
// The five parent layout modes alternate going down the chain.
struct DeepTree {
    depth: usize,
    params: [LayoutParams; 5],
    data: Vec<NodeLayoutData>,
    layout: LayoutData<usize>,
    order: Vec<usize>,
}

impl DeepTree {
    fn new(depth: usize) -> Self {
        let mut data = NodeLayoutData::new();
        for axis in [X, Y] {
            for kind in [Kind::Regular, Kind::Final] {
                data.flags.set_state(axis, kind, SOLVED);
                data.values[slot_index(axis, kind)] = 8.0;
            }
        }
        data.n_placed_children = 2;
        let layouts = [
            ChildrenLayout::Free,
            ChildrenLayout::Stack { axis: X, arrange: Arrange::Center, spacing: 0.25 },
            ChildrenLayout::Wrap { axis: Y, arrange: Arrange::Start, spacing: 0.5, line_spacing: 0.75 },
            ChildrenLayout::Block,
            ChildrenLayout::Grid { columns: MainAxisCellSize::Count(1), main_axis: X, spacing_x: 0.5, spacing_y: 0.5, backfill: false },
        ];
        let params = layouts.map(|children_layout| LayoutParams {
            children_layout, size: Xy::new_symm(Size::Pixels(8.0)), ..LayoutParams::DEFAULT
        });
        Self { depth, params, data: vec![data; depth * 2 + 1], layout: LayoutData::new(), order: Vec::new() }
    }
}

impl TreeAdapter for DeepTree {
    type NodeId = usize;
    fn root(&self) -> usize { 0 }
    fn parent(&self, i: usize) -> Option<usize> {
        match i {
            0 => None,
            _ if i <= self.depth => Some(i - 1),
            _ => Some(i - self.depth - 1),
        }
    }
    fn first_child(&self, i: usize) -> Option<usize> { (i < self.depth).then_some(i + 1) }
    fn next_sibling(&self, i: usize) -> Option<usize> {
        (i != 0 && i <= self.depth).then_some(self.depth + i)
    }
    fn node_layout_params(&self, i: usize) -> &LayoutParams { &self.params[i % self.params.len()] }
    fn node_layout_data(&self, i: usize) -> &NodeLayoutData { &self.data[i] }
    fn node_layout_data_mut(&mut self, i: usize) -> &mut NodeLayoutData { &mut self.data[i] }
    fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }
    fn write_output_rect(&mut self, i: usize, _: XyRect, _: XyRect) { self.order.push(i); }
}

#[test]
fn deep_placement_keeps_preorder_on_a_small_thread_stack() {
    std::thread::Builder::new().stack_size(128 * 1024).spawn(|| {
        let depth = 10_000;
        let mut tree = DeepTree::new(depth);
        tree.layout.set_pixel_scale(Some(PixelScale::new(1.5).unwrap()));
        let expected: Vec<_> = (0..=depth).chain((depth + 1..=2 * depth).rev()).collect();
        tree.place_nodes::<false>();
        assert_eq!(tree.order, expected);

        tree.order.clear();
        tree.place_free_placed_subtree(1, Xy::new_symm([0.0, 8.0])).unwrap();
        // The root and its last child are outside this subtree.
        assert_eq!(tree.order, expected[1..expected.len() - 1]);

        #[cfg(feature = "incremental")]
        {
            tree.order.clear();
            for data in &mut tree.data[..depth] { data.placement = PlacementWork::Descendants; }
            tree.data[depth].placement = PlacementWork::Subtree;
            tree.place_nodes::<true>();
            assert_eq!(tree.order, [depth]);
        }
    }).unwrap().join().unwrap();
}
