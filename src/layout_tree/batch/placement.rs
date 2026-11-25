use super::super::{LayoutNode, solve_frame};
use super::{Frame, Host, Node, NodeKey, State};
use crate::placement_work::PlacementWork;
use crate::{Axis, ChildrenLayout, LayoutParams, NodeLayoutData, SameInput, Size, TreeAdapter};
use slotmap::SlotMap;

impl State {
    pub(super) fn note_visibility(
        &mut self,
        key: NodeKey,
        old: &LayoutParams,
        new: &LayoutParams,
    ) -> bool {
        if old.disabled == new.disabled {
            return false;
        }
        let Some(frame) = self.frame.as_mut().filter(|frame| frame.covers_visibility) else {
            return false;
        };
        let Some(&row) = frame.indices.get(&key) else {
            return false;
        };
        let old_with_new_visibility = LayoutParams {
            disabled: new.disabled,
            ..*old
        };
        if !solve_frame::same_sizing_inputs(old_with_new_visibility, *new) {
            return false;
        }
        if self.visibility_roots.try_reserve(1).is_err() {
            return false;
        }
        self.visibility_roots.push(key);
        // Refresh needs the last settled flag to detect changes inherited
        // by descendants or canceled by another edit before the next solve.
        frame.params[row] = LayoutParams {
            disabled: frame.params[row].disabled,
            ..*new
        };
        self.visibility_dirty = true;
        if !old_with_new_visibility.same_input(new) {
            self.queue_placement(key);
        }
        true
    }

    pub(super) fn note_placement(
        &mut self,
        key: NodeKey,
        old: &LayoutParams,
        new: &LayoutParams,
    ) -> bool {
        if !solve_frame::same_sizing_inputs(*old, *new) {
            return false;
        }
        self.queue_placement(key);
        true
    }

    fn queue_placement(&mut self, key: NodeKey) {
        if self.placement_edits.try_reserve(1).is_ok() {
            self.placement_edits.push(key);
        } else {
            self.output_changed();
        }
    }

    pub(in crate::layout_tree) fn can_retain_reorder(
        &self,
        parent: NodeKey,
        params: &LayoutParams,
    ) -> bool {
        // A permutation of the same in-flow children preserves the request
        // set for a Stack or Free container. Placement of other containers
        // can also publish child-specific sizing state.
        !self.graph_dirty
            && !params.disabled
            && matches!(
                params.children_layout,
                ChildrenLayout::Free | ChildrenLayout::Stack { .. }
            )
            && self.frame.as_ref().is_some_and(|frame| {
                frame
                    .indices
                    .get(&parent)
                    .is_some_and(|&row| !frame.records[row].flags.is_block_item())
            })
    }

    pub(in crate::layout_tree) fn retain_reorder(
        &mut self,
        records: &SlotMap<NodeKey, LayoutNode>,
        touched: [Option<NodeKey>; 4],
        parent: NodeKey,
        layout: ChildrenLayout,
    ) {
        let Some(frame) = &mut self.frame else {
            return;
        };
        let mut staged = [None; 4];
        for (slot, key) in staged.iter_mut().zip(touched) {
            let Some(key) = key else { continue };
            let Some((row, node)) = frame.updated_sibling_links(records, key) else {
                return;
            };
            *slot = Some((row, node));
        }
        frame.stack_placement.invalidate();
        frame.stack_fit.invalidate();
        frame.stack_shares.invalidate();
        for (row, node) in staged.into_iter().flatten() {
            frame.nodes[row] = Some(node);
        }
        self.graph_dirty = false;
        let parent_style = &records[parent].params;
        if has_intrinsic_declaration(parent_style) || matches!(layout, ChildrenLayout::Stack { .. })
        {
            // Recompute the parent producers because in-flow sizes are folded
            // in sibling order. Always refresh placement of the reordered stack.
            if self.reordered.try_reserve(1).is_ok() {
                self.reordered.push(parent);
            } else {
                self.invalidate();
            }
            self.queue_placement(parent);
        }
    }
}

pub(super) fn has_intrinsic_declaration(params: &LayoutParams) -> bool {
    [
        Some(params.size.x),
        Some(params.size.y),
        params.min_size.x,
        params.min_size.y,
        params.max_size.x,
        params.max_size.y,
    ]
    .into_iter()
    .any(|size| matches!(size, Some(Size::FitContent | Size::Auto)))
}

impl Frame {
    pub(super) fn visibility_reuse<A: TreeAdapter<NodeId = NodeKey>>(
        &self,
        source: &A,
        roots: &[NodeKey],
        last_parked: Option<usize>,
    ) -> (Option<usize>, bool) {
        let [key] = roots else { return (None, false) };
        let Some(&row) = self.indices.get(key) else {
            return (None, false);
        };
        let Some(parent) = self.nodes[row].and_then(Node::parent) else {
            return (None, false);
        };
        let parent_style = &self.params[parent];
        // A Free parent with nonintrinsic sizes keeps the same sizing inputs
        // while one of its ordinary children is hidden.
        if !matches!(parent_style.children_layout, ChildrenLayout::Free)
            || has_intrinsic_declaration(parent_style)
        {
            return (None, false);
        }
        let old_disabled = self.params[row].disabled;
        let disabled = source.node_layout_params(*key).disabled;
        (
            (disabled && !old_disabled).then_some(row),
            !disabled && old_disabled && last_parked == Some(row),
        )
    }

    pub(super) fn mark_visibility_change<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &A,
        row: usize,
        enabled: bool,
    ) {
        if let Some(parent) = self.nodes[row].and_then(Node::parent) {
            let Some(node) = self.nodes[parent] else {
                return;
            };
            // Read the final inherited flag even if refresh has not reached
            // this parent yet. Hidden paths do not have placement work.
            let parent_style = source.node_layout_params(node.key);
            if parent_style.disabled {
                return;
            }
            if !self.params[row].free_placement
                && !matches!(parent_style.children_layout, ChildrenLayout::Free)
            {
                mark_subtree(&self.nodes, &mut self.records, parent);
                return;
            }
        }
        if enabled {
            mark_subtree(&self.nodes, &mut self.records, row);
        }
    }

    fn updated_sibling_links(
        &self,
        records: &SlotMap<NodeKey, LayoutNode>,
        key: NodeKey,
    ) -> Option<(usize, Node)> {
        let row = *self.indices.get(&key)?;
        let old = self.nodes[row]?;
        let record = records.get(key)?;
        let resolve = |link| match link {
            None => Some(None),
            Some(key) => self.indices.get(&key).copied().map(Some),
        };
        if old.parent() != resolve(record.parent)? {
            return None;
        }
        let links = Node::new(
            old.key,
            old.parent(),
            resolve(record.first_child)?,
            resolve(record.next_sibling)?,
        )
        .ok()?;
        Some((row, links))
    }

    pub(super) fn place_dirty<A: TreeAdapter<NodeId = NodeKey>>(
        &mut self,
        source: &mut A,
        edits: &[NodeKey],
    ) {
        self.stack_placement.note_dirty_marks();
        for key in edits {
            let Some(&node) = self.indices.get(key) else {
                continue;
            };
            if !self.params[node].disabled {
                mark_subtree(&self.nodes, &mut self.records, node);
            }
        }
        if self.records[self.root].placement == PlacementWork::Clean {
            return;
        }
        if self.place_start_stacks(source, true) {
            return;
        }
        self.place_general::<_, true>(source, false);
    }
}

impl<A: TreeAdapter<NodeId = NodeKey>> Host<'_, A> {
    pub(super) fn mark_sized_output(&mut self, node: usize, affects_siblings: bool) {
        self.mark_output(node, affects_siblings, None);
    }

    pub(super) fn mark_final_output(&mut self, node: usize, axis: Axis) {
        self.mark_output(node, true, Some(axis));
    }

    fn mark_output(&mut self, node: usize, affects_siblings: bool, final_axis: Option<Axis>) {
        if self.records[self.root].placement == PlacementWork::Subtree {
            return;
        }
        let style = self.node_layout_params(node);
        let affected = if affects_siblings && !style.free_placement {
            self.parent(node)
                .filter(
                    |&parent| match self.node_layout_params(parent).children_layout {
                        ChildrenLayout::Free => false,
                        // A Stack cursor reads only its main-axis child sizes.
                        ChildrenLayout::Stack { axis, .. } => {
                            final_axis.is_none_or(|changed| changed == axis)
                        }
                        _ => true,
                    },
                )
                .unwrap_or(node)
        } else {
            node
        };
        mark_subtree(self.nodes, self.records, affected);
    }
}

fn mark_subtree(nodes: &[Option<Node>], records: &mut [NodeLayoutData], node: usize) {
    if records[node].placement == PlacementWork::Subtree {
        return;
    }
    records[node].mark_placement_changed();
    let mut parent = nodes[node].and_then(Node::parent);
    while let Some(id) = parent {
        let record = &mut records[id];
        if record.placement != PlacementWork::Clean {
            // Every path already marked here extends to the root.
            break;
        }
        record.placement = record.placement.with_child(PlacementWork::Subtree, false);
        parent = nodes[id].and_then(Node::parent);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Anchor, Arrange, BatchLayoutStats, Destination, LayoutTree, MainAxisCellSize, PixelScale,
        Pos, WindowOverflow, Xy,
    };

    fn fixed() -> LayoutParams {
        LayoutParams {
            size: Xy::new(Size::Pixels(26.375), Size::Pixels(17.125)),
            position: Xy::new_symm(Pos::Start),
            ..LayoutParams::DEFAULT
        }
    }

    fn capture_batch(tree: &mut LayoutTree, viewport: Xy<f32>) {
        assert_eq!(
            tree.solve_layout_batch(viewport).unwrap(),
            BatchLayoutStats::default()
        );
        tree.invalidate();
        assert!(tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
    }

    fn assert_fresh_bits(tree: &LayoutTree, viewport: Xy<f32>) {
        let mut fresh = tree.clone();
        fresh.invalidate();
        fresh.solve_layout(viewport);
        let bits = |tree: &LayoutTree| {
            let mut pending = vec![tree.root()];
            let mut output = Vec::new();
            while let Some(node) = pending.pop() {
                output.push(
                    tree.layout(&node)
                        .ok()
                        .map(|rect| [rect.x.map(f32::to_bits), rect.y.map(f32::to_bits)]),
                );
                let first = pending.len();
                pending.extend(tree.children(&node).unwrap().map(Into::into));
                pending[first..].reverse();
            }
            output
        };
        assert_eq!(bits(tree), bits(&fresh));
    }

    #[test]
    fn local_placement_keeps_exact_rectangles_through_rounding_and_coupled_ancestors() {
        for mode in [
            ChildrenLayout::Free,
            ChildrenLayout::Stack {
                axis: Axis::Y,
                spacing: 1.375,
                arrange: Arrange::Center,
            },
            ChildrenLayout::Wrap {
                axis: Axis::X,
                spacing: 1.75,
                line_spacing: 2.625,
                arrange: Arrange::End,
            },
            ChildrenLayout::Block,
            ChildrenLayout::Grid {
                columns: MainAxisCellSize::Count(2),
                spacing_x: 3.125,
                spacing_y: 2.375,
                main_axis: Axis::X,
                backfill: false,
            },
        ] {
            let mut tree = LayoutTree::<()>::new();
            let root = tree.root();
            tree.set_pixel_scale(Some(PixelScale::try_from(1.25).unwrap()));
            tree.update_node_params(
                &root,
                LayoutParams {
                    children_layout: mode,
                    padding: Xy::new_symm([1.375, 2.625]),
                    ..LayoutParams::DEFAULT
                },
            )
            .unwrap();
            tree.add_node(&root, fixed()).unwrap();
            let branch = tree
                .add_node(
                    &root,
                    LayoutParams {
                        children_layout: ChildrenLayout::Stack {
                            axis: Axis::X,
                            arrange: Arrange::Start,
                            spacing: 1.75,
                        },
                        ..fixed()
                    },
                )
                .unwrap();
            tree.add_node(
                &branch,
                LayoutParams {
                    size: Xy::new_symm(Size::Pixels(6.125)),
                    ..fixed()
                },
            )
            .unwrap();
            let free = tree
                .add_node(
                    &root,
                    LayoutParams {
                        free_placement: true,
                        ..fixed()
                    },
                )
                .unwrap();
            let viewport = Xy::new(74.25, 83.75);
            capture_batch(&mut tree, viewport);

            let mut style = *tree.params(&branch).unwrap();
            style.position.x = Pos::End;
            style.children_origin_flipped.x = true;
            tree.update_node_params(&branch, style).unwrap();
            let mut style = *tree.params(&free).unwrap();
            style.position.x = Pos::Pixels(99.25);
            style.anchor.x = Anchor::Center;
            style.window_overflow.x = WindowOverflow::Clamp;
            tree.update_node_params(&free, style).unwrap();
            let stats = tree.solve_layout_batch(viewport).unwrap();
            assert!(!stats.rebuilt_graph && stats.computed == 0);
            assert_fresh_bits(&tree, viewport);
        }
    }

    #[test]
    fn reorder_updates_the_retained_walk_for_later_local_placement() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let left = tree.add_node(&root, fixed()).unwrap();
        let right = tree.add_node(&root, fixed()).unwrap();
        let child = tree.add_node(&left, fixed()).unwrap();
        let viewport = Xy::new(120.0, 200.0);
        capture_batch(&mut tree, viewport);
        tree.move_node(&left, Destination::LastChildOf(&root))
            .unwrap();
        let stats = tree.solve_layout_batch(viewport).unwrap();
        assert!(!stats.rebuilt_graph && stats.computed == 0);
        assert_eq!(tree.children(&root).unwrap().next(), Some(right));

        let mut style = *tree.params(&child).unwrap();
        style.position = Xy::new(Pos::End, Pos::Pixels(7.5));
        tree.update_node_params(&child, style).unwrap();
        tree.solve_layout_batch(viewport).unwrap();
        assert_fresh_bits(&tree, viewport);
    }

    #[test]
    fn visibility_edits_reflow_siblings_and_publish_newly_enabled_children() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let viewport = Xy::new(120.0, 200.0);
        tree.set_pixel_scale(Some(PixelScale::try_from(1.25).unwrap()));
        tree.update_node_params(
            &root,
            LayoutParams {
                children_layout: ChildrenLayout::Stack {
                    axis: Axis::Y,
                    arrange: Arrange::Start,
                    spacing: 3.25,
                },
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
        let mut style = fixed();
        let branch = tree.add_node(&root, style).unwrap();
        let nested = tree.add_node(&branch, fixed()).unwrap();
        let sibling = tree.add_node(&root, fixed()).unwrap();
        capture_batch(&mut tree, viewport);
        let baseline = tree.layout(&sibling).unwrap();
        for disabled in [true, false, true, false] {
            style.disabled = disabled;
            tree.update_node_params(&branch, style).unwrap();
            assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
            assert_eq!(tree.layout(&nested).is_err(), disabled);
            assert_eq!(tree.layout(&sibling).unwrap() == baseline, !disabled);
            assert_fresh_bits(&tree, viewport);
        }

        // A later pose edit to the hidden node must preserve its old
        // visibility as a pending change for the enclosing Stack.
        style.disabled = true;
        tree.update_node_params(&branch, style).unwrap();
        style.position.x = Pos::Pixels(48.375);
        tree.update_node_params(&branch, style).unwrap();
        assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
        assert_ne!(tree.layout(&sibling).unwrap(), baseline);
        assert_fresh_bits(&tree, viewport);
    }

    #[test]
    fn a_placement_edit_followed_by_hiding_can_be_published_when_reenabled() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let viewport = Xy::new(120.0, 200.0);
        let mut style = fixed();
        let child = tree.add_node(&root, style).unwrap();
        capture_batch(&mut tree, viewport);
        style.position.x = Pos::Pixels(15.5);
        tree.update_node_params(&child, style).unwrap();
        style.disabled = true;
        tree.update_node_params(&child, style).unwrap();
        assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
        assert!(tree.layout(&child).is_err());
        style.disabled = false;
        tree.update_node_params(&child, style).unwrap();
        assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
        assert!(tree.layout(&child).is_ok());
        assert_fresh_bits(&tree, viewport);
    }

    #[test]
    fn visibility_and_placement_edits_share_the_retained_order() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let viewport = Xy::new(120.5, 200.25);
        tree.set_pixel_scale(PixelScale::new(1.5));
        let mut style = LayoutParams {
            disabled: true,
            ..fixed()
        };
        let popup = tree.add_node(&root, style).unwrap();
        let child = tree.add_node(&popup, fixed()).unwrap();
        capture_batch(&mut tree, viewport);
        assert!(tree.layout(&popup).is_err());

        style.disabled = false;
        style.position = Xy::new(Pos::Pixels(110.75), Pos::Pixels(19.375));
        style.window_overflow.x = WindowOverflow::Clamp;
        tree.update_node_params(&popup, style).unwrap();
        assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
        assert_fresh_bits(&tree, viewport);
        let before = tree.layout(&child).unwrap();

        style.disabled = true;
        tree.update_node_params(&popup, style).unwrap();
        style.position.y = Pos::Pixels(58.625);
        tree.update_node_params(&popup, style).unwrap();
        style.disabled = false;
        tree.update_node_params(&popup, style).unwrap();
        assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
        assert_ne!(tree.layout(&child).unwrap(), before);
        assert_fresh_bits(&tree, viewport);
    }

    #[test]
    fn a_free_parent_can_still_read_visible_child_sizes() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let viewport = Xy::new(120.5, 200.25);
        let parent = tree
            .add_node(
                &root,
                LayoutParams {
                    size: Xy::new(Size::FitContent, Size::Pixels(60.0)),
                    ..LayoutParams::DEFAULT
                },
            )
            .unwrap();
        let mut style = fixed();
        let visible = tree.add_node(&parent, style).unwrap();
        tree.add_node(
            &parent,
            LayoutParams {
                size: Xy::new(Size::Pixels(8.0), Size::Pixels(6.0)),
                ..fixed()
            },
        )
        .unwrap();
        capture_batch(&mut tree, viewport);
        let before = tree.layout(&parent).unwrap();
        style.disabled = true;
        tree.update_node_params(&visible, style).unwrap();
        assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
        assert_ne!(tree.layout(&parent).unwrap(), before);
        assert_fresh_bits(&tree, viewport);
    }

    #[test]
    fn a_parked_free_branch_reuses_sizes_until_inputs_change() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let viewport = Xy::new(120.5, 200.25);
        let mut style = fixed();
        let popup = tree.add_node(&root, style).unwrap();
        let label = tree
            .add_node(
                &popup,
                LayoutParams {
                    size: Xy::new_symm(Size::FitContent),
                    text: crate::TextContent::Fixed,
                    ..fixed()
                },
            )
            .unwrap();
        let measure = |_, content: Option<&mut ()>, _| {
            Xy::new(if content.is_some() { 40.0 } else { 23.0 }, 12.0)
        };
        let first = tree
            .solve_layout_batch_with_measure(viewport, measure)
            .unwrap();
        assert_eq!(first, BatchLayoutStats::default());
        tree.invalidate();
        let captured = tree
            .solve_layout_batch_with_measure(viewport, measure)
            .unwrap();
        assert!(captured.rebuilt_graph);
        let before = tree.layout(&label).unwrap();
        style.disabled = true;
        tree.update_node_params(&popup, style).unwrap();
        tree.solve_layout_batch_with_measure(viewport, measure)
            .unwrap();
        style.disabled = false;
        tree.update_node_params(&popup, style).unwrap();
        let stats = tree
            .solve_layout_batch_with_measure(viewport, measure)
            .unwrap();
        assert!(!stats.rebuilt_graph && stats.computed == 0);
        assert_eq!(tree.layout(&label).unwrap(), before);

        style.disabled = true;
        tree.update_node_params(&popup, style).unwrap();
        tree.solve_layout_batch_with_measure(viewport, measure)
            .unwrap();
        tree.update_node_context(&label, Some(())).unwrap();
        tree.solve_layout_batch_with_measure(viewport, measure)
            .unwrap();
        style.disabled = false;
        tree.update_node_params(&popup, style).unwrap();
        let stats = tree
            .solve_layout_batch_with_measure(viewport, measure)
            .unwrap();
        assert!(!stats.rebuilt_graph && stats.computed > 0);
        let rect = tree.layout(&label).unwrap();
        assert_eq!(rect.x[1] - rect.x[0], 40.0);
    }

    #[test]
    fn stack_reorder_keeps_the_order_and_updates_sibling_geometry() {
        for scale in [None, PixelScale::new(1.3)] {
            let viewport = Xy::new_symm(122.375);
            let mut tree = LayoutTree::<()>::new();
            tree.set_pixel_scale(scale);
            let root = tree.root();
            let parent = tree
                .add_node(
                    &root,
                    LayoutParams {
                        size: Xy::new_symm(Size::FitContent),
                        position: Xy::new_symm(Pos::Start),
                        children_layout: ChildrenLayout::Stack {
                            axis: Axis::X,
                            spacing: 1.375,
                            arrange: Arrange::Start,
                        },
                        ..LayoutParams::DEFAULT
                    },
                )
                .unwrap();
            let first = tree.add_node(&parent, fixed()).unwrap();
            let second = tree.add_node(&parent, fixed()).unwrap();
            capture_batch(&mut tree, viewport);
            let before = tree.layout(&first).unwrap();
            tree.move_node(&second, Destination::Before(&first))
                .unwrap();
            let stats = tree.solve_layout_batch(viewport).unwrap();
            assert!(!stats.rebuilt_graph);
            assert_ne!(tree.layout(&first).unwrap(), before);
            assert_fresh_bits(&tree, viewport);
        }
    }

    #[test]
    fn stack_reorder_recomputes_share_in_the_new_sibling_order() {
        let viewport = Xy::new(16_777_216.0, 200.0);
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let mut style = *tree.params(&root).unwrap();
        style.children_layout = ChildrenLayout::Stack {
            axis: Axis::X,
            arrange: Arrange::Start,
            spacing: 0.0,
        };
        tree.update_node_params(&root, style).unwrap();
        let child = |size| LayoutParams {
            size: Xy::new(size, Size::Pixels(12.0)),
            ..fixed()
        };
        let fill = tree.add_node(&root, child(Size::Fill)).unwrap();
        let large = tree
            .add_node(&root, child(Size::Pixels(8_388_608.0)))
            .unwrap();
        let small = [
            tree.add_node(&root, child(Size::Pixels(0.5))).unwrap(),
            tree.add_node(&root, child(Size::Pixels(0.5))).unwrap(),
        ];
        capture_batch(&mut tree, viewport);
        let before = tree.layout(&fill).unwrap();
        for node in small {
            tree.move_node(&node, Destination::Before(&large)).unwrap();
        }
        assert!(!tree.solve_layout_batch(viewport).unwrap().rebuilt_graph);
        assert_ne!(tree.layout(&fill).unwrap(), before);
        assert_fresh_bits(&tree, viewport);
    }
}
