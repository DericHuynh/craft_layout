mod state;

use state::{PriorNode, PriorStyle, TicketModel, TicketWriter};
use crate::structural_changes::{ChildCursor, StructuralChange, advance_tickets, parent_change, ticket_index};
use crate::work_stack::work_stack;
use crate::{Incremental, LayoutParams, NodeLayoutData, SameInput, TreeAdapter};

// A cached node record can be detached, recycled, or brought in from another
// adapter. Disjoint ticket ranges distinguish it from the current snapshot in
// all of those cases. Reserve once per snapshot, independent of tree size.
#[cfg(target_has_atomic = "64")]
fn reserve_tickets(count: usize) -> Option<u64> {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(1);
    let mut first = NEXT.load(Ordering::Relaxed);
    loop {
        let next = advance_tickets(first, count)?;
        match NEXT.compare_exchange_weak(first, next, Ordering::Relaxed, Ordering::Relaxed) {
            Ok(_) => return Some(first),
            Err(current) => first = current,
        }
    }
}

#[cfg(not(target_has_atomic = "64"))]
fn reserve_tickets(count: usize) -> Option<u64> {
    use std::sync::Mutex;
    static NEXT: Mutex<u64> = Mutex::new(1);
    let mut next = NEXT.lock().unwrap_or_else(std::sync::PoisonError::into_inner);
    let first = *next;
    *next = advance_tickets(first, count)?;
    Some(first)
}

#[derive(Clone, Debug)]
pub(crate) struct TopologySnapshot<I> {
    first_ticket: u64,
    nodes: Vec<PriorNode<I>>,
    // Capture coalesces consecutive equal declarations. A later style edit
    // splits a shared entry or overwrites a private one in place.
    styles: Vec<PriorStyle<LayoutParams>>,
}

impl<T: TreeAdapter + ?Sized> TicketModel for T {
    type Id = T::NodeId;
}

impl<T: TreeAdapter + ?Sized> TicketWriter for T {
    #[inline]
    fn write_ticket(&mut self, id: T::NodeId, ticket: u64) {
        self.node_layout_data_mut(id).topology_index = ticket;
    }
}

impl<I: Eq> TopologySnapshot<I> {
    fn index(&self, id: I, ticket: u64) -> Option<usize> {
        let index = ticket_index(self.first_ticket, self.nodes.len(), ticket)?;
        (self.nodes.get(index)?.id == id).then_some(index)
    }

    pub(crate) fn restore_region_tickets<T: TreeAdapter<NodeId = I> + ?Sized>(
        &self, tree: &mut T, root: I, ticket: u64,
    ) -> bool
    where
        I: Copy,
    {
        let Some(start) = self.index(root, ticket) else { return false };
        if state::restoration_end(&self.nodes, start, self.first_ticket).is_none() { return false; }
        state::restore_region(tree, &self.nodes, start, self.first_ticket);
        true
    }
}

impl<I> TopologySnapshot<I> {
    pub(crate) const fn new() -> Self {
        Self { first_ticket: 1, nodes: Vec::new(), styles: Vec::new() }
    }

    fn store_style(&mut self, params: &LayoutParams) -> usize {
        if let Some(last) = self.styles.last_mut() && last.params.same_input(params) {
            last.uses += 1;
        } else {
            self.styles.push(PriorStyle { params: *params, uses: 1 });
        }
        self.styles.len() - 1
    }

    fn update_style(&mut self, index: usize, params: LayoutParams) {
        state::update_style(&mut self.nodes, &mut self.styles, index, params);
    }
}

const ROOT_PARENT: usize = usize::MAX;

/// Records style edits while the old snapshot is still read-only.
pub(crate) struct ReconcileState<'a, I> {
    current: bool,
    styles: &'a mut Vec<I>,
}

#[derive(Clone, Copy)]
pub(crate) struct ReconcileFrame<I> {
    node: I,
    index: Option<usize>,
    end: usize,
    cursor: ChildCursor,
}

type ReconcileStart<I> = (ReconcileFrame<I>, Option<I>);

impl<I> ReconcileFrame<I> {
    #[inline]
    fn advance_child(&mut self, child: Option<usize>, snapshot: &TopologySnapshot<I>) -> Option<()> {
        let following = if self.cursor.expected < self.end {
            let end = snapshot.nodes.get(self.cursor.expected)?.end;
            if end <= self.cursor.expected || end > self.end { return None; }
            Some(end)
        } else {
            None
        };
        self.cursor = self.cursor.observe(child, following);
        Some(())
    }
}

pub(crate) trait Topology: TreeAdapter {
    fn remember_topology(&mut self) {
        self.remember_topology_with(reserve_tickets);
    }

    fn remember_topology_with(&mut self, reserve: impl FnOnce(usize) -> Option<u64>) {
        let data = self.layout_data();
        if !data.track_topology { return }
        let Some(mut snapshot) = data.topology.take() else { return };
        snapshot.nodes.clear();
        snapshot.styles.clear();
        snapshot.nodes.reserve(self.layout_data().n_nodes_solved as usize);
        let root = self.root();
        let params = self.node_layout_params(root);
        let style = snapshot.store_style(params);
        snapshot.nodes.push(PriorNode { id: root, parent: ROOT_PARENT, end: 1, style });
        if !params.disabled {
            self.capture_descendants(root, &mut snapshot);
            snapshot.nodes[0].end = snapshot.nodes.len();
        }

        if let Some(first) = reserve(snapshot.nodes.len()) {
            snapshot.first_ticket = first;
            state::restore_tickets(self, &snapshot.nodes, first);
        } else {
            // No ticket range is available. An empty snapshot selects untracked
            // reconciliation next time and cannot match any old tickets.
            snapshot.nodes.clear();
            snapshot.styles.clear();
        }
        self.layout_data().topology = Some(snapshot);
    }

    fn capture_descendants(&self, root: Self::NodeId, snapshot: &mut TopologySnapshot<Self::NodeId>) {
        let mut parent = 0;
        let mut next = self.first_child(root);
        loop {
            if let Some(node) = next {
                let params = self.node_layout_params(node);
                let style = snapshot.store_style(params);
                let index = snapshot.nodes.len();
                // Leaves already have their final end. The saved parent index
                // lets a branch return without a recursive call or a stack.
                snapshot.nodes.push(PriorNode { id: node, parent, end: index + 1, style });
                if !params.disabled && let Some(first) = self.first_child(node) {
                    parent = index;
                    next = Some(first);
                    continue;
                }
                next = self.next_sibling(node);
            } else {
                if parent == 0 { break; }
                let (closed, enclosing) = state::close_branch(&mut snapshot.nodes, parent);
                parent = enclosing;
                next = self.next_sibling(closed);
            }
        }
    }

    fn update_remembered_params(&mut self, node: Self::NodeId, old: &LayoutParams) {
        let ticket = self.node_layout_data(node).topology_index;
        if ticket == 0 { return }
        let params = *self.node_layout_params(node);
        let Some(snapshot) = self.layout_data().topology.as_mut() else { return };
        let Some(index) = snapshot.index(node, ticket) else { return };
        let style = &mut snapshot.styles[snapshot.nodes[index].style];
        // An earlier unlocalized edit may not have been reconciled yet. Only
        // advance a baseline that describes the caller's registered transition.
        if style.params.same_input(old) && !style.params.same_input(&params) {
            snapshot.update_style(index, params);
        }
    }

    fn reconcile_topology(&mut self, styles: &mut Vec<Self::NodeId>) -> bool {
        let Some(mut snapshot) = self.layout_data().topology.take() else { return false };
        let mut state = ReconcileState { current: !snapshot.nodes.is_empty(), styles };
        let available = state.current && self.reconcile_subtree(self.root(), Some(ROOT_PARENT), &snapshot, &mut state).is_some();
        let available = available && (!state.current || state.styles.iter().all(|&id| {
            let ticket = self.node_layout_data(id).topology_index;
            let Some(index) = snapshot.index(id, ticket) else { return false };
            let style = snapshot.nodes[index].style;
            if !snapshot.styles.get(style).is_some_and(|entry| entry.uses > 0) { return false; }
            snapshot.update_style(index, *self.node_layout_params(id));
            true
        }));
        if !available {
            // An explicit full solve with no retained output or host measurements
            // needs no side table. On its first unlocalized edit, derive independent
            // pixel sizes from the live declarations and rebuild the uncertain regions.
            state.current = false;
            snapshot.nodes.clear();
            snapshot.styles.clear();
            self.reconcile_untracked(self.root());
        }
        state.styles.clear();
        self.layout_data().topology = Some(snapshot);
        state.current
    }

    fn reconcile_untracked(&mut self, root: Self::NodeId) {
        let mut next = Some(root);
        while let Some(node) = next {
            let params = self.node_layout_params(node);
            let first = self.first_child(node);
            let disabled = params.disabled;
            let fixed = self.node_layout_data(node).unchanged_pixel_box(params, first.is_none());
            let data = self.node_layout_data_mut(node);
            if let Some(fixed) = fixed {
                *data = fixed;
                if first.is_some() { data.mark_children_changed(); }
            } else {
                data.mark_subtree_changed();
            }
            next = crate::tree_walk::next(
                node, !disabled, |_| first, |id| self.next_sibling(id),
                |id| self.parent(id), |id| id == root,
            );
        }
    }

    fn mark_attached(&mut self, node: Self::NodeId) {
        let ticket = self.node_layout_data(node).topology_index;
        let Some(snapshot) = self.layout_data().topology.as_ref() else {
            self.node_layout_data_mut(node).mark_subtree_changed();
            return;
        };
        let prior = snapshot.index(node, ticket)
            .map(|index| snapshot.styles[snapshot.nodes[index].style].params);
        if prior.is_some_and(|params| !params.disabled && params.same_input(self.node_layout_params(node))) {
            self.node_layout_data_mut(node).mark_moved();
            return;
        }
        let data = self.node_layout_data_mut(node);
        if prior.is_none() {
            // Cached descendant slots and block-margin indices can predate a
            // detachment or come from another tree. Prepare this subtree afresh.
            *data = NodeLayoutData::new();
        }
        data.mark_subtree_changed();
    }

    // Only the current traversal supplies IDs to adapter methods. The old child
    // list is traversed entirely by indices, even if its nodes have been deleted.
    fn reconcile_subtree(
        &mut self, node: Self::NodeId, parent: Option<usize>, snapshot: &TopologySnapshot<Self::NodeId>,
        state: &mut ReconcileState<'_, Self::NodeId>,
    ) -> Option<()> {
        let mut suspended = work_stack::<_, 8>(Vec::new());
        let (mut frame, mut next) = self.enter_reconcile_node(node, parent, snapshot, state)?;
        loop {
            if let Some(child) = next {
                let expected = frame.cursor.expected;
                if !frame.cursor.changed && expected < frame.end {
                    let entry = snapshot.nodes.get(expected)?;
                    if entry.end == expected + 1
                        && self.node_layout_data(child).topology_index == advance_tickets(snapshot.first_ticket, expected)?
                        && entry.id == child
                    {
                        let old = &snapshot.styles.get(entry.style)?.params;
                        // An unchanged leaf only advances the parent's old cursor.
                        if old.same_input(self.node_layout_params(child)) && (old.disabled || self.first_child(child).is_none()) {
                            frame.cursor = frame.cursor.observe(Some(expected), Some(entry.end));
                            next = self.next_sibling(child);
                            continue;
                        }
                    }
                }

                let (child_frame, first) = self.enter_reconcile_node(child, frame.index, snapshot, state)?;
                if first.is_some() {
                    suspended.push(frame);
                    frame = child_frame;
                    next = first;
                    continue;
                }
                self.finish_reconcile_node(child_frame, state);
                frame.advance_child(child_frame.index, snapshot)?;
                next = self.next_sibling(child);
            } else {
                self.finish_reconcile_node(frame, state);
                let Some(mut enclosing) = suspended.pop() else { return Some(()) };
                enclosing.advance_child(frame.index, snapshot)?;
                next = self.next_sibling(frame.node);
                frame = enclosing;
            }
        }
    }

    fn enter_reconcile_node(
        &mut self, node: Self::NodeId, parent: Option<usize>, snapshot: &TopologySnapshot<Self::NodeId>,
        state: &mut ReconcileState<'_, Self::NodeId>,
    ) -> Option<ReconcileStart<Self::NodeId>> {
        let index = snapshot.index(node, self.node_layout_data(node).topology_index);
        let prior = index.map(|index| &snapshot.nodes[index]);
        let reusable = if let Some(entry) = prior {
            let old = &snapshot.styles.get(entry.style)?.params;
            let params = self.node_layout_params(node);
            let changed = !old.same_input(params);
            if changed {
                if old.disabled != params.disabled {
                    state.current = false;
                }
                if state.current {
                    state.styles.push(node);
                }
                self.incr_register_node_change(node, old);
            }
            !old.disabled && !changed
        } else {
            false
        };
        match parent_change(prior.map(|entry| entry.parent), parent, reusable) {
            StructuralChange::Subtree => {
                state.current = false;
                self.node_layout_data_mut(node).mark_subtree_changed();
            }
            StructuralChange::Moved => {
                state.current = false;
                self.node_layout_data_mut(node).mark_moved();
            }
            _ => {}
        }
        let disabled = self.node_layout_params(node).disabled;
        let (end, expected, first) = if disabled {
            (0, 0, None)
        } else {
            let end = prior.map_or(0, |entry| entry.end);
            let expected = index.map_or(0, |index| index + 1);
            if end < expected || end > snapshot.nodes.len() { return None; }
            (end, expected, self.first_child(node))
        };
        let cursor = ChildCursor { expected, changed: false };
        Some((ReconcileFrame { node, index, end, cursor }, first))
    }

    #[inline]
    fn finish_reconcile_node(&mut self, frame: ReconcileFrame<Self::NodeId>, state: &mut ReconcileState<'_, Self::NodeId>) {
        if frame.cursor.needs_invalidation(frame.end) {
            state.current = false;
            self.node_layout_data_mut(frame.node).mark_children_changed();
        }
    }
}

impl<T: TreeAdapter + ?Sized> Topology for T {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Arrange, Axis, ChildrenLayout, LayoutData, Pos, Size, Xy, XyRect};

    struct Adapter {
        next: [Option<usize>; 7],
        first: [Option<usize>; 7],
        parent: [Option<usize>; 7],
        params: [LayoutParams; 7],
        records: [NodeLayoutData; 7],
        output: [Option<(XyRect, XyRect)>; 7],
        layout: LayoutData<usize>,
    }

    impl TreeAdapter for Adapter {
        type NodeId = usize;
        fn root(&self) -> usize { 0 }
        fn parent(&self, id: usize) -> Option<usize> { self.parent[id] }
        fn first_child(&self, id: usize) -> Option<usize> { self.first[id] }
        fn next_sibling(&self, id: usize) -> Option<usize> { self.next[id] }
        fn node_layout_params(&self, id: usize) -> &LayoutParams { &self.params[id] }
        fn node_layout_data(&self, id: usize) -> &NodeLayoutData { &self.records[id] }
        fn node_layout_data_mut(&mut self, id: usize) -> &mut NodeLayoutData { &mut self.records[id] }
        fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }
        fn retains_output_rects(&self) -> bool { true }
        fn write_output_rect(&mut self, id: usize, r: XyRect, l: XyRect) { self.output[id] = Some((r,l)); }
    }

    fn validate(tree: &Adapter, order: &[usize], window: Xy<f32>) -> u64 {
        let snapshot = tree.layout.topology.as_ref().unwrap();
        assert!(snapshot.nodes.iter().map(|entry| entry.id).eq(order.iter().copied()));
        for (index,entry) in snapshot.nodes.iter().enumerate() {
            assert_eq!(snapshot.index(entry.id, tree.records[entry.id].topology_index), Some(index));
            assert!(snapshot.styles[entry.style].params.same_input(&tree.params[entry.id]));
        }
        for (index,style) in snapshot.styles.iter().enumerate() {
            assert_eq!(style.uses, snapshot.nodes.iter().filter(|entry| entry.style==index).count());
        }
        let mut fresh=Adapter {
            next:tree.next, first:tree.first, parent:tree.parent, params:tree.params,
            records:[NodeLayoutData::new();7], output:[None;7], layout:LayoutData::new(),
        };
        fresh.solve_layout(window);
        let bits = |r: XyRect, l: XyRect| [r.x, r.y, l.x, l.y].map(|pair| pair.map(f32::to_bits));
        for &id in order {
            if tree.params[id].disabled {continue;}
            let (r,l)=tree.output[id].unwrap();
            let (fr,fl)=fresh.output[id].unwrap();
            assert_eq!(bits(r,l),bits(fr,fl));
        }
        snapshot.first_ticket
    }

    #[test]
    fn style_rounds_keep_tickets_then_reorders_and_recycled_ids_rebuild() {
        let mut tree = Adapter {
            next: [None,Some(2),Some(3),None,Some(5),Some(6),None],
            first: [Some(1),Some(4),None,None,None,None,None],
            parent: [None,Some(0),Some(0),Some(0),Some(1),Some(1),Some(1)],
            params:[LayoutParams {
                size:Xy::new(Size::Pixels(20.0),Size::Pixels(10.0)),
                position:Xy::new_symm(Pos::Start),..LayoutParams::DEFAULT
            };7],
            records:[NodeLayoutData::new();7], output:[None;7], layout:LayoutData::new(),
        };
        for id in [0,1] {
            tree.params[id].children_layout=ChildrenLayout::Stack {axis:Axis::X,arrange:Arrange::Start,spacing:1.0};
        }
        let window=Xy::new(200.0,150.0);
        tree.solve_layout_incremental(window);
        let initial=[0,1,4,5,6,2,3];
        let ticket=validate(&tree,&initial,window);
        for round in 0..20 {
            tree.params[0].size.x=Size::Pixels(100.0+round as f32);
            tree.params[4].size.x=Size::Pixels(17.0+round as f32);
            tree.params[5].size.y=Size::Pixels(14.0+round as f32);
            tree.register_structural_change();
            tree.solve_layout_incremental(window);
            assert_eq!(validate(&tree,&initial,window),ticket,"round {round}");
        }

        tree.next[4]=Some(6);
        tree.next[6]=Some(5);
        tree.next[5]=None;
        tree.register_structural_change();
        tree.solve_layout_incremental(window);
        let changed=[0,1,4,6,5,2,3];
        let reordered=validate(&tree,&changed,window);
        assert_ne!(reordered,ticket);

        tree.records[5]=NodeLayoutData::new();
        tree.output[5]=None;
        tree.params[5].padding.x[0]=0.5;
        tree.register_structural_change();
        tree.solve_layout_incremental(window);
        let recycled=validate(&tree,&changed,window);
        assert_ne!(recycled,reordered);

        tree.params[0].size.x=Size::Pixels(99.5);
        tree.register_structural_change();
        tree.solve_layout_incremental(window);
        assert_eq!(validate(&tree,&changed,window),recycled);
    }

    #[test]
    fn ticket_exhaustion_keeps_untracked_reconciliation_available() {
        let mut tree = Adapter {
            next: [None, Some(2), None, None, None, None, None],
            first: [Some(1), None, None, None, None, None, None],
            parent: [None, Some(0), Some(0), None, None, None, None],
            params: [LayoutParams::DEFAULT; 7],
            records: [NodeLayoutData::new(); 7], output: [None; 7], layout: LayoutData::new(),
        };
        tree.params[0].children_layout = ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 1.0 };
        tree.params[1].size.x = Size::Pixels(20.0);
        tree.params[2].size.x = Size::Pixels(30.0);
        let window = Xy::new(200.0, 150.0);
        tree.solve_layout_incremental(window);
        let first = validate(&tree, &[0, 1, 2], window);

        let next = u64::MAX - 1;
        tree.remember_topology_with(|count| advance_tickets(next, count).map(|_| next));
        let snapshot = tree.layout.topology.as_ref().unwrap();
        assert!(snapshot.nodes.is_empty());
        assert!(snapshot.styles.is_empty());
        assert_eq!(snapshot.index(0, first), None);
        assert_eq!(tree.records[0].topology_index, first);

        tree.first[0] = Some(2);
        tree.next[2] = Some(1);
        tree.next[1] = None;
        tree.params[1].size.x = Size::Pixels(25.0);
        tree.register_structural_change();
        tree.solve_layout_incremental(window);
        assert_ne!(validate(&tree, &[0, 2, 1], window), first);
    }

    #[test]
    fn deep_capture_and_reconciliation_use_no_recursive_walk() {
        struct Chain {
            params: LayoutParams,
            records: Vec<NodeLayoutData>,
            layout: LayoutData<usize>,
        }

        impl TreeAdapter for Chain {
            type NodeId = usize;
            fn root(&self) -> usize { 0 }
            fn parent(&self, id: usize) -> Option<usize> { id.checked_sub(1) }
            fn first_child(&self, id: usize) -> Option<usize> {
                let child = id + 1;
                (child < self.records.len()).then_some(child)
            }
            fn next_sibling(&self, _: usize) -> Option<usize> { None }
            fn node_layout_params(&self, _: usize) -> &LayoutParams { &self.params }
            fn node_layout_data(&self, id: usize) -> &NodeLayoutData { &self.records[id] }
            fn node_layout_data_mut(&mut self, id: usize) -> &mut NodeLayoutData { &mut self.records[id] }
            fn layout_data(&mut self) -> &mut LayoutData<usize> { &mut self.layout }
            fn write_output_rect(&mut self, _: usize, _: XyRect, _: XyRect) {}
        }

        std::thread::Builder::new().stack_size(256 * 1024).spawn(|| {
            const LEN: usize = 8_192;
            let mut tree = Chain {
                params: LayoutParams::DEFAULT,
                records: vec![NodeLayoutData::new(); LEN],
                layout: LayoutData { track_topology: true, ..LayoutData::new() },
            };
            tree.remember_topology();
            let snapshot = tree.layout.topology.as_ref().unwrap();
            assert_eq!(snapshot.nodes.len(), LEN);
            for (index, node) in snapshot.nodes.iter().enumerate() {
                assert_eq!(node.id, index);
                assert_eq!(node.parent, index.checked_sub(1).unwrap_or(ROOT_PARENT));
                assert_eq!(node.end, LEN);
            }

            let mut styles = Vec::new();
            assert!(tree.reconcile_topology(&mut styles));
            assert!(tree.records.iter().all(|record| record.structural_change == StructuralChange::Clean));

            // An unavailable old range must clear the snapshot and use the
            // live walk, including on a chain deeper than the thread stack.
            tree.layout.topology.as_mut().unwrap().nodes[0].end = usize::MAX;
            assert!(!tree.reconcile_topology(&mut styles));
            assert!(tree.layout.topology.as_ref().unwrap().nodes.is_empty());
            assert!(tree.records.iter().all(|record| record.structural_change == StructuralChange::Subtree));
        }).unwrap().join().unwrap();
    }
}
