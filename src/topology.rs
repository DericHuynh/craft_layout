mod state;
mod reconcile;
mod tracked;

use state::{CaptureModel, CaptureSource, LiveTicketWriter, PriorNode, PriorStyle, ROOT_PARENT, TicketModel, TicketWriter};
use crate::structural_changes::{StructuralChange, advance_tickets};
use crate::{Incremental, LayoutParams, NodeLayoutData, SameInput, TreeAdapter};
use crate::vec_memory::{FallibleVecMemory, RustVec, try_append};

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
    reconcile_spill: Vec<tracked::Frame<I>>,
}

impl<T: TreeAdapter + ?Sized> TicketModel for T {
    type Id = T::NodeId;
}

impl<T: TreeAdapter + ?Sized> TicketWriter for T {
    #[inline]
    fn write_ticket(&mut self, id: T::NodeId, ticket: u64) {
        self.node_layout_data_mut(id).set_topology_index(ticket);
    }
}

impl<T: TreeAdapter + ?Sized> LiveTicketWriter for T {
    #[inline]
    fn next_in_region(&self, root: T::NodeId, id: T::NodeId) -> Option<T::NodeId> {
        let child = if self.node_layout_params(id).disabled { None } else { self.first_child(id) };
        crate::tree_walk::next_forward(self, root, id, child)
    }

    #[inline]
    fn same_id(&self, a: T::NodeId, b: T::NodeId) -> bool {
        a == b
    }
}

/// The capture loop owns the node vector. Style storage is written through
/// this source because each appended row also takes a style reference.
struct CaptureSnapshot<'a, T: ?Sized> {
    tree: &'a T,
    styles: &'a mut Vec<PriorStyle<LayoutParams>>,
}

impl<T: TreeAdapter + ?Sized> TicketModel for CaptureSnapshot<'_, T> {
    type Id = T::NodeId;
}

impl<T: TreeAdapter + ?Sized> CaptureModel for CaptureSnapshot<'_, T> {}

impl<T: TreeAdapter + ?Sized> CaptureSource for CaptureSnapshot<'_, T> {
    fn first_child_to_capture(&self, id: T::NodeId) -> Option<T::NodeId> {
        if self.tree.node_layout_params(id).disabled { None } else { self.tree.first_child(id) }
    }

    fn following_sibling(&self, id: T::NodeId) -> Option<T::NodeId> {
        self.tree.next_sibling(id)
    }

    fn append(&mut self, nodes: &mut Vec<PriorNode<T::NodeId>>, id: T::NodeId, parent: usize, end: usize) -> bool {
        if !RustVec::try_reserve(nodes, 1) { return false; }
        let params = self.tree.node_layout_params(id);
        let matches_last = self.styles.last().is_some_and(|last| last.params.same_input(params));
        let Some(style) = state::add_style::<_, RustVec>(self.styles, *params, matches_last) else { return false; };
        state::append_row::<_, RustVec>(nodes, id, parent, end, style);
        true
    }
}

struct ProjectTopology<'a, T: ?Sized>(&'a mut T);

impl<T: TreeAdapter + ?Sized> reconcile::Model for ProjectTopology<'_, T> {
    type Id = T::NodeId;
    type Cache = NodeLayoutData;
}

impl<T: TreeAdapter + ?Sized> reconcile::Access for ProjectTopology<'_, T> {
    #[inline]
    fn inspect(&self, node: T::NodeId) -> (Option<T::NodeId>, bool, Option<NodeLayoutData>) {
        let params = self.0.node_layout_params(node);
        let first = self.0.first_child(node);
        let fixed = self.0.node_layout_data(node).unchanged_pixel_box(params, first.is_none());
        (first, params.disabled, fixed)
    }

    #[inline]
    fn apply(&mut self, node: T::NodeId, projection: reconcile::Projection<NodeLayoutData>) {
        let data = self.0.node_layout_data_mut(node);
        match projection {
            reconcile::Projection::Retain(fixed) => *data = fixed,
            reconcile::Projection::RefreshChildren(fixed) => {
                *data = fixed;
                data.mark_children_changed();
            }
            reconcile::Projection::Rebuild => data.mark_subtree_changed(),
        }
    }

    #[inline]
    fn successor(&self, root: T::NodeId, node: T::NodeId, child: Option<T::NodeId>) -> Option<T::NodeId> {
        crate::tree_walk::next_forward(&*self.0, root, node, child)
    }
}

impl<I: Eq> TopologySnapshot<I> {
    fn index(&self, id: I, ticket: u64) -> Option<usize> {
        let (index, row) = state::ticket_row(&self.nodes, self.first_ticket, ticket)?;
        (row.id == id).then_some(index)
    }

    pub(crate) fn restore_region_tickets<T: TreeAdapter<NodeId = I> + ?Sized>(
        &self, tree: &mut T, root: I, ticket: u64,
    ) -> bool
    where
        I: Copy,
    {
        let Some(start) = self.index(root, ticket) else { return false };
        state::restore_region(tree, &self.nodes, start, self.first_ticket, root)
    }
}

impl<I> TopologySnapshot<I> {
    pub(crate) const fn new() -> Self {
        Self { first_ticket: 1, nodes: Vec::new(), styles: Vec::new(), reconcile_spill: Vec::new() }
    }

    fn prior_style(&self, index: usize) -> Option<&PriorStyle<LayoutParams>> {
        state::style_row(&self.nodes, &self.styles, index)
    }

    fn update_style(&mut self, index: usize, params: LayoutParams) -> bool {
        state::update_style::<_, _, RustVec>(&mut self.nodes, &mut self.styles, index, params)
    }
}

/// Records style edits while the old snapshot is still read-only.
pub(crate) struct ReconcileState<'a, I> {
    current: bool,
    styles: &'a mut Vec<I>,
}

struct ReconcileWalk<'a, 'b, T: TreeAdapter + ?Sized> {
    tree: &'a mut T,
    state: &'a mut ReconcileState<'b, T::NodeId>,
}

impl<T: TreeAdapter + ?Sized> tracked::Model for ReconcileWalk<'_, '_, T> {
    type Id = T::NodeId;
    type Style = LayoutParams;
}

impl<T: TreeAdapter + ?Sized> tracked::Access for ReconcileWalk<'_, '_, T> {
    #[inline]
    fn ticket(&self, node: T::NodeId) -> u64 {
        self.tree.node_layout_data(node).topology_index()
    }

    #[inline]
    fn same_id(&self, live: T::NodeId, prior: T::NodeId) -> bool { prior == live }

    #[inline]
    fn read_style(&self, node: T::NodeId) -> &LayoutParams { self.tree.node_layout_params(node) }

    #[inline]
    fn is_disabled(&self, style: &LayoutParams) -> bool { style.disabled }

    #[inline]
    fn same_style(&self, live: &LayoutParams, prior: &LayoutParams) -> bool { prior.same_input(live) }

    #[inline]
    fn first(&self, node: T::NodeId) -> Option<T::NodeId> { self.tree.first_child(node) }

    #[inline]
    fn invalidate_snapshot(&mut self) { self.state.current = false; }

    #[inline]
    fn remember_style_if_current(&mut self, node: T::NodeId) {
        if self.state.current && !try_append::<_, RustVec>(self.state.styles, node) {
            self.state.current = false;
        }
    }

    #[inline]
    fn register_style_change(&mut self, node: T::NodeId, prior: &LayoutParams) {
        self.tree.incr_register_node_change(node, prior);
    }

    #[inline]
    fn mark_parent_change(&mut self, node: T::NodeId, mark: StructuralChange) {
        self.state.current = false;
        let data = self.tree.node_layout_data_mut(node);
        match mark {
            StructuralChange::Subtree => data.mark_subtree_changed(),
            StructuralChange::Moved => data.mark_moved(),
            _ => {}
        }
    }

    #[inline]
    fn following(&self, child: T::NodeId) -> Option<T::NodeId> {
        self.tree.next_sibling(child)
    }

    #[inline]
    fn mark_children_changed(&mut self, node: T::NodeId) {
        self.state.current = false;
        self.tree.node_layout_data_mut(node).mark_children_changed();
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
        // This reservation is only a capacity hint. The capture checks each
        // actual append and can abandon optional topology tracking on failure.
        let _ = snapshot.nodes.try_reserve(self.layout_data().n_nodes_solved as usize);
        let root = self.root();
        let mut capture = CaptureSnapshot { tree: &*self, styles: &mut snapshot.styles };
        let captured = state::capture_subtree(&mut capture, &mut snapshot.nodes, root);

        if captured && let Some(first) = reserve(snapshot.nodes.len())
            && state::restoration_end(&snapshot.nodes, 0, first).is_some()
        {
            snapshot.first_ticket = first;
            state::restore_tickets(self, &snapshot.nodes, first);
        } else {
            // No complete snapshot is available. An empty snapshot selects untracked
            // reconciliation next time and cannot match any old tickets.
            snapshot.nodes.clear();
            snapshot.styles.clear();
        }
        self.layout_data().topology = Some(snapshot);
    }

    fn update_remembered_params(&mut self, node: Self::NodeId, old: &LayoutParams) {
        let ticket = self.node_layout_data(node).topology_index();
        if ticket == 0 { return }
        let params = *self.node_layout_params(node);
        let Some(snapshot) = self.layout_data().topology.as_mut() else { return };
        let Some(index) = snapshot.index(node, ticket) else { return };
        let Some(style) = snapshot.prior_style(index) else {
            snapshot.nodes.clear();
            snapshot.styles.clear();
            return;
        };
        // An earlier unlocalized edit may not have been reconciled yet. Only
        // advance a baseline that describes the caller's registered transition.
        if style.params.same_input(old) && !style.params.same_input(&params) {
            if !snapshot.update_style(index, params) {
                snapshot.nodes.clear();
                snapshot.styles.clear();
            }
        }
    }

    fn reconcile_topology(&mut self, styles: &mut Vec<Self::NodeId>) -> bool {
        let Some(mut snapshot) = self.layout_data().topology.take() else { return false };
        let mut state = ReconcileState { current: !snapshot.nodes.is_empty(), styles };
        let available = state.current && self.reconcile_subtree(self.root(), Some(ROOT_PARENT), &mut snapshot, &mut state).is_some();
        let available = available && (!state.current || state.styles.iter().all(|&id| {
            let ticket = self.node_layout_data(id).topology_index();
            let Some(index) = snapshot.index(id, ticket) else { return false };
            snapshot.update_style(index, *self.node_layout_params(id))
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
        reconcile::project(&mut ProjectTopology(self), root);
    }

    fn mark_attached(&mut self, node: Self::NodeId) {
        let ticket = self.node_layout_data(node).topology_index();
        let Some(snapshot) = self.layout_data().topology.as_ref() else {
            self.node_layout_data_mut(node).mark_subtree_changed();
            return;
        };
        let prior = snapshot.index(node, ticket)
            .and_then(|index| snapshot.prior_style(index))
            .map(|style| style.params);
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
        &mut self, node: Self::NodeId, parent: Option<usize>, snapshot: &mut TopologySnapshot<Self::NodeId>,
        state: &mut ReconcileState<'_, Self::NodeId>,
    ) -> Option<()> {
        tracked::track_reusing::<_, RustVec>(
            &mut ReconcileWalk { tree: self, state },
            node, parent, &snapshot.nodes, &snapshot.styles, snapshot.first_ticket,
            &mut snapshot.reconcile_spill,
        )
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
            assert_eq!(snapshot.index(entry.id, tree.records[entry.id].topology_index()), Some(index));
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
    fn regional_ticket_restore_never_writes_a_stale_snapshot_id() {
        let mut tree = Adapter {
            next: [None; 7],
            first: [Some(1), None, None, None, None, None, None],
            parent: [None, Some(0), None, None, None, None, None],
            params: [LayoutParams::DEFAULT; 7],
            records: [NodeLayoutData::new(); 7],
            output: [None; 7],
            layout: LayoutData::new(),
        };
        let first_ticket = (1_u64 << 32) + 5;
        let snapshot = TopologySnapshot {
            first_ticket,
            nodes: vec![
                PriorNode { id: 0, parent: ROOT_PARENT, end: 2, style: 0 },
                PriorNode { id: usize::MAX, parent: 0, end: 2, style: 0 },
            ],
            ..TopologySnapshot::new()
        };
        assert!(!snapshot.restore_region_tickets(&mut tree, 0, first_ticket));
        assert_eq!(tree.records[0].topology_index(), first_ticket);
        assert_eq!(tree.records[1].topology_index(), 0);
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
        assert_eq!(tree.records[0].topology_index(), first);

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
            let spill = &tree.layout.topology.as_ref().unwrap().reconcile_spill;
            assert!(!spill.is_empty());
            let storage = spill.as_ptr();
            assert!(tree.reconcile_topology(&mut styles));
            assert_eq!(tree.layout.topology.as_ref().unwrap().reconcile_spill.as_ptr(), storage);
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
