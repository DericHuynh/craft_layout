mod svg;
mod stack_tail;
pub(crate) mod solve_frame;
mod removal;
mod links;
mod text_scan;
mod text_measure_cache;
mod id;
mod structural_guard;
mod output;
mod records;
#[cfg(target_arch = "x86_64")]
mod ascii_width;

use crate::*;
use crate::node_data::next_dormant_grid_epoch;
use slotmap::{DefaultKey, Key, SlotMap, new_key_type};
use stack_tail::StackTail;
use solve_frame::TailEdits;
use std::sync::Arc;
use id::TreeIdentity;
pub use id::{ChildId, Destination, NodeId, TreeError};
use structural_guard::{BindContext, ContextModel, HandleLookup, HandleModel, InsertionArena, InsertionModel,
    incarnation, insert_optional_entry, insert_record, next_incarnation,
    rectangle_available, reserve_entries, resolve_record, root_capacity};
#[cfg(test)]
use structural_guard::RECT_PUBLISHED;

new_key_type! {
    pub(crate) struct NodeKey;
}

const ROOT_INCARNATION: u64 = 0;

pub(crate) type LayoutNode = records::Node<NodeKey, DefaultKey>;

/// A tree of layout nodes. It records the changes to the nodes, and `solve_layout` uses them to do an incremental relayout when it can.
///
/// `T` is the type of the context of each node, for example its text. The measure function of `solve_layout_with_measure` receives it.
///
/// The tree always has a root node. It starts as `Size::Fill` on both axes, so it covers the whole `window_size` given to `solve_layout`. All other nodes are descendants of the root.
///
/// Handles are checked before an edit takes effect. Cloning creates an independent
/// tree, starting with the same declarations and last published layout. Its
/// first solve refreshes measurements in the new handle namespace.
#[derive(Debug)]
pub struct LayoutTree<T = ()> {
    pub(crate) nodes: SlotMap<NodeKey, LayoutNode>,
    contexts: Option<SlotMap<DefaultKey, T>>,
    text_heights: text_measure_cache::Cache,
    dormant_grid_epoch: u32,
    root: NodeKey,
    owner: Arc<TreeIdentity>,
    next_incarnation: u64,
    pub(crate) layout_data: LayoutData<NodeKey>,
    warnings: Vec<LayoutWarning<NodeId>>,
    tail_edits: TailEdits<NodeKey>,
    tail_stack: Option<StackTail>,
}

impl<T: Clone> Clone for LayoutTree<T> {
    fn clone(&self) -> Self {
        let owner = Arc::new(TreeIdentity { root: self.root });
        let warnings = self.warnings.iter().cloned().map(|warning| {
            warning.map_node(|id| NodeId::new(&owner, id.key(), id.incarnation()))
        }).collect();
        let mut layout_data = self.layout_data.clone();
        // Measurement callbacks may use the full public ID as an input.
        layout_data.request_full_solve(IncrementalRelayoutOutcome::FallbackInvalidated);
        Self {
            nodes: self.nodes.clone(),
            contexts: self.contexts.clone(),
            text_heights: text_measure_cache::Cache::new::<crate::vec_memory::RustVec>(),
            dormant_grid_epoch: next_dormant_grid_epoch(self.dormant_grid_epoch),
            root: self.root,
            owner,
            next_incarnation: self.next_incarnation,
            layout_data,
            warnings,
            tail_edits: TailEdits::Other,
            tail_stack: None,
        }
    }
}

impl<T> Default for LayoutTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> LayoutTree<T> {
    /// Makes a tree that contains only the root.
    pub fn new() -> Self {
        Self::from_arena(SlotMap::with_capacity_and_key(16))
    }

    /// Makes a tree that contains only the root, with space for `capacity` nodes.
    /// The context arena allocates when a node first receives a context.
    pub fn with_capacity(capacity: usize) -> Result<Self, TreeError> {
        let capacity = root_capacity(capacity).ok_or(TreeError::Capacity)?;
        let mut nodes = SlotMap::with_key();
        reserve_entries(&mut nodes, capacity)?;
        Ok(Self::from_arena(nodes))
    }

    fn from_arena(mut nodes: SlotMap<NodeKey, LayoutNode>) -> Self {
        let root = nodes.insert_reserved(LayoutNode::new(LayoutParams::DEFAULT, ROOT_INCARNATION));
        // All mutations pass through this tree's localized registration methods.
        let layout_data = LayoutData { topology: None, ..LayoutData::new() };
        LayoutTree {
            nodes, contexts: None, text_heights: text_measure_cache::Cache::new::<crate::vec_memory::RustVec>(),
            dormant_grid_epoch: 1,
            root, owner: Arc::new(TreeIdentity { root }),
            next_incarnation: 1, layout_data, warnings: Vec::new(),
            tail_edits: TailEdits::Other, tail_stack: None,
        }
    }

    pub(crate) fn node_id(&self, key: NodeKey) -> NodeId {
        // A diagnostic about an absent key can still carry a permanently
        // stale handle. Only the root ever uses incarnation zero.
        let identity = self.nodes.get(key).map_or(ROOT_INCARNATION, |node| node.identity);
        NodeId::new(&self.owner, key, incarnation(identity))
    }

    fn resolve_node(&self, id: &NodeId) -> Result<&LayoutNode, TreeError> {
        resolve_record(self, id.belongs_to(&self.owner), id.key(), id.incarnation())
    }

    fn raw_handle(&self, node: &NodeId) -> links::relocate::Handle<NodeKey> {
        links::relocate::Handle {
            same_owner: node.belongs_to(&self.owner),
            key: node.key(),
            incarnation: node.incarnation(),
        }
    }

    fn resolve_child(&self, child: &ChildId) -> Result<(NodeKey, NodeKey, &LayoutNode), TreeError> {
        links::relocate::resolve_child(self, self.raw_handle(child))
    }

    /// Get the `NodeId` corresponding to the root node.
    pub fn root(&self) -> NodeId {
        NodeId::new(&self.owner, self.root, ROOT_INCARNATION)
    }

    /// Makes a node, and adds it as the last child of `parent`.
    pub fn add_node(&mut self, parent: &NodeId, params: LayoutParams) -> Result<ChildId, TreeError> {
        self.add_node_inner(parent, params, None)
    }

    /// Makes a node with a context, and adds it as the last child of `parent`.
    pub fn add_node_with_context(&mut self, parent: &NodeId, params: LayoutParams, context: T) -> Result<ChildId, TreeError> {
        self.add_node_inner(parent, params, Some(context))
    }

    /// Moves a node and its descendants. A rejected move leaves the tree unchanged.
    ///
    /// `Destination::Before` takes the destination parent from that sibling.
    pub fn move_node(&mut self, node: &ChildId, destination: Destination<'_>) -> Result<(), TreeError> {
        use links::relocate::MoveDestination;
        let node = self.raw_handle(node);
        let destination = match destination {
            Destination::LastChildOf(parent) => MoveDestination::LastChildOf(self.raw_handle(parent)),
            Destination::Before(sibling) => MoveDestination::Before(self.raw_handle(sibling)),
        };
        let live = self.nodes.len();
        links::relocate::move_handles(self, node, destination, live)
    }

    fn invalidate_dormant_grid(&mut self) {
        self.dormant_grid_epoch = next_dormant_grid_epoch(self.dormant_grid_epoch);
    }

    fn invalidate_hidden_grid_edit(&mut self, id: NodeKey) {
        let Some(node) = self.nodes.get_mut(id) else { return; };
        if node.params.disabled {
            if node.layout.has_dormant_grid() { node.layout = NodeLayoutData::new(); }
            // The hidden edit can affect an ancestor. Expire parked records
            // without searching for that ancestor.
            self.invalidate_dormant_grid();
        }
    }

    fn dormant_grid_axis(&self, id: NodeKey, parent: NodeKey) -> Option<Axis> {
        let node = self.nodes.get(id)?;
        let ChildrenLayout::Grid { main_axis, columns: MainAxisCellSize::Width(_), .. } =
            self.nodes.get(parent)?.params.children_layout
        else { return None; };
        if node.first_child.is_none() || node.params.free_placement
            || !matches!(*node.params.size.component(main_axis), Size::Fill)
            || !matches!(*node.params.size.component(main_axis.other()), Size::Pixels(_) | Size::FitContent)
            || !matches!(node.layout.structural_change, StructuralChange::Clean)
            || node.layout.flags.has_cycle() || node.layout.flags.is_block_item()
            || node.layout.flags.check_state(Axis::X, crate::solve::Kind::Final) != crate::solve::cycle_rules::SOLVED
            || node.layout.flags.check_state(Axis::Y, crate::solve::Kind::Final) != crate::solve::cycle_rules::SOLVED
        { return None; }
        Some(main_axis)
    }

    /// Changes the params of a node. If the parent is disabled, the node stays disabled. A change of `disabled` also applies to all the descendants. Equal params cause no relayout.
    pub fn update_node_params(&mut self, node: &NodeId, mut params: LayoutParams) -> Result<(), TreeError> {
        let i = node.key();
        let parent = self.resolve_node(node)?.parent;
        if let Some(parent) = parent {
            params.disabled |= self.nodes.get(parent).ok_or(TreeError::StaleNode)?.params.disabled;
        }
        let node = self.nodes.get(i).ok_or(TreeError::StaleNode)?;
        if node.params.same_input(&params) {
            return Ok(());
        }
        let placement_only = matches!(self.tail_edits, TailEdits::None | TailEdits::Placement)
            && solve_frame::same_sizing_inputs(node.params, params);
        self.tail_edits = if placement_only { TailEdits::Placement } else { TailEdits::Other };
        let was_disabled = node.params.disabled;
        let disabled_changed = was_disabled != params.disabled;
        let visibility_only = disabled_changed
            && LayoutParams { disabled: params.disabled, ..node.params }.same_input(&params);
        let epoch = self.dormant_grid_epoch;
        let keep_dormant = node.layout.can_restore_dormant_grid(
            visibility_only, params.disabled, self.layout_data.pending_full_solve.is_none(), epoch,
        );
        let park = if visibility_only && params.disabled && epoch != 0 && self.layout_data.pending_full_solve.is_none() {
            parent.and_then(|id| self.dormant_grid_axis(i, id))
        } else { None };
        if was_disabled && !visibility_only { self.invalidate_hidden_grid_edit(i); }
        let node = self.nodes.get_mut(i).ok_or(TreeError::StaleNode)?;
        if !keep_dormant { node.layout.clear_dormant_grid(); }
        if let Some(axis) = park { node.layout.park_grid(axis, epoch); }
        let structural = self.layout_data.record_node_change(i, &node.params, &params, &mut node.layout);
        if keep_dormant { node.layout.structural_change = StructuralChange::DormantGrid; }
        node.layout.forget_fixed_pixels();
        node.params = params;
        if placement_only {
            solve_frame::mark_parents(self, parent);
        } else if !structural && self.layout_data.pending_full_solve.is_none() {
            // A declaration can change placement even when a size bound
            // keeps its solved dimension identical.
            let affected = match parent {
                Some(parent) if !params.free_placement && self.nodes.get(parent)
                    .is_some_and(|node| !matches!(node.params.children_layout, ChildrenLayout::Free)) => parent,
                _ => i,
            };
            if let Some(node) = self.nodes.get_mut(affected) {
                node.layout.mark_placement_changed();
                let above = node.parent;
                solve_frame::mark_parents(self, above);
            }
        }
        if disabled_changed {
            self.set_subtree_disabled(i, params.disabled);
        }
        if structural && let Some(parent) = self.nodes.get_mut(parent.unwrap_or(i)) {
            self.layout_data.record_children_change(&mut parent.layout);
        }
        Ok(())
    }

    /// Removes a child and all its descendants, invalidating their handles.
    ///
    /// User context destructors run after the subtree has been removed.
    pub fn remove(&mut self, node: &ChildId) -> Result<(), TreeError> {
        let (i, parent, record) = self.resolve_child(node)?;
        let retired_leaf = if self.contexts.is_some() && record.first_child.is_none() { record.context } else { None };
        self.record_tail_edit(i, parent, false);
        self.unlink(i, parent)?;
        if let Some(key) = retired_leaf {
            // A detached leaf has no remaining removal steps. Retire its
            // payload directly so it drops after the handle becomes stale.
            self.nodes.remove(i).ok_or(TreeError::StaleNode)?;
            let retired = self.contexts.as_mut().and_then(|contexts| contexts.remove(key));
            drop(retired);
            return Ok(());
        }
        removal::remove_owned_tree(self, i)
    }

    /// Read the node's `LayoutParams`.
    pub fn params(&self, node: &NodeId) -> Result<&LayoutParams, TreeError> {
        Ok(&self.resolve_node(node)?.params)
    }

    /// Updates the context of a node and invalidates its intrinsic content measurement.
    pub fn update_node_context(&mut self, node: &NodeId, context: Option<T>) -> Result<(), TreeError> {
        let i = node.key();
        let retired = match (self.resolve_node(node)?.context, context) {
            (Some(key), Some(context)) => {
                let old = self.contexts.as_mut().and_then(|contexts| contexts.get_mut(key)).ok_or(TreeError::StaleNode)?;
                Some(std::mem::replace(old, context))
            }
            (Some(key), None) => {
                let retired = self.contexts.as_mut().and_then(|contexts| contexts.remove(key)).ok_or(TreeError::StaleNode)?;
                if let Some(node) = self.nodes.get_mut(i) { node.context = None; }
                Some(retired)
            }
            (None, Some(context)) => {
                let key = self.insert_context(context)?;
                if let Some(node) = self.nodes.get_mut(i) { node.context = Some(key); }
                None
            }
            (None, None) => None,
        };
        self.mark_content_dirty(i);
        drop(retired);
        Ok(())
    }

    fn measurement_inputs(&mut self, key: NodeKey) -> Option<(NodeId, Option<&mut T>)> {
        let node = self.nodes.get(key)?;
        let id = NodeId::new(&self.owner, key, incarnation(node.identity));
        let context = node.context.and_then(|key| self.contexts.as_mut()?.get_mut(key));
        Some((id, context))
    }

    fn context(&self, node: &LayoutNode) -> Option<&T> {
        let key = node.context?;
        self.contexts.as_ref()?.get(key)
    }

    /// Invalidates a node's intrinsic measurement after an in-place text or content edit.
    pub fn mark_content_changed(&mut self, node: &NodeId) -> Result<(), TreeError> {
        self.resolve_node(node)?;
        self.mark_content_dirty(node.key());
        Ok(())
    }

    fn mark_content_dirty(&mut self, i: NodeKey) {
        self.invalidate_hidden_grid_edit(i);
        self.tail_edits = TailEdits::Other;
        if let Some(node) = self.nodes.get_mut(i) {
            self.text_heights.invalidate_node(incarnation(node.identity));
            self.layout_data.record_content_change(i, &mut node.layout);
        }
    }

    /// Makes the next `solve_layout` a full solve. Use it when the measure function changes, for example after a font change.
    pub fn invalidate(&mut self) {
        self.invalidate_dormant_grid();
        self.text_heights.clear::<crate::vec_memory::RustVec>();
        self.layout_data.request_full_solve(IncrementalRelayoutOutcome::FallbackInvalidated);
    }

    /// Enable pixel-grid rounding for output, or disable it with `None`.
    /// The scale is the number of physical pixels per logical pixel.
    pub fn set_pixel_scale(&mut self, pixels_per_logical_pixel: Option<PixelScale>) {
        self.layout_data.set_pixel_scale(pixels_per_logical_pixel);
    }

    /// The parent of a node. Only the root has no parent.
    pub fn parent(&self, node: &NodeId) -> Result<Option<NodeId>, TreeError> {
        let Some(parent) = self.resolve_node(node)?.parent else { return Ok(None); };
        let record = self.nodes.get(parent).ok_or(TreeError::StaleNode)?;
        Ok(Some(NodeId::new(&self.owner, parent, incarnation(record.identity))))
    }

    /// Get an iterator over the node's children.
    pub fn children<'a>(&'a self, node: &NodeId) -> Result<impl Iterator<Item = ChildId> + use<'a, T>, TreeError> {
        let first = self.resolve_node(node)?.first_child;
        Ok(self.child_records(first).map(move |(key, record)| {
            ChildId(NodeId::new(&self.owner, key, incarnation(record.identity)))
        }))
    }

    fn child_records(&self, first: Option<NodeKey>) -> impl Iterator<Item = (NodeKey, &LayoutNode)> + '_ {
        let lookup = |key| self.nodes.get(key).map(|node| (key, node));
        std::iter::successors(first.and_then(lookup), move |(_, node)| node.next_sibling.and_then(lookup))
            .take(self.nodes.len())
    }

    /// The last published rectangle in logical pixels.
    ///
    /// A new node or a disabled node has no available rectangle.
    pub fn layout(&self, node: &NodeId) -> Result<XyRect, TreeError> {
        output::lookup(self, node.belongs_to(&self.owner), node.key(), node.incarnation())
    }

    /// The warnings from the last `solve_layout`. An incremental relayout reports only the warnings of the slots that it computes again.
    pub fn warnings(&self) -> &[LayoutWarning<NodeId>] {
        &self.warnings
    }

    /// Solves the layout. `window_size` is the size of the window, in logical pixels. The text of all nodes measures as zero.
    pub fn solve_layout(&mut self, window_size: Xy<f32>) -> IncrementalRelayoutOutcome {
        self.solve_owned(window_size, |_, _, _| Xy::new_symm(0.0), |_, _, _| Xy::new_symm(0.0), false)
    }

    /// Solves the layout. `window_size` is the size of the window, in logical pixels. `measure` gives the size of the text of a node, with its width optionally fixed to a wrap width.
    /// An unchanged node and width must produce the same measurement bits until
    /// its content or measurer is invalidated. The solver can reuse a measurement
    /// without calling `measure` again.
    pub fn solve_layout_with_measure(&mut self, window_size: Xy<f32>, measure: impl FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>) -> IncrementalRelayoutOutcome {
        self.solve_layout_with_measurers(window_size, measure, |_, _, _| Xy::new_symm(0.0))
    }

    /// Solves the layout using a custom intrinsic content callback and zero text measurements.
    /// Apply the measurement requirements in [`Self::solve_layout_with_measurers`].
    pub fn solve_layout_with_content_measure(
        &mut self,
        window_size: Xy<f32>,
        measure: impl FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
    ) -> IncrementalRelayoutOutcome {
        self.solve_owned(window_size, |_, _, _| Xy::new_symm(0.0), measure, false)
    }

    /// Solves the layout using callbacks for both text and custom intrinsic content.
    /// For unchanged content, each callback must return the same result bits for
    /// the same node and inputs. Call [`Self::mark_content_changed`] after in-place
    /// content edits and [`Self::invalidate`] when a measurer changes.
    pub fn solve_layout_with_measurers(
        &mut self,
        window_size: Xy<f32>,
        text: impl FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>,
        content: impl FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
    ) -> IncrementalRelayoutOutcome {
        self.solve_owned(window_size, text, content, true)
    }

    fn solve_owned(
        &mut self,
        window: Xy<f32>,
        text: impl FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>,
        content: impl FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
        cache_text: bool,
    ) -> IncrementalRelayoutOutcome {
        self.warnings.clear();
        let mut adapter = Adapter::new(self, text, content);
        adapter.cache_text = cache_text;
        solve_frame::run(&mut adapter, window).outcome
    }

    fn insert_context(&mut self, value: T) -> Result<DefaultKey, TreeError> {
        insert_optional_entry(&mut self.contexts, value)
    }

    fn add_node_inner(&mut self, parent: &NodeId, params: LayoutParams, context: Option<T>) -> Result<ChildId, TreeError> {
        let last = self.resolve_node(parent)?.last_child;
        let parent = parent.key();
        let id = self.next_incarnation;
        let next = next_incarnation(self.nodes.len(), id).ok_or(TreeError::Capacity)?;
        let (i, _) = insert_record(&mut self.nodes, &mut self.contexts, LayoutNode::new(params, id), context)?;
        self.next_incarnation = next;
        self.link(i, parent, last, None);
        self.record_tail_edit(i, parent, true);
        self.record_attachment(i, parent);
        Ok(ChildId(NodeId::new(&self.owner, i, id)))
    }

    fn record_attachment(&mut self, i: NodeKey, parent: NodeKey) {
        if self.layout_data.tracks_structure() {
            if let Some(parent) = self.nodes.get_mut(parent) {
                self.layout_data.record_children_change(&mut parent.layout);
            }
            if let Some(node) = self.nodes.get_mut(i) {
                node.layout.mark_subtree_changed();
            }
        }
    }

    fn link(&mut self, i: NodeKey, parent: NodeKey, prev: Option<NodeKey>, next: Option<NodeKey>) {
        use links::relocate::MoveEffects;
        self.before_attach(parent);
        links::attach(self, i, parent, prev, next);
        self.after_attach(i, parent);
    }

    /// Takes a node out of the children of its parent.
    fn unlink(&mut self, i: NodeKey, parent: NodeKey) -> Result<(), TreeError> {
        use links::relocate::MoveEffects;
        if !links::detach(self, i, parent) { return Err(TreeError::StaleNode); }
        self.after_detach(i, parent)
    }

    fn set_subtree_disabled(&mut self, root: NodeKey, disabled: bool) {
        // With an outstanding full solve the active slots can still belong
        // to the previous measurer. Zero cannot certify hidden reuse.
        let epoch = if self.layout_data.pending_full_solve.is_none() { self.dormant_grid_epoch } else { 0 };
        links::set_subtree_visibility(self, root, disabled, epoch);
    }

    // Visit siblings last-to-first, the same order used to paint the SVG.
    fn next_in_subtree(&self, root: NodeKey, i: NodeKey, descend: bool) -> Option<NodeKey> {
        let child = if descend { self.nodes.get(i).and_then(|entry| entry.last_child) } else { None };
        crate::tree_walk::next(self, root, i, child)
    }
}

impl<T> solve_frame::MarkModel for LayoutTree<T> {
    type Id = NodeKey;
}

impl<T> solve_frame::MarkAncestors for LayoutTree<T> {
    #[inline]
    fn mark_ancestor(&mut self, id: NodeKey) -> Option<NodeKey> {
        let record = self.nodes.get_mut(id)?;
        record.layout.placement = record.layout.placement.with_child(PlacementWork::Subtree, false);
        record.parent
    }
}

impl<T> links::VisibilityModel for LayoutTree<T> {}

impl<T> links::VisibilityWalk for LayoutTree<T> {
    fn node_count(&self) -> usize { self.nodes.len() }

    fn change_visibility(&mut self, root: NodeKey, id: NodeKey, disabled: bool, epoch: u32) -> Option<NodeKey> {
        let node = self.nodes.get_mut(id)?;
        links::apply_visibility(&mut node.params.disabled, &mut node.identity, &mut node.layout, root == id, disabled, epoch);
        self.next_in_subtree(root, id, true)
    }
}

// These keys use SlotMap's transparent, non-callback key conversion.
trait OwnedArenaKey: Key {}

impl OwnedArenaKey for NodeKey {}
impl OwnedArenaKey for DefaultKey {}

impl<K: OwnedArenaKey, V> InsertionModel for SlotMap<K, V> {
    type Key = K;
    type Value = V;
}

impl<K: OwnedArenaKey, V> InsertionArena for SlotMap<K, V> {
    #[inline]
    fn empty_slots() -> Self { Self::with_key() }

    #[inline]
    fn count(&self) -> usize { self.len() }

    #[inline]
    fn try_reserve_slots(&mut self, additional: usize) -> Result<(), TreeError> {
        self.try_reserve(additional).map_err(|_| TreeError::Capacity)
    }

    #[inline]
    fn insert_reserved(&mut self, value: V) -> K { self.insert(value) }
}

impl ContextModel<DefaultKey> for LayoutNode {}

impl BindContext<DefaultKey> for LayoutNode {
    #[inline]
    fn bind_context(mut self, key: DefaultKey) -> Self {
        self.context = Some(key);
        self
    }
}

impl<T> HandleModel for LayoutTree<T> {
    type Key = NodeKey;
    type Record = LayoutNode;
}

impl<T> HandleLookup for LayoutTree<T> {
    #[inline]
    fn read_record(&self, key: NodeKey) -> Option<&LayoutNode> {
        self.nodes.get(key)
    }

    #[inline]
    fn identity_word(node: &LayoutNode) -> u64 { node.identity }
}

impl<T> output::Model for LayoutTree<T> {}

impl<T> output::Access for LayoutTree<T> {
    #[inline]
    fn rectangle(record: &LayoutNode) -> (&XyRect, bool) { (&record.rect, record.params.disabled) }
}

impl<T> links::LinkModel for LayoutTree<T> {
    type Id = NodeKey;
}

impl<T> links::relocate::MoveEffects for LayoutTree<T> {
    #[inline]
    fn begin_move(&mut self) { self.tail_edits = TailEdits::Other; }

    #[inline]
    fn same_link(&self, left: Option<NodeKey>, right: Option<NodeKey>) -> bool { left == right }

    #[inline]
    fn after_detach(&mut self, i: NodeKey, parent: NodeKey) -> Result<(), TreeError> {
        if let Some(node) = self.nodes.get_mut(i) { node.layout.clear_dormant_grid(); }
        self.invalidate_hidden_grid_edit(parent);
        let parent = self.nodes.get_mut(parent).ok_or(TreeError::StaleNode)?;
        self.layout_data.record_children_change(&mut parent.layout);
        Ok(())
    }

    #[inline]
    fn before_attach(&mut self, parent: NodeKey) { self.invalidate_hidden_grid_edit(parent); }

    #[inline]
    fn after_attach(&mut self, i: NodeKey, parent: NodeKey) {
        if self.nodes.get(parent).is_some_and(|node| node.params.disabled) {
            self.set_subtree_disabled(i, true);
        }
    }

    #[inline]
    fn finish_move(&mut self, i: NodeKey, parent: NodeKey) {
        if self.layout_data.tracks_structure() {
            if let Some(parent) = self.nodes.get_mut(parent) {
                self.layout_data.record_children_change(&mut parent.layout);
            }
            if let Some(node) = self.nodes.get_mut(i) {
                node.layout.mark_moved();
            }
        }
    }
}

impl<T> links::LinkStore for LayoutTree<T> {
    #[inline]
    fn read_links(&self, key: NodeKey) -> Option<links::Links<NodeKey>> {
        self.nodes.get(key).map(links::project)
    }

    #[inline]
    fn edit_links(&mut self, key: NodeKey, edit: links::Edit<NodeKey>) {
        if let Some(node) = self.nodes.get_mut(key) {
            links::apply(node, edit);
        }
    }
}

impl LayoutNode {
    fn has_published_rect(&self) -> bool {
        rectangle_available(self.identity, self.params.disabled)
    }

    fn new(params: LayoutParams, identity: u64) -> Self {
        Self::initialized(params, identity, NodeLayoutData::new())
    }
}

/// Gives a `LayoutTree` and a measure function to the solver.
struct Adapter<'a, T, M, C> {
    tree: &'a mut LayoutTree<T>,
    text: M,
    content: C,
    cache_text: bool,
    // The solver's borrowed-data interface is total. A missing internal key
    // has no links or callbacks and its writes stay in this adapter.
    missing_layout: NodeLayoutData,
}

impl<'a, T, M, C> Adapter<'a, T, M, C> {
    fn new(tree: &'a mut LayoutTree<T>, text: M, content: C) -> Self {
        Self { tree, text, content, cache_text: false, missing_layout: NodeLayoutData::new() }
    }
}

const MISSING_NODE_PARAMS: LayoutParams = LayoutParams { disabled: true, ..LayoutParams::DEFAULT };

impl<T, M, C> solve_frame::FrameModel for Adapter<'_, T, M, C> {
    type Id = NodeKey;
}

impl<T, M, C> solve_frame::Frame for Adapter<'_, T, M, C>
where
    M: FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>,
    C: FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
{
    fn take_edits(&mut self) -> TailEdits<NodeKey> {
        std::mem::take(&mut self.tree.tail_edits)
    }

    fn try_tail(&mut self, parent: NodeKey, delta: structural_changes::TailDelta<NodeKey>, window: Xy<f32>) -> Option<u32> {
        self.solve_stack_tail(parent, delta, window)
    }

    fn idle_inputs(&self, window: Xy<f32>) -> solve_frame::IdleState {
        let data = &self.tree.layout_data;
        solve_frame::IdleState {
            same_viewport: data.window_size.same_input(&window),
            needs_full_solve: data.pending_full_solve.is_some(),
            sizing_dirty: data.children_changed || !data.node_changes.is_empty() || !data.content_changes.is_empty(),
            scale_changed: data.placement_scale_changed,
            has_cycle: data.has_cycle,
        }
    }

    fn clear_tail(&mut self) { self.tree.tail_stack = None; }

    fn place_retained(&mut self, _window: Xy<f32>) -> crate::place::placement_entry::RootPlacement<NodeKey> {
        self.clear_tail();
        self.place_nodes::<true>()
    }

    fn solve_incremental(&mut self, window: Xy<f32>) -> crate::incremental::FrameResult<NodeKey> {
        crate::incremental::enter_frame(self, window, false)
    }
}

impl<T, M, C> TreeAdapter for Adapter<'_, T, M, C>
where
    M: FnMut(NodeId, Option<&mut T>, Option<f32>) -> Xy<f32>,
    C: FnMut(NodeId, Option<&mut T>, ContentMeasureInput) -> Xy<f32>,
{
    type NodeId = NodeKey;

    fn solve_layout(&mut self, window_size: Xy<f32>) {
        self.solve_full::<true>(window_size);
    }

    fn retains_output_rects(&self) -> bool { true }

    #[inline(always)]
    fn root(&self) -> NodeKey {
        self.tree.root
    }

    #[inline(always)]
    fn parent(&self, i: NodeKey) -> Option<NodeKey> {
        records::lookup(self.tree, i)?.parent
    }

    #[inline(always)]
    fn first_child(&self, i: NodeKey) -> Option<NodeKey> {
        records::lookup(self.tree, i)?.first
    }

    #[inline(always)]
    fn next_sibling(&self, i: NodeKey) -> Option<NodeKey> {
        records::lookup(self.tree, i)?.next
    }

    #[inline(always)]
    fn node_layout_params(&self, i: NodeKey) -> &LayoutParams {
        match records::lookup(self.tree, i) {
            Some(node) => node.params,
            None => &MISSING_NODE_PARAMS,
        }
    }

    #[inline(always)]
    fn node_layout_data(&self, i: NodeKey) -> &NodeLayoutData {
        match records::lookup(self.tree, i) {
            Some(node) => node.layout,
            None => &self.missing_layout,
        }
    }

    #[inline(always)]
    fn node_layout_data_mut(&mut self, i: NodeKey) -> &mut NodeLayoutData {
        match self.tree.nodes.get_mut(i) {
            Some(node) => node.sizing_mut(),
            None => &mut self.missing_layout,
        }
    }

    #[inline(always)]
    fn layout_data(&mut self) -> &mut LayoutData<NodeKey> {
        &mut self.tree.layout_data
    }

    fn measure_text_width(&mut self, i: NodeKey) -> f32 {
        let Some((id, context)) = self.tree.measurement_inputs(i) else { return 0.0; };
        (self.text)(id, context, None).x
    }

    fn measure_text_height(&mut self, i: NodeKey, wrap_width: Option<f32>) -> f32 {
        if let Some(width) = wrap_width
            && self.cache_text && self.tree.layout_data.has_flow
        {
            let Some(node) = self.tree.nodes.get(i) else { return 0.0; };
            let identity = incarnation(node.identity);
            let owner = &self.tree.owner;
            let contexts = &mut self.tree.contexts;
            let text = &mut self.text;
            let mut measure = |identity, width| {
                let id = NodeId::new(owner, i, identity);
                let context = node.context.and_then(|key| contexts.as_mut()?.get_mut(key));
                text(id, context, Some(f32::from_bits(width))).y.to_bits()
            };
            let bits = self.tree.text_heights.query::<crate::vec_memory::RustVec, _>(identity, width.to_bits(), &mut measure);
            return f32::from_bits(bits);
        }
        let Some((id, context)) = self.tree.measurement_inputs(i) else { return 0.0; };
        (self.text)(id, context, wrap_width).y
    }

    fn measure_content(&mut self, i: NodeKey, input: ContentMeasureInput) -> Xy<f32> {
        let Some((id, context)) = self.tree.measurement_inputs(i) else { return Xy::new_symm(0.0); };
        (self.content)(id, context, input)
    }

    #[inline(always)]
    fn write_output_rect(&mut self, i: NodeKey, rect: XyRect, _local_rect: XyRect) {
        if let Some(node) = self.tree.nodes.get_mut(i) {
            output::publish(&mut node.rect, &mut node.identity, rect);
        }
    }

    fn layout_warning(&mut self, warning: LayoutWarning<NodeKey>) {
        // Retain the diagnostic if it fits even when amortized growth doesn't.
        if self.tree.warnings.try_reserve(1).is_ok()
            || self.tree.warnings.try_reserve_exact(1).is_ok()
        {
            let warning = warning.map_node(|id| self.tree.node_id(id));
            self.tree.warnings.push(warning);
        }
    }
}

const FONT_SIZE: f32 = 12.0;
const CHAR_WIDTH: f32 = 0.6 * FONT_SIZE;
const LINE_HEIGHT: f32 = 1.2 * FONT_SIZE;
use text_scan::windows::{LineWidths, line_widths, scan_scalar_words};

/// A measure function for `solve_layout_with_measure` that matches the text of `LayoutTree::to_svg`.
pub fn measure_monospace_text<T: AsRef<str>>(_: NodeId, text: Option<&mut T>, wrap_width: Option<f32>) -> Xy<f32> {
    let text = text.as_deref().map_or("", T::as_ref);
    let bytes = text.as_bytes();
    if wrap_width.is_none() {
        if let Some(chars) = normalized_ascii_width(bytes) {
            return Xy::new(chars as f32 * CHAR_WIDTH, if chars == 0 { 0.0 } else { LINE_HEIGHT });
        }
    } else if text.is_ascii() {
        #[cfg(target_arch = "x86_64")]
        // A wide line typically has room for a vector's completed words.
        if let Some(first) = bytes.first_chunk::<16>()
            && max_line_chars(wrap_width) >= 55
            && text_scan::text_avx2_supported(text_scan::windows::TextAvx2::AsciiWrap)
            && let Some(last) = bytes.last_chunk::<16>()
        {
            // SAFETY: The CPU and OS support both required features.
            return unsafe { text_scan::measure_wrapped_avx2(bytes, first, last, LineWidths::new(wrap_width)) };
        }
        #[cfg(target_arch = "x86_64")]
        if let Some(last) = bytes.last_chunk::<16>() {
            return measure_ascii_wrapped(bytes, last, wrap_width);
        }
        return scan_scalar_words::<true>(bytes, LineWidths::new(wrap_width)).size();
    }
    measure_unicode(text, LineWidths::new(wrap_width))
}

#[inline(never)]
fn measure_unicode(text: &str, lines: LineWidths) -> Xy<f32> {
    #[cfg(target_arch = "x86_64")]
    if text.len() >= 24
        && text_scan::text_avx2_supported(text_scan::windows::TextAvx2::UnicodeWrap)
    {
        // SAFETY: The detector checks the CPU and OS for every required feature.
        return unsafe { text_scan::measure_mixed_avx2(text, lines) };
    }

    scan_scalar_words::<false>(text.as_bytes(), lines).size()
}

#[cfg(target_arch = "x86_64")]
// Keep the long-input loop separate from the short-label measurement path.
#[inline(never)]
fn measure_ascii_wrapped(bytes: &[u8], last: &[u8; 16], wrap_width: Option<f32>) -> Xy<f32> {
    let mut lines = LineWidths::new(wrap_width);
    text_scan::for_each_ascii_word_width(bytes, last, &mut lines);
    lines.size()
}

#[cfg(target_arch = "x86_64")]
use ascii_width::width as normalized_ascii_width;

#[cfg(not(target_arch = "x86_64"))]
fn normalized_ascii_width(bytes: &[u8]) -> Option<usize> {
    use text_scan::windows::{ascii_space, count_ascii_pairs};

    if !bytes.is_ascii() { return None; }
    let Some((&first, rest)) = bytes.split_first() else { return Some(0) };
    let mut chars = usize::from(!ascii_space(first));
    let mut words = chars;
    // Limit each reduction to 64 byte pairs so the vectorized counters fit in byte lanes.
    let (preceding, preceding_tail) = bytes.get(..rest.len())?.as_chunks::<64>();
    let (following, following_tail) = rest.as_chunks::<64>();
    for (left, right) in preceding.iter().zip(following) {
        let (letters, starts) = count_ascii_pairs(left, right);
        chars = chars.saturating_add(usize::from(letters));
        words = words.saturating_add(usize::from(starts));
    }
    let (letters, starts) = count_ascii_pairs(preceding_tail, following_tail);
    chars = chars.saturating_add(usize::from(letters));
    words = words.saturating_add(usize::from(starts));
    Some(chars.saturating_add(words.saturating_sub(1)))
}

#[cfg(test)]
fn measure_word_widths(widths: impl Iterator<Item = usize>, wrap_width: Option<f32>) -> Xy<f32> {
    let mut lines = LineWidths::new(wrap_width);
    for word in widths {
        lines.add_word(word);
    }
    lines.size()
}

impl LineWidths {
    fn new(wrap_width: Option<f32>) -> Self {
        line_widths(max_line_chars(wrap_width))
    }

    fn size(self) -> Xy<f32> {
        Xy::new(self.longest as f32 * CHAR_WIDTH, self.count as f32 * LINE_HEIGHT)
    }
}

fn max_line_chars(wrap_width: Option<f32>) -> usize {
    wrap_width.map_or(usize::MAX, |width| (width / CHAR_WIDTH) as usize)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn absent_adapter_key_has_no_links_callbacks_or_live_layout_writes() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let child = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
        tree.remove(&child).unwrap();
        let key = child.key();
        let rect = Xy::new_symm([0.0, 10.0]);
        let mut adapter = Adapter::new(&mut tree,
            |_: NodeId, _: Option<&mut ()>, _: Option<f32>| panic!("text measured for an absent node"),
            |_: NodeId, _: Option<&mut ()>, _: ContentMeasureInput| panic!("content measured for an absent node"),
        );
        assert_eq!(adapter.parent(key), None);
        assert_eq!(adapter.first_child(key), None);
        assert_eq!(adapter.next_sibling(key), None);
        assert!(adapter.node_layout_params(key).disabled);
        let root_layout = adapter.node_layout_data(root.key()).size();
        adapter.node_layout_data_mut(key).values[slot_index(Axis::X, Kind::Final)] = 10.0;
        assert_eq!(adapter.node_layout_data(root.key()).size(), root_layout);
        assert_eq!(adapter.measure_text_width(key), 0.0);
        assert_eq!(adapter.measure_text_height(key, Some(10.0)), 0.0);
        let input = ContentMeasureInput {
            axis: Axis::X, known_dimensions: Xy::new_symm(None), max_size: Xy::new_symm(None),
        };
        assert_eq!(adapter.measure_content(key, input), Xy::new_symm(0.0));
        adapter.write_output_rect(key, rect, rect);
        assert_eq!(adapter.tree.layout(&root), Err(TreeError::LayoutUnavailable));
    }

    #[test]
    fn last_incarnation_remains_live_across_publication_and_capacity_failure() {
        let mut tree = LayoutTree::<()>::with_capacity(0).unwrap();
        let root = tree.root();
        tree.next_incarnation = RECT_PUBLISHED - 1;
        let child = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
        assert_eq!(tree.add_node(&root, LayoutParams::DEFAULT), Err(TreeError::Capacity));
        assert!(tree.children(&root).unwrap().eq([child.clone()]));
        assert_eq!(tree.layout(&child), Err(TreeError::LayoutUnavailable));

        tree.solve_layout(Xy::new_symm(40.0));
        assert_eq!(tree.layout(&child), Ok(Xy::new_symm([0.0, 40.0])));
        tree.update_node_params(&child, LayoutParams { disabled: true, ..LayoutParams::DEFAULT }).unwrap();
        assert_eq!(tree.layout(&child), Err(TreeError::LayoutUnavailable));
        assert!(tree.children(&root).unwrap().eq([child.clone()]));
        tree.remove(&child).unwrap();
        assert_eq!(tree.layout(&child), Err(TreeError::StaleNode));
    }

    #[test]
    fn prepared_pixels_follow_stack_style_and_visibility_edits() {
        let mut tree = LayoutTree::<()>::new();
        let root = tree.root();
        let mut frame = *tree.params(&root).unwrap();
        frame.children_layout = ChildrenLayout::Stack {
            axis: Axis::X,
            arrange: Arrange::Start,
            spacing: 1.0,
        };
        tree.update_node_params(&root, frame).unwrap();
        let mut params = LayoutParams {
            size: Xy::new_symm(Size::Pixels(10.0)),
            position: Xy::new_symm(Pos::Start),
            ..LayoutParams::DEFAULT
        };
        let first = tree.add_node(&root, params).unwrap();
        let second = tree.add_node(&root, params).unwrap();
        let window = Xy::new_symm(100.0);
        tree.solve_layout(window);
        tree.invalidate();
        tree.solve_layout(window);
        assert_eq!(tree.layout(&second).unwrap().x, [11.0, 21.0]);

        params.position.y = Pos::End;
        tree.update_node_params(&first, params).unwrap();
        tree.invalidate();
        tree.solve_layout(window);
        assert_eq!(tree.layout(&first).unwrap().y, [90.0, 100.0]);

        params.free_placement = true;
        tree.update_node_params(&first, params).unwrap();
        frame.disabled = true;
        tree.update_node_params(&root, frame).unwrap();
        assert!(!tree.nodes[second.key()].layout.cached_stack_start());
        frame.disabled = false;
        tree.update_node_params(&root, frame).unwrap();
        for _ in 0..2 {
            tree.invalidate();
            tree.solve_layout(window);
            assert_eq!(tree.layout(&first).unwrap().y, [90.0, 100.0]);
            assert_eq!(tree.layout(&second).unwrap().x, [0.0, 10.0]);
        }
    }

    #[test]
    fn numeric_placement_tracks_weight_and_clamped_style_edits() {
        let mut tree: LayoutTree = LayoutTree::new();
        let root = tree.root();
        tree.set_pixel_scale(Some(PixelScale::new(1.25).unwrap()));
        let mut group_style = LayoutParams {
            size: Xy::new(Size::Pixels(125.0), Size::Pixels(34.5)),
            max_size: Xy::new(Some(Size::Pixels(101.25)), None),
            children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 2.25 },
            position: Xy::new_symm(Pos::Start),
            ..LayoutParams::DEFAULT
        };
        let group = tree.add_node(&root, group_style).unwrap();
        let left = tree.add_node(&group, LayoutParams::DEFAULT).unwrap();
        let right = tree.add_node(&group, LayoutParams::DEFAULT).unwrap();
        let peer = tree.add_node(&root, LayoutParams {
            size: Xy::new_symm(Size::Pixels(9.0)),
            ..LayoutParams::DEFAULT
        }).unwrap();
        for _ in 0..6 {
            tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
        }
        let window = Xy::new(200.0, 110.0);
        tree.solve_layout(window);
        let mut left_style = *tree.params(&left).unwrap();
        let words = |r: XyRect| [r.x, r.y].map(|edges| edges.map(f32::to_bits));
        for weight in [2.5, 1.0, 3.0] {
            let previous_right = tree.layout(&right).unwrap();
            left_style.fill_weight = weight;
            tree.update_node_params(&left, left_style).unwrap();
            group_style.position.x = Pos::Pixels(weight * 8.25);
            group_style.size.x = Size::Pixels(135.0 + weight);
            tree.update_node_params(&group, group_style).unwrap();
            let mut full = tree.clone();
            full.solve_layout(window);
            assert!(matches!(tree.solve_layout(window), IncrementalRelayoutOutcome::Success { .. }));
            assert_ne!(tree.layout(&right).unwrap(), previous_right);
            for node in [&group, &left, &right, &peer] {
                assert_eq!(words(tree.layout(node).unwrap()), words(full.layout(&full.node_id(node.key())).unwrap()));
            }
        }
    }

    #[test]
    fn placement_only_edits_retain_exact_geometry() {
        let modes = [
            ChildrenLayout::Free,
            ChildrenLayout::Stack { axis: Axis::Y, spacing: 1.375, arrange: Arrange::Center },
            ChildrenLayout::Wrap { axis: Axis::X, spacing: 1.75, line_spacing: 2.625, arrange: Arrange::End },
            ChildrenLayout::Block,
            ChildrenLayout::Grid {
                columns: MainAxisCellSize::Count(2), spacing_x: 3.125, spacing_y: 2.375,
                main_axis: Axis::X, backfill: false,
            },
        ];
        for mode in modes {
            let mut tree = LayoutTree::<()>::new();
            tree.set_pixel_scale(Some(PixelScale::try_from(1.25).unwrap()));
            let root = tree.root();
            tree.update_node_params(&root, LayoutParams {
                children_layout: mode, padding: Xy::new_symm([1.375, 2.625]), ..LayoutParams::DEFAULT
            }).unwrap();
            let leaf = LayoutParams {
                size: Xy::new(Size::Pixels(26.375), Size::Pixels(17.125)),
                position: Xy::new_symm(Pos::Start), ..LayoutParams::DEFAULT
            };
            let clean = tree.add_node(&root, leaf).unwrap();
            let branch = tree.add_node(&root, LayoutParams {
                children_layout: ChildrenLayout::Stack { axis: Axis::X, arrange: Arrange::Start, spacing: 1.75 },
                ..leaf
            }).unwrap();
            let nested = tree.add_node(&branch, LayoutParams {
                size: Xy::new_symm(Size::Pixels(6.125)), ..leaf
            }).unwrap();
            tree.add_node(&branch, LayoutParams { size: Xy::new_symm(Size::Pixels(4.375)), ..leaf }).unwrap();
            let free = tree.add_node(&root, LayoutParams { free_placement: true, ..leaf }).unwrap();
            let viewport = Xy::new(74.25, 83.75);
            tree.solve_layout(viewport);
            let clean_rect = tree.layout(&clean).unwrap();
            let nested_rect = tree.layout(&nested).unwrap();

            let mut branch_params = *tree.params(&branch).unwrap();
            branch_params.position.x = Pos::End;
            branch_params.children_origin_flipped.x = true;
            tree.update_node_params(&branch, branch_params).unwrap();
            let mut free_params = *tree.params(&free).unwrap();
            free_params.position = Xy::new(Pos::Pixels(99.25), Pos::Pixels(19.125));
            free_params.anchor = Xy::new_symm(Anchor::Center);
            free_params.window_overflow.x = WindowOverflow::Clamp;
            tree.update_node_params(&free, free_params).unwrap();
            assert!(matches!(tree.tail_edits, TailEdits::Placement));
            assert_eq!(tree.nodes[root.key()].layout.placement, PlacementWork::Descendants);
            assert_eq!(tree.nodes[clean.key()].layout.placement, PlacementWork::Clean);

            let mut full = tree.clone();
            assert_eq!(tree.solve_layout(viewport), IncrementalRelayoutOutcome::Success { computed: 0 });
            full.solve_layout(viewport);
            assert_eq!(tree.layout(&clean).unwrap(), clean_rect);
            assert_ne!(tree.layout(&nested).unwrap(), nested_rect);
            assert!(tree.warnings().is_empty());
            for key in tree.nodes.keys() {
                let actual = tree.layout(&tree.node_id(key)).unwrap();
                let expected = full.layout(&full.node_id(key)).unwrap();
                assert_eq!(actual.x.map(f32::to_bits), expected.x.map(f32::to_bits), "{mode:?}");
                assert_eq!(actual.y.map(f32::to_bits), expected.y.map(f32::to_bits), "{mode:?}");
            }
        }
    }

    #[test]
    fn contexts_follow_nodes_through_cloning_moving_and_reuse() {
        let mut tree = LayoutTree::<String>::new();
        let root = tree.root();
        let parent = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
        let params = LayoutParams {
            size: Xy::new_symm(Size::FitContent),
            text: TextContent::Fixed,
            ..LayoutParams::DEFAULT
        };
        let node = tree.add_node(&root, params).unwrap();
        let window = Xy::new_symm(200.0);

        tree.update_node_context(&node, Some("雪".into())).unwrap();
        tree.solve_layout_with_measure(window, measure_monospace_text);
        assert!(tree.to_svg_with_text().contains(">雪</text>"));

        let mut cloned = tree.clone();
        let cloned_node = cloned.node_id(node.key()).as_child().unwrap();
        let cloned_parent = cloned.node_id(parent.key());
        cloned.update_node_context(&cloned_node, Some("café".into())).unwrap();
        cloned.move_node(&cloned_node, Destination::LastChildOf(&cloned_parent)).unwrap();
        cloned.solve_layout_with_measure(window, measure_monospace_text);
        assert!(cloned.to_svg_with_text().contains(">café</text>"));
        assert!(tree.to_svg_with_text().contains(">雪</text>"));

        cloned.update_node_context(&cloned_node, None).unwrap();
        cloned.solve_layout_with_measure(window, measure_monospace_text);
        assert!(!cloned.to_svg_with_text().contains(">café</text>"));
        cloned.remove(&cloned_node).unwrap();
        let reused = cloned.add_node_with_context(&cloned_parent, params, "été".into()).unwrap();
        assert_ne!(cloned_node, reused);
        cloned.solve_layout_with_measure(window, measure_monospace_text);
        assert!(cloned.to_svg_with_text().contains(">été</text>"));
    }

    #[test]
    fn monospace_measurement_counts_normalized_unicode_lines() {
        let root = LayoutTree::<()>::new().root();
        let mut text = " \tÅβ\u{2003}猫  four\n";
        for (width, chars, lines) in [(None, 9, 1), (Some(CHAR_WIDTH * 4.0), 4, 2), (Some(0.0), 4, 3)] {
            assert_eq!(
                measure_monospace_text(root.clone(), Some(&mut text), width),
                Xy::new(chars as f32 * CHAR_WIDTH, lines as f32 * LINE_HEIGHT),
            );
        }
        assert_eq!(measure_monospace_text::<&str>(root, None, None), Xy::new_symm(0.0));
    }

    #[test]
    fn unwrapped_measurement_uses_character_counts_after_a_non_ascii_byte() {
        let root = LayoutTree::<()>::new().root();
        for prefix in [0, 8, 15, 16, 31, 32, 127, 128, 259, 4101, 8201] {
            let mut text = "x".repeat(prefix);
            text.push_str("  \u{2003}é猫 ");
            let chars = if prefix == 0 { 2 } else { prefix + 3 };
            assert_eq!(
                measure_monospace_text(root.clone(), Some(&mut text), None),
                Xy::new(chars as f32 * CHAR_WIDTH, LINE_HEIGHT),
            );
        }
    }

    #[test]
    fn short_ascii_wrapping_keeps_word_boundaries() {
        let root = LayoutTree::<()>::new().root();
        for mut text in ["", " \t\x0b\n", "  aa\t\x0b bb  c\r\n", " abcdef "] {
            for width in [Some(0.0), Some(CHAR_WIDTH * 4.0), Some(CHAR_WIDTH * 6.0)] {
                let expected = measure_word_widths(text.split_whitespace().map(str::len), width);
                assert_eq!(measure_monospace_text(root.clone(), Some(&mut text), width), expected);
            }
        }
    }

    #[test]
    fn wrapped_measurement_matches_scalar_at_vector_boundaries() {
        let root = LayoutTree::<()>::new().root();
        let widths = [0.0, 16.0, 54.0, 55.0, 75.0, 130.0].map(|chars| Some((chars + 0.25) * CHAR_WIDTH));
        for source in [
            " x y z a b c d e f g h i j k l m n o p q r s t u v w x y z".repeat(6),
            " aaaa\t bbbb \x0bcccc ddddd e\n ffffff \x0c ggggggg ".repeat(8),
            format!("{}  word    word  {}", "x".repeat(100), "y".repeat(160)),
            " ".repeat(260),
        ] {
            for len in 14..=source.len() {
                let mut input = &source[..len];
                for width in widths {
                    let expected = measure_word_widths(input.split_whitespace().map(str::len), width);
                    assert_eq!(measure_monospace_text(root.clone(), Some(&mut input), width), expected, "length {len}, width {width:?}");
                }
            }
        }
        for prefix in [15, 16, 17, 30, 31, 32, 33, 63, 64, 65] {
            for suffix in [0, 1, 31, 64] {
                let mut input = format!("{}é\u{2003}猫{}", "x".repeat(prefix), "y".repeat(suffix));
                for width in widths {
                    let expected = measure_word_widths(input.split_whitespace().map(|word| word.chars().count()), width);
                    assert_eq!(measure_monospace_text(root.clone(), Some(&mut input), width), expected);
                }
            }
        }
    }

    #[test]
    fn subtree_operations_preserve_siblings_and_context_drop_order() {
        struct Context<'a>(u8, &'a std::cell::RefCell<Vec<u8>>);
        impl Drop for Context<'_> {
            fn drop(&mut self) {
                self.1.borrow_mut().push(self.0);
            }
        }
        let dropped = std::cell::RefCell::new(Vec::new());
        let mut tree = LayoutTree::new();
        let root = tree.root();
        let mut add = |parent: &NodeId, label| {
            tree.add_node_with_context(parent, LayoutParams::DEFAULT, Context(label, &dropped)).unwrap()
        };
        let left = add(&root, 0);
        let subtree = add(&root, 1);
        let right = add(&root, 2);
        let first = add(&subtree, 3);
        let last = add(&subtree, 4);
        let nested = add(&last, 5);
        tree.update_node_params(&subtree, LayoutParams { disabled: true, ..LayoutParams::DEFAULT }).unwrap();
        assert!([&subtree, &first, &last, &nested].into_iter().all(|id| tree.params(id).unwrap().disabled));
        assert!([&root, &left, &right].into_iter().all(|id| !tree.params(id).unwrap().disabled));
        tree.remove(&subtree).unwrap();
        assert_eq!(dropped.borrow().as_slice(), &[1, 4, 5, 3]);
        assert!(tree.children(&root).unwrap().eq([left, right]));
    }

    #[test]
    fn executed_dependency_traversals_agree_on_each_slot_pair() {
        use crate::Axis::{X, Y};
        fn zero<A>(_: NodeId, _: Option<&mut ()>, _: A) -> Xy<f32> { Xy::new_symm(0.0) }
        for axis in [X, Y] {
            for children_layout in [
                ChildrenLayout::Free,
                ChildrenLayout::Stack { axis, arrange: Arrange::Start, spacing: 1.0 },
                ChildrenLayout::Grid { main_axis: axis, columns: MainAxisCellSize::Width(13.0),
                    spacing_x: 1.0, spacing_y: 2.0, backfill: false },
            ] {
                let mut tree: LayoutTree = LayoutTree::new();
                let root = tree.root();
                let parent = tree.add_node(&root, LayoutParams {
                    size: Xy::new(Size::Pixels(80.0), Size::Auto),
                    min_size: Xy::new(Some(Size::FitContent), None),
                    content_measure: ContentMeasure::HeightForWidth,
                    children_layout, ..LayoutParams::DEFAULT
                }).unwrap();
                let mut nodes = vec![root.key(), parent.key()];
                for free_placement in [false, true] {
                    for form in [Size::Pixels(8.0), Size::AspectRatio(1.5), Size::Frac(0.3), Size::Fill, Size::FitContent] {
                        nodes.push(tree.add_node(&parent, LayoutParams {
                            size: Xy::new(form, Size::Pixels(9.0)),
                            min_size: Xy::new(Some(Size::Pixels(1.0)), Some(form)),
                            max_size: Xy::new(Some(Size::Frac(0.8)), Some(Size::Pixels(30.0))),
                            free_placement, ..LayoutParams::DEFAULT
                        }).unwrap().key());
                    }
                }
                tree.solve_layout(Xy::new_symm(200.0));

                // Assign one source a distinctive cached rank. A direct call to
                // solve_all_dependencies exposes whether that source was read.
                let mut slots = Vec::new();
                let mut adapter = Adapter::new(&mut tree, zero, zero);
                for node in nodes {
                    for axis in [X, Y] {
                        for kind in [Kind::Regular, Kind::Min, Kind::Max, Kind::Final, Kind::EvenShare] {
                            let exists = match kind {
                                Kind::EvenShare => adapter.stack_axis(node) == Some(axis),
                                Kind::Final => true,
                                _ => adapter.read_size(node, axis, kind).is_some(),
                            };
                            if exists {
                                let data = adapter.node_layout_data_mut(node);
                                data.flags.set_state(axis, kind, SOLVED);
                                data.levels[slot_index(axis, kind)] = 0;
                                slots.push(Slot { node, axis, kind });
                            }
                        }
                    }
                }
                for &source in &slots {
                    let mut f = tree.clone();
                    let mut forward = Adapter::new(&mut f, zero, zero);
                    forward.node_layout_data_mut(source.node).levels[slot_index(source.axis, source.kind)] = 100;
                    let mut rev = tree.clone();
                    let mut reverse = Adapter::new(&mut rev, zero, zero);
                    reverse.queue_dependents(source);
                    for &reader in &slots {
                        forward.layout_data().current_level = 0;
                        forward.solve_all_dependencies(reader);
                        let read = forward.layout_data().current_level == 101;
                        let notified = reverse.node_layout_data(reader.node).flags.check_state(reader.axis, reader.kind) == UNSOLVED;
                        assert_eq!(read, notified, "{children_layout:?} source {source:?} reader {reader:?}");
                    }
                }
            }
        }
    }

}

#[cfg(test)]
mod text_measure_binding_tests {
    use super::*;
    use std::{cell::Cell, rc::Rc};

    fn query(
        tree: &mut LayoutTree<Rc<Cell<u32>>>,
        key: NodeKey,
        width: f32,
        cache_text: bool,
        add_bits: u32,
    ) -> (u32, usize) {
        let mut calls = 0;
        let mut adapter = Adapter::new(
            tree,
            |_: NodeId, value: Option<&mut Rc<Cell<u32>>>, width: Option<f32>| {
                calls += 1;
                let bits = if width.map(f32::to_bits) == Some((-0.0f32).to_bits()) {
                    (-0.0f32).to_bits()
                } else {
                    value.map_or(0, |value| value.get()).wrapping_add(add_bits)
                };
                Xy::new(0.0, f32::from_bits(bits))
            },
            |_: NodeId, _: Option<&mut Rc<Cell<u32>>>, _: ContentMeasureInput| Xy::new_symm(0.0),
        );
        adapter.cache_text = cache_text;
        let bits = adapter.measure_text_height(key, Some(width)).to_bits();
        (bits, calls)
    }

    #[test]
    fn wrapped_height_memo_binds_exact_inputs_and_owned_invalidations() {
        const NAN: u32 = 0x7fa0_0032;
        let mut tree = LayoutTree::new();
        let root = tree.root();
        let parent = tree.add_node(&root, LayoutParams::DEFAULT).unwrap();
        let node = tree.add_node_with_context(&root, LayoutParams::DEFAULT, Rc::new(Cell::new(NAN))).unwrap();
        tree.layout_data.has_flow = true;
        assert_eq!(query(&mut tree, node.key(), 0.0, true, 0), (NAN, 1));
        assert_eq!(query(&mut tree, node.key(), -0.0, true, 0), (0x8000_0000, 1));
        assert_eq!(query(&mut tree, node.key(), 0.0, true, 0), (NAN, 0));
        assert_eq!(query(&mut tree, node.key(), -0.0, true, 0), (0x8000_0000, 0));

        tree.move_node(&node, Destination::LastChildOf(&parent)).unwrap();
        assert_eq!(query(&mut tree, node.key(), 0.0, true, 0), (NAN, 0));

        let replacement = Rc::new(Cell::new(17));
        tree.update_node_context(&node, Some(replacement.clone())).unwrap();
        assert_eq!(query(&mut tree, node.key(), 0.0, true, 0), (17, 1));
        replacement.set(27);
        tree.mark_content_changed(&node).unwrap();
        assert_eq!(query(&mut tree, node.key(), 0.0, true, 0), (27, 1));
        assert_eq!(query(&mut tree, node.key(), 0.0, true, 0), (27, 0));

        let mut independent = tree.clone();
        assert_eq!(query(&mut independent, node.key(), 0.0, true, 10), (37, 1));
        tree.invalidate();
        assert_eq!(query(&mut tree, node.key(), 0.0, true, 5), (32, 1));

        assert_eq!(query(&mut tree, node.key(), 0.0, false, 0), (27, 1));
        tree.remove(&node).unwrap();
        assert_eq!(query(&mut tree, node.key(), 0.0, true, 5), (0, 0));
        let new_node = tree.add_node_with_context(&root, LayoutParams::DEFAULT, Rc::new(Cell::new(47))).unwrap();
        assert_eq!(query(&mut tree, new_node.key(), 0.0, true, 5), (52, 1));
    }
}
