mod svg;
mod stack_tail;
mod removal;
mod text_scan;
mod id;
mod structural_guard;
#[cfg(target_arch = "x86_64")]
mod ascii_width;

use crate::*;
use slotmap::{DefaultKey, SlotMap, new_key_type};
use stack_tail::{StackTail, TailEdits};
use std::sync::Arc;
use id::TreeIdentity;
pub use id::{ChildId, Destination, NodeId, TreeError};
use structural_guard::{MoveParents, ParentModel, RECT_PUBLISHED, can_insert, incarnation, next_incarnation,
    publish_rect, root_capacity, validate_ancestry};

new_key_type! {
    pub(crate) struct NodeKey;
}

#[derive(Debug, Clone)]
#[repr(C)]
pub(crate) struct LayoutNode {
    // Forward traversal and placement use this prefix. User payloads live in
    // a separate arena, so their size cannot change the hot record's stride.
    pub(crate) next_sibling: Option<NodeKey>,
    pub(crate) first_child: Option<NodeKey>,
    pub(crate) parent: Option<NodeKey>,
    pub(crate) layout: NodeLayoutData,
    pub(crate) rect: XyRect,
    pub(crate) params: LayoutParams,
    pub(crate) last_child: Option<NodeKey>,
    pub(crate) prev_sibling: Option<NodeKey>,
    context: Option<DefaultKey>,
    identity: u64,
}

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
    root: NodeKey,
    owner: Arc<TreeIdentity>,
    next_incarnation: u64,
    pub(crate) layout_data: LayoutData<NodeKey>,
    warnings: Vec<LayoutWarning<NodeId>>,
    tail_edits: TailEdits,
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
        nodes.try_reserve(capacity).map_err(|_| TreeError::Capacity)?;
        Ok(Self::from_arena(nodes))
    }

    fn from_arena(mut nodes: SlotMap<NodeKey, LayoutNode>) -> Self {
        let root = nodes.insert(LayoutNode::new(LayoutParams::DEFAULT, 0));
        // All mutations pass through this tree's localized registration methods.
        let layout_data = LayoutData { topology: None, ..LayoutData::new() };
        LayoutTree {
            nodes, contexts: None, root, owner: Arc::new(TreeIdentity { root }),
            next_incarnation: 1, layout_data, warnings: Vec::new(),
            tail_edits: TailEdits::Other, tail_stack: None,
        }
    }

    pub(crate) fn node_id(&self, key: NodeKey) -> NodeId {
        NodeId::new(&self.owner, key, incarnation(self.nodes[key].identity))
    }

    fn resolve(&self, id: &NodeId) -> Result<NodeKey, TreeError> {
        if !id.belongs_to(&self.owner) {
            return Err(TreeError::ForeignNode);
        }
        let key = id.key();
        let node = self.nodes.get(key).ok_or(TreeError::StaleNode)?;
        if incarnation(node.identity) != id.incarnation() {
            return Err(TreeError::StaleNode);
        }
        Ok(key)
    }

    fn resolve_child(&self, child: &ChildId) -> Result<(NodeKey, NodeKey), TreeError> {
        let key = self.resolve(child)?;
        let parent = self.nodes[key].parent.ok_or(TreeError::StaleNode)?;
        Ok((key, parent))
    }

    /// Get the `NodeId` corresponding to the root node.
    pub fn root(&self) -> NodeId {
        self.node_id(self.root)
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
        let (i, old_parent) = self.resolve_child(node)?;
        let (parent, before_sibling) = match destination {
            Destination::LastChildOf(parent) => (self.resolve(parent)?, None),
            Destination::Before(sibling) => {
                let (sibling, parent) = self.resolve_child(sibling)?;
                if i == sibling { return Err(TreeError::BeforeSelf); }
                (parent, Some(sibling))
            }
        };
        let same_parent = old_parent == parent;
        if same_parent && self.nodes[i].next_sibling == before_sibling {
            return Ok(());
        }
        validate_ancestry(self, parent, i, self.nodes.len())?;
        self.tail_edits = TailEdits::Other;
        self.unlink(i, old_parent);
        let prev = match before_sibling {
            Some(sibling) => self.nodes[sibling].prev_sibling,
            None => self.nodes[parent].last_child,
        };
        self.link(i, parent, prev, before_sibling);
        // Unlink already marked the original parent's child list. A reorder retains
        // the moved subtree's own size dependencies and any earlier pending edits.
        if !same_parent && self.layout_data.tracks_structure() {
            self.layout_data.record_children_change(&mut self.nodes[parent].layout);
            self.nodes[i].layout.mark_moved();
        }
        Ok(())
    }

    /// Changes the params of a node. If the parent is disabled, the node stays disabled. A change of `disabled` also applies to all the descendants. Equal params cause no relayout.
    pub fn update_node_params(&mut self, node: &NodeId, mut params: LayoutParams) -> Result<(), TreeError> {
        let i = self.resolve(node)?;
        let parent = self.nodes[i].parent;
        if let Some(parent) = parent {
            params.disabled |= self.nodes[parent].params.disabled;
        }
        let node = &mut self.nodes[i];
        if node.params.same_input(&params) {
            return Ok(());
        }
        self.tail_edits = TailEdits::Other;
        let disabled_changed = node.params.disabled != params.disabled;
        let structural = self.layout_data.record_node_change(i, &node.params, &params, &mut node.layout);
        node.layout.forget_fixed_pixels();
        node.params = params;
        if disabled_changed {
            self.set_subtree_disabled(i, params.disabled);
        }
        if structural {
            self.layout_data.record_children_change(&mut self.nodes[parent.unwrap_or(i)].layout);
        }
        Ok(())
    }

    /// Removes a child and all its descendants, invalidating their handles.
    ///
    /// User context destructors run after the subtree has been removed.
    pub fn remove(&mut self, node: &ChildId) -> Result<(), TreeError> {
        let (i, parent) = self.resolve_child(node)?;
        self.record_tail_edit(i, parent, false);
        self.unlink(i, parent);
        removal::remove_owned_tree(self, i);
        Ok(())
    }

    /// Read the node's `LayoutParams`.
    pub fn params(&self, node: &NodeId) -> Result<&LayoutParams, TreeError> {
        Ok(&self.nodes[self.resolve(node)?].params)
    }

    /// Updates the context of a node and invalidates its intrinsic content measurement.
    pub fn update_node_context(&mut self, node: &NodeId, context: Option<T>) -> Result<(), TreeError> {
        let i = self.resolve(node)?;
        let retired = match (self.nodes[i].context, context) {
            (Some(key), Some(context)) => {
                let old = self.contexts.as_mut().and_then(|contexts| contexts.get_mut(key)).ok_or(TreeError::StaleNode)?;
                Some(std::mem::replace(old, context))
            }
            (Some(key), None) => {
                let retired = self.contexts.as_mut().and_then(|contexts| contexts.remove(key)).ok_or(TreeError::StaleNode)?;
                self.nodes[i].context = None;
                Some(retired)
            }
            (None, Some(context)) => {
                self.nodes[i].context = Some(self.insert_context(context)?);
                None
            }
            (None, None) => None,
        };
        self.mark_content_dirty(i);
        drop(retired);
        Ok(())
    }

    fn context_mut(&mut self, node: NodeKey) -> Option<&mut T> {
        let key = self.nodes[node].context?;
        self.contexts.as_mut()?.get_mut(key)
    }

    fn context(&self, node: &LayoutNode) -> Option<&T> {
        let key = node.context?;
        self.contexts.as_ref()?.get(key)
    }

    /// Invalidates a node's intrinsic measurement after an in-place text or content edit.
    pub fn mark_content_changed(&mut self, node: &NodeId) -> Result<(), TreeError> {
        self.mark_content_dirty(self.resolve(node)?);
        Ok(())
    }

    fn mark_content_dirty(&mut self, i: NodeKey) {
        self.tail_edits = TailEdits::Other;
        self.layout_data.record_content_change(i, &mut self.nodes[i].layout);
    }

    /// Makes the next `solve_layout` a full solve. Use it when the measure function changes, for example after a font change.
    pub fn invalidate(&mut self) {
        self.layout_data.request_full_solve(IncrementalRelayoutOutcome::FallbackInvalidated);
    }

    /// Enable pixel-grid rounding for output, or disable it with `None`.
    /// The scale is the number of physical pixels per logical pixel.
    pub fn set_pixel_scale(&mut self, pixels_per_logical_pixel: Option<PixelScale>) {
        self.layout_data.set_pixel_scale(pixels_per_logical_pixel);
    }

    /// The parent of a node. Only the root has no parent.
    pub fn parent(&self, node: &NodeId) -> Result<Option<NodeId>, TreeError> {
        Ok(self.nodes[self.resolve(node)?].parent.map(|parent| self.node_id(parent)))
    }

    /// Get an iterator over the node's children.
    pub fn children<'a>(&'a self, node: &NodeId) -> Result<impl Iterator<Item = ChildId> + use<'a, T>, TreeError> {
        let i = self.resolve(node)?;
        Ok(self.children_keys(i).map(move |child| ChildId(self.node_id(child))))
    }

    fn children_keys(&self, i: NodeKey) -> impl Iterator<Item = NodeKey> + '_ {
        std::iter::successors(self.nodes[i].first_child, |&child| self.nodes[child].next_sibling)
    }

    /// The last published rectangle in logical pixels.
    ///
    /// A new node or a disabled node has no available rectangle.
    pub fn layout(&self, node: &NodeId) -> Result<XyRect, TreeError> {
        let entry = &self.nodes[self.resolve(node)?];
        if !entry.has_published_rect() {
            return Err(TreeError::LayoutUnavailable);
        }
        Ok(entry.rect)
    }

    /// The warnings from the last `solve_layout`. An incremental relayout reports only the warnings of the slots that it computes again.
    pub fn warnings(&self) -> &[LayoutWarning<NodeId>] {
        &self.warnings
    }

    /// Solves the layout. `window_size` is the size of the window, in logical pixels. The text of all nodes measures as zero.
    pub fn solve_layout(&mut self, window_size: Xy<f32>) -> IncrementalRelayoutOutcome {
        self.solve_layout_with_measure(window_size, |_, _, _| Xy::new(0.0, 0.0))
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
        self.solve_layout_with_measurers(window_size, |_, _, _| Xy::new_symm(0.0), measure)
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
        self.warnings.clear();
        let mut adapter = Adapter { tree: self, text, content };
        let edits = std::mem::take(&mut adapter.tree.tail_edits);
        if let TailEdits::Stack { parent, delta } = edits
            && let Some(computed) = adapter.solve_stack_tail(parent, delta, window_size)
        {
            return IncrementalRelayoutOutcome::Success { computed };
        }
        // Idle frames can separate edits to the same stack.
        let data = &adapter.tree.layout_data;
        if !matches!(edits, TailEdits::None) || !data.window_size.same_input(&window_size) || data.pending_full_solve.is_some() {
            adapter.tree.tail_stack = None;
        }
        adapter.solve_layout_incremental(window_size)
    }

    fn insert_context(&mut self, value: T) -> Result<DefaultKey, TreeError> {
        let contexts = self.contexts.get_or_insert_with(SlotMap::with_key);
        if !can_insert(contexts.len()) { return Err(TreeError::Capacity); }
        contexts.try_reserve(1).map_err(|_| TreeError::Capacity)?;
        Ok(contexts.insert(value))
    }

    fn add_node_inner(&mut self, parent: &NodeId, params: LayoutParams, context: Option<T>) -> Result<ChildId, TreeError> {
        let parent = self.resolve(parent)?;
        let next = next_incarnation(self.nodes.len(), self.next_incarnation).ok_or(TreeError::Capacity)?;
        self.nodes.try_reserve(1).map_err(|_| TreeError::Capacity)?;
        let mut node = LayoutNode::new(params, self.next_incarnation);
        node.context = context.map(|value| self.insert_context(value)).transpose()?;
        self.next_incarnation = next;
        let last = self.nodes[parent].last_child;
        let i = self.nodes.insert(node);
        self.link(i, parent, last, None);
        self.record_tail_edit(i, parent, true);
        self.record_attachment(i, parent);
        Ok(ChildId(self.node_id(i)))
    }

    fn record_attachment(&mut self, i: NodeKey, parent: NodeKey) {
        if self.layout_data.tracks_structure() {
            self.layout_data.record_children_change(&mut self.nodes[parent].layout);
            self.nodes[i].layout.mark_subtree_changed();
        }
    }

    fn link(&mut self, i: NodeKey, parent: NodeKey, prev: Option<NodeKey>, next: Option<NodeKey>) {
        let node = &mut self.nodes[i];
        node.parent = Some(parent);
        node.prev_sibling = prev;
        node.next_sibling = next;
        match prev {
            Some(prev) => self.nodes[prev].next_sibling = Some(i),
            None => self.nodes[parent].first_child = Some(i),
        }
        match next {
            Some(next) => self.nodes[next].prev_sibling = Some(i),
            None => self.nodes[parent].last_child = Some(i),
        }
        if self.nodes[parent].params.disabled {
            self.set_subtree_disabled(i, true);
        }
    }

    /// Takes a node out of the children of its parent.
    fn unlink(&mut self, i: NodeKey, parent: NodeKey) {
        let node = &mut self.nodes[i];
        node.parent = None;
        let prev = node.prev_sibling.take();
        let next = node.next_sibling.take();
        match prev {
            Some(prev) => self.nodes[prev].next_sibling = next,
            None => self.nodes[parent].first_child = next,
        }
        match next {
            Some(next) => self.nodes[next].prev_sibling = prev,
            None => self.nodes[parent].last_child = prev,
        }
        self.layout_data.record_children_change(&mut self.nodes[parent].layout);
    }

    fn set_subtree_disabled(&mut self, root: NodeKey, disabled: bool) {
        let mut next = Some(root);
        while let Some(i) = next {
            let node = &mut self.nodes[i];
            node.params.disabled = disabled;
            if disabled { node.identity = publish_rect(node.identity, false); }
            node.layout.forget_fixed_pixels();
            next = self.next_in_subtree(root, i, true);
        }
    }

    // Visit siblings last-to-first, the same order used to paint the SVG.
    fn next_in_subtree(&self, root: NodeKey, i: NodeKey, descend: bool) -> Option<NodeKey> {
        crate::tree_walk::next(
            i, descend, |node| self.nodes[node].last_child, |node| self.nodes[node].prev_sibling,
            |node| self.nodes[node].parent, |node| node == root,
        )
    }
}

impl<T> ParentModel for LayoutTree<T> {
    type Id = NodeKey;
}

impl<T> MoveParents for LayoutTree<T> {
    fn parent_for_move(&self, ancestor: NodeKey, moving: NodeKey) -> Result<Option<NodeKey>, TreeError> {
        if ancestor == moving { return Err(TreeError::WouldCreateCycle); }
        self.nodes.get(ancestor).map(|node| node.parent).ok_or(TreeError::StaleNode)
    }
}

impl LayoutNode {
    fn has_published_rect(&self) -> bool {
        !self.params.disabled && self.identity & RECT_PUBLISHED != 0
    }

    fn new(params: LayoutParams, identity: u64) -> Self {
        LayoutNode {
            parent: None,
            first_child: None,
            last_child: None,
            prev_sibling: None,
            next_sibling: None,
            params,
            layout: NodeLayoutData::new(),
            rect: Xy::new([0.0, 0.0], [0.0, 0.0]),
            context: None,
            identity,
        }
    }
}

/// Gives a `LayoutTree` and a measure function to the solver.
struct Adapter<'a, T, M, C> {
    tree: &'a mut LayoutTree<T>,
    text: M,
    content: C,
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
        self.tree.nodes[i].parent
    }

    #[inline(always)]
    fn first_child(&self, i: NodeKey) -> Option<NodeKey> {
        self.tree.nodes[i].first_child
    }

    #[inline(always)]
    fn next_sibling(&self, i: NodeKey) -> Option<NodeKey> {
        self.tree.nodes[i].next_sibling
    }

    #[inline(always)]
    fn node_layout_params(&self, i: NodeKey) -> &LayoutParams {
        &self.tree.nodes[i].params
    }

    #[inline(always)]
    fn node_layout_data(&self, i: NodeKey) -> &NodeLayoutData {
        &self.tree.nodes[i].layout
    }

    #[inline(always)]
    fn node_layout_data_mut(&mut self, i: NodeKey) -> &mut NodeLayoutData {
        &mut self.tree.nodes[i].layout
    }

    #[inline(always)]
    fn layout_data(&mut self) -> &mut LayoutData<NodeKey> {
        &mut self.tree.layout_data
    }

    fn measure_text_width(&mut self, i: NodeKey) -> f32 {
        (self.text)(self.tree.node_id(i), self.tree.context_mut(i), None).x
    }

    fn measure_text_height(&mut self, i: NodeKey, wrap_width: Option<f32>) -> f32 {
        (self.text)(self.tree.node_id(i), self.tree.context_mut(i), wrap_width).y
    }

    fn measure_content(&mut self, i: NodeKey, input: ContentMeasureInput) -> Xy<f32> {
        (self.content)(self.tree.node_id(i), self.tree.context_mut(i), input)
    }

    #[inline(always)]
    fn write_output_rect(&mut self, i: NodeKey, rect: XyRect, _local_rect: XyRect) {
        let node = &mut self.tree.nodes[i];
        node.rect = rect;
        node.identity = publish_rect(node.identity, true);
    }

    fn layout_warning(&mut self, warning: LayoutWarning<NodeKey>) {
        self.tree.warnings.push(warning.map_node(|id| self.tree.node_id(id)));
    }
}

const FONT_SIZE: f32 = 12.0;
const CHAR_WIDTH: f32 = 0.6 * FONT_SIZE;
const LINE_HEIGHT: f32 = 1.2 * FONT_SIZE;

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
            && std::arch::is_x86_feature_detected!("avx2")
            && std::arch::is_x86_feature_detected!("popcnt")
            && let Some(last) = bytes.last_chunk::<16>()
        {
            // SAFETY: The CPU and OS support both required features.
            return unsafe { text_scan::measure_wrapped_avx2(bytes, first, last, LineWidths::new(wrap_width)) };
        }
        #[cfg(target_arch = "x86_64")]
        if let Some(last) = bytes.last_chunk::<16>() {
            return measure_ascii_wrapped(bytes, last, wrap_width);
        }
        let mut lines = LineWidths::new(wrap_width);
        let mut word_len = 0;
        for &byte in bytes {
            if ascii_space(byte) {
                if word_len != 0 {
                    lines.add_word(word_len);
                    word_len = 0;
                }
            } else {
                word_len += 1;
            }
        }
        if word_len != 0 {
            lines.add_word(word_len);
        }
        return lines.size();
    }
    measure_unicode(text, LineWidths::new(wrap_width))
}

#[inline(never)]
fn measure_unicode(text: &str, mut lines: LineWidths) -> Xy<f32> {
    #[cfg(target_arch = "x86_64")]
    if text.len() >= 24
        && std::arch::is_x86_feature_detected!("avx2")
        && std::arch::is_x86_feature_detected!("popcnt")
        && std::arch::is_x86_feature_detected!("bmi2")
    {
        // SAFETY: The detector checks the CPU and OS for every required feature.
        return unsafe { text_scan::measure_mixed_avx2(text, lines) };
    }

    let mut length = 0;
    for c in text.chars() {
        if c.is_whitespace() {
            if length != 0 {
                lines.add_word(length);
                length = 0;
            }
        } else {
            length += 1;
        }
    }
    if length != 0 { lines.add_word(length); }
    lines.size()
}

#[cfg(target_arch = "x86_64")]
// Keep the long-input loop separate from the short-label measurement path.
#[inline(never)]
fn measure_ascii_wrapped(bytes: &[u8], last: &[u8; 16], wrap_width: Option<f32>) -> Xy<f32> {
    let mut lines = LineWidths::new(wrap_width);
    text_scan::for_each_ascii_word_width(bytes, last, |word| lines.add_word(word));
    lines.size()
}

#[inline]
fn ascii_space(byte: u8) -> bool {
    // Unicode White_Space includes vertical tab alongside the other ASCII whitespace.
    byte == b' ' || (b'\t'..=b'\r').contains(&byte)
}

#[cfg(target_arch = "x86_64")]
use ascii_width::width as normalized_ascii_width;

#[cfg(not(target_arch = "x86_64"))]
fn normalized_ascii_width(bytes: &[u8]) -> Option<usize> {
    if !bytes.is_ascii() { return None; }
    let Some((&first, rest)) = bytes.split_first() else { return Some(0) };
    let mut chars = usize::from(!ascii_space(first));
    let mut words = chars;
    // Limit each reduction to 64 byte pairs so the vectorized counters fit in byte lanes.
    let (preceding, preceding_tail) = bytes[..rest.len()].as_chunks::<64>();
    let (following, following_tail) = rest.as_chunks::<64>();
    for (left, right) in preceding.iter().zip(following) {
        let (letters, starts) = count_ascii_pairs(left, right);
        chars += usize::from(letters);
        words += usize::from(starts);
    }
    let (letters, starts) = count_ascii_pairs(preceding_tail, following_tail);
    chars += usize::from(letters);
    words += usize::from(starts);
    Some(chars + words.saturating_sub(1))
}

#[cfg(not(target_arch = "x86_64"))]
#[inline]
fn count_ascii_pairs(preceding: &[u8], following: &[u8]) -> (u8, u8) {
    let mut chars = 0;
    let mut words = 0;
    for (&previous, &current) in preceding.iter().zip(following) {
        let is_text = !ascii_space(current);
        chars += u8::from(is_text);
        words += u8::from(ascii_space(previous) && is_text);
    }
    (chars, words)
}

#[cfg(test)]
fn measure_word_widths(widths: impl Iterator<Item = usize>, wrap_width: Option<f32>) -> Xy<f32> {
    let mut lines = LineWidths::new(wrap_width);
    for word in widths {
        lines.add_word(word);
    }
    lines.size()
}

struct LineWidths {
    count: usize,
    longest: usize,
    current: usize,
    max: usize,
}

impl LineWidths {
    fn new(wrap_width: Option<f32>) -> Self {
        Self { count: 0, longest: 0, current: 0, max: max_line_chars(wrap_width) }
    }

    #[inline]
    fn add_word(&mut self, width: usize) {
        let joined = self.current + 1 + width;
        if self.current == 0 || joined > self.max {
            self.count += 1;
            self.current = width;
        } else {
            self.current = joined;
        }
        self.longest = self.longest.max(self.current);
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
                let mut adapter = Adapter { tree: &mut tree, text: zero, content: zero };
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
                    let mut forward = Adapter { tree: &mut f, text: zero, content: zero };
                    forward.node_layout_data_mut(source.node).levels[slot_index(source.axis, source.kind)] = 100;
                    let mut rev = tree.clone();
                    let mut reverse = Adapter { tree: &mut rev, text: zero, content: zero };
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
