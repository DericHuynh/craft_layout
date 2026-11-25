//! Optional constraints for the owned layout tree. Each declaration remains
//! available in authored form while the standard solver measures and places
//! the effective boxes. Unconfigured trees use the original solve path.
mod block;
mod driver;
mod flex;
mod grid;
mod responsive;
mod viewport;
use super::typography::TypographyPatch;
use super::{LayoutTree, NodeId, NodeKey, TreeError, TreeIdentity};
use crate::{
    LayoutParams, Xy, XyRect,
    flex::{FlexItem, FlexLayout},
    logical::LogicalStyle,
};
pub use responsive::{Container, ContainerQuery, QueryLayout, QueryStyle};
use std::collections::HashMap;
use std::sync::Arc;
pub use viewport::{
    BoxReference, Edges, Length, Overflow, Placement, ScrollStyle, Side, ViewGeometry,
};

/// Extra rules for one node. A default value leaves its native declarations alone.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct NodeRules {
    /// Inherited writing context and optional logical declarations.
    pub logical: LogicalStyle,
    /// Lay children out as flexible lines.
    pub flex: Option<FlexLayout>,
    /// Heterogeneous track grid for this node's children.
    pub grid: Option<crate::tracks::TrackGrid>,
    /// Placement within the parent's track grid.
    pub grid_item: crate::tracks::GridItem,
    /// Preferred basis, weights, order and alignment when inside a flexible line.
    pub flex_item: FlexItem,
    /// First and last baseline offsets from the low cross edge, including leading padding.
    pub baselines: Xy<Option<f32>>,
    /// Viewport, scrollbars and clip policy for this box.
    pub scroll: ScrollStyle,
    /// Out-of-flow or sticky positioning.
    pub placement: Placement,
    /// Isolate content contributions and optionally expose a query container.
    pub container: Option<Container>,
    /// Conditional changes evaluated against suitable ancestors in list order.
    pub queries: Vec<ContainerQuery>,
}

/// A managed layout dependency that could not be satisfied.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuleIssue {
    /// An explicitly referenced anchor or containing box is unavailable.
    MissingReference(NodeId),
    /// A visual placement depends on itself through an anchor, containing box or descendant.
    CyclicReference(NodeId),
    /// A query has no ancestor containing the requested axis.
    MissingContainer(NodeId),
    /// Both flex and grid were selected on a single node. Flex takes precedence.
    ConflictingFormattingContexts(NodeId),
    /// A shared axis requires a track-grid parent to supply track boundaries.
    MissingParentTracks(NodeId, crate::Axis),
    /// The declarations did not settle to a fixed geometry.
    UnstableLayout,
}

#[derive(Clone, Copy, Debug)]
pub(super) enum BaselineContext {
    Flex(crate::flex::FlexAlign),
    Grid(crate::tracks::GridAlign),
}

impl BaselineContext {
    pub(super) fn aligns(self, item: Option<&NodeRules>) -> bool {
        use crate::{flex::FlexAlign, tracks::GridAlign};
        if item.is_some_and(|style| style.placement.out_of_flow()) {
            return false;
        }
        match self {
            Self::Flex(default) => matches!(
                item.and_then(|s| s.flex_item.align_self).unwrap_or(default),
                FlexAlign::FirstBaseline | FlexAlign::LastBaseline
            ),
            Self::Grid(default) => matches!(
                item.and_then(|s| s.grid_item.align.y).unwrap_or(default),
                GridAlign::FirstBaseline | GridAlign::LastBaseline
            ),
        }
    }
}

#[derive(Default, Clone, Debug)]
pub(super) struct State {
    styles: HashMap<NodeKey, NodeRules>,
    pub(super) authored: HashMap<NodeKey, LayoutParams>,
    patches: HashMap<NodeKey, TypographyPatch>,
    pub(super) baseline_contexts: HashMap<NodeKey, BaselineContext>,
    offsets: HashMap<NodeKey, Xy<f32>>,
    outputs: HashMap<NodeKey, ViewGeometry>,
    positioned_styles: HashMap<NodeKey, LayoutParams>,
    issues: Vec<RuleIssue>,
    pub(super) dirty: bool,
    window: Option<Xy<f32>>,
    view_dirty: bool,
}
impl State {
    pub(super) fn clean(&self, window: Xy<f32>) -> bool {
        !self.dirty && !self.view_dirty && self.window == Some(window)
    }
    pub(super) fn possible_baseline_contexts(&self) -> usize {
        self.styles
            .values()
            .filter(|style| {
                style.flex.is_some()
                    || style.grid.is_some()
                    || style.queries.iter().any(|query| {
                        matches!(
                            query.style.layout,
                            Some(QueryLayout::Flex(_) | QueryLayout::Grid(_))
                        )
                    })
            })
            .count()
    }
    pub(super) fn active(&self) -> bool {
        !self.styles.is_empty()
            || !self.patches.is_empty()
            || !self.authored.is_empty()
            || !self.outputs.is_empty()
            || self.window.is_some() && self.dirty
    }
    pub(super) fn cloned(&self, owner: &Arc<TreeIdentity>) -> Self {
        let mut copy = self.clone();
        for style in copy.styles.values_mut() {
            style.placement.rebind(owner);
        }
        copy.issues.clear();
        copy.dirty = true;
        copy
    }
}

impl<T> LayoutTree<T> {
    /// Replace all optional rules of a live node. A default removes the rules.
    pub fn set_rules(&mut self, id: &NodeId, style: NodeRules) -> Result<(), TreeError> {
        self.resolve_node(id)?;
        if let Some(target) = style.placement.target() {
            self.resolve_node(target)?;
            if target == id {
                return Err(TreeError::WouldCreateCycle);
            }
        }
        if self
            .rules_state
            .styles
            .get(&id.key())
            .cloned()
            .unwrap_or_default()
            == style
        {
            return Ok(());
        }
        if style == NodeRules::default() {
            self.rules_state.styles.remove(&id.key());
        } else {
            self.rules_state.styles.insert(id.key(), style);
        }
        self.rules_state.dirty = true;
        Ok(())
    }
    /// Inspect authored optional rules. An unconfigured node has no entry.
    pub fn rules(&self, id: &NodeId) -> Result<Option<&NodeRules>, TreeError> {
        self.resolve_node(id)?;
        Ok(self.rules_state.styles.get(&id.key()))
    }
    /// Geometry diagnostics from the latest managed solve.
    pub fn rule_issues(&self) -> &[RuleIssue] {
        &self.rules_state.issues
    }
    /// Request a physical scroll offset. The published view clamps it to the legal range.
    pub fn set_scroll_offset(&mut self, id: &NodeId, offset: Xy<f32>) -> Result<(), TreeError> {
        self.resolve_node(id)?;
        if self.rules_state.offsets.insert(id.key(), offset) != Some(offset) {
            self.rules_state.view_dirty = true;
        }
        Ok(())
    }
    /// The placed rectangle, visible clip and geometry of the node's scrollport.
    /// Changing a scroll offset takes effect on the next solve.
    pub fn view_geometry(&self, id: &NodeId) -> Result<ViewGeometry, TreeError> {
        let r = self.layout(id)?;
        Ok(self
            .rules_state
            .outputs
            .get(&id.key())
            .cloned()
            .unwrap_or_else(|| ViewGeometry::plain(r, self.published_window())))
    }
    pub(crate) fn set_typography_patch(
        &mut self,
        id: &NodeId,
        patch: TypographyPatch,
    ) -> Result<(), TreeError> {
        self.resolve_node(id)?;
        if self
            .rules_state
            .patches
            .get(&id.key())
            .copied()
            .unwrap_or_default()
            != patch
        {
            if patch == TypographyPatch::default() {
                self.rules_state.patches.remove(&id.key());
            } else {
                self.rules_state.patches.insert(id.key(), patch);
            }
            self.rules_state.dirty = true;
        }
        Ok(())
    }
}

fn size(rect: XyRect) -> Xy<f32> {
    Xy::new(
        (rect.x[1] - rect.x[0]).max(0.),
        (rect.y[1] - rect.y[0]).max(0.),
    )
}
