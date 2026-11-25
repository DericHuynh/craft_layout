#![doc = include_str!("../README.md")]

#![warn(missing_docs)]

#[cfg(feature = "incremental")]
#[macro_use]
mod child_walk;
#[macro_use]
mod solve;
mod declarations;
mod logical;
#[cfg(feature = "batch-pilot")]
#[allow(dead_code)] // The standalone experiment also uses the slice-based kernel API.
mod batch_order;
mod fill_budget;
pub mod flex;
pub mod tracks;
mod flow;
mod full_layout;
mod input_words;
mod margin_storage;
mod node_data;
mod node_flags;
pub mod measurement;
mod place;
mod placement_adapter;
mod placement_geometry;
mod packed_stack_leaf;
mod placement_work;
mod prepare_frame;
mod prepare_leaf;
mod prepare_nodes;
mod sizing_pass;
mod tree_walk;
mod vec_memory;
mod work_stack;
#[cfg(feature = "incremental")]
mod fixed_leaf_cache;
#[cfg(feature = "incremental")]
mod incremental;
#[cfg(feature = "incremental")]
mod topology;
#[cfg(feature = "incremental")]
mod structural_changes;
#[cfg(feature = "incremental")]
mod region_policy;
#[cfg(feature = "incremental")]
mod retained_branch;
#[cfg(feature = "incremental")]
mod layout_tree;


use std::fmt::Debug;

pub use logical::{Direction, Logical, LogicalAxis, LogicalError, LogicalStyle, WritingContext, WritingMode};
pub use declarations::{Axis, ChildrenLayout, ContentMeasure, LayoutParams, MainAxisCellSize, Margin, Size, TextContent, Xy, XyRect};
pub(crate) use declarations::{X, Y};
pub use placement_geometry::{Anchor, Arrange, Pos, WindowOverflow};
pub use solve::NodeLayoutData;
pub(crate) use solve::*;
pub(crate) use flow::*;
#[cfg(feature = "incremental")]
pub(crate) use incremental::*;
#[cfg(feature = "incremental")]
pub(crate) use topology::{Topology, TopologySnapshot};
pub(crate) use place::Place;
pub use place::FreePlacementError;
#[cfg(feature = "incremental")]
pub use incremental::IncrementalRelayoutOutcome;
#[cfg(feature = "incremental")]
pub use layout_tree::rules as layout_rules;
#[cfg(feature = "incremental")]
pub use layout_tree::typography::{Baseline, InlineMeasurer, InlineMetrics, IntrinsicWidths, IntrinsicWidth, IntrinsicSizing, TypographyError};
#[cfg(feature = "incremental")]
pub use layout_tree::{ChildId, Destination, LayoutTree, NodeId, TreeError, measure_monospace_text};
#[cfg(feature = "batch-pilot")]
pub use layout_tree::{BatchLayoutError, BatchLayoutStats};
#[cfg(feature = "incremental")]
pub use tree_walk::AttachmentError;

/// The adapter trait that allows the layout algorithm to read your UI tree and compute the layout for it.
/// 
/// See the crate documentation for an example of implementing this trait.
#[cfg_attr(feature = "incremental", doc = "The built-in [`LayoutTree`] tracks edits automatically.")]
/// Supply a finite tree with consistent parent and sibling links, and keep its
/// layout inputs stable throughout a solve. Measurement callbacks may maintain
/// caches, but their result bits must depend only on the node, the supplied
/// constraints, and its current content. Incremental solves may skip callbacks
/// and reuse their previous results. Report changes to that content before the
/// next incremental solve, and keep output and warning callbacks from changing
/// the inputs or the solver's records during a solve. Initialize new node
/// records with [`NodeLayoutData::new`] and keep a distinct record for each live ID.
/// The read and mutable accessors for an ID address that node's record.
/// Preserve the solver state in those records and in [`LayoutData`] between
/// incremental calls. The registration methods update that state for edits.
/// Adapters can forward measurement callbacks to a [`measurement::Measurer`]
/// whose implementation is checked by Verus.
pub trait TreeAdapter {
    /// An id type that can be used to refer to nodes in your UI tree.
    type NodeId: Copy + Eq + Debug;
    /// The `NodeId` that refers to the root node.
    /// 
    /// The root node works as if it was a child of a node with the full `window_size` given to `solve_layout()`. Usually it should be `Size::Fill` on both axes so that it can take all of it.
    fn root(&self) -> Self::NodeId;
    /// Get the `NodeId` for a node's parent, or `None` for the root.
    fn parent(&self, i: Self::NodeId) -> Option<Self::NodeId>;
    /// Get the `NodeId` for a node's first child, or `None` if it has no children.
    fn first_child(&self, i: Self::NodeId) -> Option<Self::NodeId>;
    /// Get the `NodeId` for a node's next sibling, or `None` if it's the last child of its parent.
    fn next_sibling(&self, i: Self::NodeId) -> Option<Self::NodeId>;
    /// Read a the [`LayoutParams`] of the node corresponding to `i`.
    fn node_layout_params(&self, i: Self::NodeId) -> &LayoutParams;
    /// Access the [`NodeLayoutData`] of the node corresponding to `i`.
    fn node_layout_data(&self, i: Self::NodeId) -> &NodeLayoutData;
    /// Get a mutable reference to the [`NodeLayoutData`] of the node corresponding to `i`.
    fn node_layout_data_mut(&mut self, i: Self::NodeId) -> &mut NodeLayoutData;
    /// The layout data for the whole tree.
    fn layout_data(&mut self) -> &mut LayoutData<Self::NodeId>;
    /// The width of the text in a node, without any wrapping, in logical pixels.
    fn measure_text_width(&mut self, _i: Self::NodeId) -> f32 { 0.0 }
    
    /// The height of the text in a node, with its width optionally fixed to `wrap_width`, in logical pixels.
    fn measure_text_height(&mut self, _i: Self::NodeId, _wrap_width: Option<f32>) -> f32 { 0.0 }

    /// Measures arbitrary intrinsic content. Return its content-box size in logical pixels.
    ///
    /// The solver uses the component requested by `input.axis`. It adds padding and applies
    /// size bounds itself. Enable the callback with `LayoutParams::content_measure`.
    fn measure_content(&mut self, _i: Self::NodeId, _input: ContentMeasureInput) -> Xy<f32> { Xy::new_symm(0.0) }
    /// Called when the layout solver computes the end result for a node's rectangle.
    /// The output is provided in both absolute coordinates and relative to the parent, in logical pixels.
    /// NaN edges use the quiet NaN encoding `0x7fc00000`.
    fn write_output_rect(&mut self, i: Self::NodeId, rect: XyRect, local_rect: XyRect);

    /// Whether the adapter keeps the last written bits of both rectangles for
    /// each live node until it receives a replacement write. Return true to
    /// skip writes to unchanged subtrees during structural relayout.
    #[cfg(feature = "incremental")]
    fn retains_output_rects(&self) -> bool { false }

    /// Capacity hint for the checked Stack leaf preparation paths.
    #[doc(hidden)]
    #[cfg(feature = "batch-pilot")]
    fn stack_leaf_count_hint(&self, node: Self::NodeId) -> u32 {
        self.node_layout_data(node).n_placed_children
    }

    /// Estimated population available for reserving prepared leaf rows.
    #[doc(hidden)]
    #[cfg(feature = "batch-pilot")]
    fn first_stack_population_hint(&self) -> u32 { 0 }

    /// Called when the layout solver finds a problem in a node's layout.
    /// 
    /// Depending on the use case, this can be reported to the user.
    fn layout_warning(&mut self, _warning: LayoutWarning<Self::NodeId>) {}

    /// Solves the layout on all nodes. `window_size` is the size of the window, in logical pixels.
    /// The default unchecked incremental solve calls this method when it falls back.
    fn solve_layout(&mut self, window_size: Xy<f32>) {
        self.solve_full::<false>(window_size);
    }

    /// Reuses measurements from the previous solve after registered changes.
    /// Report edits with [`Self::register_node_change`], [`Self::register_content_change`],
    /// [`Self::register_children_change`], or [`Self::register_child_attached`]. The checked
    /// variant compares the resulting sizes and emitted view with a full solve.
    ///
    /// Structural edits rebuild the affected sizing dependencies, including groups
    /// sharing space at the root. Unchanged intrinsic measurements can be reused
    /// within those groups. Adapters with persistent output can opt into partial
    /// placement through [`Self::retains_output_rects`].
    #[cfg(feature = "incremental")]
    fn solve_layout_incremental(&mut self, window_size: Xy<f32>) -> IncrementalRelayoutOutcome {
        self.solve_incremental(window_size, false)
    }

    /// After successful incremental measurement, compares its sizing slots and
    /// complete view against the engine's canonical full solve. Checks node order
    /// and the exact bits of both rectangles. Publishes the engine's full result,
    /// including when incremental measurement falls back. Reports
    /// `IncrementalRelayoutOutcome::CheckedIncrementalRelayoutMismatch` if the compared views differ.
    #[cfg(feature = "incremental")]
    fn solve_layout_incremental_checked(&mut self, window_size: Xy<f32>) -> IncrementalRelayoutOutcome {
        self.solve_incremental(window_size, true)
    }

    /// Records that the params of a node changed for incremental relayouts. Call it after the tree has the new params. Changes to sizing rules also refresh the affected part of the dependency graph.
    #[cfg(feature = "incremental")]
    fn register_node_change(&mut self, i: Self::NodeId, old: &LayoutParams) {
        self.incr_register_node_change(i, old);
        self.update_remembered_params(i, old);
    }

    /// Records that the text or other intrinsic content of a node changed for incremental relayouts.
    #[cfg(feature = "incremental")]
    fn register_content_change(&mut self, i: Self::NodeId) {
        self.incr_register_content_change(i);
    }

    /// Records a removal or a reorder within `parent` after updating the tree links.
    /// For a move, call this with the old parent and [`Self::register_child_attached`]
    /// with the moved child.
    #[cfg(feature = "incremental")]
    fn register_children_change(&mut self, parent: Self::NodeId) {
        self.incr_register_children_change(parent, None);
    }

    /// Records an insertion after updating the tree links. The child's current
    /// parent receives the child-list change, and the attached subtree is refreshed.
    ///
    /// # Errors
    ///
    /// Returns [`AttachmentError`] before recording a change if the child is the
    /// root or its parent chain ends outside the active tree. Supply a live ID
    /// accepted by the adapter's accessors.
    #[cfg(feature = "incremental")]
    fn register_child_attached(&mut self, child: Self::NodeId) -> Result<(), AttachmentError> {
        let parent = tree_walk::registered_parent(self, self.root(), child)?;
        self.incr_register_children_change(parent, Some(child));
        Ok(())
    }

    /// Reports changes to the tree or its layout parameters whose locations are unknown.
    /// The next incremental solve scans the live links and parameters to find the affected
    /// subtrees. Initialize replacement nodes with [`NodeLayoutData::new`], even when
    /// reusing a node ID. Report changes inside measurement callbacks with
    /// [`Self::register_content_change`]. Use [`Self::register_children_change`]
    /// and [`Self::register_child_attached`] for edits at known locations.
    #[cfg(feature = "incremental")]
    fn register_structural_change(&mut self) {
        if self.layout_data().start_children_change() {
            self.layout_data().unknown_structure = true;
        }
    }

    /// Repositions a subtree using its solved sizes and its parent's unrounded
    /// rectangle in logical pixels. A child can be placed independently when
    /// its parent uses [`ChildrenLayout::Free`] or its own `free_placement` is set.
    ///
    /// # Errors
    ///
    /// Returns [`FreePlacementError`] before writing output if the target is
    /// the root, is detached, participates in its parent's flow, belongs to
    /// a disabled subtree, or has visible nodes without the sizing values used
    /// by placement. A wrapping container also needs each in-flow child's
    /// cross-axis base size and applicable bounds. Supply a live ID accepted
    /// by the adapter's accessors.
    fn place_free_placed_subtree(&mut self, node: Self::NodeId, parent_rect: XyRect) -> Result<(), FreePlacementError> {
        self.place_free_node(node, parent_rect)
    }
}

#[cfg(feature = "incremental")]
impl std::fmt::Display for AttachmentError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Root => "the layout root has no parent to notify",
            Self::Detached => "the node is detached from the layout root",
        })
    }
}

#[cfg(feature = "incremental")]
impl std::error::Error for AttachmentError {}

impl std::fmt::Display for FreePlacementError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Root => "the layout window positions the root",
            Self::Detached => "the node is detached from the layout root",
            Self::Disabled => "the node belongs to a disabled subtree",
            Self::InFlow => "the parent positions this in-flow child",
            Self::Unsolved => "a visible node in the subtree lacks a solved size",
        })
    }
}

impl std::error::Error for FreePlacementError {}

/// A warning about a potential problem in the user's layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum LayoutWarning<Id> {
    /// A node is stuck in a dependency cycle.
    Cycle {
        /// The id of the node stuck in the cycle.
        node: Id,
        /// Which of the node's dimensions is stuck in the cycle.
        axis: Axis
    },
    /// The node's size is `AspectRatio` on both axes.
    /// 
    /// This also shows up as a `Cycle`.
    AspectRatioOnBothAxes {
        /// The id of the problematic node.
        node: Id,
    },
    /// A `FitContent` node only has `Fill` or `Frac` children, so its size collapsed to zero.
    FitContentCollapsed {
        /// The id of the problematic node.
        node: Id,
        /// Which of the node's dimensions the problem was found in.
        axis: Axis
    },
    /// The node's min size is bigger than its max size.
    MinAboveMax {
        /// The id of the problematic node.
        node: Id,
        /// Which of the node's dimensions the problem was found in.
        axis: Axis
    },
    /// A `FitContent` stack could not resolve its extent because its unconstrained fractions total 100% or more.
    ImpossibleFracChildren {
        /// The id of the problematic node.
        node: Id,
        /// Which of the node's dimensions the problem was found in.
        axis: Axis
    },
    /// The node's size is infinite or NaN.
    NotFinite {
        /// The id of the problematic node.
        node: Id,
        /// Which of the node's dimensions the problem was found in.
        axis: Axis
    },
}

#[cfg(feature = "incremental")]
impl<Id> LayoutWarning<Id> {
    pub(crate) fn map_node<Other>(self, map: impl FnOnce(Id) -> Other) -> LayoutWarning<Other> {
        match self {
            Self::Cycle { node, axis } => LayoutWarning::Cycle { node: map(node), axis },
            Self::AspectRatioOnBothAxes { node } => LayoutWarning::AspectRatioOnBothAxes { node: map(node) },
            Self::FitContentCollapsed { node, axis } => LayoutWarning::FitContentCollapsed { node: map(node), axis },
            Self::MinAboveMax { node, axis } => LayoutWarning::MinAboveMax { node: map(node), axis },
            Self::ImpossibleFracChildren { node, axis } => LayoutWarning::ImpossibleFracChildren { node: map(node), axis },
            Self::NotFinite { node, axis } => LayoutWarning::NotFinite { node: map(node), axis },
        }
    }
}

impl<Id: Debug> std::fmt::Display for LayoutWarning<Id> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LayoutWarning::Cycle { node, axis } => write!(f,
                "The {axis:?} size of node '{node:?}' is stuck in a dependency cycle."
            ),
            LayoutWarning::AspectRatioOnBothAxes { node } => write!(f,
                "Node '{node:?}' is `AspectRatio` on both axes. This will also show up as a cycle."
            ),
            LayoutWarning::FitContentCollapsed { node, axis } => write!(f,
                "The {axis:?} size of node '{node:?}' is `FitContent`, but it only has `Fill` or `Frac` children and no intrinsic content, so its size collapsed to zero."
            ),
            LayoutWarning::MinAboveMax { node, axis } => write!(f,
                "On the {axis:?} axis, the '{node:?}' node's min size is bigger than its max size. "
            ),
            LayoutWarning::ImpossibleFracChildren { node, axis } => write!(f,
                "The {axis:?} extent of `FitContent` node '{node:?}' is unresolved. Its active `Frac` children claim at least 100% of the available space."
            ),
            LayoutWarning::NotFinite { node, axis } => write!(f,
                "The {axis:?} size of node '{node:?}' is infinite or NaN."
            ),
        }
    }
}

/// Inputs to a custom intrinsic content measurement.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct ContentMeasureInput {
    /// The dimension the solver is measuring.
    pub axis: Axis,
    /// Resolved content-box dimensions required by the measurement mode, in logical pixels.
    pub known_dimensions: Xy<Option<f32>>,
    /// Explicit pixel maximums for the content box. The solver also enforces bounds declared
    /// with other size rules.
    pub max_size: Xy<Option<f32>>,
}

impl measurement::Request {
    /// Encodes the width argument of `TreeAdapter::measure_text_height`.
    #[inline]
    pub fn text_height(wrap_width: Option<f32>) -> Self {
        Self::TextHeight { wrap_width: wrap_width.map(f32::to_bits) }
    }
}

impl From<ContentMeasureInput> for measurement::Request {
    #[inline]
    fn from(input: ContentMeasureInput) -> Self {
        Self::Content {
            axis: match input.axis {
                X => measurement::Axis::X,
                Y => measurement::Axis::Y,
            },
            known_dimensions: [input.known_dimensions.x, input.known_dimensions.y].map(|value| value.map(f32::to_bits)),
            max_size: [input.max_size.x, input.max_size.y].map(|value| value.map(f32::to_bits)),
        }
    }
}

impl measurement::SizeBits {
    /// Decodes the result for a `TreeAdapter` measurement callback.
    #[inline]
    pub fn to_size(self) -> Xy<f32> {
        Xy::new(f32::from_bits(self.x), f32::from_bits(self.y))
    }
}

/// A positive finite number of physical pixels per logical pixel.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PixelScale(f32);

impl PixelScale {
    /// One physical pixel per logical pixel.
    pub const ONE: Self = Self(1.0);

    /// Returns the scale if it is positive and finite.
    pub const fn new(scale: f32) -> Option<Self> {
        if input_words::positive_finite(scale.to_bits()) { Some(Self(scale)) } else { None }
    }

    /// The number of physical pixels per logical pixel.
    pub const fn get(self) -> f32 {
        self.0
    }
}

/// The supplied pixel scale was outside the positive finite range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidPixelScale;

impl std::fmt::Display for InvalidPixelScale {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("pixel scale must be positive and finite")
    }
}

impl std::error::Error for InvalidPixelScale {}

impl TryFrom<f32> for PixelScale {
    type Error = InvalidPixelScale;

    fn try_from(scale: f32) -> Result<Self, Self::Error> {
        Self::new(scale).ok_or(InvalidPixelScale)
    }
}

/// Solver data and output settings for the whole tree.
#[derive(Debug, Clone)]
pub struct LayoutData<I> {
    pub(crate) fills_scratch: Vec<FillChild>,
    pub(crate) occupied_scratch: Vec<u64>,
    /// The `window_size` of the last solve.
    pub(crate) window_size: Xy<f32>,
    pub(crate) pixel_scale: Option<f32>,
    #[cfg(feature = "incremental")]
    pub(crate) placement_scale_changed: bool,
    pub(crate) block_margins: Vec<BlockMargins>,
    pub(crate) prepare_stack: Vec<(prepare_frame::PrepareFrame<I>, I)>,
    pub(crate) sizing_stack: Vec<SizingTask<I>>,

    #[cfg(feature = "incremental")]
    pub(crate) node_changes: Vec<(I, NodeChange)>,
    #[cfg(feature = "incremental")]
    pub(crate) content_changes: Vec<I>,
    #[cfg(feature = "incremental")]
    // The pending fallback was raised by edit intake, before any sizing ran.
    pub(crate) replay_pending: bool,
    #[cfg(feature = "incremental")]
    pub(crate) children_changed: bool,
    #[cfg(feature = "incremental")]
    pub(crate) unknown_structure: bool,
    #[cfg(feature = "incremental")]
    // Preserve the declarations/links once an adapter uses incremental layout,
    // retains output, or measures host content that can be reused by a later edit.
    pub(crate) track_topology: bool,
    #[cfg(feature = "incremental")]
    pub(crate) topology: Option<TopologySnapshot<I>>,
    #[cfg(feature = "incremental")]
    pub(crate) regions: Vec<I>,
    #[cfg(feature = "incremental")]
    pub(crate) plan_spill: Vec<incremental::Suspended<I>>,
    #[cfg(feature = "incremental")]
    pub(crate) margin_scratch: Vec<BlockMargins>,
    #[cfg(feature = "incremental")]
    pub(crate) checked_values: Vec<(I, [u32; N_SLOTS])>,
    #[cfg(feature = "incremental")]
    pub(crate) packed_stack_leaves: crate::packed_stack_leaf::PackedStackLeaves<I>,
    #[cfg(feature = "incremental")]
    pub(crate) checked_view: Vec<incremental::OutputRecord<I>>,
    #[cfg(feature = "incremental")]
    pub(crate) pending_full_solve: Option<IncrementalRelayoutOutcome>,
    #[cfg(feature = "incremental")]
    pub(crate) has_cycle: bool,
    #[cfg(feature = "incremental")]
    pub(crate) has_flow: bool,
    #[cfg(feature = "incremental")]
    pub(crate) n_nodes_solved: u32,
    /// During a full solve, 1 + the highest level of the dependencies of the slot that is being solved.
    #[cfg(feature = "incremental")]
    pub(crate) current_level: u16,
    #[cfg(feature = "incremental")]
    pub(crate) numeric_touched: Vec<I>,
    #[cfg(feature = "incremental")]
    pub(crate) queue: WorkQueue<Slot<I>>,
    #[cfg(feature = "incremental")]
    pub(crate) numeric_tape: incremental::tape::Tape<I, NodeChange, incremental::tape_plan::Ranked<I>>,
    #[cfg(feature = "incremental")]
    pub(crate) numeric_wrap: Option<bool>,
    #[cfg(feature = "incremental")]
    pub(crate) sizing_warned: bool,

    #[cfg(not(feature = "incremental"))]
    _marker: std::marker::PhantomData<I>,
}

impl<I> LayoutData<I> {
    /// Creates a new [`LayoutData`].
    pub const fn new() -> Self {
        LayoutData {
            #[cfg(feature = "incremental")]
            node_changes: Vec::new(),
            #[cfg(feature = "incremental")]
            content_changes: Vec::new(),
            #[cfg(feature = "incremental")]
            replay_pending: false,
            #[cfg(feature = "incremental")]
            children_changed: false,
            #[cfg(feature = "incremental")]
            unknown_structure: false,
            #[cfg(feature = "incremental")]
            track_topology: false,
            #[cfg(feature = "incremental")]
            topology: Some(TopologySnapshot::new()),
            #[cfg(feature = "incremental")]
            regions: Vec::new(),
            #[cfg(feature = "incremental")]
            plan_spill: Vec::new(),
            #[cfg(feature = "incremental")]
            margin_scratch: Vec::new(),
            #[cfg(feature = "incremental")]
            checked_values: Vec::new(),
            #[cfg(feature = "incremental")]
            packed_stack_leaves: crate::packed_stack_leaf::PackedStackLeaves::new(),
            #[cfg(feature = "incremental")]
            checked_view: Vec::new(),
            #[cfg(feature = "incremental")]
            pending_full_solve: Some(IncrementalRelayoutOutcome::FallbackNeverSolved),
            #[cfg(feature = "incremental")]
            has_cycle: false,
            #[cfg(feature = "incremental")]
            has_flow: false,
            #[cfg(feature = "incremental")]
            n_nodes_solved: 0,
            #[cfg(feature = "incremental")]
            current_level: 0,
            #[cfg(feature = "incremental")]
            numeric_touched: Vec::new(),
            #[cfg(feature = "incremental")]
            queue: WorkQueue::new(),
            #[cfg(feature = "incremental")]
            numeric_tape: incremental::tape::Tape::new(),
            #[cfg(feature = "incremental")]
            numeric_wrap: None,
            #[cfg(feature = "incremental")]
            sizing_warned: false,
            fills_scratch: Vec::new(),
            occupied_scratch: Vec::new(),
            window_size: Xy::new(0.0, 0.0),
            pixel_scale: None,
            #[cfg(feature = "incremental")]
            placement_scale_changed: false,
            block_margins: Vec::new(),
            prepare_stack: Vec::new(),
            sizing_stack: Vec::new(),
            #[cfg(not(feature = "incremental"))]
            _marker: std::marker::PhantomData,
        }
    }
}

impl<I> LayoutData<I> {
    /// Enable output rounding at the given number of physical pixels per logical pixel.
    /// The setting applies at the next placement. Pass `None` for fractional output.
    pub fn set_pixel_scale(&mut self, scale: Option<PixelScale>) {
        let scale = scale.map(PixelScale::get);
        #[cfg(feature = "incremental")]
        placement_adapter::set_scale::<placement_geometry::RustFloat>(
            &mut self.pixel_scale, &mut self.placement_scale_changed, scale,
        );
        #[cfg(not(feature = "incremental"))]
        { self.pixel_scale = scale; }
    }
}

impl<I> Default for LayoutData<I> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod numeric_input_tests {
    use super::{InvalidPixelScale, Margin, PixelScale};

    #[test]
    fn pixel_scale_accepts_only_positive_finite_values() {
        const MIN_SCALE: f32 = f32::from_bits(1);
        const SUBNORMAL: Option<PixelScale> = PixelScale::new(MIN_SCALE);
        const INVALID: Option<PixelScale> = PixelScale::new(f32::INFINITY);

        assert_eq!(PixelScale::ONE.get(), 1.0);
        assert_eq!(SUBNORMAL.unwrap().get().to_bits(), 1);
        assert_eq!(PixelScale::try_from(f32::MAX).unwrap().get(), f32::MAX);
        assert_eq!(INVALID, None);
        for scale in [0.0, -0.0, -1.0, -MIN_SCALE, f32::NAN, f32::NEG_INFINITY] {
            assert_eq!(PixelScale::try_from(scale), Err(InvalidPixelScale));
        }
    }

    #[test]
    fn pixel_margin_accepts_signed_finite_values_and_keeps_auto_distinct() {
        const NEGATIVE: Option<Margin> = Margin::px(-1.25);
        const INVALID: Option<Margin> = Margin::px(f32::NAN);

        assert_eq!(NEGATIVE.unwrap().as_px(), Some(-1.25));
        assert_eq!(Margin::px(f32::MAX).unwrap().as_px(), Some(f32::MAX));
        assert_eq!(Margin::px(-0.0), Some(Margin::ZERO));
        assert_eq!(Margin::ZERO.as_px().unwrap().to_bits(), 0);
        assert_eq!(Margin::AUTO.as_px(), None);
        assert_ne!(Margin::AUTO, Margin::ZERO);
        assert_eq!(Margin::px(f32::INFINITY), None);
        assert_eq!(Margin::px(f32::NEG_INFINITY), None);
        assert_eq!(INVALID, None);
    }
}
