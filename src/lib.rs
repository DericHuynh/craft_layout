#![doc = include_str!("../README.md")]

#![warn(missing_docs)]

#[macro_use]
mod child_walk;
#[macro_use]
mod solve;
mod fill_budget;
mod flow;
mod input_words;
mod margin_storage;
pub mod measurement;
mod place;
mod tree_walk;
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
use std::ops::{Index, IndexMut};

pub use solve::NodeLayoutData;
pub(crate) use solve::*;
pub(crate) use flow::*;
#[cfg(feature = "incremental")]
pub(crate) use incremental::*;
#[cfg(feature = "incremental")]
pub(crate) use topology::{Topology, TopologySnapshot};
pub(crate) use place::Place;
#[cfg(feature = "incremental")]
pub use incremental::IncrementalRelayoutOutcome;
#[cfg(feature = "incremental")]
pub use layout_tree::{ChildId, Destination, LayoutTree, NodeId, TreeError, measure_monospace_text};

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
/// the inputs to the solve in progress. Adapters can forward measurement
/// callbacks to a [`measurement::Measurer`] whose implementation is checked by Verus.
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
    fn write_output_rect(&mut self, i: Self::NodeId, rect: XyRect, local_rect: XyRect);

    /// Whether the adapter keeps the last written bits of both rectangles for
    /// each live node until it receives a replacement write. Return true to
    /// skip writes to unchanged subtrees during structural relayout.
    #[cfg(feature = "incremental")]
    fn retains_output_rects(&self) -> bool { false }

    /// Called when the layout solver finds a problem in a node's layout.
    /// 
    /// Depending on the use case, this can be reported to the user.
    fn layout_warning(&mut self, _warning: LayoutWarning<Self::NodeId>) {}

    /// Solves the layout on all nodes. `window_size` is the size of the window, in logical pixels.
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
    /// and the exact bits of both rectangles. Publishes the full result and reports
    /// `IncrementalRelayoutOutcome::CheckedIncrementalRelayoutMismatch` if they differ.
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
        let root = self.root();
        if child == root {
            return Err(AttachmentError::Root);
        }
        let parent = self.parent(child).ok_or(AttachmentError::Detached)?;
        let mut ancestor = parent;
        while ancestor != root {
            ancestor = self.parent(ancestor).ok_or(AttachmentError::Detached)?;
        }
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
    /// a disabled subtree, or has visible nodes without solved sizes. Supply
    /// a live ID accepted by the adapter's accessors.
    fn place_free_placed_subtree(&mut self, node: Self::NodeId, parent_rect: XyRect) -> Result<(), FreePlacementError> {
        self.place_free_node(node, parent_rect)
    }
}

/// Reason why a node cannot be registered as a newly attached child.
#[cfg(feature = "incremental")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum AttachmentError {
    /// The layout root has no parent to notify.
    Root,
    /// The node's parent chain ends outside the active tree.
    Detached,
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

/// Reason why a subtree cannot be repositioned independently.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FreePlacementError {
    /// The root takes its rectangle from the layout window.
    Root,
    /// The node's parent chain ends outside the active tree.
    Detached,
    /// The node or one of its ancestors is disabled.
    Disabled,
    /// The parent positions this node as an in-flow child.
    InFlow,
    /// The target or a visible descendant lacks a solved width or height.
    Unsolved,
}

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

/// The X or Y axes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Axis {
    /// The X axis.
    X,
    /// The Y axis.
    Y,
}

impl Axis {
    /// The axis orthogonal to `self`: Y if `self` is X and X if `self` is Y.
    pub fn other(&self) -> Self {
        match self {
            Axis::X => Axis::Y,
            Axis::Y => Axis::X,
        }
    }
}

pub(crate) use Axis::{X, Y};

/// A generic container for two-dimensional data.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct Xy<T> {
    /// The X component.
    pub x: T,
    /// The Y component.
    pub y: T,
}

impl<T> Xy<T> {
    /// Create a new `Xy<T>`.
    pub const fn new(x: T, y: T) -> Self {
        Self { x, y }
    }
}

impl<T: Copy> Xy<T> {
    /// Create a new `Xy<T>` with the same value on both axes.
    pub const fn new_symm(v: T) -> Self {
        Self { x: v, y: v }
    }
}

impl<T> Index<Axis> for Xy<T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, axis: Axis) -> &T {
        match axis {
            Axis::X => &self.x,
            Axis::Y => &self.y,
        }
    }
}

impl<T> IndexMut<Axis> for Xy<T> {
    #[inline(always)]
    fn index_mut(&mut self, axis: Axis) -> &mut T {
        match axis {
            Axis::X => &mut self.x,
            Axis::Y => &mut self.y,
        }
    }
}

/// A 2D rectangle, expressed as a start and end coordinates on each axis.
/// 
/// Alias of `Xy<[f32; 2]>`.
pub type XyRect = Xy<[f32; 2]>;

#[derive(Debug, Clone, Copy, PartialEq)]
/// The size of a layout node.
pub enum Size {
    /// A fixed size in logical pixels.
    Pixels(f32),
    /// A fraction of the parent element.
    /// 
    /// Collapses to zero if the parent has a size of zero, or if it's `FitContent` and has no other children that can give it a size. 
    Frac(f32),
    /// Fill all the available space in the parent element.
    /// 
    /// Multiple `Fill` children in a stack or wrap line divide its main-axis space according
    /// to their `fill_weight`.
    /// 
    /// Collapses to zero if the parent has a size of zero, or if it's `FitContent` and has no other children that can give it a size. 
    Fill,
    /// As big as the element's children or the intrinsic content such as text, plus the `padding`.
    FitContent,
    /// In-flow block width fills the containing block, while height fits the content.
    /// In other layouts both axes fit the content.
    Auto,
    /// A size that depends on the size of this same element in the other axis, according to an aspect ratio.
    AspectRatio(f32),
}

#[derive(Debug, Clone, Copy, PartialEq)]
/// The "origin" of a layout node inside its own rectangle.
/// 
/// For example, an element with `Size::Pixels(10.0)` and `Pos::Pixels(0.0)` on an axis will be placed at `[0.0, 10.0]`, `[-5.0, 5.0]` or `[-10.0, 0.0]` if its `Anchor` is `Start`, `Center` or `End` respectively.
/// 
/// Has no effect in a stack's main axis, or for `Pos` values other than `Pixels` and `Frac`.
pub enum Anchor {
    /// The left or top edge of the element's rectangle.
    Start,
    /// The center of the element's rectangle.
    Center,
    /// The right or bottom edge of the element's rectangle.
    End,
    /// Any fraction, with `0.0` corresponding to the left or top edge and `1.0` corresponding to the right or bottom edge.
    Frac(f32),
}

#[derive(Debug, Clone, Copy, PartialEq)]
/// The position of a layout node in the space of its parent.
/// 
/// If the node is a child of a stack, its `Pos` value on the stack's main axis is ignored, as the stack positions the child according to its own logic.
/// 
/// In a grid, the `Pos` value controls how the node is placed within the space of a grid cell.
/// In normal block flow, margins and the containing block determine in-flow positions.
pub enum Pos {
    /// The left or top side of the parent.
    Start,
    /// The center of the parent.
    Center,
    /// The right or bottom side of the parent.
    End,
    /// A fixed number of pixels starting from the left or top side of the parent.
    Pixels(f32),
    /// A fraction of the parent's size starting from its left or top side.
    Frac(f32),
}

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
    /// A `FitContent` node couldn't determine consistent sizes for its `Frac` children, because they add up to more than 100%.
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
                "On the {axis:?} axis, the '{node:?}' `FitContent` node couldn't determine consistent sizes for its `Frac` children, because they add up to more than 100%."
            ),
            LayoutWarning::NotFinite { node, axis } => write!(f,
                "The {axis:?} size of node '{node:?}' is infinite or NaN."
            ),
        }
    }
}

/// What to do if a freely placed node would extend past the edges of the window. It has no effect on the children of a `Stack` or a `Grid`, unless they are `free_placement`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum WindowOverflow {
    /// Leave the node where it is, even if it extends past the window edge.
    #[default]
    Ignore,
    /// Push the node back inside the window.
    Clamp,
    /// Mirror the node to the other side of its anchor point, as a right-click context menu does. If the mirrored node also doesn't fit, push it back inside the window.
    Flip,
}

/// The way that a stack's children are arranged along its main axis.
#[derive(Debug, Clone, Copy, Hash, PartialEq)]
pub enum Arrange {
    /// The children are arranged close together at the start of the stack.
    Start,
    /// The children are arranged close together at the end of the stack.
    End,
    /// The children are arranged close together in the center of the stack.
    Center,
    /// The free space is divided equally between the children, with no space at the edges.
    SpaceBetween,
    /// Each child gets an equal amount of free space on both sides, so the space at the edges is half the space between the children.
    SpaceAround,
    /// The free space is divided equally between the children and the edges.
    SpaceEvenly,
}

/// What determines the size and number of cells on the main axis of a grid.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MainAxisCellSize {
    /// Fix the number of cells and derive the cell size from the grid size.  
    Count(u32),
    /// Fix the size of the cells and derive the cell count from the grid size.
    /// 
    /// A grid with `FitContent` on its main axis uses one track. A cell width and
    /// spacing that add to zero also produce one track.
    Width(f32),
}

/// Whether the node is a stack or a grid that arranges its children according to a specific rule.
/// 
/// Individual children can override this by setting `free_placement = true`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ChildrenLayout {
    /// Every child can position itself freely according to its `Pos`.
    Free,
    /// Children are arranged on a stack.
    /// 
    /// This means that the children's `Pos` value on the stack's axis is ignored, but it can still be used to control alignment on the cross axis. 
    Stack {
        /// The way that the stack's children are arranged along its main axis.
        arrange: Arrange,
        /// The "main" axis along which the children are stacked.
        axis: Axis,
        /// The spacing between the stacked children.
        spacing: f32,
    },
    /// Place children in successive rows or columns. A child that would overflow starts a new line.
    Wrap {
        /// Primary direction of each line.
        axis: Axis,
        /// How children are distributed along each line.
        arrange: Arrange,
        /// Space between items on the same line.
        spacing: f32,
        /// Space between lines.
        line_spacing: f32,
    },
    /// Normal block flow. Children stack vertically with adjoining block margins collapsed.
    /// Block positions come from flow and inline margins. Flip the X origin for right-to-left placement.
    Block,
    /// Children are arranged in a grid.
    ///
    /// The `Pos` value of the children on both axes can still be used to place them within the space of the grid cell.
    Grid {
        /// What determines the size and number of cells on the main axis of the grid.
        columns: MainAxisCellSize,
        /// The spacing between grid elements along the `X` axis.
        spacing_x: f32,
        /// The spacing between grid elements along the `Y` axis.
        spacing_y: f32,
        /// The axis along which the children are arranged.
        main_axis: Axis,
        /// Whether later children can fill a gap left by previous children.
        /// 
        /// Gaps can only be left when elements have span greater than the default of one.
        backfill: bool,
    },
}

/// The text content of a node, if any. The solver will measure it with `TreeAdapter::measure_text_width()` and `TreeAdapter::measure_text_height()`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TextContent {
    /// The node has no text.
    None,
    /// Text that wraps. Its height depends on the node's width.
    Wrapping,
    /// Text that doesn't wrap. Its width and height don't depend on the node's size.
    Fixed,
}

/// An in-flow margin on one edge of a node's box.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Margin(u32);

impl Margin {
    /// A margin of zero logical pixels.
    pub const ZERO: Self = Self(0);

    /// Share the unused inline space in block flow. On other edges it is zero.
    pub const AUTO: Self = Self(f32::NAN.to_bits());

    /// A finite margin in logical pixels. Negative values are allowed.
    ///
    /// Returns `None` for infinite or NaN values.
    pub const fn px(pixels: f32) -> Option<Self> {
        match input_words::finite_margin(pixels.to_bits()) {
            Some(word) => Some(Self(word)),
            None => None,
        }
    }

    /// The margin in logical pixels, or `None` for an automatic margin.
    pub const fn as_px(self) -> Option<f32> {
        if self.0 == Self::AUTO.0 { None } else { Some(f32::from_bits(self.0)) }
    }

    #[inline(always)]
    pub(crate) fn pixels(self) -> f32 {
        self.as_px().unwrap_or(0.0)
    }
}

impl Debug for Margin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.as_px() {
            Some(pixels) => f.debug_tuple("Pixels").field(&pixels).finish(),
            None => f.write_str("Auto"),
        }
    }
}

impl Default for Margin {
    fn default() -> Self {
        Self::ZERO
    }
}

/// Which resolved dimension an intrinsic content measurement needs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ContentMeasure {
    /// No custom intrinsic content.
    #[default]
    None,
    /// Each dimension can be measured independently.
    Independent,
    /// The intrinsic height depends on the resolved content width.
    HeightForWidth,
    /// The intrinsic width depends on the resolved content height.
    WidthForHeight,
}

impl ContentMeasure {
    pub(crate) fn reads_other_axis(self, axis: Axis) -> bool {
        matches!((self, axis), (Self::HeightForWidth, Y) | (Self::WidthForHeight, X))
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

/// The parameters that define a node's layout, from its own sizing to how it places its children.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LayoutParams {
    /// The position of a layout node in the space of its parent.
    pub position: Xy<Pos>,
    /// The size of a layout node on its two axes.
    pub size: Xy<Size>,
    /// The minimum size of a layout node on its two axes.
    pub min_size: Xy<Option<Size>>,
    /// The maximum size of a layout node on its two axes.
    pub max_size: Xy<Option<Size>>,
    /// The space that this node keeps for itself as padding before giving space to its children.
    pub padding: Xy<[f32; 2]>,
    /// Space outside the node's box in a stack, wrap, grid, or block. Each pair uses physical
    /// start/end order (left/right or top/bottom). Free placement ignores margins.
    pub margin: Xy<[Margin; 2]>,
    /// How this node positions its children.
    pub children_layout: ChildrenLayout,
    /// Place this node freely within the parent, outside the parent's in-flow layout.
    pub free_placement: bool,
    /// Whether this node should occupy more than one cell if this node is a child of a grid.
    pub grid_span: Xy<u16>,
    /// The text content of this node, if any.
    pub text: TextContent,
    /// Optional content measured by `TreeAdapter::measure_content()`.
    pub content_measure: ContentMeasure,
    /// The image or fixed-size content of a node, if any. 
    pub image: Option<Xy<f32>>,
    /// The "origin" of a layout node inside its own rectangle.
    pub anchor: Xy<Anchor>,
    /// If true for one axis, children elements are placed starting from the right or bottom edge. If the node is a stack or a grid, the order in which children are arranged is reversed. 
    pub children_origin_flipped: Xy<bool>,
    /// The node's behavior if it extends past the edges of the window.
    pub window_overflow: Xy<WindowOverflow>,
    /// In a stack, the `Fill` children share the free space in proportion to their weight. It has no effect on the other axis.
    pub fill_weight: f32,
    /// True if a node should be ignored by the layout solver. When a node is disabled, all its descendants must be disabled too.
    pub disabled: bool,

}

impl LayoutParams {
    /// Default values for the `LayoutParams`.
    pub const DEFAULT: LayoutParams = LayoutParams {
        size: Xy { x: Size::Fill, y: Size::Fill },
        min_size: Xy { x: None, y: None },
        max_size: Xy { x: None, y: None },
        fill_weight: 1.0,
        padding: Xy { x: [0.0, 0.0], y: [0.0, 0.0] },
        margin: Xy::new_symm([Margin::ZERO; 2]),
        children_layout: ChildrenLayout::Free,
        free_placement: false,
        grid_span: Xy { x: 1, y: 1 },
        text: TextContent::None,
        content_measure: ContentMeasure::None,
        image: None,
        disabled: false,
        position: Xy { x: Pos::Center, y: Pos::Center },
        anchor: Xy { x: Anchor::Center, y: Anchor::Center },
        children_origin_flipped: Xy { x: false, y: false },
        window_overflow: Xy { x: WindowOverflow::Ignore, y: WindowOverflow::Ignore },
    };
}

impl Default for LayoutParams {
    fn default() -> Self {
        Self::DEFAULT
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
    pub(crate) prepare_stack: Vec<(PrepareFrame<I>, I)>,

    #[cfg(feature = "incremental")]
    pub(crate) node_changes: Vec<(I, NodeChange)>,
    #[cfg(feature = "incremental")]
    pub(crate) content_changes: Vec<I>,
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
    pub(crate) margin_scratch: Vec<BlockMargins>,
    #[cfg(feature = "incremental")]
    pub(crate) checked_values: Vec<(I, [u32; N_SLOTS])>,
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
    pub(crate) queue: WorkQueue<Slot<I>>,

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
            margin_scratch: Vec::new(),
            #[cfg(feature = "incremental")]
            checked_values: Vec::new(),
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
            queue: WorkQueue::new(),
            fills_scratch: Vec::new(),
            occupied_scratch: Vec::new(),
            window_size: Xy::new(0.0, 0.0),
            pixel_scale: None,
            #[cfg(feature = "incremental")]
            placement_scale_changed: false,
            block_margins: Vec::new(),
            prepare_stack: Vec::new(),
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
        {
            self.placement_scale_changed = update_scale_dirty(
                self.placement_scale_changed, self.pixel_scale != scale,
            );
        }
        self.pixel_scale = scale;
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
