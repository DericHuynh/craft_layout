//! Public layout declarations and their fixed-axis accessors.
#![allow(unexpected_cfgs)]

#[cfg(not(verus_keep_ghost))]
use crate::input_words;
#[cfg(not(verus_keep_ghost))]
use core::{fmt::Debug, ops::{Index, IndexMut}};
use crate::{Anchor, Arrange, Pos, WindowOverflow};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// The X or Y axes.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub enum Axis {
    /// The X axis.
    X,
    /// The Y axis.
    Y,
}

impl Axis {
    /// The axis orthogonal to `self`: Y if `self` is X and X if `self` is Y.
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == self.other(), out != *self,
        no_unwind
    ))]
    pub fn other(&self) -> Self {
        match self {
            Axis::X => Axis::Y,
            Axis::Y => Axis::X,
        }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(index =>
        ensures index < 2, index == self.index(),
        no_unwind
    ))]
    pub(crate) const fn index(self) -> usize {
        match self { Axis::X => 0, Axis::Y => 1 }
    }
}

pub(crate) use Axis::{X, Y};

/// A generic container for two-dimensional data.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub struct Xy<T> {
    /// The X component.
    pub x: T,
    /// The Y component.
    pub y: T,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<T> Xy<T> {
    /// Create a new `Xy<T>`.
    #[cfg_attr(verus_keep_ghost, verus_spec(pair =>
        ensures pair.x == x, pair.y == y,
        no_unwind
    ))]
    pub const fn new(x: T, y: T) -> Self {
        Self { x, y }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(component =>
        ensures *component == if axis is X { self.x } else { self.y },
        no_unwind
    ))]
    pub(crate) const fn component(&self, axis: Axis) -> &T {
        match axis {
            Axis::X => &self.x,
            Axis::Y => &self.y,
        }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(component =>
        ensures match axis {
            Axis::X => *component == old(self).x && *final(component) == final(self).x && final(self).y == old(self).y,
            Axis::Y => *component == old(self).y && *final(component) == final(self).y && final(self).x == old(self).x,
        },
        no_unwind
    ))]
    pub(crate) fn component_mut(&mut self, axis: Axis) -> &mut T {
        match axis {
            Axis::X => &mut self.x,
            Axis::Y => &mut self.y,
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<T: Copy> Xy<T> {
    /// Create a new `Xy<T>` with the same value on both axes.
    #[cfg_attr(verus_keep_ghost, verus_spec(pair =>
        ensures pair.x == v, pair.y == v,
        no_unwind
    ))]
    pub const fn new_symm(v: T) -> Self {
        Self { x: v, y: v }
    }
}

#[cfg(not(verus_keep_ghost))]
impl<T> Index<Axis> for Xy<T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, axis: Axis) -> &T {
        self.component(axis)
    }
}

#[cfg(not(verus_keep_ghost))]
impl<T> IndexMut<Axis> for Xy<T> {
    #[inline(always)]
    fn index_mut(&mut self, axis: Axis) -> &mut T {
        self.component_mut(axis)
    }
}

/// A 2D rectangle, expressed as a start and end coordinates on each axis.
///
/// Alias of `Xy<[f32; 2]>`.
pub type XyRect = Xy<[f32; 2]>;

#[derive(Debug, Clone, Copy, PartialEq)]
/// The size of a layout node.
#[cfg_attr(verus_keep_ghost, verus_verify)]
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

impl Size {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.is_flex(), no_unwind))]
    pub(crate) fn is_flex(&self) -> bool {
        matches!(self, Size::Frac(_) | Size::Fill)
    }
}

/// What determines the size and number of cells on the main axis of a grid.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
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
#[cfg_attr(verus_keep_ghost, verus_verify)]
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
#[cfg_attr(verus_keep_ghost, verus_verify)]
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
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, derive(Debug))]
pub struct Margin(u32);

impl Margin {
    /// A margin of zero logical pixels.
    pub const ZERO: Self = Self(0);

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.is_zero(), no_unwind))]
    pub(crate) fn is_zero(self) -> bool { self.0 == 0 }

    #[cfg_attr(verus_keep_ghost, verus_verify)]
    const AUTO_WORD: u32 = 0x7fc0_0000;

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) const fn is_auto(self) -> bool { self.0 == Self::AUTO_WORD }

    /// Share spare inline space in block flow. In a stack, wrap or managed flex layout,
    /// main-axis automatic edges divide the line's positive spare space equally after
    /// sizing, fixed margins and gaps, and before arrangement. A leading automatic
    /// margin can push a trailing action to the far edge of its line.
    /// In a simple stack or wrap, automatic margins on the cross axis resolve to zero.
    #[cfg(not(verus_keep_ghost))]
    pub const AUTO: Self = Self(Self::AUTO_WORD);

    /// A finite margin in logical pixels. Negative values are allowed.
    ///
    /// Returns `None` for infinite or NaN values.
    #[cfg(not(verus_keep_ghost))]
    pub const fn px(pixels: f32) -> Option<Self> {
        match input_words::finite_margin(pixels.to_bits()) {
            Some(word) => Some(Self(word)),
            None => None,
        }
    }

    /// The margin in logical pixels, or `None` for an automatic margin.
    #[cfg(not(verus_keep_ghost))]
    pub const fn as_px(self) -> Option<f32> {
        if self.0 == Self::AUTO.0 { None } else { Some(f32::from_bits(self.0)) }
    }

    #[inline(always)]
    #[cfg(not(verus_keep_ghost))]
    pub(crate) fn pixels(self) -> f32 {
        self.as_px().unwrap_or(0.0)
    }
}

#[cfg(not(verus_keep_ghost))]
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
#[cfg_attr(verus_keep_ghost, verus_verify)]
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
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.reads_other_axis(axis), no_unwind))]
    pub(crate) fn reads_other_axis(self, axis: Axis) -> bool {
        matches!((self, axis), (Self::HeightForWidth, Y) | (Self::WidthForHeight, X))
    }
}

/// The parameters that define a node's layout, from its own sizing to how it places its children.
#[derive(Debug, Clone, Copy, PartialEq)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
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
    /// Each pair is physical (left/right or top/bottom). If the box is too small for both
    /// sides, left/top consumes its share first and the content extent falls to zero inside the box.
    pub padding: Xy<[f32; 2]>,
    /// Space outside the node's box in a stack, wrap, grid, or block. Each pair uses physical
    /// start/end order (left/right or top/bottom). Free placement ignores margins.
    pub margin: Xy<[Margin; 2]>,
    /// How this node positions its children.
    pub children_layout: ChildrenLayout,
    /// Keep child block margins inside this box and separate its own before and after
    /// margins when empty. Its outer margins can still collapse with adjacent siblings.
    /// Managed flex and track grids establish this boundary automatically.
    /// In an owned tree's horizontal block flow, an isolated block avoids adjacent
    /// floats and includes its own floats in its intrinsic height. Overflow stays visible
    /// by default.
    pub isolate_block_margins: bool,
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
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn auto_margins(&self, axis: Axis) -> [bool; 2] {
        let [start, end] = *self.margin.component(axis);
        [start.is_auto(), end.is_auto()]
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn has_auto_margin(&self, axis: Axis) -> bool {
        let [start, end] = self.auto_margins(axis);
        start || end
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.block_margins_can_collapse(), no_unwind))]
    pub(crate) fn block_margins_can_collapse(&self) -> bool {
        !self.isolate_block_margins
            && matches!(self.children_layout, ChildrenLayout::Block | ChildrenLayout::Free)
            && matches!(self.text, TextContent::None) && self.image.is_none()
            && matches!(self.content_measure, ContentMeasure::None)
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.text_wraps_on(axis), no_unwind))]
    pub(crate) fn text_wraps_on(&self, axis: Axis) -> bool {
        matches!(axis, Y) && matches!(self.text, TextContent::Wrapping) && !matches!(self.size.x, Size::AspectRatio(_))
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.intrinsic_reads_other_axis(axis), no_unwind))]
    pub(crate) fn intrinsic_reads_other_axis(&self, axis: Axis) -> bool {
        self.text_wraps_on(axis) || self.content_measure.reads_other_axis(axis)
    }

    /// Default values for the `LayoutParams`.
    pub const DEFAULT: LayoutParams = LayoutParams {
        size: Xy { x: Size::Fill, y: Size::Fill },
        min_size: Xy { x: None, y: None },
        max_size: Xy { x: None, y: None },
        fill_weight: 1.0,
        padding: Xy { x: [0.0, 0.0], y: [0.0, 0.0] },
        margin: Xy::new_symm([Margin::ZERO; 2]),
        children_layout: ChildrenLayout::Free,
        isolate_block_margins: false,
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
