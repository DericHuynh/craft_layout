//! Logical geometry for hosts that author layouts in inline and block coordinates.
//!
//! Resolve the writing context from the parent before lowering this node's
//! declarations. The resulting physical parameters use the ordinary solver,
//! including its incremental and Batch paths.
use crate::{Axis, ChildrenLayout, LayoutParams, Margin, Size, Xy};

/// Inline progression within a writing mode. Text shaping uses the same input
/// but remains the responsibility of the host text engine.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// Inline progression is left-to-right in horizontal text and top-to-bottom in vertical text.
    #[default]
    Ltr,
    /// Inline progression is right-to-left in horizontal text and bottom-to-top in vertical text.
    Rtl,
}

/// Orientation of the inline axis and progression of successive lines.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum WritingMode {
    /// Lines run horizontally; successive lines run down the page.
    #[default]
    HorizontalTb,
    /// Lines run vertically; successive lines run toward the left.
    VerticalRl,
    /// Lines run vertically; successive lines run toward the right.
    VerticalLr,
}

/// An axis relative to the writing context.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicalAxis {
    /// The direction in which inline content is laid out.
    Inline,
    /// The direction in which successive lines or blocks are laid out.
    Block,
}

/// Inline and block components. An edge pair is ordered start, end.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Logical<T> {
    /// Value on the inline axis.
    pub inline: T,
    /// Value on the block axis.
    pub block: T,
}

impl<T> Logical<T> {
    /// Build a logical pair in inline, block order.
    pub const fn new(inline: T, block: T) -> Self {
        Self { inline, block }
    }
}

/// The inherited writing context resolved for one node.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct WritingContext {
    /// Inline progression.
    pub direction: Direction,
    /// Line orientation and block progression.
    pub writing_mode: WritingMode,
}

impl WritingContext {
    /// Physical axis along which a logical dimension is measured.
    pub const fn axis(self, axis: LogicalAxis) -> Axis {
        match (self.writing_mode, axis) {
            (WritingMode::HorizontalTb, LogicalAxis::Inline)
            | (WritingMode::VerticalRl | WritingMode::VerticalLr, LogicalAxis::Block) => Axis::X,
            _ => Axis::Y,
        }
    }

    /// Physical axes whose logical start is at their greater coordinate.
    pub fn origins(self) -> Xy<bool> {
        let rtl = self.direction == Direction::Rtl;
        match self.writing_mode {
            WritingMode::HorizontalTb => Xy::new(rtl, false),
            WritingMode::VerticalRl => Xy::new(true, rtl),
            WritingMode::VerticalLr => Xy::new(false, rtl),
        }
    }

    /// Map sizes or other unsigned axis quantities without reversing their values.
    pub fn physical<T>(self, values: Logical<T>) -> Xy<T> {
        match self.writing_mode {
            WritingMode::HorizontalTb => Xy::new(values.inline, values.block),
            _ => Xy::new(values.block, values.inline),
        }
    }

    /// Map logical start/end pairs into physical left/right and top/bottom.
    pub fn physical_edges<T>(self, edges: Logical<[T; 2]>) -> Xy<[T; 2]> {
        let mut result = self.physical(edges);
        let origins = self.origins();
        if origins.x {
            result.x.swap(0, 1);
        }
        if origins.y {
            result.y.swap(0, 1);
        }
        result
    }
}

/// Optional logical overrides on a node. Absent sizes and edges preserve
/// the authored physical values. Direction and writing mode inherit independently.
#[derive(Debug, Default, Clone, Copy, PartialEq)]
pub struct LogicalStyle {
    /// Override the inherited inline progression.
    pub direction: Option<Direction>,
    /// Override the inherited line orientation.
    pub writing_mode: Option<WritingMode>,
    /// Orient a Stack, Wrap, or Grid along this logical axis.
    pub main_axis: Option<LogicalAxis>,
    /// Reverse child placement along the specified logical axes, in addition to
    /// any physical reversal. For example, reverse.inline keeps a reversed
    /// toolbar in source order when its writing mode changes.
    pub reverse: Logical<bool>,
    /// Preferred inline and block sizes.
    pub size: Logical<Option<Size>>,
    /// Minimum inline and block sizes.
    pub min_size: Logical<Option<Size>>,
    /// Maximum inline and block sizes.
    pub max_size: Logical<Option<Size>>,
    /// Inline and block padding, with optional start and end overrides.
    pub padding: Logical<[Option<f32>; 2]>,
    /// Inline and block margins, with optional start and end overrides.
    pub margin: Logical<[Option<Margin>; 2]>,
}

/// An authored logical declaration cannot be executed by a physical layout mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicalError {
    /// The collapsing Block formatting context currently requires a horizontal inline axis.
    VerticalBlock,
}

impl core::fmt::Display for LogicalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::VerticalBlock => {
                f.write_str("vertical writing in a collapsing Block formatting context")
            }
        }
    }
}

impl std::error::Error for LogicalError {}

impl LogicalStyle {
    /// Inherit both components, then apply this node's overrides.
    pub fn context(self, inherited: WritingContext) -> WritingContext {
        WritingContext {
            writing_mode: self.writing_mode.unwrap_or(inherited.writing_mode),
            direction: self.direction.unwrap_or(inherited.direction),
        }
    }

    /// Resolve this node's declarations from its computed writing context.
    /// Explicit physical sizes and margins remain on their physical axes.
    /// An existing reverse Stack composes with inline or block progression.
    /// Vertical collapsing blocks need the owned tree's formatting context.
    /// Use `LayoutTree::set_rules` for these blocks.
    pub fn resolve(
        self,
        context: WritingContext,
        params: LayoutParams,
    ) -> Result<LayoutParams, LogicalError> {
        if context.writing_mode != WritingMode::HorizontalTb
            && matches!(params.children_layout, ChildrenLayout::Block)
        {
            return Err(LogicalError::VerticalBlock);
        }
        Ok(self.project(context, params))
    }

    // Owned trees also use this projection before applying the rotating Block
    // formatting context. A bare LayoutParams cannot encode that context.
    pub(crate) fn project(self, context: WritingContext, mut params: LayoutParams) -> LayoutParams {
        let flip = context.origins();
        let reverse = context.physical(self.reverse);
        params.children_origin_flipped.x ^= flip.x ^ reverse.x;
        params.children_origin_flipped.y ^= flip.y ^ reverse.y;
        if let Some(main) = self.main_axis {
            match &mut params.children_layout {
                ChildrenLayout::Stack { axis, .. } | ChildrenLayout::Wrap { axis, .. } => {
                    *axis = context.axis(main)
                }
                ChildrenLayout::Grid { main_axis, .. } => *main_axis = context.axis(main),
                _ => {}
            }
        }
        let size = context.physical(self.size);
        let min = context.physical(self.min_size);
        let max = context.physical(self.max_size);
        let padding = context.physical_edges(self.padding);
        let margin = context.physical_edges(self.margin);
        for axis in [Axis::X, Axis::Y] {
            if let Some(value) = size[axis] {
                params.size[axis] = value;
            }
            params.min_size[axis] = min[axis].or(params.min_size[axis]);
            params.max_size[axis] = max[axis].or(params.max_size[axis]);
            for side in 0..2 {
                if let Some(value) = padding[axis][side] {
                    params.padding[axis][side] = value;
                }
                if let Some(value) = margin[axis][side] {
                    params.margin[axis][side] = value;
                }
            }
        }
        params
    }
}
