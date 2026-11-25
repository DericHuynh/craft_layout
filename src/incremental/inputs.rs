use crate::{Anchor, ChildrenLayout, LayoutParams, MainAxisCellSize, Pos, Size, Xy};

/// Cache keys must preserve the sign of zero. For example, an aspect-ratio
/// height divides by its declaration, so changing +0 to -0 can switch bounds.
pub(crate) trait SameInput {
    fn same_input(&self, other: &Self) -> bool;
}

impl SameInput for f32 {
    fn same_input(&self, other: &Self) -> bool {
        self.to_bits() == other.to_bits()
    }
}

impl SameInput for [f32; 2] {
    fn same_input(&self, other: &Self) -> bool {
        self.map(f32::to_bits) == other.map(f32::to_bits)
    }
}

impl<T: SameInput> SameInput for Xy<T> {
    fn same_input(&self, other: &Self) -> bool {
        self.x.same_input(&other.x) && self.y.same_input(&other.y)
    }
}

impl<T: SameInput> SameInput for Option<T> {
    fn same_input(&self, other: &Self) -> bool {
        match (self, other) {
            (Some(a), Some(b)) => a.same_input(b),
            (None, None) => true,
            _ => false,
        }
    }
}

impl SameInput for Size {
    fn same_input(&self, other: &Self) -> bool {
        super::registration_rules::same_size::<crate::placement_geometry::RustFloat>(Some(*self), Some(*other))
    }
}

impl SameInput for Pos {
    fn same_input(&self, other: &Self) -> bool {
        use Pos::*;
        match (self, other) {
            (Pixels(a), Pixels(b)) | (Frac(a), Frac(b)) => a.same_input(b),
            (Offset { fraction: a, pixels: x }, Offset { fraction: b, pixels: y }) => a.same_input(b) && x.same_input(y),
            (Start, Start) | (Center, Center) | (End, End) => true,
            _ => false,
        }
    }
}

impl SameInput for Anchor {
    fn same_input(&self, other: &Self) -> bool {
        use Anchor::*;
        match (self, other) {
            (Frac(a), Frac(b)) => a.same_input(b),
            (Start, Start) | (Center, Center) | (End, End) => true,
            _ => false,
        }
    }
}

impl SameInput for MainAxisCellSize {
    fn same_input(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Count(a), Self::Count(b)) => a == b,
            (Self::Width(a), Self::Width(b)) => a.same_input(b),
            _ => false,
        }
    }
}

impl SameInput for ChildrenLayout {
    fn same_input(&self, other: &Self) -> bool {
        use ChildrenLayout::*;
        match (self, other) {
            (Free, Free) | (Block, Block) => true,
            (Stack { axis, arrange, spacing },
             Stack { axis: other_axis, arrange: other_arrange, spacing: other_spacing }) =>
                axis == other_axis && arrange == other_arrange && spacing.same_input(other_spacing),
            (Wrap { axis, arrange, spacing, line_spacing },
             Wrap { axis: other_axis, arrange: other_arrange, spacing: other_spacing, line_spacing: other_line_spacing }) =>
                axis == other_axis && arrange == other_arrange
                    && spacing.same_input(other_spacing) && line_spacing.same_input(other_line_spacing),
            (Grid { columns, spacing_x, spacing_y, main_axis, backfill },
             Grid { columns: other_columns, spacing_x: other_x, spacing_y: other_y, main_axis: other_axis, backfill: other_backfill }) =>
                main_axis == other_axis && backfill == other_backfill && columns.same_input(other_columns)
                    && spacing_x.same_input(other_x) && spacing_y.same_input(other_y),
            _ => false,
        }
    }
}

impl SameInput for LayoutParams {
    fn same_input(&self, other: &Self) -> bool {
        let Self { position, size, min_size, max_size, padding, margin, children_layout, isolate_block_margins, free_placement,
            grid_span, text, content_measure, image, anchor, children_origin_flipped, window_overflow,
            fill_weight, disabled } = self;
        size.same_input(&other.size) && min_size.same_input(&other.min_size) && max_size.same_input(&other.max_size)
            && padding.same_input(&other.padding) && *margin == other.margin && children_layout.same_input(&other.children_layout)
            && *isolate_block_margins == other.isolate_block_margins
            && *free_placement == other.free_placement && *grid_span == other.grid_span && *text == other.text
            && *content_measure == other.content_measure && image.same_input(&other.image)
            && position.same_input(&other.position) && anchor.same_input(&other.anchor)
            && *children_origin_flipped == other.children_origin_flipped && *window_overflow == other.window_overflow
            && fill_weight.same_input(&other.fill_weight) && *disabled == other.disabled
    }
}
