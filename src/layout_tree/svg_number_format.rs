use std::fmt::{self, Write};

pub(super) const SVG_NUMBER_CAPACITY: usize = 64;

/// Keep the coordinate cache and its fallback on the same `f32` display path.
#[inline]
pub(super) fn write_svg_number(out: &mut (impl Write + ?Sized), value: f32) -> fmt::Result {
    write!(out, "{value}")
}
