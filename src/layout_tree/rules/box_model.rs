//! Percentages that need the allocated containing box before they become pixels.
use super::driver::Frame;
use crate::{Axis, LayoutParams, LogicalAxis, Margin, Size, Xy};

/// Additional box geometry for an owned tree. Fractions add to the authored
/// pixel edges. Padding and margins use the containing block's inline size.
#[derive(Debug, Clone, Copy, Default, PartialEq)]
pub struct BoxStyle {
    /// Physical border widths, already included in LayoutParams::padding.
    /// These identify the padding box used by absolutely positioned descendants.
    pub border: Xy<[f32; 2]>,
    /// Fractional part of each padding edge.
    pub padding_fraction: Xy<[f32; 2]>,
    /// Fractional part of each non-auto margin edge.
    pub margin_fraction: Xy<[f32; 2]>,
    /// Fractional part of track or flexible-line gaps, on physical axes.
    pub gap_fraction: Xy<f32>,
    /// Declared percentages size the content box. Fixed declarations already
    /// include the fixed part of padding and borders in the native outer size.
    pub content_box: bool,
    /// Origin of reachable scroll overflow. None allows both directions.
    pub scroll_origin: Option<Xy<bool>>,
    /// Minimum content extent reported by a host, such as an unbreakable text run.
    pub content_extent: Xy<f32>,
    /// Limit an intrinsically sized positioned axis to available space, down to
    /// this minimum unbreakable extent.
    pub positioned_fit_min: Xy<Option<f32>>,
    /// Static alignment in the immediate parent on axes with no absolute inset.
    pub absolute_static: Xy<Option<f32>>,
    /// When the static alignment would overflow its containing block, keep
    /// the box inside it, preferring logical start when both sides cannot fit.
    pub safe_static: Xy<bool>,
    /// Prefer the high edge when both physical insets overconstrain a fixed box.
    pub reverse_insets: Xy<bool>,
}

pub(super) fn apply(frame: &Frame<'_>, i: usize, p: &mut LayoutParams) {
    let model = frame.nodes[i].rule.box_model;
    if model == BoxStyle::default() {
        return;
    }
    let parent = frame.nodes[i].parent;
    let containing = frame.nodes[i]
        .grid_reference
        .unwrap_or_else(|| parent.map_or(frame.window, |j| frame.content_size(j)));
    let inline = parent.map_or(Axis::X, |j| {
        frame.nodes[j].context.axis(LogicalAxis::Inline)
    });
    let edge_reference = if frame.measuring
        && parent.is_some_and(|j| {
            frame.nodes[j].rule.grid.is_some()
                || frame.is_intrinsic(j, inline, frame.nodes[j].base.size[inline])
        }) {
        0.
    } else {
        containing[inline]
    };
    for a in [Axis::X, Axis::Y] {
        let mut delta = 0.;
        for edge in 0..2 {
            let pad = model.padding_fraction[a][edge] * edge_reference;
            p.padding[a][edge] += pad;
            delta += pad;
            if model.margin_fraction[a][edge] != 0.
                && let Some(fixed) = p.margin[a][edge].as_px()
            {
                p.margin[a][edge] =
                    Margin::px(fixed + model.margin_fraction[a][edge] * edge_reference)
                        .unwrap_or(Margin::ZERO);
            }
        }
        let floor = p.padding[a].iter().sum::<f32>();
        let outer = |s: Size| match s {
            Size::Frac(f) if model.content_box => Size::Pixels(f * containing[a] + floor),
            Size::Pixels(v) if model.content_box && delta != 0. => Size::Pixels(v + delta),
            s => s,
        };
        if model.content_box {
            p.size[a] = outer(p.size[a]);
        }
        let edge_bound = |s: Size| match outer(s) {
            Size::Frac(f) if floor > 0. => Size::Pixels((f * containing[a]).max(floor)),
            Size::Pixels(v) => Size::Pixels(v.max(floor)),
            other => other,
        };
        p.min_size[a] = p.min_size[a].map(edge_bound);
        p.max_size[a] = p.max_size[a].map(edge_bound);
        if delta != 0. && p.min_size[a].is_none() {
            p.min_size[a] = Some(Size::Pixels(floor));
        }
    }
}
