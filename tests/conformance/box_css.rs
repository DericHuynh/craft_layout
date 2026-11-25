//! Lower physical box lengths from their declarations and the host's Ahem metrics.
use super::*;
use keru_layout::layout_rules::{BoxStyle, Length, Overflow, Placement};

pub(super) fn gap(style: &Style, name: &str) -> Result<(f32, f32)> {
    match style.value(name) {
        Some(Value::Percent(p)) => Ok((0., p)),
        _ => Ok((px(style, name)?, 0.)),
    }
}

pub(super) fn geometry(style: &Style, writing: WritingContext, model: &mut BoxStyle) -> Result<()> {
    for (a, sides) in [(Axis::X, ["left", "right"]), (Axis::Y, ["top", "bottom"])] {
        for (e, side) in sides.into_iter().enumerate() {
            model.border[a][e] = px(style, &format!("border-{side}"))?;
            model.padding_fraction[a][e] = gap(style, &format!("padding-{side}"))?.1;
            model.margin_fraction[a][e] = match style.value(&format!("margin-{side}")) {
                Some(Value::Percent(p)) => p,
                _ => 0.,
            };
        }
    }
    let inline = writing.axis(LogicalAxis::Inline);
    model.gap_fraction[inline] = gap(style, "column-gap")?.1;
    model.gap_fraction[inline.other()] = gap(style, "row-gap")?.1;
    Ok(())
}

pub(super) fn overflow(style: &Style, rule: &mut NodeRules, p: &mut LayoutParams) -> Result<()> {
    let bar = style.number("scrollbar-width", 0.)?;
    for (a, prop) in [(Axis::X, "overflow-x"), (Axis::Y, "overflow-y")] {
        rule.scroll.overflow[a] = match style.keyword(prop, "visible") {
            "visible" => Overflow::Visible,
            "hidden" => Overflow::Hidden,
            "scroll" => Overflow::Scroll,
            "clip" => Overflow::Clip,
            "auto" => Overflow::Auto,
            raw => return unsupported(format!("{prop}={raw}")),
        };
        rule.scroll.scrollbar[a] = bar;
        p.isolate_block_margins |= matches!(
            rule.scroll.overflow[a],
            Overflow::Scroll | Overflow::Hidden | Overflow::Auto
        );
    }
    for a in [Axis::X, Axis::Y] {
        if matches!(
            rule.scroll.overflow[a.other()],
            Overflow::Auto | Overflow::Scroll | Overflow::Hidden
        ) {
            match rule.scroll.overflow[a] {
                Overflow::Visible => {
                    rule.scroll.overflow[a] = Overflow::Auto;
                    // The archive's configured gutter is reserved on explicit scroll axes.
                    rule.scroll.scrollbar[a] = 0.;
                }
                Overflow::Clip => rule.scroll.overflow[a] = Overflow::Hidden,
                _ => {}
            }
        }
    }
    Ok(())
}

pub(super) fn relative(
    style: &Style,
    writing: WritingContext,
    parent: &LayoutParams,
    rule: &mut NodeRules,
) -> Result<()> {
    let mut offset = Xy::new_symm(Length::default());
    for (a, low, high) in [(Axis::X, "left", "right"), (Axis::Y, "top", "bottom")] {
        let low = inset(style.value(low))?;
        let high = inset(style.value(high))?;
        let reverse = writing.origins()[a];
        let high = high.map(|(f, v)| (-f, -v));
        if let Some((mut fraction, pixels)) = if reverse { high.or(low) } else { low.or(high) } {
            // A percentage block inset has no reference when block extent is intrinsic.
            if a == writing.axis(LogicalAxis::Block)
                && matches!(parent.size[a], Size::FitContent | Size::Auto)
            {
                fraction = 0.;
            }
            offset[a] = Length { fraction, pixels };
        }
    }
    if offset != Xy::new_symm(Length::default()) {
        rule.placement = Placement::Relative(offset);
    }
    Ok(())
}

/// The host's minimum contribution for intrinsic width/height declarations.
/// The fixture text backend supplies the longest unbreakable run. An
/// unwrapped flex line sums along its main axis; a stack of rows takes the
/// widest member. Absolutely positioned and hidden children reserve no space.
pub(super) fn minimum(xml: roxmltree::Node, axis: Axis, inherited: WritingContext) -> f32 {
    let style = Style::new(xml);
    let sides = if axis == Axis::X {
        ["left", "right"]
    } else {
        ["top", "bottom"]
    };
    let pad: f32 = sides
        .iter()
        .map(|side| {
            px(&style, &format!("padding-{side}")).unwrap_or(0.)
                + px(&style, &format!("border-{side}")).unwrap_or(0.)
        })
        .sum();
    if let Some(Value::Px(n)) = style.value(if axis == Axis::X { "width" } else { "height" }) {
        return if style.keyword("box-sizing", "border-box") == "content-box" {
            n + pad
        } else {
            n.max(pad)
        };
    }
    if xml.first_element_child().is_none() {
        return pad
            + xml.text().map_or(0., |s| {
                let text = AhemText::new(s.trim());
                if axis == inherited.axis(LogicalAxis::Inline) {
                    text.min_content_width()
                } else {
                    text.wrap(f32::INFINITY).1
                }
            });
    }
    let children = xml.children().filter(|n| {
        n.is_element()
            && n.attribute("display") != Some("none")
            && n.attribute("position") != Some("absolute")
    });
    let sizes = children.map(|child| minimum(child, axis, inherited));
    let block = inherited.axis(LogicalAxis::Block);
    let flex = style.keyword("display", "flex") == "flex";
    let column = style.keyword("flex-direction", "row").starts_with("column");
    let sum = if flex {
        (axis == block) == column && style.keyword("flex-wrap", "nowrap") == "nowrap"
    } else {
        axis == block
    };
    pad + if sum {
        sizes.sum()
    } else {
        sizes.fold(0., f32::max)
    }
}
