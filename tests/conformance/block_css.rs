use super::{Parent, Result, Style, unsupported};
use keru_layout::layout_rules::{BlockAlignment, Clear, Float, NodeRules, Overflow};
use keru_layout::{Axis, LayoutParams};

fn alignment(raw: &str) -> Result<BlockAlignment> {
    Ok(match raw {
        "normal" | "auto" => BlockAlignment::Normal,
        "stretch" => BlockAlignment::Stretch,
        "self-start" => BlockAlignment::SelfStart,
        "self-end" => BlockAlignment::SelfEnd,
        "start" | "flex-start" | "space-between" => BlockAlignment::Start,
        "end" | "unsafe end" | "flex-end" => BlockAlignment::End,
        "center" | "unsafe center" => BlockAlignment::Center,
        "safe center" | "space-evenly" | "space-around" => BlockAlignment::SafeCenter,
        "safe end" => BlockAlignment::SafeEnd,
        "left" | "-webkit-left" => BlockAlignment::Left,
        "right" | "-webkit-right" => BlockAlignment::Right,
        "-webkit-center" => BlockAlignment::Center,
        other => return unsupported(format!("block alignment={other}")),
    })
}

pub(super) fn lower(
    style: &Style,
    parent: Parent,
    display: &str,
    params: &mut LayoutParams,
    rule: &mut NodeRules,
) -> Result<()> {
    let b = &mut rule.block_flow;
    b.float = match style.keyword("float", "none") {
        "left" => Float::Left,
        "right" => Float::Right,
        "none" => Float::None,
        other => return unsupported(format!("float={other}")),
    };
    b.clear = match style.keyword("clear", "none") {
        "left" => Clear::Left,
        "right" => Clear::Right,
        "both" => Clear::Both,
        "none" => Clear::None,
        other => return unsupported(format!("clear={other}")),
    };
    match style.keyword("contain", "none") {
        "none" => (),
        "layout" | "content" | "paint" => {
            params.isolate_block_margins = true;
            b.contain_layout = style.get("contain") != Some("paint");
            if style.get("contain") != Some("layout") {
                for a in [Axis::X, Axis::Y] {
                    if rule.scroll.overflow[a] == Overflow::Visible {
                        rule.scroll.overflow[a] = Overflow::Clip;
                    }
                }
            }
        }
        other => return unsupported(format!("contain={other}")),
    }
    if matches!(display, "block" | "flow-root") {
        b.align_content = alignment(style.keyword("align-content", "normal"))?;
        b.justify_items = alignment(style.keyword("justify-items", "normal"))?;
        if let Some(align) = style.get("text-align") {
            if align.starts_with("-webkit-") {
                b.legacy_justify = alignment(align)?;
            }
        }
        // These axes on block boxes do not position their normal-flow children.
        style.get("align-items");
        style.get("justify-content");
    }
    if matches!(parent, Parent::Block) {
        b.stretch_block_margins = style.get("height") == Some("stretch");
        b.static_block_position = style.keyword("position", "static") == "absolute"
            && style.keyword("top", "auto") == "auto"
            && style.keyword("bottom", "auto") == "auto";
        b.justify_self = alignment(style.keyword("justify-self", "auto"))?;
    }
    Ok(())
}

/// Static position percentages refer to the immediate parent's content area.
/// The containing block independently limits a safe alignment.
pub(super) fn static_inline(
    align: BlockAlignment,
    parent_rtl: bool,
    child_rtl: bool,
) -> Option<(f32, bool)> {
    use BlockAlignment::*;
    let zero_or_one = |end: bool| if end { 1. } else { 0. };
    let fraction = match align {
        Normal | Stretch => return None,
        Left => 0.,
        Right => 1.,
        Center | SafeCenter => 0.5,
        Start => zero_or_one(parent_rtl),
        End | SafeEnd => zero_or_one(!parent_rtl),
        SelfStart => zero_or_one(child_rtl),
        SelfEnd => zero_or_one(!child_rtl),
    };
    Some((fraction, matches!(align, SafeCenter | SafeEnd)))
}
