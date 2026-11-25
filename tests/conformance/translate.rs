//! Translates fixture CSS into keru `LayoutParams`.
//!
//! The translation only uses keru features whose semantics coincide with the
//! CSS property. Anything else is reported as unsupported, so the scoreboard
//! separates "keru computes this differently" from "keru cannot express this".

use crate::ahem::AhemText;
use crate::css::{Style, Value};
use keru_layout::{
    Anchor, Arrange, Axis, ChildrenLayout, LayoutParams, LayoutTree, Margin, NodeId, Pos, Size,
    TextContent, Xy,
};

pub type Tree = LayoutTree<AhemText>;

/// How a parent lays out its in-flow children, as far as items need to know.
#[derive(Clone, Copy)]
pub enum Parent {
    /// The fixture root, placed in the window's top-left corner.
    Viewport { definite: Xy<bool> },
    Flex { main: Axis, align_items: Align },
    Block,
}

#[derive(Clone, Copy, PartialEq)]
pub enum Align {
    Stretch,
    Start,
    Center,
    End,
}

pub struct Built {
    pub node: NodeId,
    pub children: Vec<Built>,
}

type Result<T> = std::result::Result<T, String>;

fn unsupported<T>(what: impl Into<String>) -> Result<T> {
    Err(what.into())
}

fn align(raw: &str) -> Result<Option<Align>> {
    Ok(Some(match raw {
        "normal" | "stretch" => Align::Stretch,
        "flex-start" | "start" | "self-start" => Align::Start,
        "center" => Align::Center,
        "flex-end" | "end" | "self-end" => Align::End,
        "auto" => return Ok(None),
        other => return unsupported(format!("align={other}")),
    }))
}

fn arrange(raw: &str) -> Result<Arrange> {
    Ok(match raw {
        "normal" | "flex-start" | "start" => Arrange::Start,
        "flex-end" | "end" => Arrange::End,
        "center" => Arrange::Center,
        "space-between" => Arrange::SpaceBetween,
        "space-around" => Arrange::SpaceAround,
        "space-evenly" => Arrange::SpaceEvenly,
        other => return unsupported(format!("justify-content={other}")),
    })
}

fn px(style: &Style, name: &str) -> Result<f32> {
    match style.value(name) {
        None => Ok(0.0),
        Some(Value::Px(v)) => Ok(v),
        Some(Value::Number(v)) if v == 0.0 => Ok(0.0),
        Some(other) => unsupported(format!("{name}={other:?}")),
    }
}

fn margin(style: &Style, name: &str) -> Result<Margin> {
    match style.value(name) {
        None => Ok(Margin::ZERO),
        Some(Value::Px(v)) => Margin::px(v).ok_or_else(|| format!("{name}={v}")),
        Some(other) => unsupported(format!("{name}={other:?}")),
    }
}

/// A size declaration, with `extra` added to pixel values for content-box sizing.
fn size(value: Option<Value>, name: &str, extra: f32) -> Result<Option<Size>> {
    Ok(match value {
        None | Some(Value::Auto) => None,
        Some(Value::Px(v)) => Some(Size::Pixels(v + extra)),
        Some(Value::Percent(p)) if extra == 0.0 => Some(Size::Frac(p)),
        Some(Value::MaxContent) => Some(Size::FitContent),
        Some(other) => return unsupported(format!("{name}={other:?}")),
    })
}

pub fn build(tree: &mut Tree, parent: &NodeId, xml: roxmltree::Node, context: Parent) -> Result<Built> {
    let style = Style::new(xml);
    let mut params = LayoutParams::DEFAULT;

    // Properties keru has no counterpart for yet.
    for (name, initial) in [
        ("direction", "ltr"),
        ("float", "none"),
        ("clear", "none"),
        ("overflow-x", "visible"),
        ("overflow-y", "visible"),
        ("contain", "none"),
        ("writing-mode", "horizontal-tb"),
        ("text-align", "auto"),
    ] {
        let value = style.keyword(name, initial);
        if value != initial {
            return unsupported(format!("{name}={value}"));
        }
    }
    if style.number("scrollbar-width", 0.0)? != 0.0 {
        return unsupported("scrollbar-width");
    }

    // Box edges. Borders lay out exactly like padding.
    let edges = |side: &str| -> Result<f32> { Ok(px(&style, &format!("padding-{side}"))? + px(&style, &format!("border-{side}"))?) };
    params.padding = Xy::new([edges("left")?, edges("right")?], [edges("top")?, edges("bottom")?]);
    params.margin = Xy::new(
        [margin(&style, "margin-left")?, margin(&style, "margin-right")?],
        [margin(&style, "margin-top")?, margin(&style, "margin-bottom")?],
    );
    let content_box = match style.keyword("box-sizing", "border-box") {
        "border-box" => false,
        "content-box" => true,
        other => return unsupported(format!("box-sizing={other}")),
    };
    let extra = |axis: Axis| if content_box { params.padding[axis][0] + params.padding[axis][1] } else { 0.0 };
    let (extra_x, extra_y) = (extra(Axis::X), extra(Axis::Y));

    let width = size(style.value("width"), "width", extra_x)?;
    let height = size(style.value("height"), "height", extra_y)?;
    params.min_size = Xy::new(size(style.value("min-width"), "min-width", extra_x)?, size(style.value("min-height"), "min-height", extra_y)?);
    params.max_size = Xy::new(size(style.value("max-width"), "max-width", extra_x)?, size(style.value("max-height"), "max-height", extra_y)?);

    // The node's own container behavior.
    let text = xml.first_element_child().is_none().then(|| xml.text()).flatten().map(str::trim);
    let display = style.keyword("display", "flex");
    let mut own_flex_main = None;
    let mut own_align = Align::Stretch;
    match display {
        "none" => params.disabled = true,
        "flex" => {
            let direction = style.keyword("flex-direction", "row");
            let (main, reverse) = match direction {
                "row" => (Axis::X, false),
                "row-reverse" => (Axis::X, true),
                "column" => (Axis::Y, false),
                "column-reverse" => (Axis::Y, true),
                other => return unsupported(format!("flex-direction={other}")),
            };
            params.children_origin_flipped[main] = reverse;
            let gap = |name| px(&style, name);
            let (main_gap, cross_gap) = match main {
                Axis::X => (gap("column-gap")?, gap("row-gap")?),
                Axis::Y => (gap("row-gap")?, gap("column-gap")?),
            };
            let arrange = arrange(style.keyword("justify-content", "normal"))?;
            own_align = align(style.keyword("align-items", "normal"))?.unwrap_or(Align::Stretch);
            params.children_layout = match style.keyword("flex-wrap", "nowrap") {
                "nowrap" => ChildrenLayout::Stack { axis: main, arrange, spacing: main_gap },
                "wrap" => {
                    if !matches!(style.keyword("align-content", "normal"), "flex-start" | "start") {
                        return unsupported("multi-line align-content");
                    }
                    ChildrenLayout::Wrap { axis: main, arrange, spacing: main_gap, line_spacing: cross_gap }
                }
                other => return unsupported(format!("flex-wrap={other}")),
            };
            own_flex_main = Some(main);
        }
        "block" => params.children_layout = ChildrenLayout::Block,
        other => return unsupported(format!("display={other}")),
    }
    if let Some(text) = text {
        params.text = TextContent::Wrapping;
        let _ = text;
    }

    // Placement as an item of its parent.
    let absolute = match style.keyword("position", "relative") {
        "relative" => {
            for side in ["left", "right", "top", "bottom"] {
                if !matches!(style.value(side), None | Some(Value::Auto)) {
                    return unsupported("relative offsets");
                }
            }
            false
        }
        "absolute" => true,
        other => return unsupported(format!("position={other}")),
    };

    let grow = style.number("flex-grow", 0.0)?;
    let _shrink = style.number("flex-shrink", 1.0)?;
    let basis = style.value("flex-basis");
    let align_self = align(style.keyword("align-self", "auto"))?;
    let aspect = style.value("aspect-ratio");

    let mut declared = Xy::new(width, height);
    match context {
        Parent::Viewport { definite } => {
            for axis in [Axis::X, Axis::Y] {
                if declared[axis].is_none() {
                    declared[axis] = Some(if definite[axis] { Size::Fill } else { Size::FitContent });
                }
            }
            params.position = Xy::new(Pos::Start, Pos::Start);
            params.anchor = Xy::new(Anchor::Start, Anchor::Start);
        }
        _ if absolute => {
            params.free_placement = true;
            for (axis, start, end) in [(Axis::X, "left", "right"), (Axis::Y, "top", "bottom")] {
                let (pos, anchor) = match (style.value(start), style.value(end)) {
                    (None | Some(Value::Auto), None | Some(Value::Auto)) => (Pos::Start, Anchor::Start),
                    (Some(Value::Px(v)), None | Some(Value::Auto)) => (Pos::Pixels(v), Anchor::Start),
                    (Some(Value::Percent(p)), None | Some(Value::Auto)) => (Pos::Frac(p), Anchor::Start),
                    (None | Some(Value::Auto), Some(Value::Px(v))) if v == 0.0 => (Pos::End, Anchor::End),
                    _ => return unsupported("absolute insets"),
                };
                params.position[axis] = pos;
                params.anchor[axis] = anchor;
                if declared[axis].is_none() {
                    declared[axis] = Some(Size::FitContent);
                }
            }
        }
        Parent::Flex { main, align_items } => {
            let cross = main.other();
            if grow > 0.0 {
                if !matches!(basis, Some(Value::Px(v)) if v == 0.0) && !matches!(basis, Some(Value::Percent(p)) if p == 0.0) {
                    return unsupported("flex-grow with a non-zero basis");
                }
                declared[main] = Some(Size::Fill);
                params.fill_weight = grow;
            } else if let Some(basis) = basis {
                declared[main] = size(Some(basis), "flex-basis", extra(main))?;
            }
            if declared[main].is_none() {
                declared[main] = Some(Size::FitContent);
            }
            let alignment = align_self.unwrap_or(align_items);
            if declared[cross].is_none() {
                declared[cross] = Some(if alignment == Align::Stretch && aspect.is_none() { Size::Fill } else { Size::FitContent });
            }
            let (pos, anchor) = match alignment {
                Align::Stretch | Align::Start => (Pos::Start, Anchor::Start),
                Align::Center => (Pos::Center, Anchor::Center),
                Align::End => (Pos::End, Anchor::End),
            };
            params.position[cross] = pos;
            params.anchor[cross] = anchor;
        }
        Parent::Block => {
            if declared[Axis::X].is_none() {
                declared[Axis::X] = Some(Size::Auto);
            }
            if declared[Axis::Y].is_none() {
                declared[Axis::Y] = Some(Size::FitContent);
            }
        }
    }
    if let Some(aspect) = aspect {
        let Value::Number(ratio) = aspect else { return unsupported("aspect-ratio") };
        let free = [Axis::X, Axis::Y].into_iter().find(|&axis| matches!(declared[axis], Some(Size::FitContent)));
        match free {
            Some(axis) if !matches!(declared[axis.other()], Some(Size::FitContent)) => declared[axis] = Some(Size::AspectRatio(ratio)),
            _ => return unsupported("aspect-ratio without a definite axis"),
        }
    }
    params.size = Xy::new(declared.x.unwrap_or(Size::FitContent), declared.y.unwrap_or(Size::FitContent));

    let unread = style.unread();
    if !unread.is_empty() {
        return unsupported(unread.join(" "));
    }

    let node: NodeId = match text {
        Some(text) => (*tree.add_node_with_context(parent, params, AhemText::new(text)).map_err(|e| e.to_string())?).clone(),
        None => (*tree.add_node(parent, params).map_err(|e| e.to_string())?).clone(),
    };
    let child_context = match (own_flex_main, display) {
        (Some(main), _) => Parent::Flex { main, align_items: own_align },
        (None, "block") => Parent::Block,
        _ => Parent::Block,
    };
    let mut children = Vec::new();
    for child in xml.children().filter(|child| child.is_element()) {
        children.push(build(tree, &node, child, child_context)?);
    }
    Ok(Built { node, children })
}
