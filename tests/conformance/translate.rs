//! Translates fixture CSS into keru `LayoutParams`.
//!
//! The translation maps the supported CSS subset to native declarations.
//! Some declarations resolve differently under CSS flex or intrinsic sizing.
//! The runner checks documented differences against hand-derived native rectangles.

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
    Viewport { size: Xy<Option<f32>> },
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
    pub disabled: bool,
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

fn arrange(raw: &str, reverse: bool) -> Result<Arrange> {
    Ok(match raw {
        "normal" | "flex-start" => Arrange::Start,
        "flex-end" => Arrange::End,
        "start" => if reverse { Arrange::End } else { Arrange::Start },
        "end" => if reverse { Arrange::Start } else { Arrange::End },
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

/// Convert the physical CSS containing-box coordinate to the parent's native origin.
fn at(mut fraction: f32, mut pixels: f32, mut anchor: f32, flipped: bool) -> (Pos, Anchor) {
    if flipped {
        fraction = 1.0 - fraction;
        pixels = -pixels;
        anchor = 1.0 - anchor;
    }
    let anchor = match anchor { 0.0 => Anchor::Start, 0.5 => Anchor::Center, 1.0 => Anchor::End, f => Anchor::Frac(f) };
    let position = match (fraction, pixels, anchor) {
        (0.0, 0.0, Anchor::Start) => Pos::Start,
        (0.5, 0.0, Anchor::Center) => Pos::Center,
        (1.0, 0.0, Anchor::End) => Pos::End,
        (0.0, _, _) => Pos::Pixels(pixels),
        (_, 0.0, _) => Pos::Frac(fraction),
        _ => Pos::Offset { fraction, pixels },
    };
    (position, anchor)
}

fn inset(value: Option<Value>) -> Result<Option<(f32, f32)>> {
    Ok(match value {
        None | Some(Value::Auto) => None,
        Some(Value::Px(px)) => Some((0.0, px)),
        Some(Value::Percent(frac)) => Some((frac, 0.0)),
        _ => return unsupported("absolute insets"),
    })
}

fn static_alignment(parent: &LayoutParams, axis: Axis, align: Align) -> f32 {
    match parent.children_layout {
        ChildrenLayout::Stack { axis: main, arrange, .. } | ChildrenLayout::Wrap { axis: main, arrange, .. }
            if main == axis => {
                let logical = match arrange {
                    Arrange::Start | Arrange::SpaceBetween => 0.0,
                    Arrange::Center | Arrange::SpaceAround | Arrange::SpaceEvenly => 0.5,
                    Arrange::End => 1.0,
                };
                if parent.children_origin_flipped[axis] { 1.0 - logical } else { logical }
            }
        _ => match align { Align::Start | Align::Stretch => 0.0, Align::Center => 0.5, Align::End => 1.0 },
    }
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
            let arrange = arrange(style.keyword("justify-content", "normal"), reverse)?;
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
    let absolute = match style.keyword("position", "static") {
        "relative" | "static" => {
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
    // Stacks keep declared sizes in negative free space. Read the CSS factor
    // for validation; the scoreboard still compares against the Chrome result.
    let shrink = style.number("flex-shrink", 1.0)?;
    let basis = style.value("flex-basis");
    let align_self = align(style.keyword("align-self", "auto"))?;
    let aspect = style.value("aspect-ratio");

    let mut declared = Xy::new(width, height);
    match context {
        Parent::Viewport { size: window } => {
            for (axis, start, end) in [(Axis::X, "left", "right"), (Axis::Y, "top", "bottom")] {
                let [before, after] = params.margin[axis].map(|m| m.as_px().unwrap_or(0.0));
                let leading = inset(style.value(start))?;
                let trailing = inset(style.value(end))?;
                // The XML supplies a concrete viewport on definite axes. Its margins
                // and opposing insets consume space before the root box is sized.
                let length = window[axis];
                if declared[axis].is_none() {
                    declared[axis] = Some(match (length, leading, trailing) {
                        (Some(w), Some((f, p)), Some((g, q))) if absolute =>
                            Size::Pixels((w - (f * w + p) - (g * w + q) - before - after).max(0.0)),
                        (Some(w), _, _) if !absolute && axis == Axis::X =>
                            Size::Pixels((w - before - after).max(0.0)),
                        _ => Size::FitContent,
                    });
                }
                let (pos, anchor) = match (leading, trailing) {
                    (Some((fraction, offset)), _) => at(fraction, offset + before, 0.0, false),
                    (_, Some((fraction, offset))) => at(1.0 - fraction, -offset - after, 1.0, false),
                    _ => at(0.0, before, 0.0, false),
                };
                params.position[axis] = pos;
                params.anchor[axis] = anchor;
            }
        }
        _ if absolute => {
            params.free_placement = true;
            let parent_params = tree.params(parent).map_err(|e| e.to_string())?;
            let parent_element = xml.parent_element().expect("fixture parent");
            let parent_style = Style::new(parent_element);
            // Native free placement is relative to the immediate parent. A CSS
            // inset or percentage size under a static non-root parent can read
            // a different ancestor; the no-inset static position still uses
            // the local formatting context.
            let parent_is_root = parent_element.parent_element().is_some_and(|p| p.has_tag_name("input"));
            let upper_containing_block = !parent_is_root && parent_style.keyword("position", "static") == "static";
            if upper_containing_block && (
                ["left", "top", "right", "bottom"].iter().any(|key|
                    !matches!(style.value(key), None | Some(Value::Auto)))
                || ["width", "height", "min-width", "min-height", "max-width", "max-height"].iter()
                    .any(|key| matches!(style.value(key), Some(Value::Percent(_))))
            ) {
                return unsupported("absolute coordinates relative to a non-parent containing block");
            }
            let alignment = match context {
                Parent::Flex { align_items, .. } => align_self.unwrap_or(align_items),
                _ => Align::Start,
            };
            for (axis, start, end) in [(Axis::X, "left", "right"), (Axis::Y, "top", "bottom")] {
                let [before, after] = params.margin[axis].map(|m| m.as_px().unwrap_or(0.0));
                let leading = inset(style.value(start))?;
                let trailing = inset(style.value(end))?;
                let (fraction, pixels, anchor) = match (leading, trailing) {
                    (None, None) => {
                        let f = static_alignment(parent_params, axis, alignment);
                        (f, (1.0 - f) * before - f * after, f)
                    }
                    _ => {
                        // CSS insets use the padding box. Native positions use the
                        // content box, whose leading edge already includes padding.
                        let pad_start = px(&parent_style, &format!("padding-{start}"))?;
                        let pad_end = px(&parent_style, &format!("padding-{end}"))?;
                        let (f, offset, anchor) = match (leading, trailing) {
                            (Some((f, offset)), None) => (f, offset + before, 0.0),
                            (None, Some((f, offset))) => (1.0 - f, -offset - after, 1.0),
                            _ => return unsupported("opposing absolute insets"),
                        };
                        (f, offset - pad_start + f * (pad_start + pad_end), anchor)
                    }
                };
                (params.position[axis], params.anchor[axis]) =
                    at(fraction, pixels, anchor, parent_params.children_origin_flipped[axis]);
                declared[axis].get_or_insert(Size::FitContent);
            }
        }
        Parent::Flex { main, align_items } => {
            let cross = main.other();
            let parent_params = tree.params(parent).map_err(|e| e.to_string())?;
            let explicit_basis = basis.filter(|basis| !matches!(basis, Value::Auto));
            // A numeric basis is the starting flex size. A leaf's unbreakable text or
            // fixed-size children still supply its automatic minimum on the main axis.
            if explicit_basis.is_some() && declared[main].is_none() && params.min_size[main].is_none() {
                let length = if main == Axis::X { "width" } else { "height" };
                if let Some(value) = text {
                    params.min_size[main] = Some(if main == Axis::X {
                        Size::Pixels(AhemText::new(value).min_content_width() + params.padding.x.iter().sum::<f32>())
                    } else { Size::FitContent });
                } else if xml.first_element_child().is_some() && xml.children().filter(|node| node.is_element()).all(|node|
                    node.attribute(length).is_some_and(|v| matches!(Value::parse(v), Value::Px(_)))
                ) {
                    params.min_size[main] = Some(Size::FitContent);
                }
            }
            if grow > 0.0 {
                if !matches!(basis, Some(Value::Px(v)) if v == 0.0) && !matches!(basis, Some(Value::Percent(p)) if p == 0.0) {
                    return unsupported("flex-grow with a non-zero basis");
                }
                // CSS also uses the preferred main size to size an intrinsic flex
                // container. Fill stores the zero basis and weight, but has no
                // separate preferred contribution; a hard minimum would change it.
                if matches!(parent_params.size[main], Size::FitContent)
                    && matches!(declared[main], Some(Size::Pixels(value)) if value > 0.0)
                {
                    return unsupported("preferred main size with zero-basis growth in an intrinsic flex container");
                }
                declared[main] = Some(Size::Fill);
                params.fill_weight = grow;
            } else if let Some(basis) = explicit_basis {
                declared[main] = size(Some(basis), "flex-basis", extra(main))?;
            }
            // A sole shrinkable text item in a definite row takes its natural
            // width up to the available width, keeping unbreakable runs intact.
            if main == Axis::X && declared.x.is_none() && shrink == 1.0
                && params.max_size.x.is_none() && aspect.is_none()
                && matches!(parent_params.size.x, Size::Pixels(_))
                && matches!(parent_params.children_layout, ChildrenLayout::Stack { .. })
            {
                if let Some(value) = text.filter(|_| xml.parent_element().is_some_and(|p|
                    p.children().filter(|n| n.is_element() && n.attribute("position") != Some("absolute")
                        && n.attribute("display") != Some("none")).count() == 1)) {
                    let text = AhemText::new(value);
                    let padding = params.padding.x.iter().sum::<f32>();
                    declared.x = Some(Size::Fill);
                    params.max_size.x = Some(Size::Pixels(text.max_content_width() + padding));
                    params.min_size.x.get_or_insert(Size::Pixels(text.min_content_width() + padding));
                }
            }
            if declared[main].is_none() {
                declared[main] = Some(Size::FitContent);
            }
            let alignment = align_self.unwrap_or(align_items);
            if declared[cross].is_none() {
                let stretch = alignment == Align::Stretch && aspect.is_none();
                declared[cross] = Some(if stretch { Size::Fill } else { Size::FitContent });
                // Stretch happens after line sizing. When content determines the
                // line, contribute the item's hypothetical size before filling it.
                if stretch && params.min_size[cross].is_none()
                    && (matches!(parent_params.size[cross], Size::FitContent)
                        || matches!(parent_params.min_size[cross], Some(Size::FitContent))
                        || matches!(parent_params.children_layout, ChildrenLayout::Wrap { .. }))
                {
                    params.min_size[cross] = Some(Size::FitContent);
                }
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

    // CSS subtracts padding and borders from a border-box length and floors
    // the content box at zero. Native Pixels is an explicit outer extent;
    // express the CSS floor through native bounds, including on Fill items.
    for axis in [Axis::X, Axis::Y] {
        let floor = params.padding[axis][0] + params.padding[axis][1];
        if floor <= 0.0 {
            continue;
        }
        params.min_size[axis] = Some(match params.min_size[axis] {
            None => Size::Pixels(floor),
            Some(Size::Pixels(min)) => Size::Pixels(min.max(floor)),
            Some(Size::FitContent) => Size::FitContent,
            Some(_) => return unsupported("non-pixel minimum with padding/border floor"),
        });
        match params.max_size[axis] {
            Some(Size::Pixels(max)) => params.max_size[axis] = Some(Size::Pixels(max.max(floor))),
            Some(Size::FitContent) | None => {}
            Some(_) => return unsupported("non-pixel maximum with padding/border floor"),
        }
    }

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
    Ok(Built { node, disabled: params.disabled, children })
}
