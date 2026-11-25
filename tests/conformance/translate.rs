//! Translates fixture CSS into keru `LayoutParams`.
//!
//! The translation maps the supported CSS subset to native declarations.
//! Some declarations resolve differently under CSS flex or intrinsic sizing.
//! The runner checks documented differences against hand-derived native rectangles.

#[path = "block_css.rs"]
mod block_css;

#[path = "box_css.rs"]
mod box_css;
#[path = "grid_css.rs"]
mod grid_css;

use crate::ahem::AhemText;
use crate::css::{PHYSICAL_MARGINS, Style, Value, has_logical_margin};
use keru_layout::flex::{FlexAlign, FlexBasis, FlexItem, FlexLayout, FlexWrap, LineAlign};
use keru_layout::layout_rules::NodeRules;
use keru_layout::{
    Anchor, Arrange, Axis, ChildrenLayout, Direction, LayoutParams, LayoutTree, LogicalAxis,
    LogicalStyle, Margin, NodeId, Pos, Size, TextContent, WritingContext, WritingMode, Xy,
};

pub type Tree = LayoutTree<AhemText>;

/// How a parent lays out its in-flow children, as far as items need to know.
#[derive(Clone, Copy)]
pub enum Parent {
    /// The fixture root, placed in the window's top-left corner.
    Viewport {
        size: Xy<Option<f32>>,
    },
    Flex {
        main: Axis,
        align_items: Align,
        managed: bool,
        reverse_cross: bool,
    },
    Block,
    Grid(grid_css::GridContext),
}

#[derive(Clone, Copy, PartialEq)]
pub enum Align {
    Stretch,
    Start,
    Center,
    End,
    SelfStart,
    SelfEnd,
    FlexStart,
    FlexEnd,
    SafeCenter,
    SafeEnd,
    Baseline,
    LastBaseline,
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
    Ok(Some(match raw.strip_prefix("unsafe ").unwrap_or(raw) {
        "normal" | "stretch" => Align::Stretch,
        "flex-start" => Align::FlexStart,
        "start" => Align::Start,
        "self-start" => Align::SelfStart,
        "center" => Align::Center,
        "flex-end" => Align::FlexEnd,
        "end" => Align::End,
        "self-end" => Align::SelfEnd,
        "safe center" => Align::SafeCenter,
        "safe end" => Align::SafeEnd,
        "baseline" | "first baseline" => Align::Baseline,
        "last baseline" => Align::LastBaseline,
        "auto" => return Ok(None),
        other => return unsupported(format!("align={other}")),
    }))
}

fn arrange(raw: &str, reverse: bool) -> Result<Arrange> {
    Ok(
        match raw
            .strip_prefix("safe ")
            .or_else(|| raw.strip_prefix("unsafe "))
            .unwrap_or(raw)
        {
            "normal" | "flex-start" => Arrange::Start,
            "flex-end" => Arrange::End,
            "start" => {
                if reverse {
                    Arrange::End
                } else {
                    Arrange::Start
                }
            }
            "end" => {
                if reverse {
                    Arrange::Start
                } else {
                    Arrange::End
                }
            }
            "center" => Arrange::Center,
            "space-between" => Arrange::SpaceBetween,
            "space-around" => Arrange::SpaceAround,
            "space-evenly" => Arrange::SpaceEvenly,
            other => return unsupported(format!("justify-content={other}")),
        },
    )
}

fn px(style: &Style, name: &str) -> Result<f32> {
    match style.value(name) {
        None => Ok(0.0),
        Some(Value::Px(v)) => Ok(v),
        Some(Value::Number(v)) if v == 0.0 => Ok(0.0),
        Some(other) => unsupported(format!("{name}={other:?}")),
    }
}

fn margin(style: &Style, name: &str, _block_item: bool) -> Result<Margin> {
    match style.value(name) {
        None => Ok(Margin::ZERO),
        Some(Value::Auto) => Ok(Margin::AUTO),
        Some(Value::Percent(_)) => Ok(Margin::ZERO),
        Some(Value::Number(0.0)) => Ok(Margin::ZERO),
        Some(Value::Px(v)) => Margin::px(v).ok_or_else(|| format!("{name}={v}")),
        Some(other) => unsupported(format!("{name}={other:?}")),
    }
}

/// A size declaration, with `extra` added to pixel values for content-box sizing.
fn size(value: Option<Value>, name: &str, extra: f32) -> Result<Option<Size>> {
    Ok(match value {
        None | Some(Value::Auto) => None,
        Some(Value::Px(v)) => Some(Size::Pixels(v + extra)),
        Some(Value::Percent(p)) => Some(Size::Frac(p)),
        Some(Value::MaxContent | Value::FitContent | Value::MinContent) => Some(Size::FitContent),
        Some(Value::Stretch) => Some(Size::Fill),
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
    let anchor = match anchor {
        0.0 => Anchor::Start,
        0.5 => Anchor::Center,
        1.0 => Anchor::End,
        f => Anchor::Frac(f),
    };
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

fn item_alignment(value: Align, item: WritingContext, parent: &LayoutParams, cross: Axis) -> Align {
    let reversed = item.origins()[cross] != parent.children_origin_flipped[cross];
    match value {
        Align::SelfStart => {
            if reversed {
                Align::End
            } else {
                Align::Start
            }
        }
        Align::SelfEnd => {
            if reversed {
                Align::Start
            } else {
                Align::End
            }
        }
        value => value,
    }
}

fn line_item_alignment(
    value: Align,
    reverse_cross: bool,
    cross: Axis,
    item: WritingContext,
) -> Align {
    match value {
        Align::Start if reverse_cross => Align::End,
        Align::End | Align::SafeEnd if reverse_cross => Align::Start,
        Align::Baseline if cross == item.axis(LogicalAxis::Inline) => Align::FlexStart,
        Align::LastBaseline if cross == item.axis(LogicalAxis::Inline) => Align::FlexEnd,
        value => value,
    }
}

fn flex_align(align: Align) -> FlexAlign {
    match align {
        Align::Stretch => FlexAlign::Stretch,
        Align::FlexStart | Align::SelfStart | Align::Start => FlexAlign::Start,
        Align::FlexEnd | Align::SelfEnd | Align::End => FlexAlign::End,
        Align::Center => FlexAlign::Center,
        Align::SafeCenter => FlexAlign::SafeCenter,
        Align::SafeEnd => FlexAlign::SafeEnd,
        Align::Baseline => FlexAlign::FirstBaseline,
        Align::LastBaseline => FlexAlign::LastBaseline,
    }
}

fn line_align(raw: &str, reverse: bool) -> Result<LineAlign> {
    Ok(match raw.strip_prefix("unsafe ").unwrap_or(raw) {
        "stretch" | "normal" => LineAlign::Stretch,
        "flex-start" => LineAlign::Start,
        "flex-end" => LineAlign::End,
        "start" if reverse => LineAlign::End,
        "end" if reverse => LineAlign::Start,
        "start" => LineAlign::Start,
        "end" => LineAlign::End,
        "center" => LineAlign::Center,
        "space-between" => LineAlign::SpaceBetween,
        "space-around" => LineAlign::SpaceAround,
        "space-evenly" => LineAlign::SpaceEvenly,
        "safe center" => LineAlign::SafeCenter,
        "safe end" if reverse => LineAlign::Start,
        "safe end" => LineAlign::SafeEnd,
        other => return unsupported(format!("align-content={other}")),
    })
}

fn logical_style(style: &Style) -> Result<LogicalStyle> {
    Ok(LogicalStyle {
        direction: match style.get("direction") {
            None => None,
            Some("ltr") => Some(Direction::Ltr),
            Some("rtl") => Some(Direction::Rtl),
            Some(value) => return unsupported(format!("direction={value}")),
        },
        writing_mode: match style.get("writing-mode") {
            None => None,
            Some("horizontal-tb") => Some(WritingMode::HorizontalTb),
            Some("vertical-lr") => Some(WritingMode::VerticalLr),
            Some("vertical-rl") => Some(WritingMode::VerticalRl),
            Some(value) => return unsupported(format!("writing-mode={value}")),
        },
        ..LogicalStyle::default()
    })
}

fn needs_managed_margins(child: roxmltree::Node, inherited: WritingContext) -> bool {
    let dynamic = |v: &str| v == "auto" || v.ends_with('%');
    if !has_logical_margin(child) {
        return PHYSICAL_MARGINS
            .iter()
            .any(|&p| child.attribute(p).is_some_and(dynamic));
    }
    let mut style = Style::new(child);
    let Ok(logical) = logical_style(&style) else {
        // Building the child reports its unsupported writing mode.
        return false;
    };
    style.resolve_logical_margins(child, logical.context(inherited));
    PHYSICAL_MARGINS
        .iter()
        .any(|p| style.get(p).is_some_and(dynamic))
}

fn needs_managed_items(
    xml: roxmltree::Node,
    axis: Axis,
    writing: WritingContext,
    align_items: Align,
) -> bool {
    let inline = writing.axis(LogicalAxis::Inline);
    let main_size = if axis == Axis::X { "width" } else { "height" };
    let main_overflow = if axis == Axis::X {
        "overflow-x"
    } else {
        "overflow-y"
    };
    let intrinsic_parent = xml.attribute(main_size).is_none();
    xml.children()
        .filter(|n| {
            n.is_element()
                && n.attribute("display") != Some("none")
                && n.attribute("position") != Some("absolute")
        })
        .any(|child| {
            let cross_size = if inline == Axis::X { "width" } else { "height" };
            let cross_align = child
                .attribute("align-self")
                .and_then(|s| align(s).ok().flatten())
                .unwrap_or(align_items);
            let fit_inline = axis != inline
                && cross_align != Align::Stretch
                && child.attribute(cross_size).is_none()
                && child.descendants().any(|n| {
                    n.attribute("flex-wrap").is_some_and(|w| w != "nowrap")
                        || n.is_text() && n.text().is_some_and(AhemText::can_wrap)
                });
            let basis = child.attribute("flex-basis").map(Value::parse);
            let grow = child
                .attribute("flex-grow")
                .and_then(|s| s.parse::<f32>().ok())
                .unwrap_or(0.);
            let zero = matches!(basis, Some(Value::Px(v)|Value::Percent(v)) if v==0.);
            let positive_preference =
                matches!(child.attribute(main_size).map(Value::parse),Some(Value::Px(v)) if v>0.);
            let main_edges = if axis == Axis::X {
                [
                    "padding-left",
                    "padding-right",
                    "border-left",
                    "border-right",
                ]
            } else {
                [
                    "padding-top",
                    "padding-bottom",
                    "border-top",
                    "border-bottom",
                ]
            };
            // A percentage content-box basis plus padding can exceed its line even
            // for a lone item. The flex allocator must be able to shrink it.
            let relative_padded = child.attribute("box-sizing") == Some("content-box")
                && matches!(
                    child.attribute(main_size).map(Value::parse),
                    Some(Value::Percent(_))
                )
                && main_edges.iter().any(|&edge| {
                    matches!(child.attribute(edge).map(Value::parse),
                Some(Value::Px(v) | Value::Percent(v)) if v > 0.)
                });
            fit_inline
                || relative_padded
                || grow > 0. && (!zero || positive_preference && intrinsic_parent)
                || matches!(
                    basis,
                    Some(
                        Value::MaxContent
                            | Value::MinContent
                            | Value::FitContent
                            | Value::Stretch
                            | Value::Content
                    )
                )
                || child.attribute("flex-wrap").is_some_and(|w| w != "nowrap")
                || matches!(
                    child.attribute(main_overflow),
                    Some("hidden" | "scroll" | "auto")
                )
                || child
                    .attribute("align-self")
                    .is_some_and(|a| a.contains("baseline") || a.contains("safe "))
                || needs_managed_margins(child, writing)
        })
}

// Return a minimum only when it is available from the fixture's content
// declaration. Definite child lengths make an unwrapped container's native
// intrinsic measurement independent of soft line breaks on this axis.
fn content_minimum(
    xml: roxmltree::Node,
    text: Option<&str>,
    axis: Axis,
    writing: WritingContext,
    params: &LayoutParams,
) -> Option<Size> {
    if let Some(text) = text {
        return Some(if axis == writing.axis(LogicalAxis::Inline) {
            Size::Pixels(
                AhemText::new(text).min_content_width() + params.padding[axis].iter().sum::<f32>(),
            )
        } else {
            Size::FitContent
        });
    }
    let length = if axis == Axis::X { "width" } else { "height" };
    let children = xml.children().filter(|n| {
        n.is_element()
            && n.attribute("display") != Some("none")
            && n.attribute("position") != Some("absolute")
    });
    if xml.attribute("flex-wrap").is_some_and(|v| v != "nowrap") {
        return None;
    }
    let mut children = children.peekable();
    (children.peek().is_some()
        && children.all(|n| matches!(n.attribute(length).map(Value::parse), Some(Value::Px(_)))))
    .then_some(Size::FitContent)
}

fn static_alignment(parent: &LayoutParams, axis: Axis, align: Align) -> f32 {
    match parent.children_layout {
        ChildrenLayout::Stack {
            axis: main,
            arrange,
            ..
        }
        | ChildrenLayout::Wrap {
            axis: main,
            arrange,
            ..
        } if main == axis => {
            let logical = match arrange {
                Arrange::Start | Arrange::SpaceBetween => 0.0,
                Arrange::Center | Arrange::SpaceAround | Arrange::SpaceEvenly => 0.5,
                Arrange::End => 1.0,
            };
            if parent.children_origin_flipped[axis] {
                1.0 - logical
            } else {
                logical
            }
        }
        _ => {
            let logical = match align {
                Align::Start
                | Align::SelfStart
                | Align::Stretch
                | Align::FlexStart
                | Align::Baseline => 0.0,
                Align::Center | Align::SafeCenter => 0.5,
                Align::End
                | Align::SelfEnd
                | Align::SafeEnd
                | Align::LastBaseline
                | Align::FlexEnd => 1.0,
            };
            if parent.children_origin_flipped[axis] {
                1.0 - logical
            } else {
                logical
            }
        }
    }
}

pub fn build(
    tree: &mut Tree,
    parent: &NodeId,
    xml: roxmltree::Node,
    context: Parent,
) -> Result<Built> {
    let features = FixtureFeatures {
        vertical: xml.descendants().any(|n| {
            matches!(
                n.attribute("writing-mode"),
                Some("vertical-lr" | "vertical-rl")
            )
        }),
        scroll: xml
            .descendants()
            .any(|n| n.has_attribute("overflow-x") || n.has_attribute("overflow-y")),
    };
    build_in_context(
        tree,
        parent,
        xml,
        context,
        WritingContext::default(),
        LayoutParams::DEFAULT,
        features,
        None,
    )
}

/// A grid in an unrelated branch cannot change a Stack's fixed-size policy.
pub fn check_sibling_composition() {
    for sibling in ["block", "grid"] {
        let source = format!(
            r#"<input><div display="block" width="100px">
            <div width="100px" height="20px"><div width="80px"/><div width="80px"/></div>
            <div display="{sibling}" width="100px" height="20px"><div/></div>
        </div></input>"#
        );
        let xml = roxmltree::Document::parse(&source).unwrap();
        let mut tree = Tree::new();
        let root = tree.root();
        let panel = build(
            &mut tree,
            &root,
            xml.root_element().first_element_child().unwrap(),
            Parent::Viewport {
                size: Xy::new(Some(100.), Some(100.)),
            },
        )
        .unwrap();
        tree.solve_layout(Xy::new(100., 100.));
        for child in &panel.children[0].children {
            let rect = tree.layout(&child.node).unwrap();
            assert_eq!(rect.x[1] - rect.x[0], 80., "fixed width next to {sibling}");
        }
    }
}

#[derive(Clone, Copy)]
struct FixtureFeatures {
    vertical: bool,
    scroll: bool,
}

fn build_in_context(
    tree: &mut Tree,
    parent: &NodeId,
    xml: roxmltree::Node,
    context: Parent,
    inherited: WritingContext,
    parent_params: LayoutParams,
    features: FixtureFeatures,
    containing: Option<(&NodeId, WritingContext)>,
) -> Result<Built> {
    let mut style = Style::new(xml);
    let mut params = LayoutParams::DEFAULT;

    let logical = logical_style(&style)?;
    let writing = logical.context(inherited);
    style.resolve_logical_margins(xml, writing);
    params.children_origin_flipped = writing.origins();
    // Box edges. Borders lay out exactly like padding.
    let edges = |side: &str| -> Result<f32> {
        Ok(box_css::gap(&style, &format!("padding-{side}"))?.0
            + px(&style, &format!("border-{side}"))?)
    };
    params.padding = Xy::new(
        [edges("left")?, edges("right")?],
        [edges("top")?, edges("bottom")?],
    );
    let block_item = matches!(context, Parent::Block | Parent::Grid(..))
        && style.keyword("position", "static") != "absolute";
    params.margin = Xy::new(
        [
            margin(&style, "margin-left", block_item)?,
            margin(&style, "margin-right", block_item)?,
        ],
        [
            margin(&style, "margin-top", block_item)?,
            margin(&style, "margin-bottom", block_item)?,
        ],
    );
    let content_box = match style.keyword("box-sizing", "border-box") {
        "border-box" => false,
        "content-box" => true,
        other => return unsupported(format!("box-sizing={other}")),
    };
    let padding = params.padding;
    let extra = |axis: Axis| {
        if content_box {
            padding[axis][0] + padding[axis][1]
        } else {
            0.0
        }
    };
    let (extra_x, extra_y) = (extra(Axis::X), extra(Axis::Y));

    let width = size(style.value("width"), "width", extra_x)?;
    let height = size(style.value("height"), "height", extra_y)?;
    params.min_size = Xy::new(
        size(style.value("min-width"), "min-width", extra_x)?,
        size(style.value("min-height"), "min-height", extra_y)?,
    );
    params.max_size = Xy::new(
        size(style.value("max-width"), "max-width", extra_x)?,
        size(style.value("max-height"), "max-height", extra_y)?,
    );

    // The node's own container behavior.
    let text = xml
        .first_element_child()
        .is_none()
        .then(|| xml.text())
        .flatten()
        .map(str::trim);
    let display = style.keyword("display", "flex");
    let mut rule = NodeRules::default();
    box_css::geometry(&style, writing, &mut rule.box_model)?;
    box_css::overflow(&style, &mut rule, &mut params)?;
    if features.scroll {
        if rule.scroll.overflow != Xy::new_symm(keru_layout::layout_rules::Overflow::Visible) {
            rule.box_model.scroll_origin = Some(writing.origins());
        }
        if let Some(value) = text {
            let inline = writing.axis(LogicalAxis::Inline);
            let metrics = AhemText::new(value);
            rule.box_model.content_extent[inline] = metrics.min_content_width();
            rule.box_model.content_extent[inline.other()] = metrics.wrap(f32::INFINITY).1;
        }
    }
    rule.box_model.content_box = content_box
        && (rule.box_model.padding_fraction != Xy::new_symm([0.; 2])
            || [Axis::X, Axis::Y].iter().any(|&a| {
                params.padding[a].iter().sum::<f32>() > 0.
                    && [
                        if a == Axis::X { "width" } else { "height" },
                        if a == Axis::X {
                            "min-width"
                        } else {
                            "min-height"
                        },
                        if a == Axis::X {
                            "max-width"
                        } else {
                            "max-height"
                        },
                    ]
                    .iter()
                    .any(|name| matches!(style.value(name), Some(Value::Percent(_))))
            }));
    let mut own_grid = None;
    let mut own_flex_main = None;
    let mut own_align = Align::Stretch;
    let mut own_reverse_cross = false;
    if display != "flex" {
        // These declarations compute normally but apply only to flex containers.
        for name in ["flex-direction", "flex-wrap", "flex-line-count"] {
            style.get(name);
        }
    }
    match display {
        "none" => params.disabled = true,
        "flex" => {
            let direction = style.keyword("flex-direction", "row");
            let (main, reverse) = match direction {
                "row" => (writing.axis(LogicalAxis::Inline), false),
                "row-reverse" => (writing.axis(LogicalAxis::Inline), true),
                "column" => (writing.axis(LogicalAxis::Block), false),
                "column-reverse" => (writing.axis(LogicalAxis::Block), true),
                other => return unsupported(format!("flex-direction={other}")),
            };
            params.children_origin_flipped[main] ^= reverse;
            let gap = |name| box_css::gap(&style, name);
            let ((main_gap, main_percent), (cross_gap, cross_percent)) =
                if main == writing.axis(LogicalAxis::Inline) {
                    (gap("column-gap")?, gap("row-gap")?)
                } else {
                    (gap("row-gap")?, gap("column-gap")?)
                };
            let justification = style.keyword("justify-content", "normal");
            let arrange = arrange(justification, reverse)?;
            own_align = align(style.keyword("align-items", "normal"))?.unwrap_or(Align::Stretch);
            let count = style
                .keyword("flex-line-count", "1")
                .parse::<u16>()
                .map_err(|_| "invalid flex-line-count")?;
            let wrap = match style.keyword("flex-wrap", "nowrap") {
                "nowrap" => FlexWrap::NoWrap,
                "wrap" => FlexWrap::Wrap,
                "wrap-reverse" => FlexWrap::WrapReverse,
                "balance" | "wrap balance" => FlexWrap::Balance {
                    lines: count,
                    reverse: false,
                },
                "wrap-reverse balance" => FlexWrap::Balance {
                    lines: count,
                    reverse: true,
                },
                val => return unsupported(format!("flex-wrap={val}")),
            };
            let wrap_reverse = matches!(
                wrap,
                FlexWrap::WrapReverse | FlexWrap::Balance { reverse: true, .. }
            );
            own_reverse_cross = wrap_reverse;
            let line_policy = line_align(style.keyword("align-content", "normal"), wrap_reverse)?;
            params.children_layout = if wrap == FlexWrap::NoWrap {
                ChildrenLayout::Stack {
                    axis: main,
                    arrange,
                    spacing: main_gap,
                }
            } else {
                ChildrenLayout::Wrap {
                    axis: main,
                    arrange,
                    spacing: main_gap,
                    line_spacing: cross_gap,
                }
            };
            let complex_alignment = matches!(
                own_align,
                Align::Baseline | Align::LastBaseline | Align::SafeEnd | Align::SafeCenter
            );
            let grid_boundary = matches!(context, Parent::Grid(_))
                || xml.children().any(|child| {
                    child.attribute("display") == Some("grid")
                        && child.attribute("position") != Some("absolute")
                });
            if xml.first_element_child().is_some()
                && (grid_boundary
                    || wrap != FlexWrap::NoWrap
                    || complex_alignment
                    || justification.contains("safe ")
                    || main_percent != 0.
                    || cross_percent != 0.
                    || style.get("align-content").is_some()
                    || needs_managed_items(xml, main, writing, own_align))
            {
                rule.flex = Some(FlexLayout {
                    axis: main,
                    wrap,
                    gap: main_gap,
                    line_gap: cross_gap,
                    justify: arrange,
                    safe_justify: justification.starts_with("safe "),
                    align_items: flex_align(own_align),
                    align_content: line_policy,
                    ..Default::default()
                });
            }
            own_flex_main = Some(main);
        }
        "grid" => {
            let (grid, child_context) = grid_css::container(&style, writing)?;
            rule.grid = Some(grid);
            own_grid = Some(child_context);
        }
        "block" | "flow-root" => {
            params.children_layout = ChildrenLayout::Block;
            params.isolate_block_margins |= display == "flow-root";
        }
        other => return unsupported(format!("display={other}")),
    }
    block_css::lower(&style, context, display, &mut params, &mut rule)?;
    if let Some(text) = text {
        if writing.writing_mode == WritingMode::HorizontalTb {
            params.text = TextContent::Wrapping;
        } else {
            params.content_measure = keru_layout::ContentMeasure::WidthForHeight;
        }
        let _ = text;
    }

    // Placement as an item of its parent.
    let absolute = match style.keyword("position", "static") {
        "relative" => {
            box_css::relative(&style, writing, &parent_params, &mut rule)?;
            false
        }
        "static" => false,
        "absolute" => true,
        other => return unsupported(format!("position={other}")),
    };

    let grow = style.number("flex-grow", 0.0)?;
    // Stacks keep declared sizes in negative free space. Read the CSS factor
    // for validation; the scoreboard still compares against the Chrome result.
    let shrink = style.number("flex-shrink", 1.0)?;
    let basis = style.value("flex-basis");
    let align_self = if matches!(context, Parent::Grid(..)) {
        None
    } else {
        align(style.keyword("align-self", "auto"))?
    };
    let aspect = style.value("aspect-ratio");

    let mut declared = Xy::new(width, height);
    for (axis, prop) in [(Axis::X, "width"), (Axis::Y, "height")] {
        if style.value(prop) == Some(Value::MinContent) {
            declared[axis] = Some(Size::Pixels(box_css::minimum(xml, axis, writing)));
        }
    }
    match context {
        Parent::Viewport { size: window } => {
            for (axis, start, end) in [(Axis::X, "left", "right"), (Axis::Y, "top", "bottom")] {
                let [before, after] = params.margin[axis].map(|m| m.as_px().unwrap_or(0.0));
                let leading = if absolute {
                    inset(style.value(start))?
                } else {
                    None
                };
                let trailing = if absolute {
                    inset(style.value(end))?
                } else {
                    None
                };
                // The XML supplies a concrete viewport on definite axes. Its margins
                // and opposing insets consume space before the root box is sized.
                let length = window[axis];
                // The fixture viewport is a flex row with start-aligned items.
                // An unbounded viewport shrink-wraps its only child. Resolving
                // that child's 100% width then reproduces its intrinsic width.
                if display == "grid"
                    && axis == Axis::X
                    && !absolute
                    && length.is_none()
                    && before == 0.
                    && after == 0.
                    && declared[axis] == Some(Size::Frac(1.))
                {
                    declared[axis] = Some(Size::FitContent);
                }
                if declared[axis].is_none() {
                    declared[axis] = Some(match (length, leading, trailing) {
                        (Some(w), Some((f, p)), Some((g, q))) if absolute => {
                            Size::Pixels((w - (f * w + p) - (g * w + q) - before - after).max(0.0))
                        }
                        (Some(w), _, _) if !absolute && axis == Axis::X && display == "grid" => {
                            let padding: f32 = params.padding[axis].iter().sum();
                            rule.grid_fit_limit[axis] =
                                Some((w - before - after - padding).max(0.));
                            Size::FitContent
                        }
                        (Some(w), _, _) if !absolute && axis == Axis::X => {
                            Size::Pixels((w - before - after).max(0.0))
                        }
                        _ => Size::FitContent,
                    });
                }
                let (pos, anchor) = match (leading, trailing) {
                    (Some((fraction, offset)), _) => at(fraction, offset + before, 0.0, false),
                    (_, Some((fraction, offset))) => {
                        at(1.0 - fraction, -offset - after, 1.0, false)
                    }
                    _ if length.is_some() && writing.origins()[axis] => at(1.0, -after, 1.0, false),
                    _ => at(0.0, before, 0.0, false),
                };
                params.position[axis] = pos;
                params.anchor[axis] = anchor;
            }
        }
        Parent::Grid(grid) if absolute => {
            params.free_placement = true;
            (rule.grid_item, rule.grid_lines) = grid_css::item(&style, grid, writing)?;
            let mut insets = Xy::new_symm([None; 2]);
            for (a, s, e) in [(Axis::X, "left", "right"), (Axis::Y, "top", "bottom")] {
                for (slot, key) in insets[a].iter_mut().zip([s, e]) {
                    *slot = inset(style.value(key))?.map(|(fraction, pixels)| {
                        keru_layout::layout_rules::Length { fraction, pixels }
                    });
                }
                declared[a].get_or_insert(if insets[a].iter().all(Option::is_some) {
                    Size::Auto
                } else {
                    Size::FitContent
                });
            }
            if let Some((reference, reference_writing)) = containing
                && reference != parent
            {
                use keru_layout::tracks::GridAlign;
                for a in [Axis::X, Axis::Y] {
                    let f = match rule.grid_item.align[a] {
                        Some(GridAlign::End | GridAlign::SafeEnd | GridAlign::LastBaseline) => 1.,
                        Some(GridAlign::Center | GridAlign::SafeCenter) => 0.5,
                        _ => 0.,
                    };
                    rule.box_model.absolute_static[a] =
                        Some(if grid.origins[a] { 1. - f } else { f });
                    rule.box_model.safe_static[a] = matches!(
                        rule.grid_item.align[a],
                        Some(GridAlign::SafeCenter | GridAlign::SafeEnd)
                    );
                    rule.box_model.reverse_insets[a] = if insets[a].iter().all(Option::is_some) {
                        reference_writing.origins()[a]
                    } else {
                        grid.origins[a]
                    };
                }
                rule.placement = keru_layout::layout_rules::Placement::Absolute {
                    containing: keru_layout::layout_rules::BoxReference::Node(reference.clone()),
                    insets,
                };
            } else {
                rule.grid_overlay = Some(insets);
            }
        }
        _ if absolute => {
            params.free_placement = true;
            let parent_params = &parent_params;
            let parent_element = xml.parent_element().expect("fixture parent");
            let parent_style = Style::new(parent_element);
            // Native free placement is relative to the immediate parent. A CSS
            // inset or percentage size under a static non-root parent can read
            // a different ancestor; the no-inset static position still uses
            // the local formatting context.
            let parent_is_root = parent_element
                .parent_element()
                .is_some_and(|p| p.has_tag_name("input"));
            let upper_containing_block =
                !parent_is_root && parent_style.keyword("position", "static") == "static";
            let alignment = match context {
                Parent::Flex {
                    main,
                    align_items,
                    reverse_cross,
                    ..
                } => {
                    let a = item_alignment(
                        align_self.unwrap_or(align_items),
                        writing,
                        parent_params,
                        main.other(),
                    );
                    match a {
                        Align::FlexStart | Align::Stretch if reverse_cross => Align::End,
                        Align::FlexEnd if reverse_cross => Align::Start,
                        value => value,
                    }
                }
                _ => Align::Start,
            };
            let dynamic_padding = [
                "padding-left",
                "padding-right",
                "padding-top",
                "padding-bottom",
            ]
            .iter()
            .any(|key| matches!(parent_style.value(key), Some(Value::Percent(_))));
            let inline = writing.axis(LogicalAxis::Inline);
            let fitting = declared[inline].is_none()
                && (xml.first_element_child().is_some() || text.is_some())
                && (["left", "right", "margin-left", "margin-right"]
                    .iter()
                    .any(|p| style.get(p).is_some()));
            if fitting {
                rule.box_model.positioned_fit_min[inline] =
                    Some(box_css::minimum(xml, inline, writing));
            }
            let fractional = [width, height]
                .iter()
                .any(|size| matches!(size, Some(Size::Frac(_))))
                && parent_params.padding != Xy::new_symm([0.; 2]);
            let block_static = block_css::static_inline(
                rule.block_flow.justify_self,
                inherited.origins()[inline],
                writing.origins()[inline],
            );
            let safe_cross = matches!(alignment, Align::SafeCenter | Align::SafeEnd);
            let use_positioned = safe_cross
                || block_static.is_some()
                || upper_containing_block
                || dynamic_padding
                || fitting
                || fractional
                || [("left", "right"), ("top", "bottom")]
                    .iter()
                    .any(|&(l, r)| {
                        inset(style.value(l)).ok().flatten().is_some()
                            && inset(style.value(r)).ok().flatten().is_some()
                    })
                || [Axis::X, Axis::Y].iter().any(|&a| {
                    params.margin[a].iter().any(|m| m.as_px().is_none())
                        || declared[a] == Some(Size::Fill)
                })
                || ["overflow-x", "overflow-y"]
                    .iter()
                    .any(|p| parent_style.keyword(p, "visible") == "scroll");
            if use_positioned {
                use keru_layout::layout_rules::{BoxReference, Length, Placement};
                let mut insets = Xy::new_symm([None, None]);
                rule.box_model.reverse_insets = inherited.origins();
                for (a, l, r) in [(Axis::X, "left", "right"), (Axis::Y, "top", "bottom")] {
                    insets[a] = [inset(style.value(l))?, inset(style.value(r))?]
                        .map(|s| s.map(|(fraction, pixels)| Length { fraction, pixels }));
                    let both = insets[a].iter().all(Option::is_some);
                    // A static wrapper supplies static alignment, but the positioned
                    // containing block decides which of two specified insets wins.
                    if both && let Some((_, reference_writing)) = containing {
                        rule.box_model.reverse_insets[a] = reference_writing.origins()[a];
                    }
                    declared[a].get_or_insert(if both { Size::Auto } else { Size::FitContent });
                    rule.box_model.absolute_static[a] =
                        Some(static_alignment(parent_params, a, alignment));
                }
                if safe_cross && let Parent::Flex { main, .. } = context {
                    rule.box_model.safe_static[main.other()] = true;
                }
                if let Some((fraction, safe)) = block_static {
                    rule.box_model.absolute_static[inline] = Some(fraction);
                    rule.box_model.safe_static[inline] = safe;
                }
                if upper_containing_block
                    && let Some((reference, _)) = containing
                    && tree
                        .rules(reference)
                        .ok()
                        .flatten()
                        .is_some_and(|r| r.grid.is_some())
                {
                    rule.grid_lines = grid_css::placement(&style, inherited)?;
                }
                rule.placement = Placement::Absolute {
                    containing: if upper_containing_block {
                        containing.map_or(BoxReference::Window, |(id, _)| {
                            BoxReference::Node(id.clone())
                        })
                    } else {
                        BoxReference::Parent
                    },
                    insets,
                };
            } else {
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
                    (params.position[axis], params.anchor[axis]) = at(
                        fraction,
                        pixels,
                        anchor,
                        parent_params.children_origin_flipped[axis],
                    );
                    declared[axis].get_or_insert(Size::FitContent);
                }
            }
        }
        Parent::Flex {
            main,
            align_items,
            managed,
            reverse_cross,
        } => {
            let cross = main.other();
            let parent_params = &parent_params;
            let explicit_basis = basis.filter(|basis| !matches!(basis, Value::Auto));
            // A numeric basis is the starting flex size. A leaf's unbreakable text or
            // fixed-size children still supply its automatic minimum on the main axis.
            if explicit_basis.is_some()
                && declared[main].is_none()
                && params.min_size[main].is_none()
                && !matches!(
                    style.keyword(
                        if main == Axis::X {
                            "overflow-x"
                        } else {
                            "overflow-y"
                        },
                        "visible"
                    ),
                    "scroll" | "hidden" | "auto"
                )
            {
                let length = if main == Axis::X { "width" } else { "height" };
                if let Some(value) = text {
                    params.min_size[main] = Some(if main == Axis::X {
                        Size::Pixels(
                            AhemText::new(value).min_content_width()
                                + params.padding.x.iter().sum::<f32>(),
                        )
                    } else {
                        Size::FitContent
                    });
                } else if xml.first_element_child().is_some()
                    && xml.children().filter(|node| node.is_element()).all(|node| {
                        node.attribute(length)
                            .is_some_and(|v| matches!(Value::parse(v), Value::Px(_)))
                    })
                {
                    params.min_size[main] = Some(Size::FitContent);
                }
            }
            if managed {
                if main == writing.axis(LogicalAxis::Block)
                    && declared[main].is_none()
                    && params.min_size[main].is_none()
                    && xml.first_element_child().is_some()
                    && !matches!(
                        style.keyword(
                            if main == Axis::X {
                                "overflow-x"
                            } else {
                                "overflow-y"
                            },
                            "visible"
                        ),
                        "hidden" | "auto" | "scroll"
                    )
                {
                    params.min_size[main] = Some(Size::FitContent);
                }
                if declared[main].is_none()
                    && params.min_size[main].is_none()
                    && !matches!(
                        style.keyword(
                            if main == Axis::X {
                                "overflow-x"
                            } else {
                                "overflow-y"
                            },
                            "visible"
                        ),
                        "scroll" | "hidden" | "auto"
                    )
                {
                    params.min_size[main] =
                        if display == "grid" && main == writing.axis(LogicalAxis::Block) {
                            Some(Size::FitContent)
                        } else {
                            content_minimum(xml, text, main, writing, &params)
                        };
                }
                if params.min_size[main].is_none()
                    && let Some(Size::Pixels(preference)) = declared[main]
                    && !matches!(
                        style.keyword(
                            if main == Axis::X {
                                "overflow-x"
                            } else {
                                "overflow-y"
                            },
                            "visible"
                        ),
                        "hidden" | "auto" | "scroll"
                    )
                    && let Some(minimum) = content_minimum(xml, text, main, writing, &params)
                {
                    let intrinsic = match minimum {
                        Size::Pixels(v) => v,
                        _ => {
                            let column =
                                style.keyword("flex-direction", "row").starts_with("column");
                            let summing = (main == writing.axis(LogicalAxis::Block)) == column
                                && display == "flex"
                                && style.keyword("flex-wrap", "nowrap") == "nowrap";
                            let children = xml
                                .children()
                                .filter(|n| {
                                    n.is_element()
                                        && n.attribute("position") != Some("absolute")
                                        && n.attribute("display") != Some("none")
                                })
                                .map(|n| box_css::minimum(n, main, writing));
                            let inside = if summing {
                                children.sum()
                            } else {
                                children.fold(0., f32::max)
                            };
                            inside + params.padding[main].iter().sum::<f32>()
                        }
                    };
                    params.min_size[main] = Some(Size::Pixels(intrinsic.min(preference)));
                }
                rule.flex_fit_cross = (declared[cross].is_none()
                    && cross == writing.axis(LogicalAxis::Inline))
                .then(|| box_css::minimum(xml, cross, writing));
                let flex_basis = match explicit_basis {
                    None => FlexBasis::Preferred,
                    Some(Value::Px(n)) => FlexBasis::Pixels(n + extra(main)),
                    Some(Value::Percent(f)) if extra(main) == 0. => FlexBasis::Fraction(f),
                    Some(Value::Percent(f)) => FlexBasis::FractionPlus(f, extra(main)),
                    Some(Value::Content | Value::MaxContent) => FlexBasis::Content,
                    Some(Value::MinContent | Value::FitContent) => {
                        let minimum = content_minimum(xml, text, main, writing, &params);
                        match (explicit_basis, minimum) {
                            (Some(Value::MinContent), Some(Size::Pixels(v))) => {
                                FlexBasis::Pixels(v)
                            }
                            (Some(Value::MinContent), _) => FlexBasis::Content,
                            (_, Some(Size::Pixels(v))) => FlexBasis::FitContent(v),
                            _ => FlexBasis::FitContent(0.),
                        }
                    }
                    Some(Value::Stretch) => FlexBasis::Stretch,
                    value => return unsupported(format!("flex-basis={value:?}")),
                };
                rule.flex_item = FlexItem {
                    grow,
                    shrink,
                    basis: flex_basis,
                    ..FlexItem::css()
                };
            } else if grow > 0.0 {
                if !matches!(basis, Some(Value::Px(v)) if v == 0.0)
                    && !matches!(basis, Some(Value::Percent(p)) if p == 0.0)
                {
                    return unsupported("flex-grow with a non-zero basis");
                }
                // CSS also uses the preferred main size to size an intrinsic flex
                // container. Fill stores the zero basis and weight, but has no
                // separate preferred contribution; a hard minimum would change it.
                if matches!(parent_params.size[main], Size::FitContent)
                    && matches!(declared[main], Some(Size::Pixels(value)) if value > 0.0)
                {
                    return unsupported(
                        "preferred main size with zero-basis growth in an intrinsic flex container",
                    );
                }
                declared[main] = Some(Size::Fill);
                params.fill_weight = grow;
            } else if let Some(basis) = explicit_basis {
                declared[main] = size(Some(basis), "flex-basis", extra(main))?;
            }
            // A sole shrinkable text item in a definite row takes its natural
            // width up to the available width, keeping unbreakable runs intact.
            if !managed
                && main == Axis::X
                && declared.x.is_none()
                && shrink == 1.0
                && params.max_size.x.is_none()
                && aspect.is_none()
                && matches!(parent_params.size.x, Size::Pixels(_))
                && matches!(parent_params.children_layout, ChildrenLayout::Stack { .. })
            {
                if let Some(value) = text.filter(|_| {
                    xml.parent_element().is_some_and(|p| {
                        p.children()
                            .filter(|n| {
                                n.is_element()
                                    && n.attribute("position") != Some("absolute")
                                    && n.attribute("display") != Some("none")
                            })
                            .count()
                            == 1
                    })
                }) {
                    let text = AhemText::new(value);
                    let padding = params.padding.x.iter().sum::<f32>();
                    declared.x = Some(Size::Fill);
                    params.max_size.x = Some(Size::Pixels(text.max_content_width() + padding));
                    params
                        .min_size
                        .x
                        .get_or_insert(Size::Pixels(text.min_content_width() + padding));
                }
            }
            if declared[main].is_none() {
                declared[main] = Some(Size::FitContent);
            }
            let alignment = item_alignment(
                align_self.unwrap_or(align_items),
                writing,
                parent_params,
                cross,
            );
            if managed {
                rule.flex_item.align_self = Some(flex_align(line_item_alignment(
                    alignment,
                    reverse_cross,
                    cross,
                    writing,
                )));
            }
            if declared[cross].is_none() {
                let stretch = alignment == Align::Stretch && aspect.is_none();
                declared[cross] = Some(if stretch {
                    Size::Fill
                } else {
                    Size::FitContent
                });
                // Stretch happens after line sizing. When content determines the
                // line, contribute the item's hypothetical size before filling it.
                if !managed
                    && stretch
                    && params.min_size[cross].is_none()
                    && (matches!(parent_params.size[cross], Size::FitContent)
                        || matches!(parent_params.min_size[cross], Some(Size::FitContent))
                        || matches!(parent_params.children_layout, ChildrenLayout::Wrap { .. }))
                {
                    params.min_size[cross] = Some(Size::FitContent);
                }
            }
            let (pos, anchor) = match alignment {
                Align::Stretch
                | Align::Start
                | Align::SelfStart
                | Align::FlexStart
                | Align::Baseline => (Pos::Start, Anchor::Start),
                Align::SafeCenter | Align::Center => (Pos::Center, Anchor::Center),
                Align::End
                | Align::SelfEnd
                | Align::FlexEnd
                | Align::SafeEnd
                | Align::LastBaseline => (Pos::End, Anchor::End),
            };
            params.position[cross] = pos;
            params.anchor[cross] = anchor;
        }
        Parent::Grid(grid) => {
            (rule.grid_item, rule.grid_lines) = grid_css::item(&style, grid, writing)?;
            for axis in [Axis::X, Axis::Y] {
                let measure = if display == "grid" {
                    Some(Size::FitContent)
                } else {
                    content_minimum(xml, text, axis, writing, &params).or_else(|| {
                        (xml.first_element_child().is_some()
                            && axis == writing.axis(LogicalAxis::Inline))
                        .then(|| Size::Pixels(box_css::minimum(xml, axis, writing)))
                    })
                };
                rule.grid_intrinsic_minimum[axis] = measure;
                let scrollable = ["overflow-x", "overflow-y"]
                    .iter()
                    .any(|p| matches!(style.keyword(p, "visible"), "hidden" | "scroll" | "auto"));
                if !scrollable && params.min_size[axis].is_none() && declared[axis].is_none() {
                    rule.grid_content_minimum[axis] = measure;
                }
                declared[axis].get_or_insert(if aspect.is_some() {
                    Size::FitContent
                } else {
                    Size::Auto
                });
            }
        }
        Parent::Block => {
            let inline = inherited.axis(LogicalAxis::Inline);
            declared[inline].get_or_insert(Size::Auto);
            declared[inline.other()].get_or_insert(Size::FitContent);
        }
    }
    for (axis, property) in [(Axis::X, "width"), (Axis::Y, "height")] {
        if params.min_size[axis].is_none()
            && style.value(property) == Some(Value::MaxContent)
            && axis == writing.axis(LogicalAxis::Inline)
        {
            params.min_size[axis] = Some(Size::Pixels(box_css::minimum(xml, axis, writing)));
        }
    }
    if let Some(aspect) = aspect {
        let Value::Number(ratio) = aspect else {
            return unsupported("aspect-ratio");
        };
        if !(width.is_some() && height.is_some()) {
            let intrinsic =
                |a: Axis| matches!(declared[a], None | Some(Size::FitContent | Size::Auto));
            let derived = match (width, height) {
                (Some(_), None) => Axis::Y,
                (None, Some(_)) => Axis::X,
                _ if declared.x == Some(Size::FitContent)
                    && declared.y != Some(Size::FitContent) =>
                {
                    Axis::X
                }
                _ if declared.y == Some(Size::FitContent)
                    && declared.x != Some(Size::FitContent) =>
                {
                    Axis::Y
                }
                _ if intrinsic(Axis::X) != intrinsic(Axis::Y) => {
                    if intrinsic(Axis::X) {
                        Axis::X
                    } else {
                        Axis::Y
                    }
                }
                _ if text.is_some()
                    && (absolute
                        || (matches!(context, Parent::Flex { .. })
                            && params.max_size.y.is_some())) =>
                {
                    writing.axis(LogicalAxis::Block)
                }
                _ if (params.min_size.y.is_some() || params.max_size.y.is_some())
                    && params.min_size.x.is_none()
                    && params.max_size.x.is_none() =>
                {
                    Axis::X
                }
                _ if matches!(
                    context,
                    Parent::Flex {
                        main: Axis::X,
                        align_items: Align::Stretch,
                        ..
                    }
                ) && !absolute =>
                {
                    Axis::X
                }
                _ => Axis::Y,
            };
            let driving = derived.other();
            if matches!(context, Parent::Grid(_))
                && !absolute
                && width.is_none()
                && height.is_none()
            {
                declared[driving] = Some(Size::Auto);
            }
            // When unwrapped text sets the intrinsic driving dimension, respect a
            // definite bound on its ratio-dependent dimension before wrapping.
            if (absolute
                || matches!(context, Parent::Flex {main,align_items,..} if align_items != Align::Stretch || main == driving))
                && text.is_some()
                && width.is_none()
                && height.is_none()
                && declared[driving] == Some(Size::FitContent)
            {
                let transfer = |v| {
                    if driving == Axis::X {
                        v * ratio
                    } else {
                        v / ratio
                    }
                };
                if let Some(Size::Pixels(v)) = params.max_size[derived] {
                    let cap = transfer(v);
                    if params.max_size[driving].is_none() {
                        params.max_size[driving] = Some(Size::Pixels(cap));
                    }
                }
                if let Some(Size::Pixels(v)) = params.min_size[derived] {
                    let floor = transfer(v);
                    if params.min_size[driving].is_none() {
                        params.min_size[driving] = Some(Size::Pixels(floor));
                    }
                }
            }
            if matches!(context,Parent::Flex{main,align_items:Align::Stretch,..} if main!=driving)
                && !absolute
                && width.is_none()
                && height.is_none()
            {
                declared[driving] = Some(Size::Fill);
            }
            declared[derived] = Some(Size::AspectRatio(ratio));
            if matches!(context, Parent::Flex {main, managed:true,..} if main == derived)
                && style
                    .value(if derived == Axis::X {
                        "min-width"
                    } else {
                        "min-height"
                    })
                    .is_none()
            {
                // Once the ratio supplies this dimension, text reflow cannot
                // independently impose a second intrinsic minimum on it.
                params.min_size[derived] = None;
            }
        }
    }
    params.size = Xy::new(
        declared.x.unwrap_or(Size::FitContent),
        declared.y.unwrap_or(Size::FitContent),
    );

    if matches!(context, Parent::Grid(..)) {
        for axis in [Axis::X, Axis::Y] {
            if matches!(params.size[axis], Size::AspectRatio(_)) && params.min_size[axis].is_none()
            {
                rule.grid_content_minimum[axis] = Some(params.size[axis]);
            }
        }
    }

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
            Some(other) => other,
        });
        match params.max_size[axis] {
            Some(Size::Pixels(max)) => params.max_size[axis] = Some(Size::Pixels(max.max(floor))),
            Some(Size::FitContent) | None => {}
            Some(_) => {}
        }
    }

    let unread = style.unread();
    if !unread.is_empty() {
        return unsupported(unread.join(" "));
    }

    let child_params = params;
    if features.vertical {
        let origin = writing.origins();
        params.children_origin_flipped.x ^= origin.x;
        params.children_origin_flipped.y ^= origin.y;
    }
    let node: NodeId = match text {
        Some(text) => (*tree
            .add_node_with_context(parent, params, AhemText::new(text))
            .map_err(|e| e.to_string())?)
        .clone(),
        None => (*tree.add_node(parent, params).map_err(|e| e.to_string())?).clone(),
    };
    if features.vertical {
        rule.logical = logical;
    }
    let forms_containing = matches!(style.keyword("position", "static"), "relative" | "absolute")
        || style.keyword("contain", "none") != "none"
        || matches!(context, Parent::Viewport { .. });
    let managed_line = rule.flex.is_some();
    if rule != NodeRules::default() {
        tree.set_rules(&node, rule)
            .map_err(|error| error.to_string())?;
    }
    let child_context = match (own_flex_main, display) {
        (Some(main), _) => Parent::Flex {
            main,
            align_items: own_align,
            managed: managed_line,
            reverse_cross: own_reverse_cross,
        },
        (None, "grid") => Parent::Grid(own_grid.expect("parsed grid container")),
        _ => Parent::Block,
    };
    let mut children = Vec::new();
    for child in xml.children().filter(|child| child.is_element()) {
        children.push(build_in_context(
            tree,
            &node,
            child,
            child_context,
            writing,
            child_params,
            features,
            if forms_containing {
                Some((&node, writing))
            } else {
                containing
            },
        )?);
    }
    Ok(Built {
        node,
        disabled: params.disabled,
        children,
    })
}
