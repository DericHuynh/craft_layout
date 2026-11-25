//! Size containment and nearest eligible ancestor queries.
use super::RuleIssue;
use super::driver::Frame;
use crate::{
    Axis, ChildrenLayout, LayoutParams, Size, Xy, flex::FlexLayout, logical::LogicalAxis,
    tracks::TrackGrid,
};

/// A named or anonymous size-query container. A contained intrinsic dimension
/// uses its placeholder in place of descendant contributions.
#[derive(Clone, Debug, PartialEq)]
pub struct Container {
    /// Optional query name.
    pub name: Option<String>,
    /// Containment in physical X/Y axes.
    pub axes: Xy<bool>,
    /// Content-box intrinsic fallback per axis, in logical pixels.
    pub placeholder: Xy<f32>,
}
impl Container {
    /// Contain one physical axis, with a zero intrinsic placeholder.
    pub fn axis(axis: Axis) -> Self {
        Self {
            name: None,
            axes: Xy::new(axis == Axis::X, axis == Axis::Y),
            placeholder: Xy::new_symm(0.),
        }
    }
}

/// A complete replacement for a node's child formatting context while a query matches.
/// The last matching query which selects a layout wins. When none select a layout
/// the node uses its authored flex, grid or native flow again.
#[derive(Clone, Debug, PartialEq)]
pub enum QueryLayout {
    /// Use a native flow such as a stack, wrap or block.
    Native(ChildrenLayout),
    /// Arrange children in flexible lines.
    Flex(FlexLayout),
    /// Arrange children on explicit, repeated or shared tracks.
    Grid(TrackGrid),
}

/// Optional changes applied in source order when an ancestor query matches.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct QueryStyle {
    /// Override selected physical sizes.
    pub size: Xy<Option<Size>>,
    /// Replace the active formatting context, including an authored grid or flex layout.
    pub layout: Option<QueryLayout>,
    /// Shorthand for selecting a native flow. An explicit `layout` takes precedence.
    pub children_layout: Option<ChildrenLayout>,
    /// Override physical padding.
    pub padding: Option<Xy<[f32; 2]>>,
}

/// An inclusive interval over the content-box extent on a container's logical axis.
#[derive(Clone, Debug, PartialEq)]
pub struct ContainerQuery {
    /// Select the nearest eligible container with this name, or any name when absent.
    pub name: Option<String>,
    /// Axis in the queried container's writing context.
    pub axis: LogicalAxis,
    /// Inclusive lower bound.
    pub min: Option<f32>,
    /// Inclusive upper bound.
    pub max: Option<f32>,
    /// Declarations to apply while the interval matches.
    pub style: QueryStyle,
}

pub(super) fn apply(
    frame: &Frame<'_>,
    node: usize,
    params: &mut LayoutParams,
    issues: &mut Vec<RuleIssue>,
) -> Option<usize> {
    let queries = &frame.nodes[node].rule.queries;
    let mut layout_query = None;
    for (index, query) in queries.iter().enumerate() {
        let mut parent = frame.nodes[node].parent;
        let mut found = false;
        while let Some(i) = parent {
            let ancestor = &frame.nodes[i];
            let axis = ancestor.context.axis(query.axis);
            if let Some(scope) = &ancestor.rule.container
                && scope.axes[axis]
                && (query.name.is_none() || scope.name == query.name)
            {
                found = true;
                // Use the unrounded content box produced by the solver. Its
                // allocation can be smaller than its authored pixel width.
                let value = ancestor
                    .query_content
                    .unwrap_or_else(|| frame.content_size(i))[axis];
                if query.min.is_none_or(|min| value >= min)
                    && query.max.is_none_or(|max| value <= max)
                {
                    if query.style.layout.is_some() || query.style.children_layout.is_some() {
                        layout_query = Some(index);
                    }
                    if let Some(padding) = query.style.padding {
                        params.padding = padding;
                    }
                    for axis in [Axis::X, Axis::Y] {
                        if let Some(s) = query.style.size[axis] {
                            params.size[axis] = s;
                        }
                    }
                }
                break;
            }
            parent = ancestor.parent;
        }
        if !found {
            issues.push(RuleIssue::MissingContainer(frame.nodes[node].id.clone()));
        }
    }
    if let Some(index) = layout_query {
        let style = &queries[index].style;
        match &style.layout {
            Some(QueryLayout::Native(flow)) => params.children_layout = *flow,
            None => {
                if let Some(flow) = style.children_layout {
                    params.children_layout = flow;
                }
            }
            _ => {}
        }
    }
    if let Some(scope) = &frame.nodes[node].rule.container {
        for a in [Axis::X, Axis::Y] {
            if !scope.axes[a] {
                continue;
            }
            let intrinsic = scope.placeholder[a].max(0.) + params.padding[a].iter().sum::<f32>();
            // Each content-based input on the contained axis uses the placeholder.
            if frame.is_intrinsic(node, a, params.size[a]) {
                params.size[a] = Size::Pixels(intrinsic);
            }
            if matches!(params.min_size[a], Some(Size::FitContent | Size::Auto)) {
                params.min_size[a] = Some(Size::Pixels(intrinsic));
            }
            if matches!(params.max_size[a], Some(Size::FitContent | Size::Auto)) {
                params.max_size[a] = Some(Size::Pixels(intrinsic));
            }
        }
    }
    layout_query
}
