use super::Mode;
use std::collections::HashMap;

pub use current::{
    Anchor, Arrange, Axis, ChildrenLayout, LayoutParams, MainAxisCellSize, Margin, PixelScale, Pos,
    Size, TextContent, WindowOverflow, Xy, XyRect,
};

#[derive(Clone, Debug)]
pub enum NodeId {
    CurrentRoot(current::NodeId),
    CurrentChild(current::ChildId),
    Original(original::NodeId),
}

pub type ChildId = NodeId;

impl NodeId {
    fn current(&self) -> &current::NodeId {
        match self {
            Self::CurrentRoot(id) => id,
            Self::CurrentChild(id) => id,
            Self::Original(_) => unreachable!(),
        }
    }

    fn current_child(&self) -> &current::ChildId {
        match self {
            Self::CurrentChild(id) => id,
            _ => unreachable!(),
        }
    }

    fn original(&self) -> original::NodeId {
        match self {
            Self::Original(id) => *id,
            _ => unreachable!(),
        }
    }
}

pub enum Destination<'a> {
    Before(&'a ChildId),
    LastChildOf(&'a NodeId),
}

enum Tree<T> {
    Current(current::LayoutTree<T>),
    Original(
        original::LayoutTree<T>,
        HashMap<original::NodeId, LayoutParams>,
    ),
}

pub struct LayoutTree<T> {
    mode: Mode,
    tree: Tree<T>,
}

thread_local! {
    static BUILD_MODE: std::cell::Cell<Mode> = const { std::cell::Cell::new(Mode::Batch) };
}

pub(super) fn build_cases(mode: Mode) -> Vec<super::Case> {
    BUILD_MODE.set(mode);
    super::browser::cases()
        .into_iter()
        .chain(super::compositor::cases())
        .chain(super::cad::cases())
        .collect()
}

impl<T> LayoutTree<T> {
    pub fn new() -> Self {
        Self::with_capacity(16).unwrap()
    }

    pub fn with_capacity(capacity: usize) -> Result<Self, current::TreeError> {
        let mode = BUILD_MODE.get();
        let tree = if mode.original() {
            let tree = original::LayoutTree::with_capacity(capacity);
            let params = HashMap::from([(tree.root(), LayoutParams::DEFAULT)]);
            Tree::Original(tree, params)
        } else {
            Tree::Current(current::LayoutTree::with_capacity(capacity)?)
        };
        Ok(Self { mode, tree })
    }

    pub fn root(&self) -> NodeId {
        match &self.tree {
            Tree::Current(tree) => NodeId::CurrentRoot(tree.root()),
            Tree::Original(tree, _) => NodeId::Original(tree.root()),
        }
    }

    pub fn add_node(
        &mut self,
        parent: &NodeId,
        params: LayoutParams,
    ) -> Result<ChildId, current::TreeError> {
        let params = common(params);
        match &mut self.tree {
            Tree::Current(tree) => tree
                .add_node(parent.current(), params)
                .map(NodeId::CurrentChild),
            Tree::Original(tree, styles) => {
                let id = tree.add_node(parent.original(), convert_params(params));
                styles.insert(id, params);
                Ok(NodeId::Original(id))
            }
        }
    }

    pub fn add_node_with_context(
        &mut self,
        parent: &NodeId,
        params: LayoutParams,
        value: T,
    ) -> Result<ChildId, current::TreeError> {
        let params = common(params);
        match &mut self.tree {
            Tree::Current(tree) => tree
                .add_node_with_context(parent.current(), params, value)
                .map(NodeId::CurrentChild),
            Tree::Original(tree, styles) => {
                let id =
                    tree.add_node_with_context(parent.original(), convert_params(params), value);
                styles.insert(id, params);
                Ok(NodeId::Original(id))
            }
        }
    }

    pub fn params(&self, id: &NodeId) -> Result<&LayoutParams, current::TreeError> {
        match &self.tree {
            Tree::Current(tree) => tree.params(id.current()),
            Tree::Original(_, styles) => Ok(&styles[&id.original()]),
        }
    }

    pub fn update_node_params(
        &mut self,
        id: &NodeId,
        params: LayoutParams,
    ) -> Result<(), current::TreeError> {
        let params = common(params);
        match &mut self.tree {
            Tree::Current(tree) => tree.update_node_params(id.current(), params),
            Tree::Original(tree, styles) => {
                tree.update_node_params(id.original(), convert_params(params));
                styles.insert(id.original(), params);
                Ok(())
            }
        }
    }

    pub fn update_node_context(
        &mut self,
        id: &NodeId,
        value: Option<T>,
    ) -> Result<(), current::TreeError> {
        match &mut self.tree {
            Tree::Current(tree) => tree.update_node_context(id.current(), value),
            Tree::Original(tree, _) => {
                tree.update_node_context(id.original(), value);
                Ok(())
            }
        }
    }

    pub fn move_node(
        &mut self,
        id: &ChildId,
        to: Destination<'_>,
    ) -> Result<(), current::TreeError> {
        match &mut self.tree {
            Tree::Current(tree) => {
                let to = match to {
                    Destination::Before(sibling) => {
                        current::Destination::Before(sibling.current_child())
                    }
                    Destination::LastChildOf(parent) => {
                        current::Destination::LastChildOf(parent.current())
                    }
                };
                tree.move_node(id.current_child(), to)
            }
            Tree::Original(tree, _) => {
                let (parent, before) = match to {
                    Destination::Before(sibling) => {
                        let sibling = sibling.original();
                        (tree.parent(sibling).unwrap(), Some(sibling))
                    }
                    Destination::LastChildOf(parent) => (parent.original(), None),
                };
                tree.move_node(id.original(), parent, before);
                Ok(())
            }
        }
    }

    pub fn remove(&mut self, id: &ChildId) -> Result<(), current::TreeError> {
        match &mut self.tree {
            Tree::Current(tree) => tree.remove(id.current_child()),
            Tree::Original(tree, styles) => {
                let mut pending = vec![id.original()];
                while let Some(node) = pending.pop() {
                    pending.extend(tree.children(node));
                    styles.remove(&node);
                }
                tree.remove(id.original());
                Ok(())
            }
        }
    }

    // Both engines use logical pixels because snapping arrived after upstream.
    pub fn set_pixel_scale(&mut self, _: Option<PixelScale>) {}

    pub(super) fn children(&self, id: &NodeId, pending: &mut Vec<NodeId>) {
        match &self.tree {
            Tree::Current(tree) => pending.extend(
                tree.children(id.current())
                    .unwrap()
                    .map(NodeId::CurrentChild),
            ),
            Tree::Original(tree, _) => {
                pending.extend(tree.children(id.original()).map(NodeId::Original))
            }
        }
    }

    pub(super) fn layout(&self, id: &NodeId) -> Option<XyRect> {
        match &self.tree {
            Tree::Current(tree) => match tree.layout(id.current()) {
                Ok(rect) => Some(rect),
                Err(current::TreeError::LayoutUnavailable) => None,
                Err(error) => panic!("{error}"),
            },
            Tree::Original(tree, _) => {
                let id = id.original();
                if tree.params(id).disabled {
                    return None;
                }
                let rect = tree.layout(id);
                Some(Xy::new(rect.x, rect.y))
            }
        }
    }

    pub(super) fn has_warnings(&self) -> bool {
        match &self.tree {
            Tree::Current(tree) => !tree.warnings().is_empty(),
            Tree::Original(tree, _) => !tree.warnings().is_empty(),
        }
    }

    pub(super) fn invalidate_if_forced(&mut self) {
        match (&mut self.tree, self.mode) {
            (Tree::Original(tree, _), Mode::UpstreamFull) => tree.invalidate(),
            (Tree::Current(tree), Mode::TunedFull) => tree.invalidate(),
            _ => {}
        }
    }
}

impl<T: AsRef<str>> LayoutTree<T> {
    pub(super) fn solve(&mut self, window: Xy<f32>) -> bool {
        match (&mut self.tree, self.mode) {
            (Tree::Current(tree), Mode::Batch) => {
                tree.solve_layout_batch_with_measure(window, |_, text, width| {
                    let [w, h] = measure(text, width);
                    Xy::new(w, h)
                })
                .unwrap()
                .rebuilt_graph
            }
            (Tree::Current(tree), _) => !matches!(
                tree.solve_layout_with_measure(window, |_, text, width| {
                    let [w, h] = measure(text, width);
                    Xy::new(w, h)
                }),
                current::IncrementalRelayoutOutcome::Success { .. }
            ),
            (Tree::Original(tree, _), _) => !matches!(
                tree.solve_layout_with_measure(
                    original::Xy::new(window.x, window.y),
                    |_, text, width| {
                        let [w, h] = measure(text, width);
                        original::Xy::new(w, h)
                    }
                ),
                original::IncrementalRelayoutOutcome::Success { .. }
            ),
        }
    }
}

fn measure<T: AsRef<str>>(text: Option<&mut T>, width: Option<f32>) -> [f32; 2] {
    // Match the upstream monospace word wrapping without constructing lines.
    const CHAR: f32 = 12.0 * 0.6;
    const LINE: f32 = 12.0 * 1.2;
    let limit = width.map_or(usize::MAX, |width| (width / CHAR) as usize);
    let mut lines = 0;
    let mut longest = 0;
    let mut active = 0;
    for word in text.as_deref().map_or("", T::as_ref).split_whitespace() {
        let chars = word.chars().count();
        if active != 0 && active + 1 + chars <= limit {
            active += 1 + chars;
        } else {
            active = chars;
            lines += 1;
        }
        longest = longest.max(active);
    }
    [longest as f32 * CHAR, lines as f32 * LINE]
}

fn common(mut params: LayoutParams) -> LayoutParams {
    // Project the existing fixtures onto the declarations both engines share.
    params.children_layout = match params.children_layout {
        ChildrenLayout::Block => ChildrenLayout::Stack {
            axis: Axis::Y,
            arrange: Arrange::Start,
            spacing: 0.0,
        },
        ChildrenLayout::Wrap {
            axis,
            arrange,
            spacing,
            ..
        } => ChildrenLayout::Stack {
            axis,
            arrange,
            spacing,
        },
        layout => layout,
    };
    if matches!(params.size.x, Size::Auto) {
        params.size.x = Size::Fill;
    }
    if matches!(params.size.y, Size::Auto) {
        params.size.y = Size::FitContent;
    }
    params.margin = Xy::new_symm([Margin::ZERO; 2]);
    assert!(matches!(
        params.content_measure,
        current::ContentMeasure::None
    ));
    params
}

macro_rules! convert_enum {
    ($name:ident: $ty:ident { $($plain:ident),*; $($payload:ident),* }) => {
        fn $name(value: $ty) -> original::$ty {
            match value {
                $($ty::$plain => original::$ty::$plain,)*
                $($ty::$payload(value) => original::$ty::$payload(value),)*
            }
        }
    }
}
convert_enum!(axis: Axis { X, Y; });
convert_enum!(arrange: Arrange { Start, End, Center, SpaceBetween, SpaceAround, SpaceEvenly; });
convert_enum!(position: Pos { Start, End, Center; Pixels, Frac });
convert_enum!(anchor: Anchor { Start, End, Center; Frac });
convert_enum!(text_mode: TextContent { None, Wrapping, Fixed; });
convert_enum!(overflow: WindowOverflow { Ignore, Clamp, Flip; });
convert_enum!(cell_size: MainAxisCellSize { ; Count, Width });

fn size(value: Size) -> original::Size {
    match value {
        Size::Fill => original::Size::Fill,
        Size::FitContent => original::Size::FitContent,
        Size::Pixels(value) => original::Size::Pixels(value),
        Size::Frac(value) => original::Size::Frac(value),
        Size::AspectRatio(value) => original::Size::AspectRatio(value),
        Size::Auto => unreachable!(),
    }
}

fn xy<T, U>(value: Xy<T>, map: impl Fn(T) -> U) -> original::Xy<U> {
    original::Xy::new(map(value.x), map(value.y))
}

fn convert_params(params: LayoutParams) -> original::LayoutParams {
    original::LayoutParams {
        position: xy(params.position, position),
        size: xy(params.size, size),
        min_size: xy(params.min_size, |value| value.map(size)),
        max_size: xy(params.max_size, |value| value.map(size)),
        padding: xy(params.padding, |value| value),
        children_layout: match params.children_layout {
            ChildrenLayout::Free => original::ChildrenLayout::Free,
            ChildrenLayout::Stack {
                axis: main,
                arrange: how,
                spacing,
            } => original::ChildrenLayout::Stack {
                axis: axis(main),
                arrange: arrange(how),
                spacing,
            },
            ChildrenLayout::Grid {
                columns,
                spacing_x,
                spacing_y,
                main_axis,
                backfill,
            } => original::ChildrenLayout::Grid {
                columns: cell_size(columns),
                spacing_x,
                spacing_y,
                main_axis: axis(main_axis),
                backfill,
            },
            ChildrenLayout::Wrap { .. } | ChildrenLayout::Block => unreachable!(),
        },
        free_placement: params.free_placement,
        grid_span: xy(params.grid_span, |value| value),
        text: text_mode(params.text),
        image: params.image.map(|value| xy(value, |value| value)),
        anchor: xy(params.anchor, anchor),
        children_origin_flipped: xy(params.children_origin_flipped, |value| value),
        window_overflow: xy(params.window_overflow, overflow),
        fill_weight: params.fill_weight,
        disabled: params.disabled,
    }
}
