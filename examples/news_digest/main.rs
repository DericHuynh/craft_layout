//! A magazine column with filters, two physical floats, inset content and a
//! footer that clears the surviving floats. Run with --features batch-pilot
//! to compare the optional scheduler too.
use keru_layout::layout_rules::{BlockStyle, Clear, Float, NodeRules};
use keru_layout::{ChildId, ChildrenLayout, LayoutParams, LayoutTree, Pos, Size, Xy};

#[derive(Clone, Copy)]
struct State {
    width: f32,
    sponsor: bool,
    summary_minimum: f32,
}
struct Digest {
    tree: LayoutTree<()>,
    column: ChildId,
    portrait: ChildId,
    sponsor: ChildId,
    title: ChildId,
    summary: ChildId,
    footer: ChildId,
    ticks: Vec<ChildId>,
}
impl Digest {
    fn new() -> Self {
        let mut tree = LayoutTree::new();
        let root = tree.root();
        let column = tree
            .add_node(
                &root,
                LayoutParams {
                    children_layout: ChildrenLayout::Block,
                    size: Xy::new(Size::Fill, Size::FitContent),
                    position: Xy::new_symm(Pos::Start),
                    ..Default::default()
                },
            )
            .unwrap();
        let mut add = |width, height, block, style, isolate| {
            let id = tree
                .add_node(
                    &column,
                    LayoutParams {
                        size: Xy::new(width, Size::Pixels(height)),
                        children_layout: if block {
                            ChildrenLayout::Block
                        } else {
                            ChildrenLayout::Free
                        },
                        isolate_block_margins: isolate,
                        ..Default::default()
                    },
                )
                .unwrap();
            tree.set_rules(
                &id,
                NodeRules {
                    block_flow: style,
                    ..Default::default()
                },
            )
            .unwrap();
            id
        };
        let portrait = add(
            Size::Pixels(96.),
            60.,
            true,
            BlockStyle {
                float: Float::Left,
                ..Default::default()
            },
            false,
        );
        let sponsor = add(
            Size::Pixels(64.),
            40.,
            true,
            BlockStyle {
                float: Float::Right,
                ..Default::default()
            },
            false,
        );
        let title = add(Size::Auto, 24., true, Default::default(), false);
        let summary = add(Size::Auto, 36., true, Default::default(), true);
        let footer = add(
            Size::Auto,
            16.,
            true,
            BlockStyle {
                clear: Clear::Both,
                ..Default::default()
            },
            false,
        );
        let mut ticks = Vec::new();
        for part in [&portrait, &sponsor, &summary] {
            for _ in 0..8 {
                ticks.push(
                    tree.add_node(
                        part,
                        LayoutParams {
                            size: Xy::new(Size::Auto, Size::Pixels(3.)),
                            children_layout: ChildrenLayout::Block,
                            ..Default::default()
                        },
                    )
                    .unwrap(),
                );
            }
        }
        Self {
            tree,
            column,
            portrait,
            sponsor,
            title,
            summary,
            footer,
            ticks,
        }
    }
    fn update(&mut self, state: State) {
        let mut p = *self.tree.params(&self.sponsor).unwrap();
        p.disabled = !state.sponsor;
        self.tree.update_node_params(&self.sponsor, p).unwrap();
        let mut p = *self.tree.params(&self.summary).unwrap();
        p.min_size.x = Some(Size::Pixels(state.summary_minimum));
        self.tree.update_node_params(&self.summary, p).unwrap();
    }
    fn check(&self, state: State) {
        // Independent host arithmetic for this particular article design.
        let width = state.width;
        let sponsor_y = if width < 160. { 60. } else { 0. };
        let sponsor_x = width - 64.;
        let mut y = 24.;
        let (mut left, mut right);
        loop {
            left = if y < 60. { 96. } else { 0. };
            right = if state.sponsor && y < sponsor_y + 40. && y + 36. > sponsor_y {
                sponsor_x
            } else {
                width
            };
            if right - left >= state.summary_minimum {
                break;
            }
            y = [60., sponsor_y + 40.]
                .into_iter()
                .filter(|&end| end > y)
                .reduce(f32::min)
                .unwrap();
        }
        let bottom = (y + 36.)
            .max(60.)
            .max(if state.sponsor { sponsor_y + 40. } else { 0. });
        let rect = |x, y, w, h| Xy::new([x, x + w], [y, y + h]);
        assert_eq!(
            self.tree.layout(&self.column).unwrap(),
            rect(0., 0., width, bottom + 16.)
        );
        assert_eq!(
            self.tree.layout(&self.portrait).unwrap(),
            rect(0., 0., 96., 60.)
        );
        if state.sponsor {
            assert_eq!(
                self.tree.layout(&self.sponsor).unwrap(),
                rect(sponsor_x, sponsor_y, 64., 40.)
            );
        } else {
            assert!(self.tree.layout(&self.sponsor).is_err());
        }
        assert_eq!(
            self.tree.layout(&self.title).unwrap(),
            rect(0., 0., width, 24.)
        );
        assert_eq!(
            self.tree.layout(&self.summary).unwrap(),
            rect(left, y, right - left, 36.)
        );
        assert_eq!(
            self.tree.layout(&self.footer).unwrap(),
            rect(0., bottom, width, 16.)
        );
        for (i, id) in self.ticks.iter().enumerate() {
            let (x, top, w) = match i / 8 {
                0 => (0., 0., 96.),
                1 if state.sponsor => (sponsor_x, sponsor_y, 64.),
                1 => {
                    assert!(self.tree.layout(id).is_err());
                    continue;
                }
                _ => (left, y, right - left),
            };
            assert_eq!(
                self.tree.layout(id).unwrap(),
                rect(x, top + (i % 8) as f32 * 3., w, 3.)
            );
        }
        assert!(self.tree.rule_issues().is_empty());
    }
}
fn replay() {
    let mut retained = Digest::new();
    #[cfg(feature = "batch-pilot")]
    let mut batch = Digest::new();
    for (width, sponsor, min) in [
        (320., true, 0.),
        (224., true, 0.),
        (224., false, 0.),
        (224., true, 100.),
        (140., true, 100.),
        (320., true, 0.),
    ] {
        let state = State {
            width,
            sponsor,
            summary_minimum: min,
        };
        let window = Xy::new(width, 300.);
        retained.update(state);
        retained.tree.solve_layout(window);
        retained.check(state);
        let mut fresh = Digest::new();
        fresh.update(state);
        fresh.tree.solve_layout(window);
        fresh.check(state);
        #[cfg(feature = "batch-pilot")]
        {
            batch.update(state);
            batch.tree.solve_layout_batch(window).unwrap();
            batch.check(state);
        }
        println!(
            "column={width} sponsor={sponsor} summary minimum={min} summary={:?}",
            retained.tree.layout(&retained.summary).unwrap()
        );
    }
}
fn main() {
    replay()
}
#[test]
fn digest_layout_matches_the_declared_exclusions() {
    replay()
}

#[test]
fn source_positioned_article_action_scrolls_with_its_row() {
    use keru_layout::layout_rules::{BoxReference, BoxStyle, Overflow, Placement, ScrollStyle};

    let mut tree = LayoutTree::<()>::new();
    let article = tree
        .add_node(
            &tree.root(),
            LayoutParams {
                children_layout: ChildrenLayout::Block,
                size: Xy::new(Size::Pixels(100.), Size::Pixels(50.)),
                position: Xy::new_symm(Pos::Start),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &article,
        NodeRules {
            scroll: ScrollStyle {
                overflow: Xy::new(Overflow::Visible, Overflow::Scroll),
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let mut add = |height| {
        tree.add_node(
            &article,
            LayoutParams {
                size: Xy::new(Size::Pixels(90.), Size::Pixels(height)),
                ..Default::default()
            },
        )
        .unwrap()
    };
    let _heading = add(30.);
    let action = add(12.);
    let _body = add(90.);
    tree.set_rules(
        &action,
        NodeRules {
            block_flow: BlockStyle {
                static_block_position: true,
                ..Default::default()
            },
            box_model: BoxStyle {
                absolute_static: Xy::new_symm(Some(0.)),
                ..Default::default()
            },
            placement: Placement::Absolute {
                containing: BoxReference::Parent,
                insets: Xy::new_symm([None; 2]),
            },
            ..Default::default()
        },
    )
    .unwrap();
    let window = Xy::new(100., 100.);
    tree.solve_layout(window);
    assert_eq!(tree.view_geometry(&action).unwrap().rect.y, [30., 42.]);
    tree.set_scroll_offset(&article, Xy::new(0., 20.)).unwrap();
    tree.solve_layout(window);
    assert_eq!(tree.view_geometry(&action).unwrap().rect.y, [10., 22.]);
}

#[test]
fn a_flex_column_keeps_the_height_of_wrapped_floating_article_text() {
    use keru_layout::flex::FlexLayout;
    use keru_layout::{Axis, Margin, TextContent};

    let mut tree = LayoutTree::<()>::new();
    let panel = tree
        .add_node(
            &tree.root(),
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                position: Xy::new_symm(Pos::Start),
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &panel,
        NodeRules {
            flex: Some(FlexLayout {
                axis: Axis::Y,
                ..Default::default()
            }),
            ..Default::default()
        },
    )
    .unwrap();
    let section = tree
        .add_node(
            &panel,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                children_layout: ChildrenLayout::Block,
                isolate_block_margins: true,
                ..Default::default()
            },
        )
        .unwrap();
    let floated = tree
        .add_node(
            &section,
            LayoutParams {
                size: Xy::new(Size::Auto, Size::FitContent),
                margin: Xy::new([Margin::px(20.).unwrap(), Margin::ZERO], [Margin::ZERO; 2]),
                children_layout: ChildrenLayout::Block,
                ..Default::default()
            },
        )
        .unwrap();
    tree.set_rules(
        &floated,
        NodeRules {
            block_flow: BlockStyle {
                float: Float::Left,
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let text = tree
        .add_node_with_context(
            &floated,
            LayoutParams {
                text: TextContent::Wrapping,
                size: Xy::new(Size::Auto, Size::FitContent),
                ..Default::default()
            },
            (),
        )
        .unwrap();
    // Ten 20px words, 10px high. Narrowing from 80px to 60px of
    // usable width changes the caption from three lines to four.
    for (width, height) in [(100., 30.), (80., 40.), (100., 30.)] {
        tree.solve_layout_with_measure(Xy::new(width, 300.), |_, content, available| {
            if content.is_none() {
                return Xy::new_symm(0.);
            }
            let words_per_line = (available.unwrap_or(200.) / 20.).floor().clamp(1., 10.);
            Xy::new(words_per_line * 20., (10. / words_per_line).ceil() * 10.)
        });
        for id in [&panel, &section, &floated, &text] {
            assert_eq!(tree.layout(id).unwrap().y, [0., height]);
        }
        assert!(tree.rule_issues().is_empty());
    }
}
