//! Localized command strip. An action stays at inline-end as its strip rotates.
//! https://rtlstyling.com/posts/rtl-styling/
#![cfg(feature = "incremental")]

use keru_layout::flex::{FlexAlign, FlexLayout};
use keru_layout::layout_rules::NodeRules;
use keru_layout::{
    Anchor, ChildId, Direction, LayoutParams, LayoutTree, Logical, LogicalAxis, LogicalStyle,
    Margin, Pos, Size, WritingMode, Xy, XyRect,
};

#[derive(Clone, Copy)]
enum Push {
    Inline,
    PhysicalLeft,
}

struct Strip {
    tree: LayoutTree<()>,
    strip: ChildId,
    leading: ChildId,
    action: ChildId,
}

fn params() -> LayoutParams {
    LayoutParams {
        anchor: Xy::new_symm(Anchor::Start),
        position: Xy::new_symm(Pos::Start),
        ..Default::default()
    }
}

impl Strip {
    fn new(push: Push) -> Self {
        let mut tree = LayoutTree::new();
        let strip = tree.add_node(&tree.root(), params()).unwrap();
        let mut control = |width, margin_left, margin_inline_start| {
            let mut style = params();
            style.margin.x[0] = margin_left;
            let id = tree.add_node(&strip, style).unwrap();
            tree.set_rules(
                &id,
                NodeRules {
                    logical: LogicalStyle {
                        size: Logical::new(Some(Size::Pixels(width)), Some(Size::Pixels(20.))),
                        margin: Logical::new([margin_inline_start, None], [None; 2]),
                        ..Default::default()
                    },
                    ..Default::default()
                },
            )
            .unwrap();
            id
        };
        let leading = control(30., Margin::ZERO, None);
        let action = match push {
            Push::Inline => control(22., Margin::ZERO, Some(Margin::AUTO)),
            Push::PhysicalLeft => control(22., Margin::AUTO, None),
        };
        Self {
            tree,
            strip,
            leading,
            action,
        }
    }

    fn layout(
        &mut self,
        mode: WritingMode,
        dir: Direction,
        inline: f32,
        reverse: bool,
    ) -> [XyRect; 2] {
        self.tree
            .set_rules(
                &self.strip,
                NodeRules {
                    logical: LogicalStyle {
                        writing_mode: Some(mode),
                        direction: Some(dir),
                        main_axis: Some(LogicalAxis::Inline),
                        size: Logical::new(Some(Size::Pixels(inline)), Some(Size::Pixels(40.))),
                        padding: Logical::new([Some(8.), Some(12.)], [Some(3.), Some(7.)]),
                        ..Default::default()
                    },
                    flex: Some(FlexLayout {
                        gap: 6.,
                        align_items: FlexAlign::Start,
                        reverse,
                        ..Default::default()
                    }),
                    ..Default::default()
                },
            )
            .unwrap();
        self.tree.solve_layout(Xy::new(200., 200.));
        assert!(self.tree.warnings().is_empty());
        assert!(self.tree.rule_issues().is_empty());
        [&self.leading, &self.action].map(|id| self.tree.layout(id).unwrap())
    }
}

#[test]
fn trailing_action_follows_its_logical_margin_across_live_locale_and_size_edits() {
    use Direction::{Ltr, Rtl};
    use WritingMode::{HorizontalTb as H, VerticalLr as Vl, VerticalRl as Vr};
    let mut live = Strip::new(Push::Inline);
    for (mode, dir, inline, leading, action) in [
        (
            H,
            Ltr,
            144.,
            Xy::new([8., 38.], [3., 23.]),
            Xy::new([110., 132.], [3., 23.]),
        ),
        (
            H,
            Rtl,
            144.,
            Xy::new([106., 136.], [3., 23.]),
            Xy::new([12., 34.], [3., 23.]),
        ),
        (
            Vr,
            Ltr,
            144.,
            Xy::new([17., 37.], [8., 38.]),
            Xy::new([17., 37.], [110., 132.]),
        ),
        (
            Vr,
            Rtl,
            144.,
            Xy::new([17., 37.], [106., 136.]),
            Xy::new([17., 37.], [12., 34.]),
        ),
        (
            Vl,
            Rtl,
            90.,
            Xy::new([3., 23.], [52., 82.]),
            Xy::new([3., 23.], [12., 34.]),
        ),
        (
            Vl,
            Ltr,
            90.,
            Xy::new([3., 23.], [8., 38.]),
            Xy::new([3., 23.], [56., 78.]),
        ),
        (
            H,
            Ltr,
            144.,
            Xy::new([8., 38.], [3., 23.]),
            Xy::new([110., 132.], [3., 23.]),
        ),
    ] {
        let expected = [leading, action];
        assert_eq!(
            live.layout(mode, dir, inline, false),
            expected,
            "{mode:?} {dir:?} live"
        );
        assert_eq!(
            Strip::new(Push::Inline).layout(mode, dir, inline, false),
            expected,
            "{mode:?} {dir:?} fresh"
        );
    }
}

#[test]
fn physical_auto_margin_and_manual_reversal_change_the_rtl_layout() {
    use Direction::{Ltr, Rtl};
    use WritingMode::HorizontalTb as H;
    let mut physical = Strip::new(Push::PhysicalLeft);
    assert_eq!(physical.layout(H, Ltr, 144., false)[1].x, [110., 132.]);
    assert_eq!(physical.layout(H, Rtl, 144., false)[1].x, [78., 100.]);
    let mut reversed = Strip::new(Push::Inline);
    let [leading, action] = reversed.layout(H, Rtl, 144., true);
    assert_eq!(leading.x, [12., 42.]);
    assert_eq!(action.x, [48., 70.]);
}

#[test]
fn horizontal_editor_inside_a_vertical_strip_uses_its_own_inline_start() {
    let mut client = Strip::new(Push::Inline);
    // A localized control inherits the strip until its embedded number editor chooses LTR.
    let inherited = client.tree.rules(&client.action).unwrap().unwrap().clone();
    let run =
        |client: &mut Strip| client.layout(WritingMode::VerticalRl, Direction::Rtl, 144., false)[1];
    assert_eq!(run(&mut client), Xy::new([17., 37.], [12., 34.]));
    let mut editor = inherited.clone();
    editor.logical.direction = Some(Direction::Ltr);
    editor.logical.writing_mode = Some(WritingMode::HorizontalTb);
    client.tree.set_rules(&client.action, editor).unwrap();
    // Its 22px inline dimension is horizontal. Its automatic left margin is
    // on the strip's cross axis, so it follows the leading control along the main axis.
    assert_eq!(run(&mut client), Xy::new([15., 37.], [80., 100.]));
    // Keep the outer slot localized when an embedded editor should still sit
    // at the strip's trailing edge. The editor only owns its internal direction.
    let mut slot = inherited;
    slot.logical.size = Logical::new(Some(Size::Pixels(20.)), Some(Size::Pixels(22.)));
    client.tree.set_rules(&client.action, slot).unwrap();
    let editor = client.tree.add_node(&client.action, params()).unwrap();
    client
        .tree
        .set_rules(
            &editor,
            NodeRules {
                logical: LogicalStyle {
                    direction: Some(Direction::Ltr),
                    writing_mode: Some(WritingMode::HorizontalTb),
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap();
    let reserved = Xy::new([15., 37.], [12., 32.]);
    assert_eq!(run(&mut client), reserved);
    assert_eq!(client.tree.layout(&editor).unwrap(), reserved);
}
