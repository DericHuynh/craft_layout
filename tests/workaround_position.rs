#![cfg(feature = "incremental")]

use keru_layout::layout_rules::{BoxStyle, NodeRules};
use keru_layout::{Anchor, LayoutParams, LayoutTree, Pos, Size, Xy};

fn box_at_start(width: Size, height: Size) -> LayoutParams {
    LayoutParams {
        size: Xy::new(width, height),
        position: Xy::new_symm(Pos::Start),
        anchor: Xy::new_symm(Anchor::Start),
        ..LayoutParams::DEFAULT
    }
}

// https://www.w3.org/Style/Examples/007/center.en.html
#[test]
fn centering_a_content_sized_dialog_needs_no_offset_after_an_edit() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let centered = LayoutParams {
        size: Xy::new_symm(Size::FitContent),
        position: Xy::new_symm(Pos::Center),
        ..LayoutParams::DEFAULT
    };
    let dialog = tree.add_node(&root, centered).unwrap();
    let guessed = tree
        .add_node(
            &root,
            LayoutParams {
                position: Xy::new(
                    Pos::Offset {
                        fraction: 0.5,
                        pixels: -40.,
                    },
                    Pos::Offset {
                        fraction: 0.5,
                        pixels: -16.,
                    },
                ),
                anchor: Xy::new_symm(Anchor::Start),
                ..centered
            },
        )
        .unwrap();
    let contents = [&dialog, &guessed].map(|parent| {
        tree.add_node(parent, box_at_start(Size::Pixels(80.), Size::Pixels(32.)))
            .unwrap()
    });
    for (viewport, content, expected, guess) in [
        (
            (320., 180.),
            (80., 32.),
            ([120., 200.], [74., 106.]),
            ([120., 200.], [74., 106.]),
        ),
        (
            (240., 144.),
            (120., 48.),
            ([60., 180.], [48., 96.]),
            ([80., 200.], [56., 104.]),
        ),
        (
            (320., 180.),
            (80., 32.),
            ([120., 200.], [74., 106.]),
            ([120., 200.], [74., 106.]),
        ),
    ] {
        for child in &contents {
            tree.update_node_params(
                child,
                box_at_start(Size::Pixels(content.0), Size::Pixels(content.1)),
            )
            .unwrap();
        }
        tree.solve_layout(Xy::new(viewport.0, viewport.1));
        assert_eq!(
            tree.layout(&dialog).unwrap(),
            Xy::new(expected.0, expected.1)
        );
        assert_eq!(tree.layout(&guessed).unwrap(), Xy::new(guess.0, guess.1));
        assert!(tree.warnings().is_empty());
    }
}

// https://alistapart.com/article/creating-intrinsic-ratios-for-video/
#[test]
fn a_media_ratio_uses_its_own_width_in_a_half_width_card() {
    let mut tree = LayoutTree::<()>::new();
    let root = tree.root();
    let video = tree
        .add_node(
            &root,
            box_at_start(Size::Frac(0.5), Size::AspectRatio(16. / 9.)),
        )
        .unwrap();
    let card = tree
        .add_node(&root, box_at_start(Size::Frac(0.5), Size::Fill))
        .unwrap();
    // The percentage padding recipe works when its containing block is the intended video width.
    let wrapped = tree
        .add_node(&card, box_at_start(Size::Fill, Size::Pixels(0.)))
        .unwrap();
    let unwrapped = tree
        .add_node(&root, box_at_start(Size::Frac(0.5), Size::Pixels(0.)))
        .unwrap();
    for id in [&wrapped, &unwrapped] {
        tree.set_rules(
            id,
            NodeRules {
                box_model: BoxStyle {
                    padding_fraction: Xy::new([0., 0.], [0., 9. / 16.]),
                    content_box: true,
                    ..Default::default()
                },
                ..Default::default()
            },
        )
        .unwrap();
    }
    for (width, expected_width, expected_height) in
        [(320., 160., 90.), (480., 240., 135.), (320., 160., 90.)]
    {
        tree.solve_layout(Xy::new(width, 400.));
        let direct = tree.layout(&video).unwrap();
        assert_eq!(direct, Xy::new([0., expected_width], [0., expected_height]));
        assert_eq!(tree.layout(&wrapped).unwrap(), direct);
        assert_eq!(
            tree.layout(&unwrapped).unwrap(),
            Xy::new([0., expected_width], [0., 2. * expected_height])
        );
        assert!(tree.rule_issues().is_empty());
    }
}
