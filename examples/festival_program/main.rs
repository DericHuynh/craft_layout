//! Replay the owners' predicted breaks and ticket-action positions using public flex declarations.
use keru_layout::flex::{FlexAlign, FlexLayout, FlexMetrics, FlexWrap};
use keru_layout::{Axis, Margin, Xy};

fn stages(widths: &[f32]) -> Vec<FlexMetrics> {
    widths
        .iter()
        .map(|&width| FlexMetrics {
            preferred: Xy::new(width, 18.),
            ..Default::default()
        })
        .collect()
}

fn check_schedule(width: f32, cards: &[f32], minimum_lines: u16, manual_rows: &[usize]) {
    let layout = FlexLayout {
        axis: Axis::X,
        wrap: FlexWrap::Balance {
            lines: minimum_lines,
            reverse: false,
        },
        align_content: keru_layout::flex::LineAlign::Start,
        line_gap: 6.,
        ..Default::default()
    };
    let rects = layout.resolve(Xy::new(width, 150.), &stages(cards));
    assert_eq!(manual_rows.len(), rects.len());
    let mut left = 0.;
    for (i, r) in rects.iter().enumerate() {
        if i == 0 || manual_rows[i] != manual_rows[i - 1] {
            left = 0.;
        }
        let top = manual_rows[i] as f32 * 24.;
        assert_eq!(*r, Xy::new([left, left + cards[i]], [top, top + 18.]));
        left += cards[i];
    }
}

fn occupancy() {
    use keru_layout::flex::FlexItem;
    use keru_layout::layout_rules::NodeRules;
    use keru_layout::{Anchor, LayoutParams, LayoutTree, Pos, Size};

    let mut tree = LayoutTree::<()>::new();
    let window = Xy::new(500., 400.);
    let panel = tree.add_node(&tree.root(), LayoutParams::DEFAULT).unwrap();
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
    let booking = tree
        .add_node(
            &panel,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::FitContent),
                position: Xy::new_symm(Pos::Start),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    tree.set_rules(
        &booking,
        NodeRules {
            flex_item: FlexItem {
                grow: 1.,
                ..Default::default()
            },
            ..Default::default()
        },
    )
    .unwrap();
    let bar = tree
        .add_node(
            &booking,
            LayoutParams {
                size: Xy::new(Size::Fill, Size::Frac(0.75)),
                position: Xy::new_symm(Pos::Start),
                anchor: Xy::new_symm(Anchor::Start),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
    for (minimum, occupied) in [(192., 144.), (216., 162.)] {
        tree.update_node_params(
            &panel,
            LayoutParams {
                size: Xy::new(Size::Pixels(120.), Size::FitContent),
                min_size: Xy::new(None, Some(Size::Pixels(minimum))),
                position: Xy::new_symm(Pos::Start),
                anchor: Xy::new_symm(Anchor::Start),
                ..LayoutParams::DEFAULT
            },
        )
        .unwrap();
        tree.solve_layout(window);
        assert_eq!(tree.layout(&bar).unwrap().y, [0., occupied]);
        assert_eq!(tree.layout(&booking).unwrap().y, [0., minimum]);
        #[cfg(feature = "batch-pilot")]
        tree.solve_layout_batch(window).unwrap();
        assert_eq!(tree.layout(&bar).unwrap().y, [0., occupied]);
    }
}

fn rtl_directory() {
    let mut entries = stages(&[50., 30., 40., 50.]);
    for entry in &mut entries {
        entry.preferred.y = 50.;
    }
    for wrapping in [FlexWrap::NoWrap, FlexWrap::Wrap] {
        let layout = FlexLayout {
            axis: Axis::Y,
            cross_reverse: true,
            align_items: FlexAlign::FirstBaseline,
            wrap: wrapping,
            ..Default::default()
        };
        let rects = layout.resolve(Xy::new(100., 100.), &entries);
        assert_eq!(rects[1].x, [70., 100.]);
        if wrapping == FlexWrap::Wrap {
            assert_eq!(rects[2].x, [10., 50.]);
        }
    }
}

fn main() {
    for width in [130., 110.] {
        check_schedule(
            width,
            &[52., 26., 26., 26., 26., 26.],
            1,
            &[0, 0, 0, 1, 1, 1],
        );
    }
    check_schedule(130., &[26.; 5], 2, &[0, 0, 0, 1, 1]);
    check_schedule(130., &[26., 26., 26., 0., 26., 26.], 2, &[0, 0, 0, 0, 1, 1]);
    check_schedule(100., &[26.; 5], 4, &[0, 0, 1, 2, 3]);
    let mut actions = stages(&[50., 20.]);
    actions[0].first_baseline = Some(18.);
    actions[1].first_baseline = Some(10.);
    actions[1].margin.x[0] = Margin::AUTO;
    let rects = FlexLayout {
        align_items: FlexAlign::FirstBaseline,
        ..Default::default()
    }
    .resolve(Xy::new(120., 32.), &actions);
    assert_eq!(rects[1], Xy::new([100., 120.], [8., 26.]));
    occupancy();
    rtl_directory();
    println!("The six schedule states and both occupancy states matched their predictions.");
}

#[test]
fn independent_review_one_pixel_below_two_row_capacity() {
    let widths = [52., 26., 26., 26., 26., 26.];
    check_schedule(104., &widths, 1, &[0, 0, 0, 1, 1, 1]);
    check_schedule(103., &widths, 1, &[0, 0, 1, 1, 2, 2]);
}
