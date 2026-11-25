use keru_layout::{
    Arrange, Axis, ChildrenLayout, Direction, LayoutParams, Logical, LogicalAxis, LogicalError,
    LogicalStyle, Margin, Size, WritingContext, WritingMode, Xy,
};

#[test]
fn logical_edges_map_to_physical_edges_in_all_six_writing_contexts() {
    use Direction::*;
    use WritingMode::*;
    let cases = [
        (HorizontalTb, Ltr, Axis::X, [1, 2], [3, 4]),
        (HorizontalTb, Rtl, Axis::X, [2, 1], [3, 4]),
        (VerticalRl, Ltr, Axis::Y, [4, 3], [1, 2]),
        (VerticalRl, Rtl, Axis::Y, [4, 3], [2, 1]),
        (VerticalLr, Ltr, Axis::Y, [3, 4], [1, 2]),
        (VerticalLr, Rtl, Axis::Y, [3, 4], [2, 1]),
    ];
    for (writing_mode, direction, inline, x, y) in cases {
        let context = WritingContext {
            direction,
            writing_mode,
        };
        assert_eq!(context.axis(LogicalAxis::Inline), inline);
        assert_eq!(context.axis(LogicalAxis::Block), inline.other());
        assert_eq!(
            context.physical_edges(Logical::new([1, 2], [3, 4])),
            Xy::new(x, y)
        );
    }
}

#[test]
fn mixed_edges_sizes_bounds_and_reversals_lower_without_rewriting_the_source() {
    let context = WritingContext {
        writing_mode: WritingMode::VerticalRl,
        direction: Direction::Rtl,
    };
    let authored = LayoutParams {
        size: Xy::new(Size::Pixels(45.), Size::Auto),
        min_size: Xy::new(Some(Size::Pixels(12.)), None),
        children_layout: ChildrenLayout::Stack {
            axis: Axis::X,
            arrange: Arrange::End,
            spacing: 9.,
        },
        children_origin_flipped: Xy::new(true, false),
        padding: Xy::new([2., 4.], [7., 11.]),
        ..LayoutParams::DEFAULT
    };
    let style = LogicalStyle {
        main_axis: Some(LogicalAxis::Inline),
        reverse: Logical::new(true, false),
        size: Logical::new(Some(Size::Pixels(80.)), None),
        min_size: Logical::new(Some(Size::Pixels(20.)), None),
        max_size: Logical::new(None, Some(Size::Pixels(50.))),
        padding: Logical::new([Some(13.), None], [None, Some(17.)]),
        margin: Logical::new([None, Some(Margin::AUTO)], [Some(Margin::ZERO), None]),
        ..Default::default()
    };
    let result = style.resolve(context, authored).unwrap();
    assert_eq!(result.size, Xy::new(Size::Pixels(45.), Size::Pixels(80.)));
    assert_eq!(
        result.min_size,
        Xy::new(Some(Size::Pixels(12.)), Some(Size::Pixels(20.)))
    );
    assert_eq!(result.max_size, Xy::new(Some(Size::Pixels(50.)), None));
    assert_eq!(result.padding, Xy::new([17., 4.], [7., 13.]));
    assert_eq!(result.margin.y, [Margin::AUTO, Margin::ZERO]);
    assert_eq!(result.children_origin_flipped, Xy::new(false, false));
    assert_eq!(
        result.children_layout,
        ChildrenLayout::Stack {
            axis: Axis::Y,
            arrange: Arrange::End,
            spacing: 9.
        }
    );
    assert_eq!(authored.padding, Xy::new([2., 4.], [7., 11.]));
}

#[test]
fn direction_and_line_orientation_inherit_independently() {
    let parent = WritingContext {
        direction: Direction::Rtl,
        writing_mode: WritingMode::VerticalRl,
    };
    let one = LogicalStyle {
        direction: Some(Direction::Ltr),
        ..Default::default()
    }
    .context(parent);
    assert_eq!(
        one,
        WritingContext {
            direction: Direction::Ltr,
            writing_mode: WritingMode::VerticalRl
        }
    );
    let two = LogicalStyle {
        writing_mode: Some(WritingMode::HorizontalTb),
        ..Default::default()
    }
    .context(parent);
    assert_eq!(
        two,
        WritingContext {
            direction: Direction::Rtl,
            writing_mode: WritingMode::HorizontalTb
        }
    );
    let block = LayoutParams {
        children_layout: ChildrenLayout::Block,
        ..LayoutParams::DEFAULT
    };
    assert_eq!(
        LogicalStyle::default().resolve(parent, block),
        Err(LogicalError::VerticalBlock)
    );
    assert!(LogicalStyle::default().resolve(two, block).is_ok());
}
