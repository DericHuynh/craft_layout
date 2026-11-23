// This harness is compiled as a child of the production incremental module by
// same_input.py. Bits is the field-by-field oracle generated from rustdoc.
use super::*;
use crate::same_input_proof::Bits;

#[derive(PartialEq)]
enum ChildRules {
    Free,
    Stack(Axis),
    Wrap(Axis),
    Block,
    CountGrid(Axis, bool, u32),
    WidthGrid(Axis, bool),
}

fn child_rules(layout: ChildrenLayout) -> ChildRules {
    match layout {
        ChildrenLayout::Free => ChildRules::Free,
        ChildrenLayout::Block => ChildRules::Block,
        ChildrenLayout::Stack { axis, .. } => ChildRules::Stack(axis),
        ChildrenLayout::Wrap { axis, .. } => ChildRules::Wrap(axis),
        ChildrenLayout::Grid {
            main_axis,
            backfill,
            columns,
            ..
        } => match columns {
            MainAxisCellSize::Count(n) => ChildRules::CountGrid(main_axis, backfill, n),
            MainAxisCellSize::Width(_) => ChildRules::WidthGrid(main_axis, backfill),
        },
    }
}

fn size_rules(p: &LayoutParams, axis: Axis) -> [Option<std::mem::Discriminant<Size>>; 3] {
    [Some(p.size[axis]), p.min_size[axis], p.max_size[axis]]
        .map(|s| s.map(|value| std::mem::discriminant(&value)))
}

fn same_rules(a: &LayoutParams, b: &LayoutParams) -> bool {
    a.disabled == b.disabled
        && a.free_placement == b.free_placement
        && a.grid_span == b.grid_span
        && a.text == b.text
        && a.content_measure == b.content_measure
        && a.image.is_some() == b.image.is_some()
        && child_rules(a.children_layout) == child_rules(b.children_layout)
        && size_rules(a, X) == size_rules(b, X)
        && size_rules(a, Y) == size_rules(b, Y)
}

// On a fixed rule, these are the direct layout inputs to each axis's inner
// size. A width or spacing edit to a grid can change the opposite track count.
fn track_inputs(layout: ChildrenLayout, axis: Axis) -> [u32; 3] {
    match layout {
        ChildrenLayout::Free | ChildrenLayout::Block => [0; 3],
        ChildrenLayout::Stack {
            axis: main,
            spacing,
            ..
        } => [if axis == main { spacing.to_bits() } else { 0 }, 0, 0],
        ChildrenLayout::Wrap {
            axis: main,
            spacing,
            line_spacing,
            ..
        } => [
            if axis == main { spacing } else { line_spacing }.to_bits(),
            0,
            0,
        ],
        ChildrenLayout::Grid {
            columns,
            spacing_x,
            spacing_y,
            ..
        } => [
            match columns {
                MainAxisCellSize::Count(n) => n,
                MainAxisCellSize::Width(w) => w.to_bits(),
            },
            spacing_x.to_bits(),
            spacing_y.to_bits(),
        ],
    }
}

#[kani::proof]
#[kani::unwind(16)]
fn reports_all_numeric_inputs() {
    let old: LayoutParams = kani::any();
    let new: LayoutParams = kani::any();
    let tracking: bool = kani::any();
    let rules_unchanged = same_rules(&old, &new);
    let report = NodeChange::between(&old, &new, tracking);
    assert_eq!(report.is_some(), rules_unchanged);
    let Some(change) = report else { return };
    if !tracking {
        assert_eq!(change, NodeChange::default());
        return;
    }

    let mut changed_maximum = false;
    let mut changed_padding = false;
    for axis in [X, Y] {
        let declarations = [
            (Kind::Regular, old.size[axis].matches_bits(&new.size[axis])),
            (
                Kind::Min,
                old.min_size[axis].matches_bits(&new.min_size[axis]),
            ),
            (
                Kind::Max,
                old.max_size[axis].matches_bits(&new.max_size[axis]),
            ),
        ];
        for (kind, same) in declarations {
            let queued =
                registration_rules::declaration_changed(change.declared, slot_index(axis, kind));
            assert_eq!(queued, !same);
        }
        let padding = !old.padding[axis].matches_bits(&new.padding[axis]);
        changed_padding |= padding;
        changed_maximum |= !old.max_size[axis].matches_bits(&new.max_size[axis]);
        assert_eq!(
            change.inner[axis],
            padding
                || track_inputs(old.children_layout, axis)
                    != track_inputs(new.children_layout, axis)
        );
        assert_eq!(
            change.margin[axis],
            !new.free_placement && !old.margin[axis].matches_bits(&new.margin[axis])
        );
    }
    assert_eq!(
        change.fill_weight,
        !new.free_placement && !old.fill_weight.matches_bits(&new.fill_weight)
    );
    let host_constraints_changed =
        new.content_measure != ContentMeasure::None && (changed_padding || changed_maximum);
    assert_eq!(
        change.content,
        !old.image.matches_bits(&new.image) || host_constraints_changed
    );
}

#[kani::proof]
#[kani::unwind(16)]
fn structural_inputs_request_rebuild() {
    let old: LayoutParams = kani::any();
    let new: LayoutParams = kani::any();
    if same_rules(&old, &new) {
        return;
    }
    let mut layout = LayoutData::new();
    layout.pending_full_solve = match kani::any::<u8>() {
        0 => Some(IncrementalRelayoutOutcome::FallbackFlow),
        1 => Some(IncrementalRelayoutOutcome::FallbackTooMuchWork),
        _ => None,
    };
    let mut edited = NodeLayoutData::new();
    let mut parent = NodeLayoutData::new();
    // These are the registration calls made by update_node_params after it
    // resolves inherited visibility, separate from the owned tree's arena.
    let structural = layout.record_node_change(0, &old, &new, &mut edited);
    assert!(structural);
    assert_eq!(edited.structural_change, StructuralChange::Subtree);
    if kani::any::<bool>() {
        layout.record_children_change(&mut edited);
        assert_eq!(edited.structural_change, StructuralChange::Subtree);
    } else {
        layout.record_children_change(&mut parent);
        assert_eq!(parent.structural_change, StructuralChange::Children);
    }
    assert!(layout.children_changed);
    assert!(layout.pending_full_solve.is_none());
}
