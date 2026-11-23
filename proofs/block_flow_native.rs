//! Model-check the native float operations and the verified per-item schedule.
#[path = "../src/block_flow.rs"]
mod kernel;

use kernel::{BlockFlow, BlockItem, BlockMargins, CollapsedMargin, Scalar};

fn ordered_bits(value: f32) -> u32 {
    let bits = value.to_bits();
    if bits & 0x8000_0000 == 0 {
        bits ^ 0x8000_0000
    } else {
        !bits
    }
}

fn legal_edge(value: f32) -> bool {
    value.is_finite() && value.to_bits() != 0x8000_0000
}

fn same_value(actual: f32, reference: f32) -> bool {
    actual.to_bits() == reference.to_bits() || (actual.is_nan() && reference.is_nan())
}

#[kani::proof]
fn native_margin_extrema_follow_bit_rank() {
    let (left, right): (f32, f32) = kani::any();
    kani::assume(legal_edge(left) && legal_edge(right));
    let greater = if ordered_bits(left) > ordered_bits(right) {
        left
    } else {
        right
    };
    let lesser = if ordered_bits(left) < ordered_bits(right) {
        left
    } else {
        right
    };
    assert_eq!(Scalar::maximum(left, right).to_bits(), greater.to_bits());
    assert_eq!(Scalar::minimum(left, right).to_bits(), lesser.to_bits());

    let edge = CollapsedMargin::new(left);
    assert_eq!(
        edge.positive.to_bits(),
        if left > 0.0 { left.to_bits() } else { 0 }
    );
    assert_eq!(
        edge.negative.to_bits(),
        if left < 0.0 { left.to_bits() } else { 0 }
    );
}

fn arbitrary_group() -> CollapsedMargin {
    let (positive, negative): (f32, f32) = kani::any();
    kani::assume(legal_edge(positive) && positive >= 0.0);
    kani::assume(legal_edge(negative) && negative <= 0.0);
    CollapsedMargin { positive, negative }
}

// The native max/min match the independent bit order under the precondition
// proved by native_margin_extrema_follow_bit_rank.
fn join(left: CollapsedMargin, right: CollapsedMargin) -> CollapsedMargin {
    CollapsedMargin {
        positive: left.positive.max(right.positive),
        negative: left.negative.min(right.negative),
    }
}

fn same_group(left: CollapsedMargin, right: CollapsedMargin) -> bool {
    left.positive.to_bits() == right.positive.to_bits()
        && left.negative.to_bits() == right.negative.to_bits()
}

#[kani::proof]
fn native_push_matches_group_transition() {
    let (top, bottom): (bool, bool) = kani::any();
    let blank = CollapsedMargin::default();
    let mut flow = BlockFlow::from_edges(top, bottom);
    assert!(
        same_value(flow.end, 0.0) && flow.outgoing.all_through && same_group(flow.pending, blank)
    );
    assert!(same_group(flow.outgoing.before, blank) && same_group(flow.outgoing.after, blank));
    assert!(flow.collapse_top == top && flow.collapse_bottom == bottom);

    flow.end = kani::any();
    kani::assume(flow.end.is_finite());
    flow.pending = arbitrary_group();
    flow.outgoing.before = arbitrary_group();
    flow.outgoing.after = arbitrary_group();
    flow.outgoing.all_through = kani::any();
    let item = BlockItem {
        before: arbitrary_group(),
        after: arbitrary_group(),
        size: kani::any(),
        through: kani::any(),
    };
    kani::assume(item.size.is_finite());
    let group = join(flow.pending, item.before);
    let exits_top = top && flow.outgoing.all_through;
    let unchanged_end = item.through.then_some(flow.end);
    let expected_pending = if item.through {
        join(group, item.after)
    } else {
        item.after
    };
    let expected_before = if !item.through && exits_top {
        group
    } else {
        flow.outgoing.before
    };
    let expected_after = flow.outgoing.after;
    let all_through = item.through && flow.outgoing.all_through;
    flow.push(item);
    if let Some(end) = unchanged_end {
        assert_eq!(flow.end.to_bits(), end.to_bits());
    }
    assert!(same_group(flow.pending, expected_pending));
    assert!(
        same_group(flow.outgoing.before, expected_before)
            && same_group(flow.outgoing.after, expected_after)
    );
    assert_eq!(flow.outgoing.all_through, all_through);
    assert!(flow.collapse_top == top && flow.collapse_bottom == bottom);
}

#[kani::proof]
fn native_add_uses_binary32() {
    let (left, right): (f32, f32) = kani::any();
    kani::assume(!left.is_nan() && !right.is_nan());
    kani::assume(
        !(left.is_infinite()
            && right.is_infinite()
            && left.is_sign_negative() != right.is_sign_negative()),
    );
    assert_eq!(Scalar::add(left, right).to_bits(), (left + right).to_bits());
}

#[kani::proof]
fn native_finish_matches_group_exit() {
    let flow = BlockFlow {
        end: kani::any(),
        pending: arbitrary_group(),
        outgoing: BlockMargins {
            before: arbitrary_group(),
            after: arbitrary_group(),
            all_through: kani::any(),
        },
        collapse_top: kani::any(),
        collapse_bottom: kani::any(),
    };
    let lead = flow.collapse_top && flow.outgoing.all_through;
    let diverges_at_bottom = !lead && flow.collapse_bottom;
    let before = if lead {
        flow.pending
    } else {
        flow.outgoing.before
    };
    let after = if diverges_at_bottom {
        flow.pending
    } else {
        flow.outgoing.after
    };
    let end = if lead || diverges_at_bottom {
        flow.end
    } else {
        flow.end + (flow.pending.positive + flow.pending.negative)
    };
    let expected_height = if end.is_nan() || end < 0.0 { 0.0 } else { end };
    let through = flow.outgoing.all_through;
    let (height, outgoing) = flow.finish();
    // f32::max allows either signed zero for equal arguments. They compare
    // equal here, but all margin elements use their original exact bits.
    assert!(same_value(height, expected_height) || (height == 0.0 && expected_height == 0.0));
    assert!(same_group(outgoing.before, before) && same_group(outgoing.after, after));
    assert_eq!(outgoing.all_through, through);
}

// An omitted nested margin must give its parent exactly the same adjoining
// edges and collapse-through eligibility as an explicitly stored margin.
#[kani::proof]
fn implicit_summary_is_observationally_equal() {
    let (top, bottom, size): (f32, f32, f32) = kani::any();
    kani::assume(legal_edge(top) && legal_edge(bottom));
    let (adjoins, children_empty): (bool, bool) = kani::any();
    let summary = BlockMargins {
        before: arbitrary_group(),
        after: arbitrary_group(),
        all_through: kani::any(),
    };
    kani::assume(summary.is_implicit(children_empty));
    let implicit = BlockItem::from_edges(top, bottom, size, adjoins, children_empty, None);
    let stored = BlockItem::from_edges(top, bottom, size, adjoins, children_empty, Some(summary));
    assert!(same_group(implicit.before, stored.before) && same_group(implicit.after, stored.after));
    assert_eq!(implicit.size.to_bits(), stored.size.to_bits());
    assert_eq!(implicit.through, stored.through);
}
