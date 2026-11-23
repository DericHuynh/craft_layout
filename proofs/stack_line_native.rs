//! IEEE binary32 refinement of the stack cursor and published edges.
//! Run with `kani --no-overflow-checks -Z unstable-options proofs/stack_line_native.rs --cbmc-args --fpa`.
//! NaN and infinity are valid arithmetic results and the assertions check them directly.
#[path = "../src/stack_line.rs"]
mod kernel;

// Rust permits different NaN payloads after arithmetic. All other bit
// patterns, including positive and negative zero, are observable here.
fn same(actual: f32, expected: f32) -> bool {
    actual.to_bits() == expected.to_bits() || (actual.is_nan() && expected.is_nan())
}

fn f() -> f32 { f32::from_bits(kani::any()) }

// A zero edge consumes no space and preserves the word it is attached to.
fn adjusted(value: f32, edge: f32) -> f32 {
    if edge.to_bits() & 0x7fff_ffff == 0 { value } else { value + edge }
}

fn physical_margins_and_cursor_match<const REVERSED: bool>() {
    let cursor = f();
    let size = f();
    let gap = f();
    let [left, right] = [f(), f()];
    let [before, after] = [f(), f()];
    let mut next = cursor;
    let edge = kernel::place(&mut next, REVERSED, [left, right], size, [before, after], gap);
    if REVERSED {
        let leading = adjusted(cursor, after);
        let high = (left + right) - leading;
        assert!(same(edge[0], high - size));
        assert!(same(edge[1], high));
        assert!(same(next, leading + (adjusted(size, before) + gap)));
    } else {
        let leading = adjusted(cursor, before);
        assert!(same(edge[0], leading));
        assert!(same(edge[1], leading + size));
        assert!(same(next, leading + (adjusted(size, after) + gap)));
        // This is the previous sibling and size consumed by append placement.
        assert!(same(kernel::after_item(edge[0], size, after, gap), next));
    }
}

fn start_shortcut_matches<const HORIZONTAL: bool>() {
    let main = f();
    let cross = f();
    let (width, height, gap) = (f(), f(), f());
    let signed_zero = if kani::any() { 0.0 } else { -0.0 };
    let mut next = main;
    let start = kernel::place_start(&mut next, cross, HORIZONTAL, [width, height], gap);
    let mut full_next = main;
    let (size, cross_size, along, across) = if HORIZONTAL {
        (width, height, start[0], start[1])
    } else {
        (height, width, start[1], start[0])
    };
    let full = kernel::place(&mut full_next, false, [f(), f()], size, [signed_zero; 2], gap);
    assert!(same(next, full_next));
    assert!(same(along[0], full[0]) && same(along[1], full[1]));
    let edge = adjusted(cross, signed_zero);
    assert!(same(across[0], edge) && same(across[1], edge + cross_size));
}

#[kani::proof]
#[kani::solver(z3)]
fn forward_margins_and_resume() { physical_margins_and_cursor_match::<false>(); }

#[kani::proof]
#[kani::solver(z3)]
fn reversed_margins() { physical_margins_and_cursor_match::<true>(); }

#[kani::proof]
#[kani::solver(z3)]
fn horizontal_start() { start_shortcut_matches::<true>(); }

#[kani::proof]
#[kani::solver(z3)]
fn vertical_start() { start_shortcut_matches::<false>(); }

// SMT floating-point sorts represent all NaNs as one abstract value. Check
// copied words with the bit-vector backend so every NaN payload is observable.
#[kani::proof]
#[kani::solver(cadical)]
fn untouched_origins_keep_their_words() {
    let start = f();
    let cross = f();
    let horizontal: bool = kani::any();
    let zero = if kani::any() { 0.0 } else { -0.0 };
    let mut cursor = start;
    let general = kernel::place(&mut cursor, false, [f(), f()], f(), [zero, f()], f());
    assert_eq!(general[0].to_bits(), start.to_bits());
    let mut cursor = start;
    let xy = kernel::place_start(&mut cursor, cross, horizontal, [f(), f()], f());
    let (x, y) = if horizontal { (start, cross) } else { (cross, start) };
    assert_eq!(xy[0][0].to_bits(), x.to_bits());
    assert_eq!(xy[1][0].to_bits(), y.to_bits());
}
