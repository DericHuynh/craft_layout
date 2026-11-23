//! Canonical local entry sequence for the full and regional sizing walks.

// Expand at the caller so the two Finals stay separate and the specialized
// requests keep their existing direct branches in the per-node traversal.
macro_rules! visit_sizing_roots {
    ($first:expr, $second:expr; $axis:ident => $final:block; $block:expr => $flow:block; $wrap:expr => $share:block) => {{
        { let $axis = $first; $final }
        { let $axis = $second; $final }
        if $block $flow
        if $wrap $share
    }};
}
pub(crate) use visit_sizing_roots;
