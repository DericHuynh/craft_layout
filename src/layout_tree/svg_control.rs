//! Paint and borrowed-line drivers shared by the renderer and the proof.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use super::text_windows::{joined_width, separated_by_space};
#[cfg(not(verus_keep_ghost))]
use super::super::text_scan::windows::{joined_width, separated_by_space};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait SvgPaint<N, E> {
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn paint(&mut self, node: N) -> Result<Option<N>, E>;
}

#[cfg(not(verus_keep_ghost))]
impl<N, E, F: FnMut(N) -> Result<Option<N>, E>> SvgPaint<N, E> for F {
    fn paint(&mut self, node: N) -> Result<Option<N>, E> { self(node) }
}

/// A reverse-preorder render visits each live node at most once. Enforce its
/// arena bound even if a link is stale or the successor repeats a node.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
pub(crate) fn paint_nodes<N: Copy, E: Copy, P: SvgPaint<N, E>>(
    root: N, live_nodes: usize, invalid: E, paint: &mut P,
) -> Result<(), E> {
    let mut next = Some(root);
    let mut remaining = live_nodes;
    #[cfg_attr(verus_keep_ghost, verus_spec(decreases remaining))]
    while let Some(node) = next {
        if remaining == 0 { return Err(invalid); }
        remaining -= 1;
        next = match paint.paint(node) {
            Ok(next) => next,
            Err(error) => return Err(error),
        };
    }
    Ok(())
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct WordSpan {
    pub(crate) start: usize,
    pub(crate) end: usize,
    pub(crate) width: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait SvgWords {
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn next_word(&mut self) -> Option<WordSpan>;
}

#[cfg(not(verus_keep_ghost))]
impl<F: FnMut() -> Option<WordSpan>> SvgWords for F {
    fn next_word(&mut self) -> Option<WordSpan> { self() }
}

/// Borrow the next output line. Retain one word when it starts the next line.
/// The source may return arbitrary spans, so check range and forward progress
/// before consuming one. A rejected span ends the line iterator.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures match out {
        None => true,
        Some((line, _)) => after <= line.start < line.end <= text.len()
            && match *final(pending) {
                Some(word) => line.end <= word.start < word.end <= text.len(),
                None => true,
            },
    },
    no_unwind
))]
pub(crate) fn next_line<W: SvgWords>(
    text: &[u8], max: usize, after: usize, words: &mut W, pending: &mut Option<WordSpan>,
) -> Option<(WordSpan, bool)> {
    let mut line = if let Some(word) = *pending {
        *pending = None;
        word
    } else {
        words.next_word()?
    };
    if line.start < after || line.start >= line.end || line.end > text.len() { return None; }

    let mut single_spaces = true;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant after <= line.start < line.end <= text.len(),
            match *pending {
                Some(word) => line.end <= word.start < word.end <= text.len(),
                None => true,
            },
        invariant_except_break pending.is_none(),
        decreases text.len() - line.end,
    ))]
    loop {
        let Some(word) = words.next_word() else { break; };
        if word.start < line.end || word.start >= word.end || word.end > text.len() { return None; }
        let width = joined_width(line.width, word.width);
        if width > max {
            *pending = Some(word);
            break;
        }
        single_spaces &= separated_by_space(text, line.end, word.start);
        line.end = word.end;
        line.width = width;
    }
    Some((line, single_spaces))
}
