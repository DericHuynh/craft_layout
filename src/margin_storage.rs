//! A zero word represents an implicit collapsed margin. Explicit indices use one-based storage.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns margin_index(bits), no_unwind))]
pub fn margin_index(bits: u32) -> Option<usize> {
    if bits == 0 {
        None
    } else {
        Some((bits - 1) as usize)
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(word =>
    requires index < u32::MAX,
    ensures word != 0, margin_index(word) == Some(index),
    no_unwind
))]
pub fn margin_word(index: usize) -> u32 {
    assert!(index < u32::MAX as usize, "too many block containers");
    index as u32 + 1
}

/// Copy one live entry in traversal order. The result is its new index.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires index < source.len(),
    ensures next == old(live).len(), final(live)@ == old(live)@.push(source@[index as int]),
))]
pub fn copy_margin<T: Copy>(source: &[T], live: &mut Vec<T>, index: usize) -> usize {
    let next = live.len();
    live.push(source[index]);
    next
}

/// Store one exported summary. Zero remains available for an unpublished or
/// implicit margin, and freshly packed arenas may assign different indices.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(word =>
    requires old(arena).len() < u32::MAX,
    ensures final(arena)@ == old(arena)@.push(summary),
        margin_index(word) == Some(old(arena).len()),
))]
pub fn publish_margin<T: Copy>(arena: &mut Vec<T>, summary: T) -> u32 {
    let word = margin_word(arena.len());
    arena.push(summary);
    word
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(summary =>
    requires index < arena.len(),
    ensures summary == arena@[index as int],
    no_unwind
))]
pub fn read_margin<T: Copy>(arena: &[T], index: usize) -> T {
    arena[index]
}
