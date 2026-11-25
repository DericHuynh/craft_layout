//! Block placement needs only the presence of in-flow children. Use the rest
//! of the child word and the unused share slot to store a one-based arena index.
#![allow(unexpected_cfgs)]
use crate::vec_memory::VecMemory;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const WORD_BASE: u64 = 0x1_0000_0000;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns block_has_children(child_word), no_unwind))]
pub fn block_has_children(child_word: u32) -> bool {
    child_word % 2 != 0
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns margin_index(low, child_word), no_unwind))]
pub fn margin_index(low: u32, child_word: u32) -> Option<usize> {
    let word = (child_word / 2) as u64 * WORD_BASE + low as u64;
    if word == 0 || word - 1 > usize::MAX as u64 {
        None
    } else {
        Some((word - 1) as usize)
    }
}

/// Rust limits a Vec of nonzero-sized elements to isize::MAX bytes. The
/// 63-bit one-based index covers every entry in a BlockMargins arena.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(words =>
    ensures
        block_has_children(words.1) == block_has_children(child_word),
        margin_index(words.0, words.1) == match index {
            Some(i) if i < isize::MAX as usize => Some(i),
            _ => None,
        },
    no_unwind
))]
pub fn margin_words(index: Option<usize>, child_word: u32) -> (u32, u32) {
    let word = match index {
        Some(index) if index < isize::MAX as usize => index as u64 + 1,
        _ => 0,
    };
    let low = (word % WORD_BASE) as u32;
    let high = (word / WORD_BASE) as u32;
    let new_child_word = high * 2 + child_word % 2;
    #[cfg(verus_keep_ghost)]
    proof! {
        use vstd::arithmetic::div_mod::*;
        lemma_fundamental_div_mod(word as int, WORD_BASE as int);
        lemma_fundamental_div_mod_converse(new_child_word as int, 2, high as int, (child_word % 2) as int);
    }
    (low, new_child_word)
}

/// Copy one live entry in traversal order. The result is its new index.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    ensures match next {
        Some(n) => index < source.len() && n == old(live).len()
            && final(live)@ == old(live)@.push(source@[index as int]),
        None => index >= source.len() && final(live)@ == old(live)@,
    },
    no_unwind
))]
pub(crate) fn copy_margin<T: Copy, M: VecMemory>(source: &[T], live: &mut Vec<T>, index: usize) -> Option<usize> {
    let margin = read_margin(source, index)?;
    Some(append_margin::<_, M>(live, margin))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(index =>
    ensures index == old(arena).len(), final(arena)@ == old(arena)@.push(summary),
    no_unwind
))]
pub(crate) fn append_margin<T: Copy, M: VecMemory>(arena: &mut Vec<T>, summary: T) -> usize {
    let index = arena.len();
    M::append(arena, summary);
    index
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(summary =>
    ensures summary == if index < arena.len() { Some(arena@[index as int]) } else { None },
    no_unwind
))]
pub fn read_margin<T: Copy>(arena: &[T], index: usize) -> Option<T> {
    if index < arena.len() { Some(arena[index]) } else { None }
}

#[cfg(all(test, target_pointer_width = "64"))]
#[test]
fn margin_indices_above_u32_keep_the_child_marker() {
    for index in [None, Some(u32::MAX as usize), Some(isize::MAX as usize - 1)] {
        for has_children in [false, true] {
            let (low, child_word) = margin_words(index, u32::from(has_children));
            assert_eq!(margin_index(low, child_word), index);
            assert_eq!(block_has_children(child_word), has_children);
        }
    }
}
