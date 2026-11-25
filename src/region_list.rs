//! Replace any regions tentatively chosen below a node by the node itself.
#![allow(unexpected_cfgs)]
use crate::vec_memory::{FallibleVecMemory, VecMemory, try_append};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(added =>
    ensures ({
        let prefix = old(regions)@.take(vstd::math::min(start as int, old(regions).len() as int));
        final(regions)@ == if added { prefix.push(parent) } else { prefix }
    }),
    no_unwind
))]
pub(crate) fn replace_descendants<I: Copy, M: VecMemory + FallibleVecMemory>(
    regions: &mut Vec<I>, start: usize, parent: I,
) -> bool {
    M::truncate(regions, start);
    try_append::<_, M>(regions, parent)
}
