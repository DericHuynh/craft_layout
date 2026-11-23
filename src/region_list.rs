//! Replace any regions tentatively chosen below a node by the node itself.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires start <= old(regions).len(),
    ensures final(regions)@ == old(regions)@.take(start as int).push(parent),
))]
pub(crate) fn replace_descendants<I: Copy>(regions: &mut Vec<I>, start: usize, parent: I) {
    regions.truncate(start);
    regions.push(parent);
}
