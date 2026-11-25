//! The full solve shared by the public adapter and incremental fallback.
#![allow(unexpected_cfgs)]

use crate::declarations::Xy;
use crate::sizing_pass;
use crate::vec_memory::VecMemory;
#[cfg(not(verus_keep_ghost))]
use crate::place::placement_entry::RootPlacement;
#[cfg(verus_keep_ghost)]
use crate::placement::{entry::RootPlacement, node::PlacementLinks};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: sizing_pass::Access {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    type Change: Copy;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).order() == old(self).order(), no_unwind))]
    fn changes(&mut self) -> (&mut bool, &mut bool, &mut Vec<Self::Change>, &mut Vec<Self::Id>);

    #[cfg_attr(verus_keep_ghost, verus_spec(placement =>
        requires old(self).order().ordered(),
        ensures final(self).order() == old(self).order(), placement.evidence@.valid(),
            !placement.evidence@.partial, placement.evidence@.links == PlacementLinks::from_order(old(self).order()),
        no_unwind
    ))]
    fn place_full(&mut self) -> RootPlacement<Self::Id>;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    fn keeps_rectangles(&self) -> bool;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).order() == old(self).order(), no_unwind))]
    fn tracking_topology(&mut self) -> &mut bool;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).order().ordered(),
        ensures final(self).order() == old(self).order(),
        no_unwind
    ))]
    fn save_topology(&mut self);
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
fn begin<T: Access + ?Sized, M: VecMemory>(tree: &mut T) {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    {
        tree.packed_stack_leaves().clear::<M>();
        let (children, unknown, declarations, content) = tree.changes();
        *children = false;
        *unknown = false;
        M::clear(declarations);
        M::clear(content);
    }
    #[cfg(not(any(feature = "incremental", verus_keep_ghost)))]
    let _ = tree;
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placement =>
    requires old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(), placement.evidence@.valid(),
        !placement.evidence@.partial,
        placement.evidence@.links == PlacementLinks::from_order(final(tree).order()),
    no_unwind
))]
fn finish<T: Access + ?Sized>(tree: &mut T) -> RootPlacement<T::Id> {
    let placement = tree.place_full();
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    {
        tree.packed_stack_leaves().uniform_capture_open = false;
        if tree.keeps_rectangles() { *tree.tracking_topology() = true; }
        tree.save_topology();
    }
    placement
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(solved =>
    requires old(tree).order().ordered(), old(tree).order().closed_subtrees(),
    ensures final(tree).order() == old(tree).order(),
        solved.0.evidence@.valid(final(tree).order(), window), solved.1.evidence@.valid(),
        solved.0.evidence@.valid_wrapped::<T::Float>(),
        !solved.1.evidence@.partial, solved.1.evidence@.links == PlacementLinks::from_order(final(tree).order()),
    no_unwind
))]
pub(crate) fn run<T: Access + ?Sized, M: VecMemory, const REGISTERED_PIXELS: bool>(
    tree: &mut T, window: Xy<f32>,
) -> (sizing_pass::FullSizing<T::Id>, RootPlacement<T::Id>) {
    begin::<T, M>(tree);
    let sizing = sizing_pass::measure_full::<T, M, REGISTERED_PIXELS>(tree, window);
    let placement = finish(tree);
    (sizing, placement)
}

/// Run the ordinary full solve, committing placement only when sizing detects no dependency cycle.
#[cfg(any(feature = "batch-pilot", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(accepted =>
    requires old(tree).order().ordered(), old(tree).order().closed_subtrees(),
    ensures final(tree).order() == old(tree).order(),
        !accepted ==> !final(tree).packed_state().uniform_capture_open,
    no_unwind
))]
pub(crate) fn run_acyclic<T: Access + ?Sized, M: VecMemory, const REGISTERED_PIXELS: bool>(
    tree: &mut T, window: Xy<f32>,
) -> bool {
    begin::<T, M>(tree);
    sizing_pass::measure_full::<T, M, REGISTERED_PIXELS>(tree, window);
    if *tree.sizing_flags().0 {
        tree.packed_stack_leaves().uniform_capture_open = false;
        return false;
    }
    finish(tree);
    true
}
