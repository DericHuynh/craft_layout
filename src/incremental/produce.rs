//! Native selection of the direct or general ranked slot finisher.
#![allow(unexpected_cfgs)]

use crate::declarations::ChildrenLayout;
use crate::sizing_pass;
#[cfg(verus_keep_ghost)]
use crate::prepare_nodes::live;
#[cfg(verus_keep_ghost)]
use super::producers;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::placement::geometry::FloatClassification;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::{self, Kind};
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::Kind;
#[cfg(verus_keep_ghost)]
use crate::dependencies::{sizing_finish, sizing_requests::Request};
#[cfg(not(verus_keep_ghost))]
use crate::solve::{sizing_finish, sizing_requests::Request};

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn final_regular<T: crate::prepare_nodes::RecordModel + ?Sized>(tree: &T, slot: Request<T::Id>) -> f32 {
    tree.layout_record(slot.node).values[kernel::slot_index(slot.vertical as usize, Kind::Regular) as int]
}

pub(crate) open spec fn finished<T: crate::prepare_nodes::RecordModel + ?Sized>(tree: &T, slot: Request<T::Id>) -> bool {
    kernel::read_state(tree.layout_record(slot.node).flags.0, sizing_finish::key(slot).1 as u32) == kernel::SOLVED
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Computed<I> {
    #[cfg(verus_keep_ghost)]
    pub(crate) stored: sizing_finish::StoredSize<I>,
    #[cfg(verus_keep_ghost)]
    pub(crate) direct: bool,
    #[cfg(not(verus_keep_ghost))]
    marker: core::marker::PhantomData<I>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: crate::prepare_nodes::Records {
    /// Run the canonical sizing finisher with retained Grid cell lookup.
    #[cfg_attr(verus_keep_ghost, verus_spec(stored =>
        requires live(old(self), slot.node),
        ensures final(self).order() == old(self).order(), finished(final(self), slot),
            stored.slot == slot,
            stored.value == final(self).layout_record(slot.node).values[sizing_finish::key(slot).1 as int],
        no_unwind
    ))]
    fn finish_retaining_grid(&mut self, slot: Request<Self::Id>) -> sizing_finish::StoredSize<Self::Id>;
}

/// The direct path publishes exactly one packed Final and forwards all other
/// requests to the same canonical computation used by full sizing.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(computed =>
    requires live(old(tree), slot.node), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(), finished(final(tree), slot),
        computed.stored.slot == slot,
        computed.stored.value == final(tree).layout_record(slot.node).values[sizing_finish::key(slot).1 as int],
        !(slot.kind is Final) ==> !computed.direct,
        computed.direct ==> {
            let before = old(tree).layout_record(slot.node);
            let after = final(tree).layout_record(slot.node);
            let index = sizing_finish::key(slot).1 as int;
            &&& slot.kind is Final
            &&& !sizing_finish::assigns_width_grid(old(tree).layout_params(slot.node), slot.axis())
            &&& sizing_finish::permits_direct_final(old(tree).layout_params(slot.node), slot.axis(), before.flags)
            &&& T::Float::finite_word(final_regular(old(tree), slot))
            &&& after.values@ == before.values@.update(index, final_regular(old(tree), slot))
            &&& after == (crate::node_data::NodeLayoutData { values: after.values, flags: after.flags, ..before })
            &&& producers::writes_only::<T::Float, T::Id>(
                sizing_pass::record_book(old(tree)), sizing_pass::record_book(final(tree)),
                Set::empty().insert(producers::scalar_lane(slot)),
            )
            &&& forall |other: T::Id| other != slot.node ==>
                #[trigger] final(tree).layout_record(other) == old(tree).layout_record(other)
        },
    no_unwind
))]
pub(crate) fn compute<T: Access + ?Sized>(tree: &mut T, slot: Request<T::Id>) -> Computed<T::Id> {
    let axis = slot.axis();
    match slot.kind {
        Kind::EvenShare => {
            if let ChildrenLayout::Wrap { axis: main, .. } = tree.params(slot.node).children_layout {
                if main.index() == axis.index() {
                    let _ = sizing_pass::reset_wrap_items(tree, slot.node);
                }
            }
        }
        Kind::Final => {
            if let Some(intrinsic) = sizing_finish::unbounded_final_input(tree.params(slot.node), axis) {
                let data = tree.edit(slot.node);
                if data.try_finish_unbounded_final::<T::Float>(axis, intrinsic) {
                    #[cfg(verus_keep_ghost)]
                    let value = kernel::read_slot(&data.values, axis.index(), Kind::Final);
                    #[cfg(verus_keep_ghost)]
                    proof! {
                        let style = old(tree).layout_params(slot.node);
                        let flags = old(tree).layout_record(slot.node).flags;
                        producers::scalar_store_is_local::<T::Float, T::Id>(
                            sizing_pass::record_book(old(tree)), sizing_pass::record_book(tree), slot,
                            final_regular(old(tree), slot),
                        );
                        assert(sizing_finish::permits_direct_final(style, axis, flags)) by {
                            assert(exists |fit: bool| sizing_finish::has_unbounded_final_inputs(style, axis, fit)
                                && (!fit || flags.0 & crate::node_flags::NodeFlags::flex_child(axis) == 0));
                        }
                    }
                    return Computed {
                        #[cfg(verus_keep_ghost)]
                        stored: sizing_finish::StoredSize { slot, value },
                        #[cfg(verus_keep_ghost)]
                        direct: true,
                        #[cfg(not(verus_keep_ghost))]
                        marker: core::marker::PhantomData,
                    };
                }
            }
        }
        _ => {}
    }
    let _stored = tree.finish_retaining_grid(slot);
    Computed {
        #[cfg(verus_keep_ghost)]
        stored: _stored,
        #[cfg(verus_keep_ghost)]
        direct: false,
        #[cfg(not(verus_keep_ghost))]
        marker: core::marker::PhantomData,
    }
}
