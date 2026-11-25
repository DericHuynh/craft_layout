//! The owned node record and its exact sizing and placement projections.
#![allow(unexpected_cfgs)]

use crate::{declarations::{LayoutParams, Xy, XyRect}, node_data::NodeLayoutData};
#[cfg(not(verus_keep_ghost))]
use super::structural_guard::HandleLookup;
#[cfg(verus_keep_ghost)]
use crate::{owned_guard::HandleLookup, prepare_frame::Order};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(not(verus_keep_ghost), derive(Debug, Clone))]
#[repr(C)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct Node<I, C> {
    // Forward traversal and placement use this prefix. User payloads live in
    // a separate arena, so their size cannot change the hot record's stride.
    pub(crate) next_sibling: Option<I>,
    pub(crate) first_child: Option<I>,
    pub(crate) parent: Option<I>,
    pub(crate) layout: NodeLayoutData,
    pub(crate) params: LayoutParams,
    pub(crate) last_child: Option<I>,
    pub(crate) prev_sibling: Option<I>,
    pub(crate) context: Option<C>,
    // Publish the edges and the incarnation's availability bit together.
    pub(crate) rect: XyRect,
    pub(crate) identity: u64,
}

#[cfg(any(feature = "batch-pilot", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(count =>
    ensures count <= population,
        count as int == if first <= last && last - first < population {
            last - first + 1
        } else { 0 },
    no_unwind
))]
pub(super) fn leaf_count_hint(first: u64, last: u64, population: u32) -> u32 {
    let Some(distance) = last.checked_sub(first) else { return 0; };
    if distance >= population as u64 { return 0; }
    distance as u32 + 1
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) struct Fields<'a, I> {
    pub parent: Option<I>,
    pub first: Option<I>,
    pub next: Option<I>,
    pub params: &'a LayoutParams,
    pub layout: &'a NodeLayoutData,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(super) open spec fn matches_fields<I,C>(fields: Fields<'_, I>, record: &Node<I,C>) -> bool {
    &&& fields.parent == record.parent
    &&& fields.first == record.first_child
    &&& fields.next == record.next_sibling
    &&& *fields.params == record.params
    &&& *fields.layout == record.layout
}

/// The arena determines liveness and link values. A preorder witness supplies
/// only the interval and depth ranks used to bound iteration.
pub(super) open spec fn order<I,C>(
    records: Map<I, Node<I,C>>, interval: spec_fn(I) -> (nat, nat), depth: spec_fn(I) -> nat,
) -> Order<I> {
    Order {
        live: |key: I| records.contains_key(key),
        interval, depth,
        parent: |key: I| if records.contains_key(key) { records[key].parent } else { None },
        first: |key: I| if records.contains_key(key) { records[key].first_child } else { None },
        sibling: |key: I| if records.contains_key(key) { records[key].next_sibling } else { None },
    }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<I: Copy, C> Node<I, C> {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_spec(node =>
        ensures node == (Node {
            next_sibling: None, first_child: None, parent: None,
            layout, rect: Xy { x: [0.0, 0.0], y: [0.0, 0.0] }, params,
            last_child: None, prev_sibling: None, context: None, identity,
        }),
        no_unwind
    ))]
    pub(super) fn initialized(params: LayoutParams, identity: u64, layout: NodeLayoutData) -> Self {
        Self {
            next_sibling: None, first_child: None, parent: None,
            layout, rect: Xy::new([0.0, 0.0], [0.0, 0.0]), params,
            last_child: None, prev_sibling: None, context: None, identity,
        }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(fields => ensures matches_fields(fields, self), no_unwind))]
    fn fields(&self) -> Fields<'_, I> {
        Fields { parent: self.parent, first: self.first_child, next: self.next_sibling,
            params: &self.params, layout: &self.layout }
    }

    /// Changes to sizing words cannot change the node's declared inputs,
    /// identity, links or last published geometry.
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(layout =>
        ensures *layout == old(self).layout,
            *final(self) == (Node { layout: *final(layout), ..*old(self) }),
        no_unwind
    ))]
    pub(super) fn sizing_mut(&mut self) -> &mut NodeLayoutData { &mut self.layout }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.is_some() == arena.records().contains_key(key),
        result.is_some() ==> matches_fields(result.unwrap(), &arena.records()[key]),
    no_unwind
))]
pub(super) fn lookup<'a, S, I: Copy + 'a, C: 'a>(arena: &'a S, key: I) -> Option<Fields<'a, I>>
    where S: HandleLookup<Key = I, Record = Node<I, C>>,
{
    match arena.read_record(key) {
        Some(record) => Some(record.fields()),
        None => None,
    }
}
