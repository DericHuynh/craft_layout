//! The owned arena publishes an absolute rectangle for a live incarnation.
#![allow(unexpected_cfgs)]

use crate::declarations::XyRect;
#[cfg(not(verus_keep_ghost))]
use super::structural_guard::{HandleLookup, HandleModel, TreeError, publish_rect, rectangle_available, resolve_record};
#[cfg(verus_keep_ghost)]
use crate::owned_guard::{HandleLookup, HandleModel, RECT_PUBLISHED, TreeError, incarnation, publish_rect,
    rectangle_available, resolve_record};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures *final(output) == rect,
        *final(identity) == (*old(identity) | RECT_PUBLISHED),
        incarnation(*final(identity)) == incarnation(*old(identity)),
    no_unwind
))]
pub(super) fn publish(output: &mut XyRect, identity: &mut u64, rect: XyRect) {
    *output = rect;
    *identity = publish_rect(*identity, true);
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (if rectangle_available(identity, disabled) { Some(*output) } else { None }),
    no_unwind
))]
fn read(output: &XyRect, identity: u64, disabled: bool) -> Option<XyRect> {
    if rectangle_available(identity, disabled) { Some(*output) } else { None }
}

#[cfg(not(verus_keep_ghost))]
pub(super) trait Model: HandleModel {}

#[cfg(verus_keep_ghost)]
verus! {
pub(super) trait Model: HandleModel {
    spec fn output(record: &Self::Record) -> (XyRect, bool);
}

pub(super) open spec fn read_key<A: Model>(arena: &A, same_owner: bool, key: A::Key, requested: u64)
    -> Result<XyRect, TreeError> {
    if !same_owner { Err(TreeError::ForeignNode) }
    else if arena.records().contains_key(key) && incarnation(A::record_identity(&arena.records()[key])) == requested {
        let record = &arena.records()[key];
        let (rect, disabled) = A::output(record);
        if rectangle_available(A::record_identity(record), disabled) { Ok(rect) }
        else { Err(TreeError::LayoutUnavailable) }
    } else { Err(TreeError::StaleNode) }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(super) trait Access: Model + HandleLookup {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures (*out.0, out.1) == Self::output(record),
        no_unwind
    ))]
    fn rectangle(record: &Self::Record) -> (&XyRect, bool);
}

/// Resolve the handle before consulting the allocation's publication bit.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result == read_key(arena, same_owner, key, requested),
    no_unwind
))]
pub(super) fn lookup<A: Access>(arena: &A, same_owner: bool, key: A::Key, requested: u64)
    -> Result<XyRect, TreeError> {
    let record = match resolve_record(arena, same_owner, key, requested) {
        Ok(record) => record,
        Err(error) => return Err(error),
    };
    let (rect, disabled) = A::rectangle(record);
    match read(rect, A::identity_word(record), disabled) {
        Some(rect) => Ok(rect),
        None => Err(TreeError::LayoutUnavailable),
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) struct Record {
    pub identity: u64,
    pub disabled: bool,
    pub rectangle: XyRect,
}

/// The counter names an incarnation that neither the live arena nor any
/// handle from a previous allocation can use yet.
pub(crate) open spec fn incarnation_namespace<I>(records: Map<I, Record>, next: u64) -> bool {
    &&& 0 < next <= RECT_PUBLISHED
    &&& forall |id: I| #[trigger] records.contains_key(id) ==> incarnation(records[id].identity) < next
    &&& forall |a: I, b: I| #![trigger records.contains_key(a), records.contains_key(b)]
        records.contains_key(a) && records.contains_key(b) && a != b
        ==> incarnation(records[a].identity) != incarnation(records[b].identity)
}

/// Changing a key's slot generation cannot make its earlier handles resolve
/// to the fresh incarnation, even if the slot map generation wraps.
pub(crate) proof fn allocate_incarnation<I>(records: Map<I, Record>, id: I, added: Record, next: u64, previous: u64)
    requires incarnation_namespace(records, next), next < RECT_PUBLISHED,
        !records.contains_key(id), incarnation(added.identity) == next,
    ensures incarnation_namespace(records.insert(id, added), (next + 1) as u64),
        previous < next ==> previous != incarnation(added.identity),
{
    let after = records.insert(id, added);
    assert forall |key: I| #[trigger] after.contains_key(key) implies
        incarnation(after[key].identity) < next + 1 by {
        if key != id { assert(records.contains_key(key)); }
    }
    assert forall |a: I, b: I| #![trigger after.contains_key(a), after.contains_key(b)]
        after.contains_key(a) && after.contains_key(b) && a != b implies
        incarnation(after[a].identity) != incarnation(after[b].identity) by {
        if a != id { assert(records.contains_key(a)); }
        if b != id { assert(records.contains_key(b)); }
    }
}

pub(crate) proof fn remove_incarnation<I>(records: Map<I, Record>, id: I, next: u64)
    requires incarnation_namespace(records, next),
    ensures incarnation_namespace(records.remove(id), next),
{}

pub(crate) type Placement<I> = (I, XyRect);

pub(crate) open spec fn observed(record: Record) -> Option<(u64, XyRect)> {
    if rectangle_available(record.identity, record.disabled) {
        Some((incarnation(record.identity), record.rectangle))
    } else { None }
}

pub(crate) open spec fn place<I>(records: Map<I, Record>, event: Placement<I>) -> Map<I, Record> {
    let (id, rectangle) = event;
    if records.contains_key(id) {
        let record = records[id];
        records.insert(id, Record { rectangle, identity: record.identity | RECT_PUBLISHED, ..record })
    } else { records }
}

pub(crate) open spec fn publish_events<I>(records: Map<I, Record>, events: Seq<Placement<I>>) -> Map<I, Record>
    decreases events.len(),
{
    if events.len() == 0 { records }
    else { place(publish_events(records, events.drop_last()), events.last()) }
}

pub(crate) open spec fn latest<I>(events: Seq<Placement<I>>, id: I) -> Option<XyRect>
    decreases events.len(),
{
    if events.len() == 0 { None }
    else if events.last().0 == id { Some(events.last().1) }
    else { latest(events.drop_last(), id) }
}

/// Replaying placement does not change the live keys, incarnation, or
/// visibility. Each enabled key reads its latest event or its prior rectangle.
pub(crate) proof fn placement_observation<I>(before: Map<I, Record>, events: Seq<Placement<I>>, id: I)
    ensures ({
        let after = publish_events(before, events);
        &&& after.dom() == before.dom()
        &&& after.contains_key(id) ==> {
            &&& incarnation(after[id].identity) == incarnation(before[id].identity)
            &&& after[id].disabled == before[id].disabled
            &&& observed(after[id]) == if before[id].disabled { None }
                else if let Some(rect) = latest(events, id) { Some((incarnation(before[id].identity), rect)) }
                else { observed(before[id]) }
        }
    }),
    decreases events.len(),
{
    if events.len() == 0 { return; }
    let prefix = events.drop_last();
    let event = events.last();
    placement_observation(before, prefix, id);
    let prior = publish_events(before, prefix);
    let after = place(prior, event);
    assert(after.dom() =~= before.dom());
    if before.contains_key(id) && id == event.0 {
        let old_word = prior[id].identity;
        let new_word = after[id].identity;
        assert((new_word & !RECT_PUBLISHED) == (old_word & !RECT_PUBLISHED)
            && (new_word & RECT_PUBLISHED != 0)) by(bit_vector)
                requires new_word == (old_word | RECT_PUBLISHED);
    }
}

/// Map the owned public view to the absolute words of the shared frame model.
/// The latter also carries local rectangles for custom adapters.
pub(crate) open spec fn absolute_words(rect: XyRect, word: spec_fn(f32) -> u32) -> crate::RectBits {
    (word(rect.x@[0]), word(rect.x@[1]), word(rect.y@[0]), word(rect.y@[1]))
}

pub(crate) open spec fn placement_key<I>(records: Map<I, Record>, id: I) -> crate::Key {
    crate::Key { incarnation: incarnation(records[id].identity) as nat, phase: crate::Phase::Placement }
}

pub(crate) open spec fn placement_id<I>(records: Map<I, Record>, key: crate::Key) -> I {
    choose|id: I| records.contains_key(id) && #[trigger] placement_key(records, id) == key
}

/// Current physical IDs and public incarnations name the same placement
/// writes, even when the arena has recycled a slot.
pub(crate) proof fn owned_callback_incarnations<I, F: crate::prepare_frame::FrameFloat>(
    records: Map<I, Record>, next: u64, preorder: Seq<I>,
    previous: crate::frame_equivalence::NativeOutputs<I>, rows: Seq<crate::frame_equivalence::NativeWrite<I>>,
)
    requires incarnation_namespace(records, next),
        forall|i: int| 0 <= i < preorder.len() ==> records.contains_key(#[trigger] preorder[i]),
        forall|i: int| 0 <= i < rows.len() ==> preorder.contains((#[trigger] rows[i]).0),
    ensures ({
        let key = |id: I| placement_key(records, id);
        let id = |key: crate::Key| placement_id(records, key);
        let visible = preorder.map_values(key).to_set();
        let before = crate::frame_equivalence::project_native_view::<I, F>(visible, id, previous);
        let after = crate::frame_equivalence::native_commit(previous, rows);
        crate::frame_equivalence::project_native_view::<I, F>(visible, id, after)
            == crate::replay_publication::apply_rows(before, crate::frame_equivalence::native_rows::<I, F>(rows, key))
    }),
{
    let key = |id: I| placement_key(records, id);
    let id = |key: crate::Key| placement_id(records, key);
    let keys = preorder.map_values(key);
    let visible = keys.to_set();
    keys.to_set_ensures();
    assert forall|k: crate::Key| #[trigger] visible.contains(k) implies key(id(k)) == k by {
        let i = choose|i: int| 0 <= i < keys.len() && keys[i] == k;
        assert(records.contains_key(preorder[i]) && key(preorder[i]) == k);
        assert(key(id(k)) == k);
    }
    assert forall|i: int| 0 <= i < rows.len() implies {
        let node = (#[trigger] rows[i]).0;
        visible.contains(key(node)) && id(key(node)) == node
    } by {
        let node = rows[i].0;
        let j = choose|j: int| 0 <= j < preorder.len() && preorder[j] == node;
        assert(keys[j] == key(node));
        assert(visible.contains(key(node)));
        assert(records.contains_key(id(key(node))) && records.contains_key(node));
        assert(incarnation(records[id(key(node))].identity) == incarnation(records[node].identity));
    }
    crate::frame_equivalence::native_callbacks_project_to_frame_commit::<I, F>(previous, rows, visible, id, key);
}

pub(crate) open spec fn observed_words(record: Record, word: spec_fn(f32) -> u32) -> Option<(u64, crate::RectBits)> {
    match observed(record) {
        Some((identity, rectangle)) => Some((identity, absolute_words(rectangle, word))),
        None => None,
    }
}

pub(crate) open spec fn visible_view<I>(
    records: Map<I, Record>, preorder: Seq<I>, word: spec_fn(f32) -> u32,
) -> Seq<(u64, crate::RectBits)>
    decreases preorder.len(),
{
    if preorder.len() == 0 { Seq::empty() }
    else {
        let id = preorder.last();
        let prefix = visible_view(records, preorder.drop_last(), word);
        match if records.contains_key(id) { observed_words(records[id], word) } else { None } {
            Some(record) => prefix.push(record),
            None => prefix,
        }
    }
}

/// Matching public reads on the same physical preorder imply matching
/// visible documents. Inactive and detached backing records are omitted.
pub(crate) proof fn equal_owned_views<I>(
    left: Map<I, Record>, right: Map<I, Record>, preorder: Seq<I>, word: spec_fn(f32) -> u32,
)
    requires
        forall |id: I| #[trigger] preorder.contains(id) ==> left.contains_key(id) == right.contains_key(id),
        forall |id: I| #[trigger] preorder.contains(id) && left.contains_key(id)
            ==> observed_words(left[id], word) == observed_words(right[id], word),
    ensures visible_view(left, preorder, word) == visible_view(right, preorder, word),
    decreases preorder.len(),
{
    if preorder.len() > 0 {
        let prefix = preorder.drop_last();
        assert forall |id: I| #[trigger] prefix.contains(id) implies preorder.contains(id) by {
            let j = choose|j: int| 0 <= j < prefix.len() && prefix[j] == id;
            assert(preorder[j] == prefix[j]);
        }
        assert(preorder[preorder.len() - 1] == preorder.last());
        assert(preorder.contains(preorder.last()));
        equal_owned_views(left, right, prefix, word);
    }
}

pub(crate) open spec fn absolute_event<I>(
    events: Seq<Placement<I>>, id: I, word: spec_fn(f32) -> u32,
) -> Option<crate::RectBits> {
    match latest(events, id) {
        Some(rect) => Some(absolute_words(rect, word)),
        None => None,
    }
}

pub(crate) open spec fn fresh_storage<I>(records: Map<I, Record>) -> Map<I, Record> {
    Map::new(records.dom(), |id: I| Record { identity: incarnation(records[id].identity), ..records[id] })
}

/// Compare placement of one current document against an arena without any
/// published rectangles. Every enabled incarnation must have a fresh event.
/// Retained storage supplies a word only when the retained stream skipped it.
pub(crate) proof fn retained_owned_projection<I>(
    records: Map<I, Record>, preorder: Seq<I>,
    retained: Seq<Placement<I>>, fresh: Seq<Placement<I>>, word: spec_fn(f32) -> u32,
)
    requires
        forall |id: I| #[trigger] preorder.contains(id) && records.contains_key(id) && !records[id].disabled
            ==> absolute_event(fresh, id, word).is_some(),
        forall |id: I| #[trigger] preorder.contains(id) && records.contains_key(id) && !records[id].disabled
            ==> if absolute_event(retained, id, word).is_some() {
                absolute_event(retained, id, word) == absolute_event(fresh, id, word)
            } else {
                observed_words(records[id], word) == Some((
                    incarnation(records[id].identity), absolute_event(fresh, id, word).unwrap(),
                ))
            },
    ensures
        visible_view(publish_events(records, retained), preorder, word) ==
            visible_view(publish_events(fresh_storage(records), fresh), preorder, word),
        forall |id: I| #[trigger] preorder.contains(id) && records.contains_key(id) ==>
            observed(publish_events(records, retained)[id]).is_some() == !records[id].disabled,
{
    let left = publish_events(records, retained);
    let storage = fresh_storage(records);
    let right = publish_events(storage, fresh);
    assert(storage.dom() =~= records.dom());
    assert forall |id: I| #[trigger] preorder.contains(id) implies {
        &&& left.contains_key(id) == records.contains_key(id)
        &&& left.contains_key(id) == right.contains_key(id)
        &&& left.contains_key(id) ==> {
            &&& observed_words(left[id], word) == observed_words(right[id], word)
            &&& observed(left[id]).is_some() == !records[id].disabled
        }
    } by {
        placement_observation(records, retained, id);
        placement_observation(storage, fresh, id);
        if records.contains_key(id) {
            let identity = records[id].identity;
            let cleared = storage[id].identity;
            assert((cleared & !RECT_PUBLISHED) == cleared) by(bit_vector)
                requires cleared == (identity & !RECT_PUBLISHED);
        }
    }
    equal_owned_views(left, right, preorder, word);
    assert forall |id: I| #[trigger] preorder.contains(id) && records.contains_key(id) implies
        observed(left[id]).is_some() == !records[id].disabled by {
        assert(left.contains_key(id));
    }
}
}
