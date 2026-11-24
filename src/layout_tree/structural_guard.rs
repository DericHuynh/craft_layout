//! Bounds and validation used before editing the owned tree.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const KEY_LIMIT: usize = u32::MAX as usize;

// The upper bit shares the cold identity word with rectangle publication.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) const RECT_PUBLISHED: u64 = 1 << 63;

/// Why a layout-tree operation could not be completed.
#[cfg_attr(not(verus_keep_ghost), non_exhaustive)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TreeError {
    /// The handle belongs to another tree.
    ForeignNode,
    /// The node was removed.
    StaleNode,
    /// A move would make a node an ancestor of itself.
    WouldCreateCycle,
    /// A node cannot be moved before itself.
    BeforeSelf,
    /// The node has no published rectangle, or is disabled.
    LayoutUnavailable,
    /// The requested capacity or another insertion cannot be reserved.
    Capacity,
}

/// A requested reservation must leave room for the arena sentinel and root.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.is_some() == (requested < KEY_LIMIT),
        out.is_some() ==> 1 <= out.unwrap() < KEY_LIMIT,
        out.is_some() ==> out.unwrap() == (if requested < 1 { 1usize } else { requested }),
    no_unwind
))]
pub(crate) fn root_capacity(requested: usize) -> Option<usize> {
    if requested >= KEY_LIMIT { None }
    else { Some(if requested == 0 { 1 } else { requested }) }
}

/// There is room for one more live key in addition to the arena sentinel.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns can_insert(live), no_unwind))]
pub(crate) fn can_insert(live: usize) -> bool {
    live < KEY_LIMIT - 1
}

/// An admitted insertion cannot overflow or reuse the publication bit.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.is_some() == (live + 1 < KEY_LIMIT && current < RECT_PUBLISHED),
        out.is_some() ==> out.unwrap() == current + 1 && out.unwrap() <= RECT_PUBLISHED,
        out.is_some() ==> current & RECT_PUBLISHED == 0,
    no_unwind
))]
pub(crate) fn next_incarnation(live: usize, current: u64) -> Option<u64> {
    if !can_insert(live) || current >= RECT_PUBLISHED { return None; }
    #[cfg(verus_keep_ghost)]
    proof! { assert(current & RECT_PUBLISHED == 0) by(bit_vector) requires current < RECT_PUBLISHED; }
    Some(current + 1)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns incarnation(word), no_unwind))]
pub(crate) fn incarnation(word: u64) -> u64 {
    word & !RECT_PUBLISHED
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out == (if published { word | RECT_PUBLISHED } else { word & !RECT_PUBLISHED }),
        incarnation(out) == incarnation(word),
        (out & RECT_PUBLISHED != 0) == published,
    no_unwind
))]
pub(crate) fn publish_rect(word: u64, published: bool) -> u64 {
    let bits = if published { word | RECT_PUBLISHED } else { word & !RECT_PUBLISHED };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert((bits & !RECT_PUBLISHED) == (word & !RECT_PUBLISHED)
            && ((bits & RECT_PUBLISHED) != 0) == published) by(bit_vector)
            requires bits == (if published { word | RECT_PUBLISHED } else { word & !RECT_PUBLISHED });
    }
    bits
}

/// Stale geometry stays unavailable until the solver has published a rectangle
/// for this live incarnation and the node is enabled.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns rectangle_available(word, disabled), no_unwind))]
pub(crate) fn rectangle_available(word: u64, disabled: bool) -> bool {
    !disabled && word & RECT_PUBLISHED != 0
}

#[cfg(verus_keep_ghost)]
verus! {
// SlotMap reserves entry zero. When it has no vacant entry to reuse, all
// other entries are live and the next key is the current physical length.
// A successful reservation for another live value leaves capacity for that
// key as well as the sentinel. These arithmetic facts discharge the bound
// checks in SlotMap's append branch under its storage invariant.
pub(crate) proof fn slotmap_insert_bounds(live: usize, slots: usize, capacity: usize,
    reuses_vacancy: bool,
)
    requires can_insert(live), slots <= capacity, live + 2 <= capacity,
        !reuses_vacancy ==> slots == live + 1,
    ensures live + 1 < KEY_LIMIT,
        !reuses_vacancy ==> slots < KEY_LIMIT && slots < capacity && slots + 1 <= KEY_LIMIT,
{}

/// SlotMap 1.1.1, basic.rs:try_reserve subtracts the physical slots already
/// held, excluding its sentinel. Vec's successful reservation covers at
/// least that many additional physical slots.
pub(crate) proof fn slotmap_reserve_covers_live(live: usize, slots: usize, additional: usize,
    needed: usize, capacity: usize,
)
    requires 1 <= slots, live + additional < KEY_LIMIT,
        needed == vstd::math::max(0, live + additional - (slots - 1)),
        slots + needed <= capacity,
    ensures live + additional < capacity,
        live + additional <= usize::MAX,
{}

/// SlotMap checks generation equality before accessing a slot union. Keys
/// always have odd versions and free slots always have even versions. When
/// removing an occupied slot, incrementing the generation wraps safely.
pub(crate) proof fn slotmap_generation_checks(version: u32, key_version: u32)
    requires key_version & 1 == 1,
    ensures version == key_version ==> version & 1 == 1,
        version & 1 == 1 ==> version.wrapping_add(1) & 1 == 0,
        (version | 1) > 0,
{
    assert((version & 1 == 1 ==> version.wrapping_add(1) & 1 == 0) && (version | 1) > 0) by(bit_vector);
}
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait InsertionModel {
    type Key: Copy;
    type Value;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait InsertionModel {
    type Key: Copy;
    type Value;
    spec fn entries(&self) -> Map<Self::Key, Self::Value>;
    spec fn live_count(&self) -> usize;
    // Capacity measures all representable live slots, excluding the sentinel.
    spec fn reserved(&self) -> usize;
}
}

/// Safe operations of the pinned slot arena, for the generated node and
/// context keys. Allocation is confined to the fallible reserve operation.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait InsertionArena: InsertionModel + Sized {
    #[cfg_attr(verus_keep_ghost, verus_spec(arena =>
        ensures arena.live_count() == 0, arena.entries().is_empty(),
        no_unwind
    ))]
    fn empty_slots() -> Self;

    #[cfg_attr(verus_keep_ghost, verus_spec(count =>
        ensures count == self.live_count(),
        no_unwind
    ))]
    fn count(&self) -> usize;

    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires old(self).live_count() + additional < KEY_LIMIT,
        ensures final(self).live_count() == old(self).live_count(),
            final(self).entries() == old(self).entries(),
            result.is_ok() ==> old(self).live_count() + additional <= final(self).reserved(),
            result.is_err() ==> result == Err(TreeError::Capacity),
        no_unwind
    ))]
    fn try_reserve_slots(&mut self, additional: usize) -> Result<(), TreeError>;

    #[cfg_attr(verus_keep_ghost, verus_spec(key =>
        requires can_insert(old(self).live_count()), old(self).live_count() < old(self).reserved(),
        ensures final(self).live_count() == old(self).live_count() + 1,
            !old(self).entries().contains_key(key),
            final(self).entries() == old(self).entries().insert(key, value),
        no_unwind
    ))]
    fn insert_reserved(&mut self, value: Self::Value) -> Self::Key;
}

/// Reserve by live count and leave key zero and the terminal key unused.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures final(arena).live_count() == old(arena).live_count(),
        final(arena).entries() == old(arena).entries(),
        result.is_ok() ==> old(arena).live_count() + additional < KEY_LIMIT
            && old(arena).live_count() + additional <= final(arena).reserved(),
        result.is_err() ==> result == Err(TreeError::Capacity),
    no_unwind
))]
pub(crate) fn reserve_entries<A: InsertionArena>(arena: &mut A, additional: usize) -> Result<(), TreeError> {
    if additional >= KEY_LIMIT.saturating_sub(arena.count()) {
        return Err(TreeError::Capacity);
    }
    arena.try_reserve_slots(additional)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        Ok(key) => final(arena).live_count() == old(arena).live_count() + 1
            && !old(arena).entries().contains_key(key)
            && final(arena).entries() == old(arena).entries().insert(key, value),
        Err(error) => error == TreeError::Capacity
            && final(arena).live_count() == old(arena).live_count()
            && final(arena).entries() == old(arena).entries(),
    },
    no_unwind
))]
pub(crate) fn insert_entry<A: InsertionArena>(arena: &mut A, value: A::Value) -> Result<A::Key, TreeError> {
    match reserve_entries(arena, 1) {
        Ok(()) => Ok(arena.insert_reserved(value)),
        Err(error) => Err(error),
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn optional_entries<A: InsertionModel>(arena: &Option<A>) -> Map<A::Key, A::Value> {
    match arena { Some(arena) => arena.entries(), None => Map::empty() }
}
}

/// Keep the context arena unallocated until the first context is supplied.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        Ok(key) => !optional_entries(old(arena)).contains_key(key)
            && optional_entries(final(arena)) == optional_entries(old(arena)).insert(key, value),
        Err(error) => error == TreeError::Capacity && optional_entries(final(arena)) == optional_entries(old(arena)),
    },
    no_unwind
))]
pub(crate) fn insert_optional_entry<A: InsertionArena>(arena: &mut Option<A>, value: A::Value) -> Result<A::Key, TreeError> {
    if arena.is_none() { *arena = Some(A::empty_slots()); }
    match arena {
        Some(arena) => insert_entry(arena, value),
        None => Err(TreeError::Capacity),
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait ContextModel<K>: Sized {}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait ContextModel<K>: Sized {
    spec fn with_context(self, key: K) -> Self;
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait BindContext<K>: ContextModel<K> {
    #[cfg_attr(verus_keep_ghost, verus_spec(record =>
        ensures record == self.with_context(key),
        no_unwind
    ))]
    fn bind_context(self, key: K) -> Self;
}

/// Reserve the node slot before installing the context. With a successful
/// reserve, publishing the node cannot fail after its context is installed.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        Ok((node, context_key)) => {
            &&& !old(nodes).entries().contains_key(node)
            &&& final(nodes).live_count() == old(nodes).live_count() + 1
            &&& match (context, context_key) {
                (Some(payload), Some(key)) => !optional_entries(old(contexts)).contains_key(key)
                    && optional_entries(final(contexts)) == optional_entries(old(contexts)).insert(key, payload)
                    && final(nodes).entries() == old(nodes).entries().insert(node, value.with_context(key)),
                (None, None) => optional_entries(final(contexts)) == optional_entries(old(contexts))
                    && final(nodes).entries() == old(nodes).entries().insert(node, value),
                _ => false,
            }
        },
        Err(error) => error == TreeError::Capacity && final(nodes).live_count() == old(nodes).live_count()
            && final(nodes).entries() == old(nodes).entries()
            && optional_entries(final(contexts)) == optional_entries(old(contexts)),
    },
    no_unwind
))]
pub(crate) fn insert_record<A, C>(nodes: &mut A, contexts: &mut Option<C>, value: A::Value, context: Option<C::Value>)
    -> Result<(A::Key, Option<C::Key>), TreeError>
where
    A: InsertionArena,
    C: InsertionArena,
    A::Value: BindContext<C::Key>,
{
    if let Err(error) = reserve_entries(nodes, 1) {
        return Err(error);
    }
    let (value, context_key) = match context {
        Some(payload) => {
            let key = match insert_optional_entry(contexts, payload) {
                Ok(key) => key,
                Err(error) => return Err(error),
            };
            (value.bind_context(key), Some(key))
        }
        None => (value, None),
    };
    Ok((nodes.insert_reserved(value), context_key))
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait HandleModel {
    type Key: Copy;
    type Record;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait HandleModel {
    type Key: Copy;
    type Record;
    spec fn records(&self) -> Map<Self::Key, Self::Record>;
    spec fn record_identity(record: &Self::Record) -> u64;
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait HandleLookup: HandleModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(record =>
        ensures record.is_some() == self.records().contains_key(key),
            record.is_some() ==> *record.unwrap() == self.records()[key],
        no_unwind
    ))]
    fn read_record(&self, key: Self::Key) -> Option<&Self::Record>;

    #[cfg_attr(verus_keep_ghost, verus_spec(word =>
        ensures word == Self::record_identity(record),
        no_unwind
    ))]
    fn identity_word(record: &Self::Record) -> u64;
}

/// Recognize a live key before any caller uses it to edit or access a node.
/// A recycled slot matches only its current incarnation.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures !same_owner ==> out == Err(TreeError::ForeignNode),
        out.is_ok() == (same_owner && store.records().contains_key(key)
            && incarnation(S::record_identity(&store.records()[key])) == requested),
        out.is_ok() ==> *out.unwrap() == store.records()[key],
        same_owner && out.is_err() ==> out == Err(TreeError::StaleNode),
    no_unwind
))]
pub(crate) fn resolve_record<S: HandleLookup>(store: &S, same_owner: bool, key: S::Key, requested: u64)
    -> Result<&S::Record, TreeError>
{
    if !same_owner { return Err(TreeError::ForeignNode); }
    match store.read_record(key) {
        Some(record) if incarnation(S::identity_word(record)) == requested => Ok(record),
        _ => Err(TreeError::StaleNode),
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait ParentModel {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait ParentModel {
    type Id: Copy;
    spec fn links(&self) -> Map<Self::Id, Option<Self::Id>>;
}
}

/// Read one live parent link and reject the node being moved.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait MoveParents: ParentModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        ensures out == if ancestor == moving {
            Err(TreeError::WouldCreateCycle)
        } else if self.links().contains_key(ancestor) {
            Ok(self.links()[ancestor])
        } else {
            Err(TreeError::StaleNode)
        },
        no_unwind
    ))]
    fn parent_for_move(&self, ancestor: Self::Id, moving: Self::Id) -> Result<Option<Self::Id>, TreeError>;
}

/// Verify that attaching under `parent` cannot create a cycle, without changing
/// any links. A malformed, nonterminating chain exhausts the live-node bound.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures complete_path(store.links(), path@, parent, live) ==>
        out == if path@.contains(moving) { Err(TreeError::WouldCreateCycle) } else { Ok(()) },
    no_unwind
))]
pub(crate) fn validate_ancestry<A: MoveParents>(
    store: &A, parent: A::Id, moving: A::Id, live: usize,
    #[cfg(verus_keep_ghost)] path: Ghost<Seq<A::Id>>,
) -> Result<(), TreeError> {
    let mut remaining = live;
    let mut ancestor = Some(parent);
    #[cfg(verus_keep_ghost)]
    let complete = path_is_complete(store, path, parent, live);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant remaining <= live, complete@ == complete_path(store.links(), path@, parent, live),
            complete@ ==> live - remaining <= path@.len(),
            complete@ ==> ancestor == ancestor_at(path@, live - remaining),
            complete@ ==> (forall |j: int| 0 <= j < live - remaining ==> #[trigger] path@[j] != moving),
        ensures complete@ ==> live - remaining == path@.len(),
            complete@ ==> (forall |j: int| 0 <= j < live - remaining ==> #[trigger] path@[j] != moving),
        decreases remaining,
    ))]
    while let Some(current) = ancestor {
        if remaining == 0 {
            #[cfg(verus_keep_ghost)]
            proof! { assert(!complete@); }
            return Err(TreeError::WouldCreateCycle);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            if complete@ {
                assert(store.links().contains_key(current));
                assert(store.links()[current] == ancestor_at(path@, live - remaining + 1));
            }
        }
        ancestor = match store.parent_for_move(current, moving) {
            Ok(parent) => parent,
            Err(err) => {
                #[cfg(verus_keep_ghost)]
                proof! { assert(complete@ ==> path@.contains(moving)); }
                return Err(err);
            }
        };
        remaining -= 1;
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(complete@ ==> !path@.contains(moving)); }
    Ok(())
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn ancestor_at<I>(path: Seq<I>, i: int) -> Option<I> {
    if i < path.len() { Some(path[i]) } else { None }
}

pub(crate) open spec fn complete_path<I>(
    links: Map<I, Option<I>>, path: Seq<I>, parent: I, live: usize,
) -> bool {
    &&& 0 < path.len() <= live
    &&& path[0] == parent
    &&& forall |i: int| 0 <= i < path.len() ==> {
        let node = #[trigger] path[i];
        links.contains_key(node) && links[node] == ancestor_at(path, i + 1)
    }
}

fn path_is_complete<A: MoveParents>(
    store: &A, path: Ghost<Seq<A::Id>>, parent: A::Id, live: usize,
) -> (complete: Ghost<bool>)
    ensures complete@ == complete_path(store.links(), path@, parent, live),
    no_unwind
{
    Ghost(complete_path(store.links(), path@, parent, live))
}

}
