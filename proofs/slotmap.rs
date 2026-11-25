//! Physical-state proof for the SlotMap operations used by the owned tree.
//! The source binding is checked by slotmap_native.py against SlotMap 1.1.1.
#![feature(proc_macro_hygiene)]

use vstd::prelude::*;

verus! {

pub struct Slot<V> {
    pub version: u32,
    pub value: Option<V>,
    pub next_free: int,
}

// `vacancies` is a ghost enumeration of the dependency's singly linked list.
pub struct Arena<V> {
    pub slots: Seq<Slot<V>>,
    pub free_head: int,
    pub live: nat,
    pub capacity: usize,
    pub vacancies: Seq<int>,
}

pub struct Key {
    pub index: u32,
    pub version: u32,
}

pub open spec fn pointer(chain: Seq<int>, i: int, end: int) -> int {
    if i < chain.len() { chain[i] } else { end }
}

pub open spec fn occupied(version: u32) -> bool {
    version & 1 == 1
}

pub open spec fn valid<V>(arena: Arena<V>) -> bool {
    let slots = arena.slots;
    let vacancies = arena.vacancies;
    &&& 1 <= slots.len() <= arena.capacity && slots.len() <= u32::MAX
    &&& slots[0] == Slot::<V> { version: 0, value: None, next_free: 0 }
    &&& arena.live + vacancies.len() + 1 == slots.len()
    &&& arena.free_head == pointer(vacancies, 0, slots.len() as int)
    &&& vacancies.no_duplicates()
    &&& forall|j: int| 0 <= j < vacancies.len() ==> {
        let ix = #[trigger] vacancies[j];
        &&& 0 < ix < slots.len()
        &&& slots[ix].next_free == pointer(vacancies, j + 1, slots.len() as int)
    }
    &&& forall|i: int| 0 < i < slots.len() ==> {
        let slot = #[trigger] slots[i];
        &&& slot.value.is_some() == occupied(slot.version)
        &&& slot.value.is_none() == vacancies.contains(i)
    }
}

pub open spec fn at<V>(arena: Arena<V>, key: Key) -> Option<V> {
    if 0 <= key.index < arena.slots.len()
        && arena.slots[key.index as int].version == key.version
        && occupied(key.version) {
        arena.slots[key.index as int].value
    } else { None }
}

pub open spec fn new<V>(capacity: usize) -> Arena<V> {
    Arena {
        slots: seq![Slot::<V> { version: 0, value: None, next_free: 0 }],
        free_head: 1,
        live: 0,
        capacity,
        vacancies: Seq::empty(),
    }
}

pub proof fn new_preserves_invariants<V>(capacity: usize)
    requires capacity > 0,
    ensures valid(new::<V>(capacity)),
{}

// `Vec::try_reserve` preserves its values and succeeds only with at least
// this many physical slots. The return is a mathematical usize-sized value.
pub open spec fn reserve_needed<V>(arena: Arena<V>, additional: usize) -> int {
    vstd::math::max(0, arena.live + additional - (arena.slots.len() - 1))
}

pub proof fn reserve_preserves_invariants<V>(arena: Arena<V>, additional: usize, actual_capacity: usize)
    requires valid(arena), arena.live + additional < u32::MAX,
        actual_capacity >= arena.slots.len() + reserve_needed(arena, additional),
    ensures
        valid(Arena { capacity: actual_capacity, ..arena }),
        arena.live + additional < actual_capacity,
        arena.slots.len() + reserve_needed(arena, additional) <= usize::MAX,
{}

pub open spec fn reused<V>(arena: Arena<V>) -> bool {
    arena.free_head < arena.slots.len()
}

pub open spec fn insertion_key<V>(arena: Arena<V>) -> Key {
    if reused(arena) {
        Key { index: arena.free_head as u32, version: arena.slots[arena.free_head].version | 1 }
    } else {
        Key { index: arena.slots.len() as u32, version: 1 }
    }
}

pub open spec fn insert<V>(arena: Arena<V>, value: V) -> Arena<V> {
    let key = insertion_key(arena);
    let slot = Slot { version: key.version, value: Some(value), next_free: 0 };
    if reused(arena) {
        Arena {
            slots: arena.slots.update(arena.free_head, slot),
            free_head: arena.slots[arena.free_head].next_free,
            live: arena.live + 1,
            vacancies: arena.vacancies.drop_first(),
            ..arena
        }
    } else {
        Arena {
            slots: arena.slots.push(slot),
            free_head: key.index as int + 1,
            live: arena.live + 1,
            ..arena
        }
    }
}

proof fn vacancy_uses_head(chain: Seq<int>, index: int)
    requires chain.len() > 0, chain.no_duplicates(),
    ensures chain.drop_first().contains(index) == (chain.contains(index) && index != chain[0]),
{
    let tail = chain.drop_first();
    if chain.contains(index) {
        let j = choose |j: int| 0 <= j < chain.len() && chain[j] == index;
        if j != 0 { assert(tail[j-1] == index); }
    }
    if tail.contains(index) {
        let j = choose |j: int| 0 <= j < tail.len() && tail[j] == index;
        assert(chain[j+1] == index);
        assert(chain[j+1] != chain[0]);
    }
}

pub proof fn insert_preserves_invariants<V>(arena: Arena<V>, value: V)
    requires valid(arena), arena.live + 1 < u32::MAX, arena.live + 1 < arena.capacity,
    ensures valid(insert(arena, value)),
        occupied(insertion_key(arena).version),
        !reused(arena) ==> arena.slots.len() < u32::MAX && arena.slots.len() < arena.capacity,
        at(arena, insertion_key(arena)).is_none(),
        forall|key: Key| #[trigger] at(insert(arena, value), key) ==
            if key == insertion_key(arena) { Some(value) } else { at(arena, key) },
{
    let saved = insert(arena, value);
    let old = arena.slots;
    let chain = arena.vacancies;
    let index = arena.free_head;
    let key = insertion_key(arena);
    if reused(arena) {
        assert(chain.len() > 0 && index == chain[0]);
        assert(0 < index < old.len());
        assert(key.index as int == index);
        assert(chain.contains(index));
        assert(old[index].value.is_none());
        let version = old[index].version;
        assert((version | 1) & 1 == 1) by(bit_vector);
        let tail = saved.vacancies;
        assert(saved.slots[0] == old[0]);
        assert(saved.free_head == pointer(tail, 0, old.len() as int)) by {
            if tail.len() > 0 { assert(tail[0] == chain[1]); }
        }
        assert(tail.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < j < tail.len() implies tail[i] != tail[j] by {
                assert(tail[i] == chain[i+1] && tail[j] == chain[j+1]);
            }
        }
        assert forall|j: int| 0 <= j < tail.len() implies {
            let ix = #[trigger] tail[j];
            &&& 0 < ix < saved.slots.len()
            &&& saved.slots[ix].next_free == pointer(tail, j+1, saved.slots.len() as int)
        } by {
            let ix = tail[j];
            assert(ix == chain[j+1]);
            assert(ix != index);
            if j+1 < tail.len() { assert(tail[j+1] == chain[j+2]); }
        }
        assert forall|i: int| 0 < i < saved.slots.len() implies {
            let s = #[trigger] saved.slots[i];
            &&& s.value.is_some() == occupied(s.version)
            &&& s.value.is_none() == tail.contains(i)
        } by { vacancy_uses_head(chain, i); }
    } else {
        assert(chain.len() == 0) by {
            if chain.len() > 0 { assert(0 < chain[0] < old.len()); }
        }
        assert(arena.live + 1 == old.len());
        assert(key.index == old.len());
        assert(key.version == 1u32);
        assert(1u32 & 1u32 == 1u32) by(bit_vector);
        assert forall|i: int| 0 < i < saved.slots.len() implies {
            let s = #[trigger] saved.slots[i];
            &&& s.value.is_some() == occupied(s.version)
            &&& s.value.is_none() == saved.vacancies.contains(i)
        } by {
            if i != old.len() { assert(old[i] == saved.slots[i]); }
        }
    }
    assert(valid(saved));
    assert forall|lookup: Key| #[trigger] at(saved, lookup) ==
        (if lookup == key { Some(value) } else { at(arena, lookup) }) by {
        if lookup.index < old.len() && lookup.index != key.index {
            assert(saved.slots[lookup.index as int] == old[lookup.index as int]);
        }
    }
}

pub open spec fn after_removal<V>(arena: Arena<V>, key: Key) -> Arena<V> {
    if at(arena, key).is_some() {
        Arena {
            slots: arena.slots.update(key.index as int, Slot {
                version: key.version.wrapping_add(1), value: None, next_free: arena.free_head,
            }),
            free_head: key.index as int,
            live: (arena.live - 1) as nat,
            vacancies: seq![key.index as int] + arena.vacancies,
            ..arena
        }
    } else { arena }
}

proof fn vacancy_count_less_than_slots(chain: Seq<int>, slots: nat)
    requires chain.no_duplicates(), forall |i: int| 0 <= i < chain.len() ==> 0 < #[trigger] chain[i] < slots,
        exists |index: int| 0 < index < slots && !chain.contains(index),
    ensures chain.len() + 1 < slots,
{
    let missing = choose |index: int| 0 < index < slots && !chain.contains(index);
    let free_set = chain.to_set();
    chain.unique_seq_to_set();
    let known = free_set.insert(missing).insert(0);
    let range = vstd::set_lib::set_int_range(0, slots as int);
    assert(known.subset_of(range)) by {
        assert forall |i: int| known.contains(i) implies range.contains(i) by {
            if i != 0 && i != missing {
                assert(chain.contains(i));
                let at = choose |j: int| 0 <= j < chain.len() && chain[j] == i;
                assert(0 < chain[at] < slots);
            }
        }
    }
    vstd::set_lib::lemma_len_subset(known, range);
}

proof fn prepend_vacancy_properties(chain: Seq<int>, first: int)
    requires chain.no_duplicates(), !chain.contains(first),
    ensures (seq![first] + chain).no_duplicates(),
        forall|i: int| (#[trigger] (seq![first] + chain).contains(i)) == (i == first || chain.contains(i)),
{
    let front = seq![first];
    assert forall|i: int, j: int| 0 <= i < front.len() && 0 <= j < chain.len() implies front[i] != chain[j] by {
        assert(front[i] == first);
        assert(chain.contains(chain[j]));
    }
    vstd::seq_lib::lemma_no_dup_in_concat(front, chain);
    let head = front + chain;
    assert forall|i: int| #[trigger] head.contains(i) == (i == first || chain.contains(i)) by {
        if head.contains(i) {
            let at = choose |j: int| 0 <= j < head.len() && head[j] == i;
            if at == 0 { assert(i == first); } else { assert(chain[at - 1] == i); }
        }
        if i == first { assert(head[0] == i); }
        if chain.contains(i) {
            let at = choose |j: int| 0 <= j < chain.len() && chain[j] == i;
            assert(head[at + 1] == i);
        }
    }
}

proof fn relink_removed_slot<V>(arena: Arena<V>, key: Key)
    requires valid(arena), at(arena, key).is_some(), 0 < key.index,
        !arena.vacancies.contains(key.index as int),
    ensures ({
        let after = after_removal(arena, key);
        let head = after.vacancies;
        forall|j: int| 0 <= j < head.len() ==> {
            let ix = #[trigger] head[j];
            &&& 0 < ix < after.slots.len()
            &&& after.slots[ix].next_free == pointer(head, j+1, after.slots.len() as int)
        }
    }),
{
    let index = key.index as int;
    let chain = arena.vacancies;
    let after = after_removal(arena, key);
    let head = after.vacancies;
    assert forall|j: int| 0 <= j < head.len() implies {
        let ix = #[trigger] head[j];
        &&& 0 < ix < after.slots.len()
        &&& after.slots[ix].next_free == pointer(head, j+1, after.slots.len() as int)
    } by {
        let ix = head[j];
        if j == 0 {
            assert(ix == index);
            if chain.len() > 0 { assert(head[1] == chain[0]); }
        } else {
            assert(ix == chain[j-1]);
            assert(chain.contains(ix));
            assert(ix != index);
            if j+1 < head.len() { assert(head[j+1] == chain[j]); }
        }
    }
}

proof fn removed_slot_occupancy<V>(arena: Arena<V>, key: Key)
    requires valid(arena), at(arena, key).is_some(), occupied(key.version), !arena.vacancies.contains(key.index as int),
    ensures ({
        let after = after_removal(arena, key);
        let head = after.vacancies;
        forall|i: int| 0 < i < after.slots.len() ==> {
            let slot = #[trigger] after.slots[i];
            &&& slot.value.is_some() == occupied(slot.version)
            &&& slot.value.is_none() == head.contains(i)
        }
    }),
{
    let index = key.index as int;
    let old = arena.slots;
    let chain = arena.vacancies;
    let after = after_removal(arena, key);
    let head = after.vacancies;
    let version = key.version;
    assert(version.wrapping_add(1) & 1 == 0) by(bit_vector) requires version & 1 == 1;
    prepend_vacancy_properties(chain, index);
    assert forall|i: int| 0 < i < after.slots.len() implies {
        let slot = #[trigger] after.slots[i];
        &&& slot.value.is_some() == occupied(slot.version)
        &&& slot.value.is_none() == head.contains(i)
    } by {
        assert(head.contains(i) == (i == index || chain.contains(i)));
        if i != index { assert(old[i] == after.slots[i]); }
    }
}

pub proof fn remove_preserves_invariants<V>(arena: Arena<V>, key: Key)
    requires valid(arena), occupied(key.version),
    ensures valid(after_removal(arena, key)),
        at(arena, key).is_some() ==> arena.live > 0 && 0 < key.index < arena.slots.len(),
        forall|lookup: Key| #[trigger] at(after_removal(arena, key), lookup) ==
            if key == lookup { None } else { at(arena, lookup) },
{
    if at(arena, key).is_some() {
        let index = key.index as int;
        let old = arena.slots;
        let chain = arena.vacancies;
        let after = after_removal(arena, key);
        assert(0 < index < old.len());
        assert(!chain.contains(index));
        assert(exists |i: int| 0 < i < old.len() && !chain.contains(i));
        vacancy_count_less_than_slots(chain, old.len());
        assert(arena.live > 0);
        prepend_vacancy_properties(chain, index);
        relink_removed_slot(arena, key);
        removed_slot_occupancy(arena, key);
        assert(valid(after));
        assert forall|lookup: Key| #[trigger] at(after, lookup) ==
            (if key == lookup { None } else { at(arena, lookup) }) by {
            if lookup.index < old.len() && lookup.index != key.index {
                assert(after.slots[lookup.index as int] == old[lookup.index as int]);
            }
        }
    }
}

// The checked lookup tests the physical index and generation. A matched
// generated key denotes the initialized member of SlotMap's union.
pub proof fn matching_key_reads_initialized_value<V>(arena: Arena<V>, key: Key)
    requires valid(arena), occupied(key.version),
        key.index < arena.slots.len(), arena.slots[key.index as int].version == key.version,
    ensures at(arena, key).is_some(),
        !arena.vacancies.contains(key.index as int),
{
    assert(0u32 & 1u32 == 0u32) by(bit_vector);
    assert(arena.slots[0].version == 0);
    assert(key.index > 0);
    assert(arena.slots[key.index as int].value.is_some());
}

/// A removed context can always fit in an exact reservation by byte size.
/// The initial arena already held the corresponding slots at the larger stride.
pub proof fn retired_value_fits<V>(
    initial: Arena<V>, remaining: Arena<V>, retired: usize, value_bytes: usize, slot_bytes: usize,
)
    requires
        valid(initial),
        retired + remaining.live == initial.live,
        remaining.live > 0,
        value_bytes <= slot_bytes,
        initial.capacity * slot_bytes <= isize::MAX,
    ensures
        retired + 1 < u32::MAX,
        (retired + 1) * value_bytes <= isize::MAX,
{
    let count = retired as int + 1;
    let capacity = initial.capacity as int;
    let item = value_bytes as int;
    let slot = slot_bytes as int;
    assert(0 < count <= capacity);
    assert(count * item <= capacity * slot) by(nonlinear_arith)
        requires 0 < count <= capacity, 0 <= item <= slot;
}

pub open spec fn write<V>(arena: Arena<V>, key: Key, value: V) -> Arena<V> {
    let index = key.index as int;
    if at(arena, key).is_some() {
        Arena { slots: arena.slots.update(index, Slot { value: Some(value), ..arena.slots[index] }), ..arena }
    } else { arena }
}

// A write through `get_mut` changes the initialized payload only. The borrow
// bars a second edit to the map while the reference is in use.
pub proof fn mutable_lookup_preserves_invariants<V>(arena: Arena<V>, key: Key, value: V)
    requires valid(arena), occupied(key.version),
    ensures valid(write(arena, key, value)),
        forall|lookup: Key| #[trigger] at(write(arena, key, value), lookup) ==
            if key == lookup && at(arena, key).is_some() { Some(value) } else { at(arena, lookup) },
{
    if at(arena, key).is_some() {
        matching_key_reads_initialized_value(arena, key);
        let next = write(arena, key, value);
        let index = key.index as int;
        let old = arena.slots;
        let vacancies = arena.vacancies;
        assert(0 < index < old.len());
        assert forall|i: int| 0 < i < old.len() implies {
            let slot = #[trigger] next.slots[i];
            &&& slot.version == old[i].version
            &&& slot.next_free == old[i].next_free
            &&& slot.value.is_some() == old[i].value.is_some()
        } by {};
        assert forall|j: int| 0 <= j < vacancies.len() implies {
            let ix = #[trigger] vacancies[j];
            &&& 0 < ix < next.slots.len()
            &&& next.slots[ix].next_free == pointer(vacancies, j + 1, next.slots.len() as int)
        } by {};
        assert(valid(next));
        assert forall|lookup: Key| #[trigger] at(next, lookup) ==
            (if lookup == key { Some(value) } else { at(arena, lookup) }) by {
            if lookup.index < old.len() && lookup.index != key.index {
                assert(next.slots[lookup.index as int] == old[lookup.index as int]);
            }
        }
    }
}

pub open spec fn slot_clone<V>(slot: Slot<V>, index: int, duplicated: spec_fn(int, V) -> V) -> Slot<V> {
    Slot { value: match slot.value { Some(value) => Some(duplicated(index, value)), None => None }, ..slot }
}

pub open spec fn cloned<V>(arena: Arena<V>, capacity: usize, duplicated: spec_fn(int, V) -> V) -> Arena<V> {
    Arena { slots: arena.slots.map(|i: int, slot: Slot<V>| slot_clone(slot, i, duplicated)), capacity, ..arena }
}

pub proof fn clone_preserves_invariants<V>(arena: Arena<V>, capacity: usize, duplicated: spec_fn(int, V) -> V)
    requires valid(arena), arena.slots.len() <= capacity,
    ensures valid(cloned(arena, capacity, duplicated)),
        forall|key: Key| #[trigger] at(cloned(arena, capacity, duplicated), key) ==
            match at(arena, key) { Some(value) => Some(duplicated(key.index as int, value)), None => None },
{
    let next = cloned(arena, capacity, duplicated);
    let vacancies = arena.vacancies;
    assert forall|j: int| 0 <= j < vacancies.len() implies {
        let ix = #[trigger] vacancies[j];
        &&& 0 < ix < next.slots.len()
        &&& next.slots[ix].next_free == pointer(vacancies, j + 1, next.slots.len() as int)
    } by {};
    assert(valid(next));
}

pub open spec fn entry<V>(contents: Map<Key, V>, key: Key) -> Option<V> {
    if contents.contains_key(key) { Some(contents[key]) } else { None }
}

pub open spec fn describes<V>(arena: Arena<V>, contents: Map<Key, V>) -> bool {
    forall|key: Key| #[trigger] entry(contents, key) == at(arena, key)
}

pub proof fn new_refines_empty_entries<V>(capacity: usize)
    requires capacity > 0,
    ensures valid(new::<V>(capacity)), describes(new::<V>(capacity), Map::<Key, V>::empty()),
{
    new_preserves_invariants::<V>(capacity);
    let arena = new::<V>(capacity);
    let empty = Map::<Key, V>::empty();
    assert(0u32 & 1u32 == 0u32) by(bit_vector);
    assert forall|key: Key| #[trigger] entry(empty, key) == at(arena, key) by {};
}

pub proof fn insert_refines_entries<V>(arena: Arena<V>, value: V, contents: Map<Key, V>)
    requires valid(arena), describes(arena, contents),
        arena.live + 1 < u32::MAX, arena.live + 1 < arena.capacity,
    ensures !contents.contains_key(insertion_key(arena)),
        describes(insert(arena, value), contents.insert(insertion_key(arena), value)),
{
    insert_preserves_invariants(arena, value);
    let new_key = insertion_key(arena);
    assert(entry(contents, new_key).is_none());
    let inserted = contents.insert(new_key, value);
    assert forall|key: Key| #[trigger] entry(inserted, key) == at(insert(arena, value), key) by {
        assert(entry(contents, key) == at(arena, key));
        assert(at(insert(arena, value), key) == if key == new_key { Some(value) } else { at(arena, key) });
    }
}

pub proof fn remove_refines_entries<V>(arena: Arena<V>, key: Key, contents: Map<Key, V>)
    requires valid(arena), describes(arena, contents), occupied(key.version),
    ensures describes(after_removal(arena, key), contents.remove(key)),
{
    remove_preserves_invariants(arena, key);
    let removed = contents.remove(key);
    assert forall|lookup: Key| #[trigger] entry(removed, lookup) == at(after_removal(arena, key), lookup) by {
        assert(entry(contents, lookup) == at(arena, lookup));
        assert(at(after_removal(arena, key), lookup) == if lookup == key { None } else { at(arena, lookup) });
    }
}

pub proof fn write_refines_entries<V>(arena: Arena<V>, key: Key, value: V, contents: Map<Key, V>)
    requires valid(arena), describes(arena, contents), occupied(key.version),
    ensures describes(write(arena, key, value), if contents.contains_key(key) { contents.insert(key, value) } else { contents }),
{
    mutable_lookup_preserves_invariants(arena, key, value);
    assert(entry(contents, key) == at(arena, key));
    let updated = if contents.contains_key(key) { contents.insert(key, value) } else { contents };
    assert forall|lookup: Key| #[trigger] entry(updated, lookup) == at(write(arena, key, value), lookup) by {
        assert(entry(contents, lookup) == at(arena, lookup));
        assert(at(write(arena, key, value), lookup) ==
            if lookup == key && at(arena, key).is_some() { Some(value) } else { at(arena, lookup) });
    }
}

} // verus!
