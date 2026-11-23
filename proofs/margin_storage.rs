//! Reindex retained collapsed margins without changing values or allocating
//! per-node metadata. The adapter's visible traversal supplies live indices.
use vstd::prelude::*;
#[path = "../src/margin_storage.rs"]
mod kernel;

verus! {

pub open spec fn packed<T>(old: Seq<T>, owners: Seq<Option<usize>>) -> Seq<T>
    decreases owners.len(),
{
    if owners.len() == 0 { Seq::empty() } else {
        let prior = packed(old, owners.drop_last());
        if let Some(index) = owners.last() { prior.push(old[index as int]) } else { prior }
    }
}

pub open spec fn remapped<T>(old: Seq<T>, owners: Seq<Option<usize>>, cursor: int) -> Option<int> {
    if owners[cursor].is_some() { Some(packed(old, owners.take(cursor)).len() as int) } else { None }
}

/// The append-and-remap operation preserves each observed nested margin for an
/// arbitrary visible order. Reading an implicit margin still uses the default.
pub proof fn compact_keeps_observations<T>(old: Seq<T>, owners: Seq<Option<usize>>, cursor: int)
    requires 0 <= cursor < owners.len(),
        forall |i:int| 0 <= i < owners.len() && (#[trigger] owners[i]).is_some()
            ==> owners[i].unwrap() < old.len(),
    ensures ({
        let cache = packed(old, owners);
        match remapped(old, owners, cursor) {
            Some(new_index) => {
                &&& owners[cursor].is_some()
                &&& 0 <= new_index < cache.len()
                &&& cache[new_index] == old[owners[cursor].unwrap() as int]
            },
            None => owners[cursor].is_none(),
        }
    }),
    decreases owners.len(),
{
    let prefix = owners.drop_last();
    if cursor < prefix.len() {
        compact_keeps_observations(old, prefix, cursor);
        assert(prefix.take(cursor) =~= owners.take(cursor));
    } else {
        assert(prefix =~= owners.take(cursor));
        assert(owners.last() == owners[cursor]);
    }
}

/// At most one explicit margin belongs to each visible block. When the solver
/// compacts, this bounds the new arena by the live block count.
pub proof fn compact_length<T>(old: Seq<T>, owners: Seq<Option<usize>>)
    ensures packed(old, owners).len() <= owners.len(),
    decreases owners.len(),
{
    if owners.len() > 0 {
        compact_length(old, owners.drop_last());
    }
}
}
