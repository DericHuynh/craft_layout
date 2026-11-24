//! Exact in-place updates to the retained preorder records.
#[path = "../src/topology/state.rs"]
pub(crate) mod kernel;
#[path = "../src/topology/reconcile.rs"]
mod reconcile;
#[path = "../src/topology/tracked.rs"]
mod tracked;

use vstd::prelude::*;
use kernel::{PriorNode, PriorStyle};

verus! {

/// The production rewrite changes tickets for its exact prefix and no other IDs.
pub proof fn ticket_prefix_preserves_frame<I>(
    old: Map<I, u64>, nodes: Seq<PriorNode<I>>, first: u64, count: nat, id: I,
)
    requires
        count <= nodes.len(),
        forall |i: int| 0 <= i < nodes.len() ==>
            old.contains_key((#[trigger] nodes[i]).id),
    ensures
        kernel::ticket_prefix(old, nodes, first, count).dom() == old.dom(),
        old.contains_key(id) && !kernel::has_identity(nodes, count, id) ==>
            kernel::ticket_prefix(old, nodes, first, count)[id] == old[id],
    decreases count,
{
    if count > 0 {
        let last = count - 1;
        ticket_prefix_preserves_frame(old, nodes, first, last as nat, id);
        let prefix = kernel::ticket_prefix(old, nodes, first, last as nat);
        let updated = kernel::ticket_prefix(old, nodes, first, count);
        assert(updated == prefix.insert(nodes[last].id, (first + last) as u64));
        assert(old.contains_key(nodes[last].id));
        assert(updated.dom() =~= old.dom());
        if old.contains_key(id) && !kernel::has_identity(nodes, count, id) {
            assert(!kernel::has_identity(nodes, last as nat, id));
            assert(nodes[last].id != id) by {
                if nodes[last].id == id {
                    assert(exists |i: int| 0 <= i < count && (#[trigger] nodes[i]).id == id) by {
                        assert(0 <= last < count && nodes[last].id == id);
                    }
                }
            }
        }
    }
}

/// A previously written ticket survives later writes for other captured nodes.
pub proof fn ticket_prefix_restores_index<I>(
    old: Map<I, u64>, nodes: Seq<PriorNode<I>>, first: u64, count: nat, index: int,
)
    requires 0 <= index < count <= nodes.len(), kernel::unique_ids(nodes),
    ensures kernel::ticket_prefix(old, nodes, first, count)[nodes[index].id] == (first + index) as u64,
    decreases count,
{
    let last = count - 1;
    let prefix = kernel::ticket_prefix(old, nodes, first, last as nat);
    let updated = kernel::ticket_prefix(old, nodes, first, count);
    assert(updated == prefix.insert(nodes[last].id, (first + last) as u64));
    if index < last {
        ticket_prefix_restores_index(old, nodes, first, last as nat, index);
        assert(nodes[index].id != nodes[last].id);
    }
}

/// Once reconciliation establishes that the old preorder still describes the
/// live tree, repairing a region with potentially reset tickets is equivalent
/// to reissuing the full snapshot's tickets if the other tickets still match.
pub proof fn repaired_region_matches_full_write<I>(
    before: Map<I, u64>, nodes: Seq<PriorNode<I>>, first: u64, root: int,
)
    requires
        0 <= root < nodes.len(), root < nodes[root].end <= nodes.len(),
        0 < first, first as int + nodes.len() <= u64::MAX,
        kernel::unique_ids(nodes),
        forall |i: int| 0 <= i < nodes.len() ==>
            before.contains_key((#[trigger] nodes[i]).id),
        forall |i: int| 0 <= i < nodes.len() && (i < root || nodes[root].end <= i)
            ==> before[(#[trigger] nodes[i]).id] == (first + i) as u64,
    ensures
        kernel::ticket_prefix(
            before, nodes.subrange(root, nodes[root].end as int),
            (first + root) as u64, (nodes[root].end - root) as nat,
        ) == kernel::ticket_prefix(before, nodes, first, nodes.len()),
{
    let end = nodes[root].end as int;
    let region = nodes.subrange(root, end);
    let base = (first + root) as u64;
    let repaired = kernel::ticket_prefix(before, region, base, region.len());
    let full = kernel::ticket_prefix(before, nodes, first, nodes.len());
    assert forall |i: int, j: int| 0 <= i < j < region.len()
        implies (#[trigger] region[i]).id != (#[trigger] region[j]).id by {
        assert(region[i] == nodes[root + i]);
        assert(region[j] == nodes[root + j]);
    }
    assert forall |i: int| 0 <= i < region.len()
        implies before.contains_key((#[trigger] region[i]).id) by {
        assert(region[i] == nodes[root + i]);
    }
    ticket_prefix_preserves_frame(before, region, base, region.len(), nodes[root].id);
    ticket_prefix_preserves_frame(before, nodes, first, nodes.len(), nodes[root].id);
    assert forall |id: I| before.contains_key(id) implies #[trigger] repaired[id] == full[id] by {
        if kernel::has_identity(nodes, nodes.len(), id) {
            let i = choose |i: int| 0 <= i < nodes.len() && (#[trigger] nodes[i]).id == id;
            ticket_prefix_restores_index(before, nodes, first, nodes.len(), i);
            if root <= i < end {
                assert(region[i - root] == nodes[i]);
                ticket_prefix_restores_index(before, region, base, region.len(), i - root);
                assert((base as int + i - root) as u64 == (first as int + i) as u64);
            } else {
                assert(!kernel::has_identity(region, region.len(), id)) by {
                    if kernel::has_identity(region, region.len(), id) {
                        let j = choose |j: int| 0 <= j < region.len() && (#[trigger] region[j]).id == id;
                        assert(region[j] == nodes[root + j]);
                        assert(i != root + j);
                        assert(nodes[i].id != nodes[root + j].id);
                    }
                }
                ticket_prefix_preserves_frame(before, region, base, region.len(), id);
            }
        } else {
            assert(!kernel::has_identity(region, region.len(), id)) by {
                if kernel::has_identity(region, region.len(), id) {
                    let j = choose |j: int| 0 <= j < region.len() && (#[trigger] region[j]).id == id;
                    assert(exists |i: int| 0 <= i < nodes.len() && (#[trigger] nodes[i]).id == id) by {
                        assert(region[j] == nodes[root + j] && 0 <= root + j < nodes.len());
                    }
                }
            }
            ticket_prefix_preserves_frame(before, nodes, first, nodes.len(), id);
            ticket_prefix_preserves_frame(before, region, base, region.len(), id);
        }
    }
    assert(repaired =~= full);
}

pub open spec fn owner_count<I>(nodes: Seq<PriorNode<I>>, stop: nat, slot: usize) -> nat
    decreases stop,
{
    if stop == 0 { 0 }
    else {
        owner_count(nodes, (stop - 1) as nat, slot)
            + if nodes[stop - 1].style == slot { 1nat } else { 0nat }
    }
}

pub open spec fn valid_styles<I, P>(nodes: Seq<PriorNode<I>>, styles: Seq<PriorStyle<P>>) -> bool {
    &&& forall |i: int| 0 <= i < nodes.len() ==> (#[trigger] nodes[i]).style < styles.len()
    &&& forall |slot: int| 0 <= slot < styles.len() ==>
        0 < (#[trigger] styles[slot]).uses
        && styles[slot].uses == owner_count(nodes, nodes.len(), slot as usize)
}

proof fn count_updated_row<I>(nodes: Seq<PriorNode<I>>, index: int, row: PriorNode<I>, stop: nat, slot: usize)
    requires 0 <= index < nodes.len(), stop <= nodes.len(),
    ensures ({
        let lost = if index < stop && nodes[index].style == slot { 1nat } else { 0nat };
        let gained = if index < stop && row.style == slot { 1nat } else { 0nat };
        owner_count(nodes.update(index, row), stop, slot) + lost
            == owner_count(nodes, stop, slot) + gained
    }),
    decreases stop,
{
    if stop > 0 {
        count_updated_row(nodes, index, row, (stop - 1) as nat, slot);
        if index == stop - 1 {
            assert(nodes.update(index, row)[stop - 1] == row);
        } else {
            assert(nodes.update(index, row)[stop - 1] == nodes[stop - 1]);
        }
    }
}

proof fn count_unused_slot<I>(nodes: Seq<PriorNode<I>>, stop: nat, slot: usize)
    requires stop <= nodes.len(), forall |i: int| 0 <= i < stop ==> (#[trigger] nodes[i]).style != slot,
    ensures owner_count(nodes, stop, slot) == 0,
    decreases stop,
{
    if stop > 0 {
        count_unused_slot(nodes, (stop - 1) as nat, slot);
        assert(nodes[stop - 1].style != slot);
    }
}

proof fn count_has_owner<I>(nodes: Seq<PriorNode<I>>, stop: nat, owner: int, slot: usize)
    requires 0 <= owner < stop <= nodes.len(), nodes[owner].style == slot,
    ensures owner_count(nodes, stop, slot) > 0,
    decreases stop,
{
    if owner < stop - 1 {
        count_has_owner(nodes, (stop - 1) as nat, owner, slot);
    }
}

proof fn count_has_two_owners<I>(nodes: Seq<PriorNode<I>>, stop: nat, a: int, b: int, slot: usize)
    requires 0 <= a < b < stop <= nodes.len(), nodes[a].style == slot, nodes[b].style == slot,
    ensures owner_count(nodes, stop, slot) >= 2,
    decreases stop,
{
    if b == stop - 1 {
        count_has_owner(nodes, (stop - 1) as nat, a, slot);
    } else {
        count_has_two_owners(nodes, (stop - 1) as nat, a, b, slot);
    }
}

/// The physical update implemented by the production function changes one
/// logical style and maintains the exact ownership counts, even for a shared row.
pub proof fn preserving_style_update<I, P>(
    nodes: Seq<PriorNode<I>>, styles: Seq<PriorStyle<P>>, index: int, params: P,
)
    requires valid_styles(nodes, styles), 0 <= index < nodes.len(), styles.len() <= usize::MAX,
    ensures ({
        let (new_nodes, new_styles) = kernel::physical_style_update(nodes, styles, index, params);
        &&& valid_styles(new_nodes, new_styles)
        &&& new_nodes.len() == nodes.len()
        &&& forall |j: int| 0 <= j < nodes.len() ==>
            (#[trigger] new_nodes[j]).id == nodes[j].id
            && new_nodes[j].parent == nodes[j].parent && new_nodes[j].end == nodes[j].end
            && new_styles[new_nodes[j].style as int].params
                == if j == index { params } else { styles[nodes[j].style as int].params }
    }),
{
    let (new_nodes, new_styles) = kernel::physical_style_update(nodes, styles, index, params);
    let slot = nodes[index].style;
    let style = styles[slot as int];
    assert(slot < styles.len());
    if style.uses == 1 {
        assert(new_nodes == nodes);
        assert forall |j: int| 0 <= j < nodes.len()
            implies (#[trigger] new_nodes[j]).id == nodes[j].id
                && new_nodes[j].parent == nodes[j].parent && new_nodes[j].end == nodes[j].end
                && new_styles[new_nodes[j].style as int].params
                    == if j == index { params } else { styles[nodes[j].style as int].params } by {
            if j != index && nodes[j].style == slot {
                let (a, b) = if j < index { (j, index) } else { (index, j) };
                count_has_two_owners(nodes, nodes.len(), a, b, slot);
                assert(false);
            }
        }
        assert forall |s: int| 0 <= s < new_styles.len()
            implies 0 < (#[trigger] new_styles[s]).uses
                && new_styles[s].uses == owner_count(new_nodes, new_nodes.len(), s as usize) by {
            assert(new_styles[s].uses == styles[s].uses);
        }
    } else {
        let fresh = styles.len() as usize;
        let row = PriorNode { style: fresh, ..nodes[index] };
        assert(new_nodes == nodes.update(index, row));
        assert forall |j: int| 0 <= j < nodes.len()
            implies (#[trigger] new_nodes[j]).style < new_styles.len()
                && new_nodes[j].id == nodes[j].id
                && new_nodes[j].parent == nodes[j].parent && new_nodes[j].end == nodes[j].end
                && new_styles[new_nodes[j].style as int].params
                    == if j == index { params } else { styles[nodes[j].style as int].params } by {
            if j == index {
                assert(new_nodes[j] == row);
            } else {
                assert(new_nodes[j] == nodes[j]);
            }
        }
        assert forall |s: int| 0 <= s < new_styles.len()
            implies 0 < (#[trigger] new_styles[s]).uses
                && new_styles[s].uses == owner_count(new_nodes, new_nodes.len(), s as usize) by {
            count_updated_row(nodes, index, row, nodes.len(), s as usize);
            if s == fresh as int {
                assert forall |j: int| 0 <= j < nodes.len()
                    implies (#[trigger] nodes[j]).style != fresh by {
                    assert(nodes[j].style < styles.len());
                }
                count_unused_slot(nodes, nodes.len(), fresh);
            } else {
                assert(0 < styles[s].uses);
                assert(styles[s].uses == owner_count(nodes, nodes.len(), s as usize));
            }
        }
    }
}
}
