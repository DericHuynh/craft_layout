//! The parts of a retained topology snapshot that can be updated in place.
#![allow(unexpected_cfgs)]
use crate::vec_memory::{CapacityMemory, FallibleVecMemory, try_append};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use crate::structural::kernel::{advance_tickets, ticket_index, ticket_index_spec};
#[cfg(not(verus_keep_ghost))]
use crate::structural_changes::{advance_tickets, ticket_index};

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub const ROOT_PARENT: usize = usize::MAX;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[derive(Clone, Copy)]
pub struct PriorNode<I> {
    pub id: I,
    pub parent: usize,
    /// Exclusive end of this node's captured preorder subtree.
    pub end: usize,
    pub style: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[derive(Clone, Copy)]
pub struct PriorStyle<P> {
    pub params: P,
    pub uses: usize,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(nodes).len() < M::capacity(old(nodes)),
    ensures final(nodes)@ == old(nodes)@.push(PriorNode { id, parent, end, style }),
    no_unwind
))]
pub(crate) fn append_row<I: Copy, M: CapacityMemory>(
    nodes: &mut Vec<PriorNode<I>>, id: I, parent: usize, end: usize, style: usize,
) {
    M::push_reserved(nodes, PriorNode { id, parent, end, style });
}

/// The ticket offset names exactly one in-bounds row of this snapshot.
/// The caller still compares the recorded ID to the current live ID.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.is_some() == ticket_index_spec(first, nodes.len(), ticket).is_some(),
        if let Some((index, row)) = out {
            ticket_index_spec(first, nodes.len(), ticket) == Some(index)
                && index < nodes.len() && *row == nodes@[index as int]
        } else { true },
    no_unwind
))]
pub fn ticket_row<I>(nodes: &[PriorNode<I>], first: u64, ticket: u64) -> Option<(usize, &PriorNode<I>)> {
    let index = ticket_index(first, nodes.len(), ticket)?;
    Some((index, &nodes[index]))
}

/// Close this preorder subtree and resume at its parent's next child.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(resume =>
    requires 0 < index < old(nodes).len(), old(nodes)@[index as int].parent < index,
    ensures
        resume == (old(nodes)@[index as int].id, old(nodes)@[index as int].parent),
        resume.1 < index,
        final(nodes)@ == old(nodes)@.update(index as int,
            PriorNode { end: old(nodes).len(), ..old(nodes)@[index as int] }),
    no_unwind
))]
pub fn close_branch<I: Copy>(nodes: &mut [PriorNode<I>], index: usize) -> (I, usize) {
    let end = nodes.len();
    let row = &mut nodes[index];
    row.end = end;
    (row.id, row.parent)
}

/// The row is available only when both its retained indices are valid.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(slot =>
    ensures slot == if index < nodes.len()
        && nodes@[index as int].style < styles.len()
        && styles@[nodes@[index as int].style as int].uses > 0 {
            Some(nodes@[index as int].style)
        } else { None },
    no_unwind
))]
pub fn style_slot<I, P>(nodes: &[PriorNode<I>], styles: &[PriorStyle<P>], index: usize) -> Option<usize> {
    if index >= nodes.len() { return None; }
    let slot = nodes[index].style;
    if slot >= styles.len() || styles[slot].uses == 0 { return None; }
    Some(slot)
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(style =>
    ensures if let Some(row) = style {
        index < nodes.len() && nodes@[index as int].style < styles.len()
            && *row == styles@[nodes@[index as int].style as int] && row.uses > 0
    } else { true },
    no_unwind
))]
pub fn style_row<'a, I, P>(
    nodes: &[PriorNode<I>], styles: &'a [PriorStyle<P>], index: usize,
) -> Option<&'a PriorStyle<P>> {
    let slot = style_slot(nodes, styles, index)?;
    Some(&styles[slot])
}

/// Locate the first child and the exclusive end of a retained preorder row.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(range =>
    ensures range == match index {
        None => Some((0usize, 0usize)),
        Some(i) => if i < nodes.len() && i < nodes@[i as int].end <= nodes.len() {
            Some(((i + 1) as usize, nodes@[i as int].end))
        } else { None },
    },
    no_unwind
))]
pub fn child_range<I>(nodes: &[PriorNode<I>], index: Option<usize>) -> Option<(usize, usize)> {
    let Some(index) = index else { return Some((0, 0)); };
    if index >= nodes.len() { return None; }
    let end = nodes[index].end;
    if end <= index || end > nodes.len() { return None; }
    Some((index + 1, end))
}

/// A candidate child must end strictly after its own row without crossing
/// the exclusive end of the parent.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    ensures next == if expected >= end { Some(None) }
        else if expected < nodes.len() && expected < nodes@[expected as int].end <= end {
            Some(Some(nodes@[expected as int].end))
        } else { None },
    no_unwind
))]
pub fn following_child<I>(nodes: &[PriorNode<I>], expected: usize, end: usize) -> Option<Option<usize>> {
    if expected >= end { return Some(None); }
    if expected >= nodes.len() { return None; }
    let following = nodes[expected].end;
    if following <= expected || following > end { return None; }
    Some(Some(following))
}

/// Locate a candidate cached leaf without allowing a stale row index or ticket
/// overflow. Only the live identity and style comparison remain to the caller.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(leaf =>
    ensures match leaf {
        Some(Some((row, ticket))) =>
            expected < parent_end && expected < nodes.len() && !changed
                && *row == nodes@[expected as int] && row.end == expected + 1
                && first as int + expected == ticket,
        Some(None) => changed || expected >= parent_end
            || expected < nodes.len() && nodes@[expected as int].end != expected + 1,
        None => !changed && expected < parent_end && (expected >= nodes.len()
            || nodes@[expected as int].end == expected + 1 && first as int + expected > u64::MAX),
    },
    no_unwind
))]
pub fn expected_leaf<I>(
    nodes: &[PriorNode<I>], expected: usize, parent_end: usize, changed: bool, first: u64,
) -> Option<Option<(&PriorNode<I>, u64)>> {
    if changed || expected >= parent_end { return Some(None); }
    if expected >= nodes.len() { return None; }
    let entry = &nodes[expected];
    if entry.end != expected + 1 { return Some(None); }
    let ticket = advance_tickets(first, expected)?;
    Some(Some((entry, ticket)))
}

/// Record one style use, coalescing with the last row when the host reports
/// equal inputs. A failed reservation leaves the captured styles unchanged.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures match result {
        Some(slot) => slot < final(styles).len()
            && if matches_last && old(styles).len() > 0 {
                let last = old(styles).len() - 1;
                slot == last && final(styles)@ == old(styles)@.update(last, PriorStyle {
                    params: old(styles)@[last].params, uses: (old(styles)@[last].uses + 1) as usize,
                })
            } else {
                slot == old(styles).len() && final(styles)@ == old(styles)@.push(PriorStyle { params, uses: 1 })
            },
        None => final(styles)@ == old(styles)@,
    },
    no_unwind
))]
pub fn add_style<P: Copy, M: FallibleVecMemory>(
    styles: &mut Vec<PriorStyle<P>>, params: P, matches_last: bool,
) -> Option<usize> {
    let len = styles.len();
    if matches_last && len > 0 {
        let slot = len - 1;
        let uses = styles[slot].uses.checked_add(1)?;
        styles[slot].uses = uses;
        return Some(slot);
    }
    if try_append::<_, M>(styles, PriorStyle { params, uses: 1 }) { Some(len) } else { None }
}

/// The range and ticket arithmetic must be valid before replaying any ticket.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.is_some() == (root < nodes.len() && 0 < first
        && root < nodes@[root as int].end <= nodes.len()
        && first as int + nodes@[root as int].end <= u64::MAX),
        out.is_some() ==> out.unwrap() == nodes@[root as int].end,
    no_unwind
))]
pub fn restoration_end<I>(nodes: &[PriorNode<I>], root: usize, first: u64) -> Option<usize> {
    if root >= nodes.len() || first == 0 { return None; }
    let end = nodes[root].end;
    if root >= end || end > nodes.len() { return None; }
    first.checked_add(end as u64)?;
    Some(end)
}

#[cfg(verus_keep_ghost)]
verus! {
pub trait TicketModel {
    type Id: Copy;
    spec fn tickets(&self) -> Map<Self::Id, u64>;
}

pub open spec fn unique_ids<I>(nodes: Seq<PriorNode<I>>) -> bool {
    forall |i: int, j: int| 0 <= i < j < nodes.len() ==>
        (#[trigger] nodes[i]).id != (#[trigger] nodes[j]).id
}

pub open spec fn ticket_prefix<I>(old: Map<I, u64>, nodes: Seq<PriorNode<I>>, first: u64, count: nat)
    -> Map<I, u64>
    decreases count,
{
    if count == 0 { old }
    else {
        let i = count - 1;
        ticket_prefix(old, nodes, first, i as nat).insert(nodes[i].id, (first + i) as u64)
    }
}

pub open spec fn has_identity<I>(nodes: Seq<PriorNode<I>>, count: nat, id: I) -> bool {
    exists |i: int| 0 <= i < count && (#[trigger] nodes[i]).id == id
}

pub open spec fn physical_style_update<I, P>(
    nodes: Seq<PriorNode<I>>, styles: Seq<PriorStyle<P>>, index: int, params: P,
) -> (Seq<PriorNode<I>>, Seq<PriorStyle<P>>) {
    let node = nodes[index];
    let slot = node.style as int;
    let style = styles[slot];
    if style.uses == 1 {
        (nodes, styles.update(slot, PriorStyle { params, uses: 1 }))
    } else {
        let changed = PriorNode { style: styles.len() as usize, ..node };
        (
            nodes.update(index, changed),
            styles.update(slot, PriorStyle { uses: (style.uses - 1) as usize, ..style })
                .push(PriorStyle { params, uses: 1 }),
        )
    }
}
}

#[cfg(not(verus_keep_ghost))]
pub trait TicketModel {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub struct CapturePosition<I> {
    pub index: nat,
    pub end: nat,
    pub parent: Option<I>,
}

pub trait CaptureModel: TicketModel {
    spec fn positions(&self) -> Map<Self::Id, CapturePosition<Self::Id>>;
    spec fn capture_size(&self) -> nat;
}

pub open spec fn bounded_positions<W: CaptureModel + ?Sized>(source: &W) -> bool {
    forall |id: W::Id| #[trigger] source.positions().contains_key(id) ==> {
        let row = source.positions()[id];
        &&& source.tickets().contains_key(id)
        &&& row.index < row.end <= source.capture_size()
    }
}

fn saved_rows<I>(rows: &Vec<PriorNode<I>>) -> (snapshot: Ghost<Seq<PriorNode<I>>>)
    ensures snapshot@ == rows@,
    no_unwind
{
    Ghost(rows@)
}
}

#[cfg(not(verus_keep_ghost))]
pub trait CaptureModel: TicketModel {}

/// Host links are stable for a capture. Storage appends either reserve both
/// records or return failure; they cannot alter earlier captured rows.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait CaptureSource: CaptureModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires self.positions().contains_key(id),
        ensures if next.is_some() {
            let child = next.unwrap();
            &&& self.positions().contains_key(child)
            &&& self.positions()[child].index == self.positions()[id].index + 1
            &&& self.positions()[child].parent == Some(id)
        } else {
            self.positions()[id].end == self.positions()[id].index + 1
        },
        no_unwind
    ))]
    fn first_child_to_capture(&self, id: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires self.positions().contains_key(id),
        ensures if next.is_some() {
            let sibling = next.unwrap();
            &&& self.positions().contains_key(sibling)
            &&& self.positions()[sibling].index == self.positions()[id].end
            &&& self.positions()[sibling].parent == self.positions()[id].parent
        } else {
            self.positions()[id].parent.is_some() ==> {
                let parent = self.positions()[id].parent.unwrap();
                &&& self.positions().contains_key(parent)
                &&& self.positions()[parent].end == self.positions()[id].end
            }
        },
        no_unwind
    ))]
    fn following_sibling(&self, id: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(added =>
        requires old(self).tickets().contains_key(id),
        ensures
            final(self).tickets() == old(self).tickets(),
            final(self).positions() == old(self).positions(),
            final(self).capture_size() == old(self).capture_size(),
            added ==> final(nodes)@.len() == old(nodes)@.len() + 1
                && final(nodes)@.drop_last() == old(nodes)@
                && final(nodes)@.last().id == id
                && final(nodes)@.last().parent == parent
                && final(nodes)@.last().end == end,
            !added ==> final(nodes)@ == old(nodes)@,
        no_unwind
    ))]
    fn append(&mut self, nodes: &mut Vec<PriorNode<Self::Id>>, id: Self::Id, parent: usize, end: usize) -> bool;
}

/// Build the snapshot in preorder. Each row stores an earlier parent index,
/// which doubles as the continuation when an entire sibling list is consumed.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(captured =>
    requires
        old(nodes).len() == 0, bounded_positions(old(source)),
        old(source).positions().contains_key(root),
        old(source).positions()[root].index == 0,
        old(source).positions()[root].end == old(source).capture_size(),
    ensures final(source).tickets() == old(source).tickets(),
        captured ==> final(nodes).len() > 0 && final(nodes).len() == old(source).capture_size()
            && final(nodes)@[0].id == root
            && final(nodes)@[0].parent == ROOT_PARENT && final(nodes)@[0].end == final(nodes).len()
            && (forall |i: int| 0 <= i < final(nodes).len() ==>
                old(source).tickets().contains_key((#[trigger] final(nodes)@[i]).id)),
    no_unwind
))]
pub fn capture_subtree<W: CaptureSource + ?Sized>(source: &mut W, nodes: &mut Vec<PriorNode<W::Id>>, root: W::Id)
    -> bool
{
    if !source.append(nodes, root, ROOT_PARENT, 1) { return false; }
    let mut parent = 0;
    let mut next = source.first_child_to_capture(root);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            source.tickets() == old(source).tickets(),
            source.positions() == old(source).positions(),
            source.capture_size() == old(source).capture_size(),
            bounded_positions(source),
            source.positions()[root].end == source.capture_size(),
            parent < nodes.len() <= source.capture_size(),
            nodes@[0].id == root, nodes@[0].parent == ROOT_PARENT,
            if next.is_some() {
                let id = next.unwrap();
                &&& source.positions().contains_key(id)
                &&& source.positions()[id].index == nodes.len()
                &&& source.positions()[id].parent == Some(nodes@[parent as int].id)
            } else {
                source.positions()[nodes@[parent as int].id].end == nodes.len()
            },
            forall |i: int| 0 <= i < nodes.len() ==>
                source.positions().contains_key((#[trigger] nodes@[i]).id)
                && source.positions()[nodes@[i].id].index == i,
            forall |i: int| 0 < i < nodes.len() ==>
                (#[trigger] nodes@[i]).parent < i
                && source.positions()[nodes@[i].id].parent == Some(nodes@[nodes@[i].parent as int].id),
        decreases source.capture_size() - nodes.len(), parent,
    ))]
    loop {
        #[cfg(verus_keep_ghost)]
        let before = saved_rows(nodes);
        if let Some(id) = next {
            let index = nodes.len();
            let Some(end) = index.checked_add(1) else { return false; };
            if !source.append(nodes, id, parent, end) { return false; }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall |i: int| 0 <= i < nodes.len() implies
                    source.positions().contains_key((#[trigger] nodes@[i]).id)
                    && source.positions()[nodes@[i].id].index == i by {
                    if i < index { assert(nodes@[i] == before@[i]); }
                    else { assert(nodes@[i].id == id); }
                }
            }
            if let Some(first) = source.first_child_to_capture(id) {
                parent = index;
                next = Some(first);
            } else {
                next = source.following_sibling(id);
            }
        } else if parent != 0 {
            let (closed, enclosing) = close_branch(nodes.as_mut_slice(), parent);
            #[cfg(verus_keep_ghost)]
            proof! {
                assert forall |i: int| 0 <= i < nodes.len() implies
                    source.positions().contains_key((#[trigger] nodes@[i]).id)
                    && source.positions()[nodes@[i].id].index == i by {
                    assert(nodes@[i].id == before@[i].id);
                }
            }
            parent = enclosing;
            next = source.following_sibling(closed);
        } else {
            let end = nodes.len();
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(source.positions()[root].end == end);
                assert(end == old(source).capture_size());
            }
            nodes[0].end = end;
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(nodes.len() == end);
                assert(nodes@[0].id == root && nodes@[0].parent == ROOT_PARENT && nodes@[0].end == end);
                assert(nodes@.len() == end);
                assert forall |i: int| 0 <= i < nodes.len() implies
                    old(source).tickets().contains_key((#[trigger] nodes@[i]).id) by {
                    assert(nodes@[i].id == before@[i].id);
                    assert(source.positions().contains_key(before@[i].id));
                }
            }
            return true;
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait TicketWriter: TicketModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).tickets().contains_key(id),
        ensures final(self).tickets() == old(self).tickets().insert(id, ticket),
        no_unwind
    ))]
    fn write_ticket(&mut self, id: Self::Id, ticket: u64);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        0 < first, first as int + nodes.len() <= u64::MAX,
        forall |i: int| 0 <= i < nodes.len() ==>
            old(writer).tickets().contains_key((#[trigger] nodes@[i]).id),
    ensures final(writer).tickets() == ticket_prefix(old(writer).tickets(), nodes@, first, nodes.len() as nat),
    no_unwind
))]
pub fn restore_tickets<W: TicketWriter + ?Sized>(writer: &mut W, nodes: &[PriorNode<W::Id>], first: u64) {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            index <= nodes.len(), first as int + nodes.len() <= u64::MAX,
            forall |i: int| 0 <= i < nodes.len() ==>
                old(writer).tickets().contains_key((#[trigger] nodes@[i]).id),
            writer.tickets() == ticket_prefix(old(writer).tickets(), nodes@, first, index as nat),
            writer.tickets().dom() == old(writer).tickets().dom(),
        decreases nodes.len() - index,
    ))]
    while index < nodes.len() {
        let node = &nodes[index];
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(nodes@[index as int].id == node.id);
        }
        writer.write_ticket(node.id, first + index as u64);
        #[cfg(verus_keep_ghost)]
        proof! {
            let old_prefix = ticket_prefix(old(writer).tickets(), nodes@, first, index as nat);
            assert(ticket_prefix(old(writer).tickets(), nodes@, first, (index + 1) as nat) ==
                old_prefix.insert(node.id, (first as int + index) as u64));
            assert(writer.tickets().dom() =~= old(writer).tickets().dom());
        }
        index += 1;
    }
}

/// A write to a retained record may target only an ID from the live tree walk.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait LiveTicketWriter: TicketWriter {
    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires self.tickets().contains_key(root), self.tickets().contains_key(id),
        ensures if let Some(next) = next { self.tickets().contains_key(next) } else { true },
        no_unwind
    ))]
    fn next_in_region(&self, root: Self::Id, id: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(matched => ensures matched == (a == b), no_unwind))]
    fn same_id(&self, a: Self::Id, b: Self::Id) -> bool;
}

/// Match the recorded preorder against the live subtree as tickets are restored.
/// If the snapshot is stale, stop before using a retained record's ID to write.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(restored =>
    requires old(writer).tickets().contains_key(live_root),
    ensures final(writer).tickets().dom() == old(writer).tickets().dom(),
        restored ==> root < nodes.len() && root < nodes@[root as int].end <= nodes.len()
            && ({
                let end = nodes@[root as int].end as int;
                let region = nodes@.subrange(root as int, end);
                &&& forall |i: int| 0 <= i < region.len() ==>
                    old(writer).tickets().contains_key((#[trigger] region[i]).id)
                &&& final(writer).tickets() == ticket_prefix(
                    old(writer).tickets(), region,
                    (first as int + root) as u64, region.len(),
                )
            }),
    no_unwind
))]
pub fn restore_region<W: LiveTicketWriter + ?Sized>(
    writer: &mut W, nodes: &[PriorNode<W::Id>], root: usize, first: u64, live_root: W::Id,
) -> bool {
    let Some(end) = restoration_end(nodes, root, first) else { return false; };
    let (prefix, _) = nodes.split_at(end);
    let (_, region) = prefix.split_at(root);
    let base = first + root as u64;
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(region@ =~= nodes@.subrange(root as int, end as int));
    }
    let mut live = Some(live_root);
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            index <= region.len(), base as int + region.len() <= u64::MAX,
            writer.tickets().dom() == old(writer).tickets().dom(),
            writer.tickets().contains_key(live_root),
            live.is_some() ==> writer.tickets().contains_key(live.unwrap()),
            forall |i: int| 0 <= i < index ==>
                old(writer).tickets().contains_key((#[trigger] region@[i]).id),
            writer.tickets() == ticket_prefix(old(writer).tickets(), region@, base, index as nat),
        decreases region.len() - index,
    ))]
    while index < region.len() {
        let Some(id) = live else { return false; };
        let recorded = region[index].id;
        if !writer.same_id(id, recorded) { return false; }
        writer.write_ticket(id, base + index as u64);
        #[cfg(verus_keep_ghost)]
        proof! {
            let old_prefix = ticket_prefix(old(writer).tickets(), region@, base, index as nat);
            assert(ticket_prefix(old(writer).tickets(), region@, base, (index + 1) as nat) ==
                old_prefix.insert(recorded, (base as int + index) as u64));
            assert(writer.tickets().dom() =~= old(writer).tickets().dom());
        }
        live = writer.next_in_region(live_root, id);
        index += 1;
    }
    live.is_none()
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result ==>
        index < old(nodes).len() && old(nodes)@[index as int].style < old(styles).len()
        && old(styles)@[old(nodes)@[index as int].style as int].uses > 0
        && (final(nodes)@, final(styles)@) == physical_style_update(old(nodes)@, old(styles)@, index as int, params),
        !result ==> final(nodes)@ == old(nodes)@ && final(styles)@ == old(styles)@,
    no_unwind
))]
pub fn update_style<I, P: Copy, M: FallibleVecMemory>(
    nodes: &mut [PriorNode<I>], styles: &mut Vec<PriorStyle<P>>, index: usize, params: P,
) -> bool {
    let Some(slot) = style_slot(nodes, styles.as_slice(), index) else { return false; };
    if styles[slot].uses == 1 {
        styles[slot].params = params;
    } else {
        let next = styles.len();
        if !try_append::<_, M>(styles, PriorStyle { params, uses: 1 }) { return false; }
        styles[slot].uses -= 1;
        nodes[index].style = next;
        #[cfg(verus_keep_ghost)]
        proof! {
            let entry = PriorStyle { uses: (old(styles)@[slot as int].uses - 1) as usize, ..old(styles)@[slot as int] };
            assert(styles@ =~= old(styles)@.update(slot as int, entry).push(PriorStyle { params, uses: 1 }));
        }
    }
    true
}
