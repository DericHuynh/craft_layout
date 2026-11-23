//! The parts of a retained topology snapshot that can be updated in place.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug))]
pub struct PriorNode<I> {
    pub id: I,
    pub parent: usize,
    /// Exclusive end of this node's captured preorder subtree.
    pub end: usize,
    pub style: usize,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug))]
pub struct PriorStyle<P> {
    pub params: P,
    pub uses: usize,
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

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait TicketWriter: TicketModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).tickets().contains_key(id),
        ensures final(self).tickets() == old(self).tickets().insert(id, ticket),
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

/// Reissue tickets only for the recorded preorder subtree of this root.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        root < nodes.len(),
        root < nodes@[root as int].end <= nodes.len(),
        0 < first, first as int + nodes@[root as int].end <= u64::MAX,
        forall |i: int| root <= i < nodes@[root as int].end ==>
            old(writer).tickets().contains_key((#[trigger] nodes@[i]).id),
    ensures ({
        let end = nodes@[root as int].end as int;
        final(writer).tickets() == ticket_prefix(
            old(writer).tickets(), nodes@.subrange(root as int, end),
            (first as int + root) as u64, (end - root) as nat,
        )
    }),
))]
pub fn restore_region<W: TicketWriter + ?Sized>(
    writer: &mut W, nodes: &[PriorNode<W::Id>], root: usize, first: u64,
) {
    let end = nodes[root].end;
    let region = &nodes[root..end];
    #[cfg(verus_keep_ghost)]
    proof! {
        assert forall |j: int| 0 <= j < region.len()
            implies old(writer).tickets().contains_key((#[trigger] region@[j]).id) by {
            assert(region@[j] == nodes@[root as int + j]);
        }
    }
    restore_tickets(writer, region, first + root as u64);
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires index < old(nodes).len(),
        old(nodes)@[index as int].style < old(styles).len(),
        old(styles)@[old(nodes)@[index as int].style as int].uses > 0,
    ensures
        (final(nodes)@, final(styles)@) == physical_style_update(old(nodes)@, old(styles)@, index as int, params),
))]
pub fn update_style<I, P: Copy>(
    nodes: &mut [PriorNode<I>], styles: &mut Vec<PriorStyle<P>>, index: usize, params: P,
) {
    let slot = nodes[index].style;
    let style = &mut styles[slot];
    if style.uses == 1 {
        style.params = params;
    } else {
        style.uses -= 1;
        nodes[index].style = styles.len();
        styles.push(PriorStyle { params, uses: 1 });
    }
}
