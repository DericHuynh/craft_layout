//! Liveness of the targets emitted by the production sizing scheduler.
use super::*;
use vstd::prelude::*;

verus! {

pub(crate) open spec fn optional<I>(live: Set<I>, node: Option<I>) -> bool {
    match node {
        Some(id) => live.contains(id),
        None => true,
    }
}

/// Each observation used to derive another ID stays within the same live
/// tree. Declarations and flags may choose an edge but cannot invent an ID.
pub(crate) open spec fn closed<I: Copy>(topology: Topology<I>, live: Set<I>) -> bool {
    &&& forall |id: I| live.contains(id) ==>
        #[trigger] optional(live, (topology.parent)(id))
    &&& forall |slot: Request<I>| live.contains(slot.node) ==>
        #[trigger] optional(live, (topology.stack_parent)(slot))
    &&& forall |id: I, index: int| live.contains(id) && 0 <= index < (topology.children)(id).len() ==>
        live.contains((#[trigger] (topology.children)(id)[index]).node)
    &&& forall |id: I, index: int| live.contains(id) && 0 <= index < (topology.block_children)(id).len() ==>
        live.contains((#[trigger] (topology.block_children)(id)[index]).id)
}

pub(crate) open spec fn all<I>(live: Set<I>, slots: Seq<Request<I>>) -> bool {
    forall |index: int| 0 <= index < slots.len() ==> live.contains((#[trigger] slots[index]).node)
}

proof fn concatenate<I>(live: Set<I>, first: Seq<Request<I>>, last: Seq<Request<I>>)
    requires all(live, first), all(live, last),
    ensures all(live, first + last),
{
    let joined = first + last;
    assert forall |i: int| 0 <= i < joined.len() implies live.contains((#[trigger] joined[i]).node) by {
        if i < first.len() { assert(joined[i] == first[i]); }
        else { assert(joined[i] == last[i - first.len()]); }
    }
}

proof fn declarations_live<I: Copy>(topology: Topology<I>, live: Set<I>, slot: Request<I>, intrinsic: bool, count: nat)
    requires live.contains(slot.node),
    ensures all(live, declaration_prefix(topology, slot, intrinsic, count)),
    decreases count,
{
    if count != 0 {
        let index = (count - 1) as nat;
        declarations_live(topology, live, slot, intrinsic, index);
        let prefix = declaration_prefix(topology, slot, intrinsic, index);
        let next = declaration_prefix(topology, slot, intrinsic, count);
        assert forall |i: int| 0 <= i < next.len() implies live.contains((#[trigger] next[i]).node) by {
            if i < prefix.len() { assert(next[i] == prefix[i]); }
            else { assert(next[i].node == slot.node); }
        }
    }
}

proof fn intrinsic_children_live<I: Copy>(topology: Topology<I>, live: Set<I>, slot: Request<I>, count: nat)
    requires count <= (topology.children)(slot.node).len(),
        forall |i: int| 0 <= i < (topology.children)(slot.node).len() ==>
            live.contains((#[trigger] (topology.children)(slot.node)[i]).node),
    ensures all(live, child_prefix(topology, slot, count)),
    decreases count,
{
    if count != 0 {
        let index = (count - 1) as nat;
        intrinsic_children_live(topology, live, slot, index);
        let prefix = child_prefix(topology, slot, index);
        let child = (topology.children)(slot.node)[index as int];
        if child.in_flow {
            assert(live.contains(child.node));
            let row = target(child.node, slot.vertical, slot.kind);
            declarations_live(topology, live, row, true, 3);
            concatenate(live, prefix, declaration_prefix(topology, row, true, 3));
        } else {
            concatenate(live, prefix, Seq::empty());
        }
    }
}

proof fn wrap_decl_targets<I: Copy>(live: Set<I>, node: I, parent: I, main: bool,
    producer: Producer, flags: &[bool; 3], count: nat,
)
    requires live.contains(node),
    ensures all(live, wrap_spec::declarations(node, producer, flags, count).map_values(
        |request: WrapRequest<I>| wrap_slot(parent, main, request))),
    decreases count,
{
    let project = |request: WrapRequest<I>| wrap_slot(parent, main, request);
    if count != 0 {
        let index = (count - 1) as nat;
        wrap_decl_targets(live, node, parent, main, producer, flags, index);
        let prefix = wrap_spec::declarations(node, producer, flags, index).map_values(project);
        let current = wrap_spec::declarations(node, producer, flags, count).map_values(project);
        assert forall |i: int| 0 <= i < current.len() implies live.contains((#[trigger] current[i]).node) by {
            if i < prefix.len() { assert(current[i] == prefix[i]); }
            else {
                assert(current[i] == project(wrap_spec::declaration(node, producer, index as usize)));
                assert(current[i].node == node);
            }
        }
    }
}

proof fn wrap_child_targets<I: Copy>(rows: Seq<wrap_spec::Child<I>>, live: Set<I>, parent: I, main: bool,
    producer: Producer, count: nat,
)
    requires count <= rows.len(),
        forall |i: int| 0 <= i < rows.len() ==> live.contains((#[trigger] rows[i]).id),
    ensures all(live, wrap_spec::child_requests(rows, producer, count).map_values(
        |request: WrapRequest<I>| wrap_slot(parent, main, request))),
    decreases count,
{
    if count != 0 {
        let index = (count - 1) as nat;
        wrap_child_targets(rows, live, parent, main, producer, index);
        let child = rows[index as int];
        let project = |request: WrapRequest<I>| wrap_slot(parent, main, request);
        let prefix = wrap_spec::child_requests(rows, producer, index).map_values(project);
        let part = wrap_spec::row_requests(child, producer).map_values(project);
        if child.in_flow {
            assert(live.contains(child.id));
            if producer is Cross {
                wrap_decl_targets(live, child.id, parent, main, producer, &child.cross, 3);
                let declarations = wrap_spec::declarations(child.id, producer, &child.cross, 3).map_values(project);
                let first = seq![target(child.id, main, Kind::Final)];
                assert(part =~= first + declarations);
                concatenate(live, first, declarations);
            } else if child.has_fill {
                wrap_decl_targets(live, child.id, parent, main, producer, &child.share, 3);
            } else {
                assert(part[0].node == child.id);
            }
        }
        assert(wrap_spec::child_requests(rows, producer, count).map_values(project) =~= prefix + part);
        concatenate(live, prefix, part);
    }
}

proof fn wrap_targets<I: Copy>(topology: Topology<I>, live: Set<I>, slot: Request<I>, main: bool, producer: Producer)
    requires live.contains(slot.node),
        forall |i: int| 0 <= i < (topology.children)(slot.node).len() ==>
            live.contains((#[trigger] (topology.children)(slot.node)[i]).node),
    ensures all(live, wrap_inputs(topology, slot.node, main, producer)),
{
    let rows = wrap_rows(topology, slot.node, main);
    assert forall |i: int| 0 <= i < rows.len() implies live.contains((#[trigger] rows[i]).id) by {
        let tree_child = (topology.children)(slot.node)[i];
        assert(rows[i].id == tree_child.node);
    }
    wrap_child_targets(rows, live, slot.node, main, producer, rows.len());
    let own = wrap_slot(slot.node, main, wrap_spec::own(producer));
    assert(own.node == slot.node);
    concatenate(live, seq![own], wrap_spec::child_requests(rows, producer, rows.len()).map_values(
        |request: WrapRequest<I>| wrap_slot(slot.node, main, request)));
}

proof fn block_targets<I: Copy>(rows: Seq<block_spec::Child<I>>, live: Set<I>, count: nat)
    requires count <= rows.len(),
        forall |i: int| 0 <= i < rows.len() ==> live.contains((#[trigger] rows[i]).id),
    ensures all(live, block_spec::block_inputs(rows, count).map_values(|request: BlockRequest<I>| block_slot(request))),
    decreases count,
{
    if count != 0 {
        let index = (count - 1) as nat;
        block_targets(rows, live, index);
        let child = rows[index as int];
        let project = |request: BlockRequest<I>| block_slot(request);
        let prefix = block_spec::block_inputs(rows, index).map_values(project);
        let part = block_spec::child_inputs(child).map_values(project);
        assert forall |i: int| 0 <= i < part.len() implies live.contains((#[trigger] part[i]).node) by {
            assert(live.contains(child.id));
            assert(part[i].node == child.id);
        }
        assert(block_spec::block_inputs(rows, count).map_values(project) =~= prefix + part);
        concatenate(live, prefix, part);
    }
}

/// The parent modes occur only while evaluating a declared size.
pub(crate) open spec fn declaration_input<I: Copy>(topology: Topology<I>, slot: Request<I>) -> Input<I> {
    match slot.kind {
        Kind::Final | Kind::Flow | Kind::EvenShare => Input::None,
        _ => match (topology.form)(slot) {
            Some(form) => form.input_for(if form is Fill { (topology.stack_parent)(slot) } else { None }),
            None => Input::None,
        },
    }
}

/// A single native request only observes IDs from its own parent and child rows.
pub(crate) proof fn inputs_stay_in_neighborhood<I: Copy>(topology: Topology<I>, live: Set<I>, slot: Request<I>)
    requires live.contains(slot.node),
        declaration_input(topology, slot) is ParentFinal ==> optional(live, (topology.parent)(slot.node)),
        declaration_input(topology, slot) is ParentShare ==> optional(live, (topology.stack_parent)(slot)),
        forall |i: int| 0 <= i < (topology.children)(slot.node).len() ==>
            live.contains((#[trigger] (topology.children)(slot.node)[i]).node),
        forall |i: int| 0 <= i < (topology.block_children)(slot.node).len() ==>
            live.contains((#[trigger] (topology.block_children)(slot.node)[i]).id),
    ensures all(live, inputs(topology, slot)),
{
    match slot.kind {
        Kind::Final => declarations_live(topology, live, slot, false, 3),
        Kind::EvenShare => wrap_targets(topology, live, slot, slot.vertical, Producer::Share),
        Kind::Flow => match (topology.flow_mode)(slot.node) {
            FlowMode::Block => {
                let rows = (topology.block_children)(slot.node);
                assert forall |i: int| 0 <= i < rows.len() implies live.contains((#[trigger] rows[i]).id) by {}
                block_targets(rows, live, rows.len());
            }
            FlowMode::Wrap(main) => wrap_targets(topology, live, slot, main, Producer::Cross),
            FlowMode::Other => {},
        },
        _ => {
            match (topology.form)(slot) {
                None => {},
                Some(form) => {
                    let stack = if form is Fill { (topology.stack_parent)(slot) } else { None };
                    match form.input_for(stack) {
                        Input::None | Input::OppositeFinal => {},
                        Input::ParentFinal => {
                            assert(optional(live, (topology.parent)(slot.node)));
                            if let Some(parent) = (topology.parent)(slot.node) {
                                assert(live.contains(parent));
                            }
                        }
                        Input::ParentShare(parent) => {
                            assert(optional(live, (topology.stack_parent)(slot)));
                            assert(stack == Some(parent));
                        }
                        Input::IntrinsicChildren => {
                            if !(topology.intrinsic_flow)(slot) {
                                intrinsic_children_live(topology, live, slot, (topology.children)(slot.node).len());
                            }
                            let current = inputs(topology, slot);
                            assert forall |i: int| 0 <= i < current.len()
                                implies live.contains((#[trigger] current[i]).node) by {
                                if (topology.intrinsic_flow)(slot) {
                                    assert(current[i].node == slot.node);
                                } else {
                                    let prefix = child_prefix(topology, slot, (topology.children)(slot.node).len());
                                    if i < prefix.len() { assert(current[i] == prefix[i]); }
                                    else { assert(current[i].node == slot.node); }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// This is the same sequence used by the native callback and spill buffer.
pub(crate) proof fn inputs_stay_live<I: Copy>(topology: Topology<I>, live: Set<I>, slot: Request<I>)
    requires closed(topology, live), live.contains(slot.node),
    ensures all(live, inputs(topology, slot)),
{
    assert(optional(live, (topology.parent)(slot.node)));
    assert(optional(live, (topology.stack_parent)(slot)));
    inputs_stay_in_neighborhood(topology, live, slot);
}

pub(crate) open spec fn chain<I>(rows: Seq<I>, first: Option<I>, sibling: spec_fn(I) -> Option<I>) -> bool {
    &&& first == if rows.len() == 0 { None } else { Some(rows[0]) }
    &&& forall |i: int| 0 <= i < rows.len() ==>
        #[trigger] sibling(rows[i]) == if i + 1 < rows.len() { Some(rows[i + 1]) } else { None }
}

proof fn chain_position_live<I>(rows: Seq<I>, first: Option<I>, sibling: spec_fn(I) -> Option<I>,
    live: Set<I>, position: nat,
)
    requires chain(rows, first, sibling), optional(live, first), position < rows.len(),
        forall |node: I| live.contains(node) ==> #[trigger] optional(live, sibling(node)),
    ensures live.contains(rows[position as int]),
    decreases position,
{
    if position != 0 {
        let before = (position - 1) as nat;
        chain_position_live(rows, first, sibling, live, before);
        assert(sibling(rows[before as int]) == Some(rows[position as int]));
        assert(optional(live, sibling(rows[before as int])));
    }
}

pub(crate) open spec fn child_ids<I: Copy>(topology: Topology<I>, node: I) -> Seq<I> {
    (topology.children)(node).map_values(|child: Child<I>| child.node)
}

pub(crate) open spec fn block_ids<I: Copy>(topology: Topology<I>, node: I) -> Seq<I> {
    (topology.block_children)(node).map_values(|child: block_spec::Child<I>| child.id)
}

/// The native sources enumerate the same stable first-child and sibling links
/// for ordinary and Block rows. A stack parent is a filtered parent lookup.
pub(crate) proof fn live_links_close<I: Copy>(topology: Topology<I>, live: Set<I>,
    first: spec_fn(I) -> Option<I>, sibling: spec_fn(I) -> Option<I>,
)
    requires
        forall |node: I| live.contains(node) ==> #[trigger] optional(live, first(node)),
        forall |node: I| live.contains(node) ==> #[trigger] optional(live, sibling(node)),
        forall |node: I| live.contains(node) ==> #[trigger] optional(live, (topology.parent)(node)),
        forall |slot: Request<I>| (#[trigger] (topology.stack_parent)(slot)).is_some()
            ==> (topology.stack_parent)(slot) == (topology.parent)(slot.node),
        forall |node: I| live.contains(node) ==> #[trigger] chain(child_ids(topology, node), first(node), sibling),
        forall |node: I| live.contains(node) ==> #[trigger] chain(block_ids(topology, node), first(node), sibling),
    ensures closed(topology, live),
{
    assert forall |slot: Request<I>| live.contains(slot.node)
        implies #[trigger] optional(live, (topology.stack_parent)(slot)) by {
        if (topology.stack_parent)(slot).is_some() {
            assert(optional(live, (topology.parent)(slot.node)));
        }
    }
    assert forall |node: I, i: int| live.contains(node) && 0 <= i < (topology.children)(node).len()
        implies live.contains((#[trigger] (topology.children)(node)[i]).node) by {
        let rows = child_ids(topology, node);
        chain_position_live(rows, first(node), sibling, live, i as nat);
    }
    assert forall |node: I, i: int| live.contains(node) && 0 <= i < (topology.block_children)(node).len()
        implies live.contains((#[trigger] (topology.block_children)(node)[i]).id) by {
        let rows = block_ids(topology, node);
        chain_position_live(rows, first(node), sibling, live, i as nat);
    }
}

/// Undefined observations outside the live tree can take the empty values.
/// This provides a total logical model for the verifier's generic signatures.
pub(crate) open spec fn extend<I: Copy>(topology: Topology<I>, live: Set<I>) -> Topology<I> {
    Topology {
        form: |slot: Request<I>| if live.contains(slot.node) { (topology.form)(slot) } else { None },
        stack_parent: |slot: Request<I>| if live.contains(slot.node) { (topology.stack_parent)(slot) } else { None },
        parent: |node: I| if live.contains(node) { (topology.parent)(node) } else { None },
        parent_flow: |slot: Request<I>, parent: I| live.contains(slot.node) && live.contains(parent)
            && (topology.parent_flow)(slot, parent),
        parent_other: |slot: Request<I>, parent: I| live.contains(slot.node) && live.contains(parent)
            && (topology.parent_other)(slot, parent),
        intrinsic_flow: |slot: Request<I>| live.contains(slot.node) && (topology.intrinsic_flow)(slot),
        intrinsic_other: |slot: Request<I>| live.contains(slot.node) && (topology.intrinsic_other)(slot),
        children: |node: I| if live.contains(node) { (topology.children)(node) } else { Seq::empty() },
        flow_mode: |node: I| if live.contains(node) { (topology.flow_mode)(node) } else { FlowMode::Other },
        block_children: |node: I| if live.contains(node) { (topology.block_children)(node) } else { Seq::empty() },
    }
}

proof fn declaration_extension<I: Copy>(topology: Topology<I>, live: Set<I>,
    slot: Request<I>, intrinsic: bool, count: nat,
)
    requires live.contains(slot.node),
    ensures declaration_prefix(extend(topology, live), slot, intrinsic, count)
        == declaration_prefix(topology, slot, intrinsic, count),
    decreases count,
{
    if count != 0 {
        declaration_extension(topology, live, slot, intrinsic, (count - 1) as nat);
    }
}

proof fn child_extension<I: Copy>(topology: Topology<I>, live: Set<I>, slot: Request<I>, count: nat)
    requires closed(topology, live), live.contains(slot.node), count <= (topology.children)(slot.node).len(),
    ensures child_prefix(extend(topology, live), slot, count) == child_prefix(topology, slot, count),
    decreases count,
{
    if count != 0 {
        let index = (count - 1) as nat;
        child_extension(topology, live, slot, index);
        let row = (topology.children)(slot.node)[index as int];
        if row.in_flow {
            assert(live.contains(row.node));
            declaration_extension(topology, live, target(row.node, slot.vertical, slot.kind), true, 3);
        }
    }
}

proof fn wrap_extension<I: Copy>(topology: Topology<I>, live: Set<I>, node: I, main: bool)
    requires live.contains(node), closed(topology, live),
    ensures wrap_rows(extend(topology, live), node, main) == wrap_rows(topology, node, main),
{
    let rows = (topology.children)(node);
    let before = wrap_rows(topology, node, main);
    let after = wrap_rows(extend(topology, live), node, main);
    assert(before =~= after) by {
        assert forall |i: int| 0 <= i < rows.len() implies before[i] == after[i] by {
            assert(live.contains(rows[i].node));
        }
    }
}

pub(crate) proof fn extension_preserves_live_requests<I: Copy>(topology: Topology<I>, live: Set<I>, slot: Request<I>)
    requires live.contains(slot.node), closed(topology, live),
    ensures inputs(extend(topology, live), slot) == inputs(topology, slot),
        ordered_children(extend(topology, live), slot) == ordered_children(topology, slot),
{
    match slot.kind {
        Kind::Final => declaration_extension(topology, live, slot, false, 3),
        Kind::EvenShare => wrap_extension(topology, live, slot.node, slot.vertical),
        Kind::Flow => {
            if let FlowMode::Wrap(main) = (topology.flow_mode)(slot.node) {
                wrap_extension(topology, live, slot.node, main);
            }
        }
        _ => {
            assert(optional(live, (topology.parent)(slot.node)));
            child_extension(topology, live, slot, (topology.children)(slot.node).len());
        }
    }
}

pub(crate) proof fn extension_is_ordered<I: Copy>(topology: Topology<I>, live: Set<I>)
    requires closed(topology, live),
        forall |slot: Request<I>| live.contains(slot.node) ==> #[trigger] ordered_children(topology, slot),
    ensures forall |slot: Request<I>| #[trigger] ordered_children(extend(topology, live), slot),
{
    assert forall |slot: Request<I>| #[trigger] ordered_children(extend(topology, live), slot) by {
        if live.contains(slot.node) {
            extension_preserves_live_requests(topology, live, slot);
        } else {
            let empty = wrap_rows(extend(topology, live), slot.node, slot.vertical);
            assert(empty.len() == 0);
        }
    }
}

/// A native visit or worklist visit is either a root or was issued earlier by
/// this scheduler. The claim holds for revisits and dependency cycles.
pub(crate) proof fn trace_stays_live<I: Copy>(topology: Topology<I>, live: Set<I>, roots: Seq<Request<I>>,
    trace: Seq<Request<I>>, count: nat,
)
    requires closed(topology, live), all(live, roots), count <= trace.len(),
        forall |i: int| 0 <= i < count ==>
            roots.contains(#[trigger] trace[i])
            || exists |j: int| 0 <= j < i && #[trigger] inputs(topology, trace[j]).contains(trace[i]),
    ensures all(live, trace.take(count as int)),
    decreases count,
{
    if count != 0 {
        let i = count - 1;
        trace_stays_live(topology, live, roots, trace, i as nat);
        if roots.contains(trace[i]) {
            let at = choose |k: int| 0 <= k < roots.len() && #[trigger] roots[k] == trace[i];
            assert(live.contains(roots[at].node));
        } else {
            let j = choose |j: int| 0 <= j < i && #[trigger] inputs(topology, trace[j]).contains(trace[i]);
            assert(trace.take(i)[j] == trace[j]);
            let requests = inputs(topology, trace[j]);
            inputs_stay_live(topology, live, trace[j]);
            let at = choose |k: int| 0 <= k < requests.len() && #[trigger] requests[k] == trace[i];
            assert(live.contains(requests[at].node));
        }
        assert(trace.take((i + 1) as int) =~= trace.take(i).push(trace[i]));
        concatenate(live, trace.take(i), seq![trace[i]]);
        assert(trace.take(i).push(trace[i]) =~= trace.take(i) + seq![trace[i]]);
    }
}

pub(crate) open spec fn packed_key<I>(number: spec_fn(I) -> int, slot: Request<I>) -> int {
    number(slot.node) * cycle_rules::N_SLOTS as int
        + cycle_rules::slot_index(slot.vertical as usize, slot.kind) as int
}

/// A finite numbering of the live nodes supplies the bounded universe used
/// by the explicit-stack proof. Shared physical slots keep their common key.
pub(crate) proof fn requested_keys_are_bounded<I: Copy>(topology: Topology<I>, live: Set<I>, slot: Request<I>,
    number: spec_fn(I) -> int, nodes: nat,
)
    requires closed(topology, live), live.contains(slot.node),
        forall |node: I| live.contains(node) ==> 0 <= #[trigger] number(node) < nodes,
    ensures forall |i: int| 0 <= i < inputs(topology, slot).len()
        ==> 0 <= #[trigger] packed_key(number, inputs(topology, slot)[i]) < nodes * cycle_rules::N_SLOTS,
{
    inputs_stay_live(topology, live, slot);
    assert forall |i: int| 0 <= i < inputs(topology, slot).len() implies
        0 <= #[trigger] packed_key(number, inputs(topology, slot)[i]) < nodes * cycle_rules::N_SLOTS by {
        let input = inputs(topology, slot)[i];
        let index = cycle_rules::slot_index(input.vertical as usize, input.kind);
        assert(index < cycle_rules::N_SLOTS);
        assert(live.contains(input.node));
        assert(0 <= number(input.node) < nodes);
    }
}

} // verus!
