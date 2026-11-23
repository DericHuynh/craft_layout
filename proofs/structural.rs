//! Tail edit summaries and reconciliation of saved preorder topology.
use vstd::prelude::*;
#[path = "../src/structural_changes.rs"]
pub(crate) mod kernel;
use kernel::{record_spec, TailDelta};

verus! {
pub open spec fn represents<I: Copy>(original: Seq<I>, current: Seq<I>, delta: TailDelta<I>) -> bool {
    let prefix = original.len() - delta.removed;
    &&& 0 <= prefix
    &&& current.len() == prefix + delta.added
    &&& forall|i: int| 0 <= i < prefix ==> #[trigger] current[i] == original[i]
    &&& delta.first_added == if delta.added == 0 { None } else { Some(current[prefix]) }
}

pub proof fn empty_delta_describes_original<I: Copy>(original: Seq<I>)
    ensures represents(original, original, TailDelta { first_added: None, added: 0, removed: 0 }),
{}

// This induction step applies to every accepted push or pop in an arbitrary batch.
// The old and live sequences may also contain ignored or independently sized siblings.
pub proof fn accepted_edit_preserves_prefix<I: Copy>(
    original: Seq<I>, current: Seq<I>, delta: TailDelta<I>, id: I, inserting: bool,
)
    requires
        represents(original, current, delta),
        !inserting ==> current.len() > 0 && current.last() == id,
        record_spec(delta, id, inserting).is_some(),
    ensures
        represents(original, if inserting {current.push(id)} else {current.drop_last()},
            record_spec(delta, id, inserting).unwrap()),
{
    let next = if inserting {current.push(id)} else {current.drop_last()};
    let updated = record_spec(delta, id, inserting).unwrap();
    let kept = original.len() - updated.removed;
    assert forall|i: int| 0 <= i < kept implies #[trigger] next[i] == original[i] by {
        assert(current[i] == original[i]);
    }
    if updated.added > 0 && delta.added > 0 {
        assert(next[kept] == current[kept]);
    }
}

pub proof fn first_added_is_unique_boundary<I: Copy>(original: Seq<I>, current: Seq<I>, delta: TailDelta<I>)
    requires represents(original, current, delta), current.no_duplicates(), delta.added > 0,
    ensures
        delta.first_added == Some(current[original.len() - delta.removed]),
        forall|i: int| 0 <= i < current.len() && i != original.len() - delta.removed ==>
            Some(#[trigger] current[i]) != delta.first_added,
{}
}

use kernel::{ChildCursor, ticket_index_spec};
use kernel::{StructuralChange, parent_change};

verus! {

/// A child visible to the adapter is represented by its subtree and its subsequent
/// siblings. A disabled node appears as a node with no captured descendants.
pub enum Forest {
    Empty,
    Node { children: Box<Forest>, siblings: Box<Forest> },
}

pub open spec fn length(forest: Forest) -> nat
    decreases forest,
{
    match forest {
        Forest::Empty => 0,
        Forest::Node { children, siblings } => 1 + length(*children) + length(*siblings),
    }
}

pub struct Prior {
    pub parent: usize,
    pub end: usize,
}

// The snapshot pushes the root, recursively appends its children, then records the
// exclusive end. Child node identities are their indices in this particular snapshot.
pub open spec fn capture(forest: Forest, start: int, parent: usize) -> Seq<Prior>
    decreases forest,
{
    match forest {
        Forest::Empty => Seq::empty(),
        Forest::Node { children, siblings } => {
            let next = start + 1 + length(*children);
            seq![Prior { parent, end: next as usize }]
                + capture(*children, start + 1, start as usize) + capture(*siblings, next, parent)
        },
    }
}

pub open spec fn direct_children(forest: Forest, start: int) -> Seq<usize>
    decreases forest,
{
    match forest {
        Forest::Empty => Seq::empty(),
        Forest::Node { children, siblings } =>
            seq![start as usize] + direct_children(*siblings, start + 1 + length(*children)),
    }
}

proof fn captured_length(forest: Forest, start: int, parent: usize)
    ensures capture(forest, start, parent).len() == length(forest),
    decreases forest,
{
    if let Forest::Node { children, siblings } = forest {
        captured_length(*children, start + 1, start as usize);
        captured_length(*siblings, start + 1 + length(*children), parent);
    }
}

pub open spec fn direct_chain(table: Seq<Prior>, cursor: usize, end: usize, parent: usize, roots: Seq<usize>) -> bool
    decreases roots.len(),
{
    if roots.len() == 0 { cursor == end }
    else {
        &&& cursor < end <= table.len()
        &&& roots.first() == cursor
        &&& table[cursor as int].parent == parent
        &&& cursor < table[cursor as int].end <= end
        &&& direct_chain(table, table[cursor as int].end, end, parent, roots.drop_first())
    }
}

// The chain premise for reconciliation follows from the preorder construction.
pub proof fn snapshot_contains_direct_chain(table: Seq<Prior>, forest: Forest, start: usize, parent: usize)
    requires
        start as int + length(forest) <= usize::MAX,
        start as int + length(forest) <= table.len(),
        table.subrange(start as int, start as int + length(forest)) == capture(forest, start as int, parent),
    ensures direct_chain(table, start, (start as int + length(forest)) as usize, parent,
        direct_children(forest, start as int)),
    decreases forest,
{
    if let Forest::Node { children, siblings } = forest {
        let next = start as int + 1 + length(*children);
        let end = start as int + length(forest);
        captured_length(*children, start as int + 1, start);
        captured_length(*siblings, next, parent);
        let segment = table.subrange(start as int, end);
        assert(table[start as int] == segment[0]);
        assert(table.subrange(next, end) =~= capture(*siblings, next, parent)) by {
            assert forall|i: int| 0 <= i < length(*siblings) implies
                #[trigger] table.subrange(next, end)[i] == capture(*siblings, next, parent)[i] by {
                assert(table[next + i] == segment[1 + length(*children) + i]);
            }
        }
        snapshot_contains_direct_chain(table, *siblings, next as usize, parent);
        assert(direct_children(forest, start as int).drop_first() =~= direct_children(*siblings, next));
    }
}

pub open spec fn same_children(old: Seq<usize>, live: Seq<Option<usize>>) -> bool {
    &&& old.len() == live.len()
    &&& forall|i: int| 0 <= i < old.len() ==> #[trigger] live[i] == Some(old[i])
}

pub open spec fn scan_children(table: Seq<Prior>, end: usize, state: ChildCursor, live: Seq<Option<usize>>)
    -> ChildCursor
    decreases live.len(),
{
    if live.len() == 0 { state }
    else {
        let following = if state.expected < end { Some(table[state.expected as int].end) } else { None };
        scan_children(table, end, state.observe(live.first(), following), live.drop_first())
    }
}

// A missing live ticket indicates insertion or replacement, even if the host reuses
// an ID. The final comparison with the exclusive end catches a deleted suffix.
pub proof fn detects_every_child_list_edit(
    table: Seq<Prior>, end: usize, parent: usize, state: ChildCursor, old: Seq<usize>, live: Seq<Option<usize>>,
)
    requires direct_chain(table, state.expected, end, parent, old),
    ensures scan_children(table, end, state, live).needs_invalidation(end)
        == (state.changed || !same_children(old, live)),
    decreases live.len(),
{
    if live.len() > 0 {
        if old.len() == 0 {
            let next = state.observe(live.first(), None);
            detects_every_child_list_edit(table, end, parent, next, old, live.drop_first());
        } else {
            let next = state.observe(live.first(), Some(table[state.expected as int].end));
            detects_every_child_list_edit(table, end, parent, next, old.drop_first(), live.drop_first());
            let tails_equal = same_children(old.drop_first(), live.drop_first());
            if same_children(old, live) {
                assert forall|i: int| 0 <= i < old.drop_first().len() implies
                    #[trigger] live.drop_first()[i] == Some(old.drop_first()[i]) by {
                    assert(live[i + 1] == Some(old[i + 1]));
                }
            } else if tails_equal && live.first() == Some(old.first()) {
                assert forall|i: int| 0 <= i < old.len() implies #[trigger] live[i] == Some(old[i]) by {
                    if i > 0 { assert(live.drop_first()[i - 1] == Some(old.drop_first()[i - 1])); }
                }
            }
        }
    }
}

pub proof fn reconcile_captured_children(
    table: Seq<Prior>, old_forest: Forest, start: usize, parent: usize, live: Seq<Option<usize>>,
)
    requires
        start as int + length(old_forest) <= usize::MAX,
        start as int + length(old_forest) <= table.len(),
        table.subrange(start as int, start as int + length(old_forest)) == capture(old_forest, start as int, parent),
    ensures ({
        let end = (start as int + length(old_forest)) as usize;
        !scan_children(table, end, ChildCursor { expected: start, changed: false }, live).needs_invalidation(end)
            == same_children(direct_children(old_forest, start as int), live)
    }),
{
    snapshot_contains_direct_chain(table, old_forest, start, parent);
    detects_every_child_list_edit(table, (start as int + length(old_forest)) as usize, parent,
        ChildCursor { expected: start, changed: false }, direct_children(old_forest, start as int), live);
}

pub open spec fn invalidates_parent_input(mark: StructuralChange) -> bool {
    matches!(mark, StructuralChange::Moved | StructuralChange::Subtree)
}

pub open spec fn invalidates_child_input(mark: StructuralChange) -> bool {
    matches!(mark, StructuralChange::Children | StructuralChange::Subtree)
}

// Retained is a transient marker during measurement. Registration folds child
// and move notifications before measurement begins, in either order.
pub proof fn structural_marks_accumulate(mark: StructuralChange)
    requires mark != StructuralChange::Retained,
    ensures
        invalidates_parent_input(mark.with_move()),
        invalidates_child_input(mark.with_move()) == invalidates_child_input(mark),
        invalidates_child_input(mark.with_children()),
        invalidates_parent_input(mark.with_children()) == invalidates_parent_input(mark),
        mark.with_move().with_children() == StructuralChange::Subtree,
        mark.with_children().with_move() == StructuralChange::Subtree,
        mark.with_move().with_move() == mark.with_move(),
        mark.with_children().with_children() == mark.with_children(),
{}

pub open spec fn reconcile_marks(
    initial: StructuralChange, prior_parent: Option<usize>, current_parent: Option<usize>, reusable: bool,
    changed_children: bool,
) -> StructuralChange {
    let attached = match parent_change(prior_parent, current_parent, reusable) {
        StructuralChange::Moved => initial.with_move(),
        StructuralChange::Subtree => StructuralChange::Subtree,
        _ => initial,
    };
    if changed_children { attached.with_children() } else { attached }
}

pub proof fn reconciled_mark_covers_structural_changes(
    initial: StructuralChange, prior_parent: Option<usize>, current_parent: Option<usize>, reusable: bool,
    table: Seq<Prior>, forest: Forest, start: usize, parent: usize, live: Seq<Option<usize>>,
)
    requires
        initial != StructuralChange::Retained,
        start as int + length(forest) <= usize::MAX,
        start as int + length(forest) <= table.len(),
        table.subrange(start as int, start as int + length(forest)) == capture(forest, start as int, parent),
    ensures ({
        let end = (start as int + length(forest)) as usize;
        let changed = scan_children(table, end, ChildCursor { expected: start, changed: false }, live).needs_invalidation(end);
        let mark = reconcile_marks(initial, prior_parent, current_parent, reusable, changed);
        let new_node = prior_parent.is_none();
        let moved = prior_parent != current_parent;
        let children_changed = !same_children(direct_children(forest, start as int), live);
        &&& new_node || (moved && !reusable) ==> mark == StructuralChange::Subtree
        &&& moved || new_node || invalidates_parent_input(initial) ==> invalidates_parent_input(mark)
        &&& children_changed || invalidates_child_input(initial) ==> invalidates_child_input(mark)
        &&& moved && children_changed ==> mark == StructuralChange::Subtree
        &&& !new_node && !moved && !children_changed ==> mark == initial
    }),
{
    reconcile_captured_children(table, forest, start, parent, live);
    structural_marks_accumulate(initial);
}

pub proof fn tickets_distinguish_incarnations(
    first: u64, count: usize, index: usize, next_first: u64, next_count: usize,
)
    requires
        first > 0, index < count, first as int + count <= next_first,
    ensures ({
        let ticket = (first as int + index) as u64;
        &&& ticket_index_spec(first, count, ticket) == Some(index)
        &&& ticket_index_spec(next_first, next_count, ticket) == None
        &&& ticket_index_spec(first, count, 0) == None
    }),
{}
}

use kernel::{tail_can_reuse, tail_replaces_prefix};

verus! {

// The bit patterns in the cursor and output can represent any geometry. The
// deterministic item function includes start alignment, margins and gap using the
// full solver's evaluation order. Disabled or free items may leave the cursor alone.
pub type Item<I, V> = spec_fn(I, u32, u32) -> (u32, V);

pub open spec fn place_items<I, V>(items: Seq<I>, origin: u32, share: u32, item: Item<I, V>) -> (u32, Seq<V>)
    decreases items.len(),
{
    if items.len() == 0 { (origin, Seq::empty()) }
    else {
        let (cursor, previous) = place_items(items.drop_last(), origin, share, item);
        let (next, output) = item(items.last(), cursor, share);
        (next, previous.push(output))
    }
}

proof fn place_slices<I, V>(items: Seq<I>, cut: int, origin: u32, share: u32, item: Item<I, V>)
    requires 0 <= cut <= items.len(),
    ensures ({
        let prefix = place_items(items.take(cut), origin, share, item);
        let suffix = place_items(items.skip(cut), prefix.0, share, item);
        place_items(items, origin, share, item) == (suffix.0, prefix.1 + suffix.1)
    }),
    decreases items.len(),
{
    if cut == items.len() {
        assert(items.take(cut) =~= items);
    } else {
        let prev = items.drop_last();
        place_slices(prev, cut, origin, share, item);
        assert(prev.take(cut) =~= items.take(cut));
        assert(prev.skip(cut) =~= items.skip(cut).drop_last());
        assert(items.skip(cut).last() == items.last());
        let prefix = place_items(items.take(cut), origin, share, item);
        let suffix = place_items(items.skip(cut), prefix.0, share, item);
        assert(place_items(items, origin, share, item).1 =~= prefix.1 + suffix.1);
    }
}

pub proof fn retained_tail_places_same_view<I: Copy, V>(
    old: Seq<I>, live: Seq<I>, delta: TailDelta<I>, origin: u32,
    old_share: u32, new_share: u32, scale_changed: bool, start: bool, item: Item<I, V>,
)
    requires represents(old, live, delta), !tail_replaces_prefix(old_share, new_share, scale_changed, start),
    ensures ({
        let cut = old.len() - delta.removed;
        let prefix = place_items(old.take(cut), origin, old_share, item);
        let retained = place_items(old, origin, old_share, item).1.take(cut);
        let appended = place_items(live.skip(cut), prefix.0, new_share, item);
        &&& old_share == new_share && start && !scale_changed
        &&& place_items(live, origin, new_share, item) == (appended.0, retained + appended.1)
    }),
{
    let cut = old.len() - delta.removed;
    let prefix = old.take(cut);
    assert(prefix =~= live.take(cut));
    place_slices(old, cut, origin, old_share, item);
    place_slices(live, cut, origin, new_share, item);
    place_length(prefix, origin, old_share, item);
    assert(place_items(old, origin, old_share, item).1.take(cut) =~= place_items(prefix, origin, old_share, item).1);
}

proof fn place_length<I, V>(items: Seq<I>, origin: u32, share: u32, item: Item<I, V>)
    ensures place_items(items, origin, share, item).1.len() == items.len(),
    decreases items.len(),
{
    if items.len() > 0 { place_length(items.drop_last(), origin, share, item); }
}

pub proof fn reused_dependent_leaf_has_identical_share(exhausted: bool, old_share: u32, independent: bool, new_share: u32)
    requires tail_can_reuse(exhausted, old_share, independent), exhausted ==> new_share == 0,
    ensures !independent ==> new_share == old_share,
{}

pub open spec fn count<I>(items: Seq<I>, eligible: spec_fn(I) -> bool) -> nat
    decreases items.len(),
{
    if items.len() == 0 { 0 } else {
        count(items.drop_last(), eligible) + if eligible(items.last()) { 1nat } else { 0nat }
    }
}

// Every accepted edited leaf counts in all three statistics (placed nodes, Fill
// leaves, total measured nodes). Unchanged siblings may count differently in each.
pub proof fn accepted_edit_updates_count<I: Copy>(
    original: Seq<I>, current: Seq<I>, delta: TailDelta<I>, id: I, inserting: bool, eligible: spec_fn(I) -> bool,
)
    requires
        eligible(id), !inserting ==> current.len() > 0 && current.last() == id,
        delta.removed <= count(original, eligible),
        count(current, eligible) == count(original, eligible) - delta.removed + delta.added,
        record_spec(delta, id, inserting).is_some(),
    ensures ({
        let next = if inserting {current.push(id)} else {current.drop_last()};
        let updated = record_spec(delta, id, inserting).unwrap();
        &&& updated.removed <= count(original, eligible)
        &&& count(next, eligible) == count(original, eligible) - updated.removed + updated.added
    }),
{
    if inserting {
        assert(current.push(id).drop_last() =~= current);
        assert(current.push(id).last() == id);
    }
}

/// Replay a finite history of eligible tail edits. A pop must name the current
/// last child. Counter overflow takes the same rejection path as the recorder.
pub open spec fn apply_batch<I: Copy>(
    current: Seq<I>, delta: TailDelta<I>, edits: Seq<(I, bool)>, eligible: spec_fn(I) -> bool,
) -> Option<(Seq<I>, TailDelta<I>)>
    decreases edits.len(),
{
    if edits.len() == 0 {
        Some((current, delta))
    } else {
        let (id, inserting) = edits.first();
        if !eligible(id) || (!inserting && (current.len() == 0 || current.last() != id)) {
            None
        } else {
            match record_spec(delta, id, inserting) {
                None => None,
                Some(updated) => apply_batch(
                    if inserting { current.push(id) } else { current.drop_last() },
                    updated, edits.drop_first(), eligible,
                ),
            }
        }
    }
}

proof fn continue_batch<I: Copy>(
    original: Seq<I>, current: Seq<I>, delta: TailDelta<I>, edits: Seq<(I, bool)>, eligible: spec_fn(I) -> bool,
)
    requires
        represents(original, current, delta), delta.removed <= count(original, eligible),
        count(current, eligible) == count(original, eligible) - delta.removed + delta.added,
    ensures match apply_batch(current, delta, edits, eligible) {
        Some((live, result)) => {
            &&& represents(original, live, result)
            &&& result.removed <= count(original, eligible)
            &&& count(live, eligible) == count(original, eligible) - result.removed + result.added
        },
        None => true,
    },
    decreases edits.len(),
{
    if edits.len() > 0 {
        let (id, inserting) = edits.first();
        if eligible(id) && (inserting || (current.len() > 0 && current.last() == id)) {
            if let Some(updated) = record_spec(delta, id, inserting) {
                accepted_edit_preserves_prefix(original, current, delta, id, inserting);
                accepted_edit_updates_count(original, current, delta, id, inserting, eligible);
                continue_batch(original, if inserting {current.push(id)} else {current.drop_last()},
                    updated, edits.drop_first(), eligible);
            }
        }
    }
}

// The offset counts unaffected nodes outside this sibling list, e.g. when updating
// the whole-tree measured-node count. The other counters use offset zero.
pub proof fn complete_tail_batch<I: Copy>(
    original: Seq<I>, edits: Seq<(I, bool)>, eligible: spec_fn(I) -> bool, outside: nat,
)
    ensures match apply_batch(original, TailDelta { first_added: None, added: 0, removed: 0 }, edits, eligible) {
        Some((live, delta)) => {
            &&& represents(original, live, delta)
            &&& delta.removed <= count(original, eligible)
            &&& outside + count(live, eligible)
                == outside + count(original, eligible) - delta.removed + delta.added
        },
        None => true,
    },
{
    let initial = TailDelta { first_added: None, added: 0, removed: 0 };
    empty_delta_describes_original(original);
    continue_batch(original, original, initial, edits, eligible);
}
}

verus! {

// S contains the non-NaN binary32 values. The ordering identifies signed zeros,
// and the share is represented by its output bits. fill_budget.py checks the
// concrete LLVM operations implementing the following one-step laws.
#[verifier::reject_recursive_types(S)]
pub struct Budget<S> {
    pub zero: S,
    pub valid: spec_fn(S) -> bool,
    pub fee: spec_fn(S) -> bool,
    pub is_zero: spec_fn(S) -> bool,
    pub le: spec_fn(S, S) -> bool,
    pub charge: spec_fn(S, S) -> S,
    pub after_gaps: spec_fn(S, S) -> S,
    pub exhausted: spec_fn(S, S, S) -> bool,
    pub share_bits: spec_fn(S) -> u32,
}

pub open spec fn budget_laws<S>(b: Budget<S>) -> bool {
    &&& forall |x:S| (b.valid)(x) ==> #[trigger] (b.le)(x,x)
    &&& forall |x:S,y:S,z:S| #[trigger] (b.le)(x,y) && #[trigger] (b.le)(y,z) ==> (b.le)(x,z)
    &&& forall |x:S,c:S| (b.valid)(x) && (b.fee)(c) ==>
        (b.valid)(#[trigger] (b.charge)(x,c)) && (b.le)((b.charge)(x,c),x)
    &&& forall |x:S,y:S,c:S| (b.le)(x,y) && (b.fee)(c) ==>
        (b.le)(#[trigger] (b.charge)(x,c), #[trigger] (b.charge)(y,c))
    &&& forall |x:S,c:S| (b.valid)(x) && (b.is_zero)(c) ==> (b.le)(x, #[trigger] (b.charge)(x,c))
    &&& forall |x:S| (b.le)(x,b.zero) ==> #[trigger] (b.share_bits)(x) == 0u32
    &&& forall |inner:S,gaps:S| (b.le)(b.zero,inner) && (b.le)(b.zero,gaps) ==>
        (b.valid)(#[trigger] (b.after_gaps)(inner,gaps)) && (b.le)((b.after_gaps)(inner,gaps),inner)
    &&& forall |inner:S,gaps:S,bound:S| (b.le)(b.zero,inner) && (b.le)(b.zero,gaps) &&
        #[trigger] (b.exhausted)(inner,gaps,bound) ==>
            (b.le)((b.after_gaps)(inner,gaps),b.zero) || (b.le)(bound,b.zero)
}

pub open spec fn charge_all<S>(b: Budget<S>, space:S, costs:Seq<S>) -> S
    decreases costs.len(),
{
    if costs.len() == 0 { space }
    else { (b.charge)(charge_all(b,space,costs.drop_last()),costs.last()) }
}

proof fn bound_after_charges<S>(b: Budget<S>, x:S, y:S, costs:Seq<S>, zeros:bool)
    requires
        budget_laws(b), (b.valid)(x), (b.valid)(y), (b.le)(x,y),
        forall |i:int| 0 <= i < costs.len() ==> (b.fee)(#[trigger] costs[i]) && (zeros ==> (b.is_zero)(costs[i])),
    ensures
        (b.valid)(charge_all(b,x,costs)), (b.valid)(charge_all(b,y,costs)),
        (b.le)(charge_all(b,x,costs),charge_all(b,y,costs)),
        (b.le)(charge_all(b,x,costs),x), (b.le)(charge_all(b,y,costs),y),
        zeros ==> (b.le)(x,charge_all(b,x,costs)),
    decreases costs.len(),
{
    if costs.len() > 0 {
        let prefix = costs.drop_last();
        assert forall |i:int| 0 <= i < prefix.len() implies
            (b.fee)(#[trigger] prefix[i]) && (zeros ==> (b.is_zero)(prefix[i])) by {
            assert((b.fee)(costs[i]) && (zeros ==> (b.is_zero)(costs[i])));
        }
        bound_after_charges(b,x,y,prefix,zeros);
        assert(costs.last() == costs[costs.len()-1]);
    }
}

// Kept costs are reduced in the full solver's original left-to-right order.
// Popped leaves contributed only zero fees to the cached bound; appended leaves
// may only consume more space. If the guard accepts, the full share is +0.0.
pub proof fn exhausted_tail_share<S>(b: Budget<S>, inner:S, gaps:S, kept:Seq<S>, popped:Seq<S>, appended:Seq<S>)
    requires
        budget_laws(b), (b.valid)(inner), (b.le)(b.zero,inner), (b.le)(b.zero,gaps),
        forall |i:int| 0 <= i < kept.len() ==> (b.fee)(#[trigger] kept[i]),
        forall |i:int| 0 <= i < popped.len() ==> (b.fee)(#[trigger] popped[i]) && (b.is_zero)(popped[i]),
        forall |i:int| 0 <= i < appended.len() ==> (b.fee)(#[trigger] appended[i]),
        (b.exhausted)(inner,gaps,charge_all(b,charge_all(b,inner,kept),popped)),
    ensures (b.share_bits)(charge_all(b,charge_all(b,(b.after_gaps)(inner,gaps),kept),appended)) == 0u32,
{
    let available = (b.after_gaps)(inner,gaps);
    let raw_prefix = charge_all(b,inner,kept);
    let remaining = charge_all(b,available,kept);
    bound_after_charges(b,available,inner,kept,false);
    bound_after_charges(b,raw_prefix,raw_prefix,popped,true);
    bound_after_charges(b,remaining,remaining,appended,false);
}

}

verus! {

// A recoverable sibling exposes its unrounded first edge. Its size and trailing
// margin are inputs of advance, just as in Place::place_appended_stack_leaf.
// A disabled or freely positioned sibling may yield no cursor witness.
pub type GeometryAt<I,V> = spec_fn(I, u32, u32) -> (Option<u32>, V);
pub type Advance<I> = spec_fn(I, u32, u32) -> u32;

pub open spec fn stack_item_at<I,V>(geometry:GeometryAt<I,V>, advance:Advance<I>) -> Item<I,(Option<u32>,V)> {
    |id:I,cursor:u32,share:u32| {
        let output = geometry(id,cursor,share);
        let next = match output.0 { Some(first) => advance(id,first,share), None => cursor };
        (next, output)
    }
}

pub proof fn append_resumes_from_cached_first_edge<I:Copy,V>(
    old:Seq<I>, live:Seq<I>, delta:TailDelta<I>, origin:u32, share:u32,
    geometry:GeometryAt<I,V>, advance:Advance<I>,
)
    requires
        represents(old,live,delta),
        ({
            let cut = old.len() - delta.removed;
            cut > 0 ==> place_items(old,origin,share,stack_item_at(geometry,advance)).1[cut-1].0.is_some()
        }),
    ensures ({
        let cut = old.len() - delta.removed;
        let item = stack_item_at(geometry,advance);
        let cached = place_items(old,origin,share,item).1;
        let cursor = if cut == 0 { origin } else { advance(old[cut-1],cached[cut-1].0.unwrap(),share) };
        let appended = place_items(live.skip(cut),cursor,share,item);
        &&& place_items(old.take(cut),origin,share,item).0 == cursor
        &&& place_items(live,origin,share,item) == (appended.0,cached.take(cut) + appended.1)
    }),
{
    let cut = old.len() - delta.removed;
    let prefix = old.take(cut);
    let item = stack_item_at(geometry,advance);
    let cached = place_items(old,origin,share,item).1;
    retained_tail_places_same_view(old,live,delta,origin,share,share,false,true,item);
    place_slices(old,cut,origin,share,item);
    place_length(prefix,origin,share,item);
    if cut > 0 {
        let before = place_items(prefix.drop_last(),origin,share,item).0;
        let last = geometry(prefix.last(),before,share);
        assert(prefix.last() == old[cut-1]);
        assert(cached[cut-1] == place_items(prefix,origin,share,item).1[cut-1]);
        assert(cached[cut-1] == last);
    }
}

}
