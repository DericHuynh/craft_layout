//! Entry points that prepare a placement frame and invoke the checked driver.
#![allow(unexpected_cfgs)]

#[cfg(not(verus_keep_ghost))]
use crate::placement_geometry::FloatBounds;
#[cfg(not(verus_keep_ghost))]
use super::{free_placement, placement_modes as modes, placement_node as node};
#[cfg(verus_keep_ghost)]
use super::{geometry::FloatBounds, modes, node};
#[cfg(verus_keep_ghost)]
use crate::tree_walk::{free_placement, free_placement_order};
use crate::vec_memory::VecMemory;
use free_placement::{FreePlacementError, PreflightHost};
use modes::{Frame, ParentTarget, RootTarget, StackMath};
use node::Edges;
#[cfg(any(feature = "incremental", verus_keep_ghost))]
use modes::Branch;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait RootPlacementTarget<I>: ParentTarget<I> + RootTarget<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).links() == old(self).links(), final(self).hidden() == old(self).hidden(),
            final(self).plain() == old(self).plain(), final(self).root_key() == old(self).root_key(),
            final(self).written() == old(self).written(), final(self).rectangles() == old(self).rectangles(),
            forall|id: I| #[trigger] final(self).mark(id) == old(self).mark(id),
        no_unwind
    ))]
    fn prepare_rounding(&mut self, scale: Option<f32>);
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
pub(crate) struct RootPlacement<I> {
    #[cfg(verus_keep_ghost)]
    pub(crate) evidence: Ghost<RootEvidence<I>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[cfg(verus_keep_ghost)]
verus! {
#[verifier::reject_recursive_types(I)]
pub(crate) struct RootStart<I> {
    pub inputs: modes::SiblingInputs<I>,
    pub root: I,
    pub ordinary: bool,
    pub size: [f32; 2],
    pub scale: Option<f32>,
    pub writes: Seq<I>,
    pub rectangles: Map<I, (Edges, Edges)>,
}

#[verifier::reject_recursive_types(I)]
pub(crate) struct RootEvidence<I> {
    pub start: RootStart<I>,
    pub links: node::PlacementLinks<I>,
    pub partial: bool,
    pub frame: Option<(I, Edges, Option<f32>)>,
    pub writes: Seq<I>,
    pub rectangles: Map<I, (Edges, Edges)>,
}

impl<I> RootEvidence<I> {
    pub(crate) open spec fn valid(self) -> bool {
        &&& self.links == self.start.inputs.links
        &&& self.links.finite() && self.links.cost(Some(self.start.root)) > 0
        &&& self.frame == if (self.start.inputs.hidden)(self.start.root) { None } else {
            let [width, height] = self.start.size;
            Some((self.start.root, [[0.0f32, width], [0.0f32, height]], self.start.scale))
        }
        &&& (self.start.ordinary || !self.partial) ==> self.writes == self.start.writes
            + modes::subtree_writes(self.start.inputs, self.start.root, self.partial)
    }
}

pub(crate) open spec fn ordered_writes<I>(
    links: node::PlacementLinks<I>, rows: Seq<I>, first: nat, limit: nat,
) -> bool {
    &&& forall|i: int| 0 <= i < rows.len() ==> first <= links.rank(#[trigger] rows[i]) < limit
    &&& forall|i: int, j: int| 0 <= i < j < rows.len()
        ==> links.rank(#[trigger] rows[i]) < links.rank(#[trigger] rows[j])
}

proof fn join_writes<I>(links: node::PlacementLinks<I>, left: Seq<I>, right: Seq<I>, first: nat, middle: nat, limit: nat)
    requires first <= middle <= limit,
        ordered_writes(links, left, first, middle), ordered_writes(links, right, middle, limit),
    ensures ordered_writes(links, left + right, first, limit),
{
    let rows = left + right;
    assert forall|i: int| 0 <= i < rows.len() implies first <= links.rank(#[trigger] rows[i]) < limit by {
        if i < left.len() { assert(rows[i] == left[i]); }
        else { assert(rows[i] == right[i - left.len()]); }
    }
    assert forall|i: int, j: int| 0 <= i < j < rows.len()
        implies links.rank(#[trigger] rows[i]) < links.rank(#[trigger] rows[j]) by {
        if j < left.len() {
            assert(rows[i] == left[i] && rows[j] == left[j]);
        } else if i < left.len() {
            assert(rows[i] == left[i] && rows[j] == right[j - left.len()]);
        } else {
            assert(rows[i] == right[i - left.len()] && rows[j] == right[j - left.len()]);
        }
    }
}

proof fn subtree_write_ranks<I>(inputs: modes::SiblingInputs<I>, id: I, partial: bool)
    requires inputs.links.finite(), inputs.links.cost(Some(id)) > 0,
    ensures ordered_writes(inputs.links, modes::subtree_writes(inputs, id, partial),
        inputs.links.rank(id), inputs.links.end(id)),
    decreases inputs.links.cost(Some(id)), 0int,
{
    let links = inputs.links;
    let own = modes::sibling_write(inputs, id, partial);
    let boundary = links.rank(id) + 1;
    assert(links.covers(id));
    assert(ordered_writes(links, own, links.rank(id), boundary));
    let descendants = match modes::sibling_child(inputs, id, partial) {
        Some((_, child, pending)) => {
            assert(links.first(id) == Some(child));
            let rows = modes::forest_writes(inputs, Some(child), pending);
            forest_write_ranks(inputs, child, pending);
            assert(ordered_writes(links, rows, boundary, links.end(id)));
            rows
        },
        None => Seq::empty(),
    };
    join_writes(links, own, descendants, links.rank(id), boundary, links.end(id));
}

proof fn forest_write_ranks<I>(inputs: modes::SiblingInputs<I>, id: I, partial: bool)
    requires inputs.links.finite(), inputs.links.cost(Some(id)) > 0,
    ensures ordered_writes(inputs.links, modes::forest_writes(inputs, Some(id), partial),
        inputs.links.rank(id), inputs.links.limit(id)),
    decreases inputs.links.cost(Some(id)), 1int,
{
    let links = inputs.links;
    assert(links.covers(id));
    let branch = modes::subtree_writes(inputs, id, partial);
    subtree_write_ranks(inputs, id, partial);
    let rest = match links.next(id) {
        Some(sibling) => {
            forest_write_ranks(inputs, sibling, partial);
            let rows = modes::forest_writes(inputs, Some(sibling), partial);
            assert(ordered_writes(links, rows, links.end(id), links.limit(id)));
            rows
        },
        None => Seq::empty(),
    };
    modes::forest_starts_with_subtree(inputs, id, partial);
    assert(rest =~= modes::forest_writes(inputs, links.next(id), partial));
    assert(modes::forest_writes(inputs, Some(id), partial) == branch + rest);
    join_writes(links, branch, rest, links.rank(id), links.end(id), links.limit(id));
}

/// A rooted full or ordinary placement publishes a live ID at most once in its pass.
pub(crate) proof fn root_writes_distinct<I>(evidence: RootEvidence<I>)
    requires evidence.valid(), evidence.start.ordinary || !evidence.partial,
    ensures evidence.writes.skip(evidence.start.writes.len() as int).no_duplicates(),
{
    let root = evidence.start.root;
    let fresh = evidence.writes.skip(evidence.start.writes.len() as int);
    let selected = modes::subtree_writes(evidence.start.inputs, root, evidence.partial);
    assert(fresh =~= selected);
    subtree_write_ranks(evidence.start.inputs, root, evidence.partial);
    assert forall|i: int, j: int| 0 <= i < fresh.len() && 0 <= j < fresh.len() && i != j
        implies #[trigger] fresh[i] != #[trigger] fresh[j] by {
        if i < j { assert(evidence.links.rank(fresh[i]) < evidence.links.rank(fresh[j])); }
        else { assert(evidence.links.rank(fresh[j]) < evidence.links.rank(fresh[i])); }
    }
}

proof fn subtree_writes_within_full<I>(
    candidate: modes::SiblingInputs<I>, reference: modes::SiblingInputs<I>, root: I, partial: bool, id: I,
)
    requires candidate.links == reference.links, candidate.hidden == reference.hidden,
        candidate.links.finite(), candidate.links.covers(root),
    ensures
        !partial ==> modes::subtree_writes(candidate, root, partial) == modes::subtree_writes(reference, root, false),
        modes::subtree_writes(candidate, root, partial).contains(id)
            ==> modes::subtree_writes(reference, root, false).contains(id),
    decreases candidate.links.cost(Some(root)), 0int,
{
    let own = modes::sibling_write(candidate, root, partial);
    let full_own = modes::sibling_write(reference, root, false);
    assert(own == full_own || own.len() == 0);
    assert(!partial ==> own == full_own);
    let selected = modes::sibling_child(candidate, root, partial);
    let forced = modes::sibling_child(reference, root, false);
    let children = match selected {
        Some((_, child, child_partial)) => {
            assert(forced == Some((root, child, false)));
            assert(candidate.links.first(root) == Some(child));
            forest_writes_within_full(candidate, reference, child, child_partial, id);
            modes::forest_writes(candidate, Some(child), child_partial)
        },
        None => Seq::empty(),
    };
    let full_children = match forced {
        Some((_, child, _)) => modes::forest_writes(reference, Some(child), false),
        None => Seq::empty(),
    };
    assert(!partial ==> selected == forced);
    assert(!partial ==> children == full_children);
    assert(children.contains(id) ==> full_children.contains(id));
    concat_contains(own, children, id);
    concat_contains(full_own, full_children, id);
}

proof fn concat_contains<I>(left: Seq<I>, right: Seq<I>, id: I)
    ensures (left + right).contains(id) == (left.contains(id) || right.contains(id)),
{
    let joined = left + right;
    if joined.contains(id) {
        let i = choose|i: int| 0 <= i < joined.len() && joined[i] == id;
        if i < left.len() {
            assert(left[i] == id);
        } else {
            assert(right[i - left.len()] == id);
        }
    } else if left.contains(id) {
        let i = choose|i: int| 0 <= i < left.len() && left[i] == id;
        assert(joined[i] == id);
    } else if right.contains(id) {
        let i = choose|i: int| 0 <= i < right.len() && right[i] == id;
        assert(joined[left.len() + i] == id);
    }
}

proof fn forest_writes_within_full<I>(
    candidate: modes::SiblingInputs<I>, reference: modes::SiblingInputs<I>, first: I, partial: bool, id: I,
)
    requires candidate.links == reference.links, candidate.hidden == reference.hidden,
        candidate.links.finite(), candidate.links.covers(first),
    ensures
        !partial ==> modes::forest_writes(candidate, Some(first), partial)
            == modes::forest_writes(reference, Some(first), false),
        modes::forest_writes(candidate, Some(first), partial).contains(id)
            ==> modes::forest_writes(reference, Some(first), false).contains(id),
    decreases candidate.links.cost(Some(first)), 1int,
{
    subtree_writes_within_full(candidate, reference, first, partial, id);
    modes::forest_starts_with_subtree(candidate, first, partial);
    modes::forest_starts_with_subtree(reference, first, false);
    let following = candidate.links.next(first);
    if let Some(next) = following {
        forest_writes_within_full(candidate, reference, next, partial, id);
    } else {
        assert(modes::forest_writes(candidate, following, partial)
            =~= modes::forest_writes(reference, following, false));
    }
    let left = modes::subtree_writes(candidate, first, partial);
    let right = modes::forest_writes(candidate, following, partial);
    concat_contains(left, right, id);
    concat_contains(modes::subtree_writes(reference, first, false), modes::forest_writes(reference, following, false), id);
}

/// Compare the IDs visited by two actual root placements of the same visible
/// tree. Full passes agree even when they choose different placement kernels.
/// A partial pass emits an ordered selection of those same IDs.
pub(crate) proof fn root_writes_follow_full_order<I>(candidate: RootEvidence<I>, reference: RootEvidence<I>, id: I)
    requires candidate.valid(), reference.valid(), !reference.partial,
        candidate.start.ordinary || !candidate.partial,
        candidate.start.root == reference.start.root, candidate.links == reference.links,
        candidate.start.inputs.hidden == reference.start.inputs.hidden,
    ensures ({
        let actual = candidate.writes.skip(candidate.start.writes.len() as int);
        let full = reference.writes.skip(reference.start.writes.len() as int);
        &&& !candidate.partial ==> actual == full
        &&& actual.contains(id) ==> full.contains(id)
        &&& ordered_writes(candidate.links, actual, candidate.links.rank(candidate.start.root),
            candidate.links.end(candidate.start.root))
        &&& ordered_writes(reference.links, full, reference.links.rank(reference.start.root),
            reference.links.end(reference.start.root))
    }),
{
    let a = candidate.start.inputs;
    let b = reference.start.inputs;
    let root = candidate.start.root;
    let actual = candidate.writes.skip(candidate.start.writes.len() as int);
    let full = reference.writes.skip(reference.start.writes.len() as int);
    assert(actual =~= modes::subtree_writes(a, root, candidate.partial));
    assert(full =~= modes::subtree_writes(b, root, false));
    subtree_writes_within_full(a, b, root, candidate.partial, id);
    subtree_write_ranks(a, root, candidate.partial);
    subtree_write_ranks(b, root, false);
}

pub(crate) open spec fn start_at<I, T: RootPlacementTarget<I>>(tree: &T) -> RootStart<I> {
    RootStart {
        inputs: modes::sibling_inputs(tree), root: tree.root_key(), ordinary: tree.plain(),
        size: tree.solved_size(tree.root_key()), scale: tree.configured_scale(),
        writes: tree.written(), rectangles: tree.rectangles(),
    }
}

fn save_root<I, T: RootPlacementTarget<I>>(tree: &T) -> (start: Ghost<RootStart<I>>)
    ensures start@ == start_at(tree), no_unwind
{ Ghost(start_at(tree)) }

fn save_root_plan<I: Copy>(plan: Option<(I, Edges, Option<f32>)>)
    -> (evidence: Ghost<Option<(I, Edges, Option<f32>)>>)
    ensures evidence@ == plan, no_unwind
{ Ghost(plan) }

fn placed_root<I, T: RootPlacementTarget<I>, const PARTIAL: bool>(
    tree: &T, start: Ghost<RootStart<I>>, frame: Ghost<Option<(I, Edges, Option<f32>)>>,
) -> (evidence: Ghost<RootEvidence<I>>)
    ensures evidence@ == (RootEvidence { start: start@, links: tree.links(), partial: PARTIAL,
        frame: frame@, writes: tree.written(), rectangles: tree.rectangles() }),
    no_unwind
{ Ghost(RootEvidence { start: start@, links: tree.links(), partial: PARTIAL,
    frame: frame@, writes: tree.written(), rectangles: tree.rectangles() }) }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placement => ensures placement.evidence@ == evidence@, no_unwind))]
fn placement<I>(#[cfg(verus_keep_ghost)] evidence: Ghost<RootEvidence<I>>) -> RootPlacement<I> {
    RootPlacement {
        #[cfg(verus_keep_ghost)]
        evidence,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

/// Clear the scale-change flag, prepare the requested rounding backend, and
/// publish the visible root and descendants under the same ordered links.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires order@.ordered(), old(tree).links() == node::PlacementLinks::from_order(order@),
    ensures final(tree).links() == old(tree).links(),
        (old(tree).plain() || !PARTIAL) ==> final(tree).written() == old(tree).written()
            + modes::subtree_writes(modes::sibling_inputs(old(tree)), old(tree).root_key(), PARTIAL),
        result.evidence@.valid(), result.evidence@.partial == PARTIAL,
        result.evidence@.start == start_at(old(tree)), result.evidence@.links == final(tree).links(),
        result.evidence@.writes == final(tree).written(), result.evidence@.rectangles == final(tree).rectangles(),
    no_unwind
))]
pub(crate) fn root<
    I: Copy, T: RootPlacementTarget<I>, M: StackMath + FloatBounds, V: VecMemory, const N: usize, const PARTIAL: bool,
>(tree: &mut T, #[cfg(verus_keep_ghost)] order: Ghost<crate::prepare_frame::Order<I>>) -> RootPlacement<I> {
    #[cfg(verus_keep_ghost)]
    proof! { node::finite_from_order(order@); }
    #[cfg(verus_keep_ghost)]
    let start = save_root(tree);
    let plan = modes::root_plan(tree);
    #[cfg(verus_keep_ghost)]
    let planned = save_root_plan(plan);
    let Some((root, rect, scale)) = plan else {
        return placement(#[cfg(verus_keep_ghost)] placed_root::<_, _, PARTIAL>(tree, start, planned));
    };
    tree.prepare_rounding(scale);
    #[cfg(verus_keep_ghost)]
    proof! {
        if old(tree).plain() || !PARTIAL {
            let before = modes::sibling_inputs(old(tree));
            let after = modes::sibling_inputs(tree);
            modes::preserved_marks(before, after, before.links.rank(root));
            modes::subtrees_keep_unvisited_marks(before, after, root, PARTIAL);
        }
    }
    modes::place_subtree::<_, _, M, V, N, PARTIAL>(tree, root, rect, [0.0, 0.0]);
    placement(#[cfg(verus_keep_ghost)] placed_root::<_, _, PARTIAL>(tree, start, planned))
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait FreeTarget<I>: ParentTarget<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).links() == old(self).links(), no_unwind))]
    fn mark_repositioned(&mut self, node: I);
}

/// Check an independent subtree and publish it only after every required
/// sizing read is ready.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires order@.ordered(), order@.closed_subtrees(), (order@.live)(node),
        old(tree).links() == node::PlacementLinks::from_order(order@),
        free_placement_order::preflight_links(old(tree), order@),
    ensures final(tree).links() == old(tree).links(),
        result.is_err() ==> final(tree).written() == old(tree).written()
            && final(tree).rectangles() == old(tree).rectangles(),
    no_unwind
))]
pub(crate) fn free<
    I: Copy, T: FreeTarget<I> + RootPlacementTarget<I> + PreflightHost<Id = I>,
    M: StackMath + FloatBounds, V: VecMemory, const N: usize,
>(tree: &mut T, node: I, parent_rect: Edges, #[cfg(verus_keep_ghost)] order: Ghost<crate::prepare_frame::Order<I>>)
    -> Result<(), FreePlacementError>
{
    let root = tree.root_id();
    #[cfg(verus_keep_ghost)]
    proof! {
        node::finite_from_order(order@);
        free_placement_order::subtree_preflight_order(tree, node, order@);
    }
    #[cfg(verus_keep_ghost)]
    let witness = free_order(order, node);
    let parent = match free_placement::preflight(tree, root, node, #[cfg(verus_keep_ghost)] witness) {
        Ok(parent) => parent,
        Err(error) => return Err(error),
    };
    let scale = tree.pixel_scale();
    tree.prepare_rounding(scale);
    free_admitted::<_, _, M, V, N>(tree, parent, node, parent_rect);
    Ok(())
}

#[cfg(verus_keep_ghost)]
verus! {
fn free_order<I>(order: Ghost<crate::prepare_frame::Order<I>>, root: I) -> (witness: Ghost<free_placement_order::PreflightOrder<I>>)
    ensures witness@ == free_placement_order::PreflightOrder::from_order(order@, root),
    no_unwind
{ Ghost(free_placement_order::PreflightOrder::from_order(order@, root)) }
}

/// A successful preflight admits this node and parent. The caller has prepared
/// the optional rounding backend for the same pass.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tree).links().finite(), old(tree).links().cost(Some(node)) > 0,
    ensures final(tree).links() == old(tree).links(),
    no_unwind
))]
fn free_admitted<
    I: Copy, T: FreeTarget<I>, M: StackMath + FloatBounds, V: VecMemory, const N: usize,
>(tree: &mut T, parent: I, node: I, parent_rect: Edges) {
    let origin = node::snapped_origin(node::NodeTarget::snap(tree, parent_rect));
    let modes::ParentStyle { padding, flipped, .. } = tree.parent_style(parent);
    let frame = Frame { edges: parent_rect, origin, padding, flipped };
    let size = tree.size(node);
    let rect = modes::free_rect(tree, node, &frame, size);
    modes::place_subtree::<_, _, M, V, N, false>(tree, node, rect, origin);
    tree.mark_repositioned(node);
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tree).links().finite(), old(tree).links().cost(Some(parent)) > 0,
        old(tree).links().first(parent) == Some(first),
    ensures final(tree).links() == old(tree).links(),
        (old(tree).plain() || !PARTIAL) ==> final(tree).written()
            == old(tree).written() + modes::forest_writes(modes::sibling_inputs(old(tree)), Some(first), PARTIAL),
    no_unwind
))]
pub(crate) fn children<
    I: Copy, T: ParentTarget<I>, M: StackMath + FloatBounds, V: VecMemory, const N: usize, const PARTIAL: bool,
>(tree: &mut T, parent: I, first: I, rect: Edges, origin: [f32; 2]) {
    #[cfg(verus_keep_ghost)]
    proof! { assert(tree.links().covers(parent)); }
    modes::walk::<_, _, M, V, N>(tree, Branch { parent, first, rect, origin, partial: PARTIAL });
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(placed =>
    ensures final(tree).links() == old(tree).links(),
        placed ==> old(tree).links().first(child).is_none(),
        final(tree).written() == if placed { old(tree).written().push(child) } else { old(tree).written() },
        !placed ==> final(tree).rectangles() == old(tree).rectangles(),
        placed ==> final(tree).rectangles() == old(tree).rectangles().insert(child, final(tree).rectangles()[child]),
    no_unwind
))]
pub(crate) fn append<I: Copy, T: ParentTarget<I> + RootTarget<I>, M: StackMath>(
    tree: &mut T, parent: I, child: I, rect: Edges, previous: Option<(I, Edges)>,
) -> bool {
    let rounded = tree.pixel_scale().is_some();
    modes::append_stack_leaf::<_, _, M>(tree, parent, child, rect, previous, rounded)
}
