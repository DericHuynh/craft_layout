//! Apply selected structural regions in their planned order.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
use super::plan;
#[path = "block_replay.rs"]
pub(crate) mod block;
use crate::declarations::{Axis, Size, X, Y};
use crate::sizing_pass;
use crate::vec_memory::VecMemory;
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::Kind;
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel::Kind, prepare_frame::Order, prepare_nodes::live};
#[cfg(not(verus_keep_ghost))]
use super::{IncrementalRelayoutOutcome, PlacementWork};
#[cfg(verus_keep_ghost)]
use crate::{placement::kernel::PlacementWork, publication::IncrementalRelayoutOutcome};

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub(crate) struct Totals {
    pub nodes: u32,
    pub slots: u32,
    pub blocks: usize,
}

impl Totals {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.include(other), no_unwind))]
    pub(crate) fn include(self, other: Totals) -> Totals {
        Totals {
            nodes: self.nodes.saturating_add(other.nodes),
            slots: self.slots.saturating_add(other.slots),
            blocks: self.blocks.saturating_add(other.blocks),
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn included<I>(initial: Totals, measured: Seq<(I, Totals)>) -> Totals
    decreases measured.len(),
{
    if measured.len() == 0 { initial }
    else { included(initial, measured.drop_last()).include(measured.last().1) }
}

pub(crate) open spec fn ids<I>(measured: Seq<(I, Totals)>) -> Seq<I> {
    Seq::new(measured.len(), |i: int| measured[i].0)
}

#[verifier::reject_recursive_types(I)]
pub(crate) struct RegionWork<I> {
    pub complete: bool,
    pub chosen: Seq<I>,
    pub initial: Totals,
    pub measured: Seq<(I, Totals)>,
    pub prepared: Seq<sizing_pass::RegionPrepared<I>>,
    // Before choosing cuts and again before regional measurement starts.
    pub planning: plan::SizingCache<I>,
}

impl<I> RegionWork<I> {
    pub(crate) open spec fn valid(self, outcome: IncrementalRelayoutOutcome) -> bool {
        &&& self.prepared.len() == self.measured.len()
        &&& self.measured.len() <= self.chosen.len()
        &&& ids(self.measured) == self.chosen.take(self.measured.len() as int)
        &&& if !self.complete {
            self.measured.len() == 0 && outcome is FallbackTooMuchWork
        } else if self.measured.len() < self.chosen.len() {
            outcome is FallbackFlow
        } else {
            outcome == (IncrementalRelayoutOutcome::Success { computed: included(self.initial, self.measured).slots })
        }
    }

    pub(crate) open spec fn prepared_in(self, order: Order<I>) -> bool {
        &&& self.planning.order == order
        &&& forall |i: int| 0 <= i < self.measured.len() ==>
            (#[trigger] self.prepared[i]).valid(order, self.measured[i].0, false)
    }
}

fn region_work<I>(complete: bool, regions: &[I], initial: Totals, measured: Ghost<Seq<(I, Totals)>>,
    prepared: Ghost<Seq<sizing_pass::RegionPrepared<I>>>, planning: Ghost<plan::SizingCache<I>>,
)
    -> (work: Ghost<RegionWork<I>>)
    ensures work@ == (RegionWork { complete, chosen: regions@, initial, measured: measured@, prepared: prepared@, planning: planning@ }),
    no_unwind
{
    Ghost(RegionWork { complete, chosen: regions@, initial, measured: measured@, prepared: prepared@, planning: planning@ })
}

fn planning_observation<A: crate::prepare_nodes::Records + ?Sized>(scene: &A) -> (cache: Ghost<plan::SizingCache<A::Id>>)
    ensures cache@ == plan::sizing_cache(scene), no_unwind
{ Ghost(plan::sizing_cache(scene)) }

use crate::dependencies::sizing_requests::{self as requests, Request, Topology};

/// A sizing source and the planner have the same physical parent/child links.
/// Prepared flags can select a dependency without changing its physical ID.
pub(crate) open spec fn physical_request_links<I: Copy>(order: Order<I>, topology: Topology<I>, slot: Request<I>) -> bool {
    &&& (topology.parent)(slot.node) == (order.parent)(slot.node)
    &&& (topology.stack_parent)(slot).is_some() ==> (topology.stack_parent)(slot) == (order.parent)(slot.node)
    &&& requests::live::chain(requests::live::child_ids(topology, slot.node), (order.first)(slot.node), order.sibling)
    &&& requests::live::chain(requests::live::block_ids(topology, slot.node), (order.first)(slot.node), order.sibling)
}

proof fn child_row_link<I>(order: Order<I>, parent: I, rows: Seq<I>, at: nat)
    requires order.ordered(), (order.live)(parent), at < rows.len(),
        requests::live::chain(rows, (order.first)(parent), order.sibling),
    ensures order.child(parent, rows[at as int]),
    decreases at,
{
    if at == 0 {
        order.node_facts(parent);
        assert((order.first)(parent) == Some(rows[0]));
    } else {
        let previous = (at - 1) as nat;
        child_row_link(order, parent, rows, previous);
        let child = rows[previous as int];
        order.node_facts(child);
        assert((order.sibling)(child) == Some(rows[at as int]));
    }
}

pub(crate) proof fn request_has_physical_neighbor<I: Copy>(order: Order<I>, topology: Topology<I>, reader: Request<I>, at: int)
    requires order.ordered(), (order.live)(reader.node), physical_request_links(order, topology, reader),
        0 <= at < requests::inputs(topology, reader).len(),
    ensures ({
        let target = requests::inputs(topology, reader)[at].node;
        &&& (order.live)(target)
        &&& target == reader.node || order.child(target, reader.node) || order.child(reader.node, target)
    }),
{
    let id = reader.node;
    let ordinary = requests::live::child_ids(topology, id);
    let block = requests::live::block_ids(topology, id);
    let local = ordinary.to_set().union(block.to_set()).insert(id);
    let neighbors = match (order.parent)(id) {
        Some(parent) => local.insert(parent),
        None => local,
    };
    assert(requests::live::optional(neighbors, (topology.parent)(id)));
    assert(requests::live::optional(neighbors, (topology.stack_parent)(reader)));
    assert forall |i: int| 0 <= i < (topology.children)(id).len()
        implies neighbors.contains((#[trigger] (topology.children)(id)[i]).node) by {
        let child = (topology.children)(id)[i].node;
        assert(ordinary[i] == child);
        assert(ordinary.contains(child));
    }
    assert forall |i: int| 0 <= i < (topology.block_children)(id).len()
        implies neighbors.contains((#[trigger] (topology.block_children)(id)[i]).id) by {
        let child = (topology.block_children)(id)[i].id;
        assert(block[i] == child);
        assert(block.contains(child));
    }
    requests::live::inputs_stay_in_neighborhood(topology, neighbors, reader);
    let input = requests::inputs(topology, reader)[at].node;
    assert(neighbors.contains(input));
    if input != id {
        if (order.parent)(id) == Some(input) {
            assert((order.live)(input) && order.child(input, id));
        } else if ordinary.contains(input) {
            let i = choose |i: int| 0 <= i < ordinary.len() && ordinary[i] == input;
            child_row_link(order, id, ordinary, i as nat);
        } else {
            assert(block.contains(input));
            let i = choose |i: int| 0 <= i < block.len() && block[i] == input;
            child_row_link(order, id, block, i as nat);
        }
    }
}

/// A sizing edge can cross a subtree only via its root and the root's parent.
/// This classifies IDs from the same request list the sizing engine emits.
pub(crate) proof fn request_crosses_cut_at_root<I: Copy>(
    order: Order<I>, topology: Topology<I>, cut: I, reader: Request<I>, at: int,
)
    requires order.ordered(), order.closed_subtrees(), (order.live)(cut), (order.live)(reader.node),
        physical_request_links(order, topology, reader), 0 <= at < requests::inputs(topology, reader).len(),
    ensures ({
        let target = requests::inputs(topology, reader)[at].node;
        &&& order.inside(cut, reader.node) && !order.inside(cut, target)
            ==> reader.node == cut && order.child(target, cut)
        &&& !order.inside(cut, reader.node) && order.inside(cut, target)
            ==> target == cut && order.child(reader.node, cut)
    }),
{
    request_has_physical_neighbor(order, topology, reader, at);
    let target = requests::inputs(topology, reader)[at].node;
    if order.inside(cut, reader.node) && !order.inside(cut, target) {
        assert(!order.child(reader.node, target));
        assert(order.child(target, reader.node));
        if reader.node != cut {
            assert(order.inside(cut, (order.parent)(reader.node).unwrap()));
        }
    } else if !order.inside(cut, reader.node) && order.inside(cut, target) {
        assert(!order.child(target, reader.node));
        assert(order.child(reader.node, target));
        if target != cut {
            assert(order.inside(cut, (order.parent)(target).unwrap()));
        }
    }
}

/// An in-cut request at an independent Free edge can pull only the
/// corresponding Final of the physical parent. The exact layout flags of
/// Free exclude stack shares, Flow and cross-axis grid metadata there.
pub(crate) proof fn free_cut_reads_only_parent_final<I: Copy>(
    order: Order<I>, topology: Topology<I>, cut: I, reader: Request<I>, at: int,
)
    requires order.ordered(), order.closed_subtrees(), (order.live)(cut),
        order.inside(cut, reader.node), physical_request_links(order, topology, reader),
        0 <= at < requests::inputs(topology, reader).len(),
        !order.inside(cut, requests::inputs(topology, reader)[at].node),
        (topology.stack_parent)(reader).is_none(),
        forall |parent: I| (order.parent)(cut) == Some(parent) ==>
            !(#[trigger] (topology.parent_flow)(reader, parent)) && !(topology.parent_other)(reader, parent),
    ensures ({
        let input = requests::inputs(topology, reader)[at];
        reader.node == cut && (order.parent)(cut) == Some(input.node)
            && input.kind is Final && input.vertical == reader.vertical
    }),
{
    let input = requests::inputs(topology, reader)[at];
    request_crosses_cut_at_root(order, topology, cut, reader, at);
    if !(requests::live::declaration_input(topology, reader) is ParentFinal) {
        let ordinary = requests::live::child_ids(topology, cut);
        let block = requests::live::block_ids(topology, cut);
        let local = ordinary.to_set().union(block.to_set()).insert(cut);
        assert forall |i: int| 0 <= i < (topology.children)(cut).len() implies
            local.contains((#[trigger] (topology.children)(cut)[i]).node) by {
            let child = (topology.children)(cut)[i].node;
            assert(ordinary[i] == child && ordinary.contains(child));
        }
        assert forall |i: int| 0 <= i < (topology.block_children)(cut).len() implies
            local.contains((#[trigger] (topology.block_children)(cut)[i]).id) by {
            let child = (topology.block_children)(cut)[i].id;
            assert(block[i] == child && block.contains(child));
        }
        requests::live::inputs_stay_in_neighborhood(topology, local, reader);
        assert(local.contains(input.node));
        if ordinary.contains(input.node) {
            let i = choose |i: int| 0 <= i < ordinary.len() && ordinary[i] == input.node;
            child_row_link(order, cut, ordinary, i as nat);
        } else {
            let i = choose |i: int| 0 <= i < block.len() && block[i] == input.node;
            child_row_link(order, cut, block, i as nat);
        }
        assert(false);
    }
    assert((topology.parent)(cut) == Some(input.node));
    assert(!(topology.parent_flow)(reader, input.node));
    assert(requests::inputs(topology, reader) == seq![requests::target(input.node, reader.vertical, Kind::Final)]);
}

/// Distinct cuts returned by the production planner cannot directly depend on
/// one another. An outside parent may still mediate a dependency.
pub(crate) proof fn selected_cuts_have_no_direct_sizing_edge<I: Copy>(
    order: Order<I>, topology: Topology<I>, chosen: Seq<I>, reader_cut: int, target_cut: int,
    reader: Request<I>, at: int,
)
    requires order.ordered(), order.closed_subtrees(), plan::ordered_cuts(chosen, order),
        0 <= reader_cut < chosen.len(), 0 <= target_cut < chosen.len(), reader_cut != target_cut,
        (order.live)(chosen[reader_cut]), (order.live)(chosen[target_cut]),
        order.inside(chosen[reader_cut], reader.node), physical_request_links(order, topology, reader),
        0 <= at < requests::inputs(topology, reader).len(),
    ensures !order.inside(chosen[target_cut], requests::inputs(topology, reader)[at].node),
{
    let from = chosen[reader_cut];
    let to = chosen[target_cut];
    let target = requests::inputs(topology, reader)[at].node;
    if reader_cut < target_cut {
        assert((order.interval)(from).1 <= (order.interval)(to).0);
    } else {
        assert((order.interval)(to).1 <= (order.interval)(from).0);
    }
    if order.inside(to, target) {
        assert(!order.inside(from, target));
        request_crosses_cut_at_root(order, topology, from, reader, at);
        assert(reader.node == from && order.child(target, from));
        assert(order.inside(to, reader.node));
        assert(false);
    }
}

/// The finite canonical graph encodes the native requests in their emitted order.
pub(crate) open spec fn canonical_requests_at_cut<I: Copy>(
    frame: crate::replay_view::Replay, order: Order<I>, topology: Topology<I>, cut: I,
    decode: spec_fn(int) -> Request<I>,
) -> bool {
    &&& forall |key: int| #[trigger] frame.inside(key) == (0 <= key < frame.n && order.inside(cut, decode(key).node))
    &&& forall |key: int| 0 <= key < frame.n ==> {
        let reader = #[trigger] decode(key);
        &&& (order.live)(reader.node)
        &&& physical_request_links(order, topology, reader)
        &&& (frame.edges)(key).len() == requests::inputs(topology, reader).len()
    }
    &&& forall |key: int, j: int| 0 <= key < frame.n && 0 <= j < (frame.edges)(key).len() ==>
        decode(#[trigger] (frame.edges)(key)[j]) == requests::inputs(topology, decode(key))[j]
    &&& forall |key: int| !(0 <= key < frame.n) ==> (#[trigger] (frame.edges)(key)).len() == 0
}

/// Cross-region readiness is needed only for edges between the cut root and
/// its physical parent. Closing the cut also preserves seeded and pinned words.
pub(crate) proof fn physical_parent_boundary_closes_cut<I: Copy>(
    frame: crate::replay_view::Replay, order: Order<I>, topology: Topology<I>, cut: I,
    decode: spec_fn(int) -> Request<I>,
)
    requires order.ordered(), order.closed_subtrees(), (order.live)(cut),
        canonical_requests_at_cut(frame, order, topology, cut, decode),
        crate::cycles::dfs::bounded(frame.document(), frame.edges, frame.n),
        forall |i: int| 0 <= i < frame.visits.len() ==> (#[trigger] frame.visits[i]).owned_by(frame.owner),
        forall |key: int| #[trigger] frame.inside(key) ==> {
            &&& (frame.initial_state)(key) == (frame.regional_state)(key)
            &&& frame.initial.contains_key(key) && frame.cached.contains_key(key)
            &&& frame.cached[key] == frame.initial[key]
        },
        forall |key: int| #[trigger] frame.pinned(key) ==> {
            &&& frame.initial.contains_key(key) && frame.cached.contains_key(key)
            &&& frame.cached[key] == frame.initial[key]
        },
        forall |key: int, j: int| 0 <= key < frame.n && 0 <= j < (frame.edges)(key).len() ==> {
            let input = #[trigger] (frame.edges)(key)[j];
            &&& (order.parent)(cut) == Some(decode(key).node) && decode(input).node == cut
                ==> (frame.initial_state)(key) == crate::cycles::kernel::SOLVED
            &&& decode(key).node == cut && (order.parent)(cut) == Some(decode(input).node)
                ==> (frame.initial_state)(input) == crate::cycles::kernel::SOLVED
        },
    ensures frame.closed(),
{
    assert forall |key: int, j: int| 0 <= j < (frame.edges)(key).len() implies {
        let input = #[trigger] (frame.edges)(key)[j];
        &&& !frame.inside(key) && frame.inside(input) ==> (frame.initial_state)(key) == crate::cycles::kernel::SOLVED
        &&& frame.inside(key) && !frame.inside(input) ==> frame.pinned(input)
    } by {
        let input = (frame.edges)(key)[j];
        assert(0 <= key < frame.n);
        assert(0 <= input < frame.n);
        let reader = decode(key);
        let target = decode(input);
        assert(target == requests::inputs(topology, reader)[j]);
        if frame.inside(key) != frame.inside(input) {
            request_crosses_cut_at_root(order, topology, cut, reader, j);
        }
    }
    assert(frame.scheduled());
}

pub(crate) open spec fn document_root<I>(order: Order<I>, root: I) -> bool {
    &&& (order.live)(root)
    &&& (order.parent)(root).is_none()
    &&& forall |node: I| #[trigger] (order.live)(node) && (order.parent)(node).is_none() ==> node == root
}

proof fn root_contains_live_node<I>(order: Order<I>, root: I, node: I)
    requires order.ordered(), document_root(order, root), (order.live)(node),
    ensures order.inside(root, node),
    decreases (order.depth)(node),
{
    order.node_facts(node);
    if node != root {
        assert((order.parent)(node).is_some());
        let parent = (order.parent)(node).unwrap();
        assert((order.live)(parent) && order.child(parent, node));
        root_contains_live_node(order, root, parent);
    }
}

pub(crate) proof fn document_root_closes_region<I>(order: Order<I>, root: I)
    requires order.ordered(), document_root(order, root),
    ensures forall |node: I| #[trigger] (order.live)(node) ==> order.inside(root, node),
{
    assert forall |node: I| #[trigger] (order.live)(node) implies order.inside(root, node) by {
        root_contains_live_node(order, root, node);
    }
}

proof fn complete_region_visits(
    visits: Seq<crate::production_schedule::NodeRequests>, inside: spec_fn(int) -> bool,
)
    requires forall |i: int| 0 <= i < visits.len() ==> inside((#[trigger] visits[i]).node),
    ensures crate::production_schedule::region_nodes(visits, inside) == visits,
    decreases visits.len(),
{
    if visits.len() != 0 {
        let rest = visits.drop_first();
        assert forall |i: int| 0 <= i < rest.len() implies inside((#[trigger] rest[i]).node) by {
            assert(rest[i] == visits[i + 1]);
        }
        complete_region_visits(rest, inside);
        assert(seq![visits.first()] + rest =~= visits);
    }
}

pub(crate) proof fn document_root_keeps_sizing_order(
    order: Order<int>, root: int, visits: Seq<crate::production_schedule::NodeRequests>,
)
    requires order.ordered(), document_root(order, root),
        forall |i: int| 0 <= i < visits.len() ==> (order.live)((#[trigger] visits[i]).node),
    ensures crate::production_schedule::region_nodes(visits, |node: int| order.inside(root, node)) == visits,
{
    document_root_closes_region(order, root);
    let inside = |node: int| order.inside(root, node);
    assert forall |i: int| 0 <= i < visits.len() implies inside((#[trigger] visits[i]).node) by {
        let node = visits[i].node;
        assert((order.live)(node));
        assert(order.inside(root, node));
    }
    complete_region_visits(visits, inside);
}

/// The retained leaf's local input includes the content identity and the
/// unchanged declaration, bound and padding words. For a constrained read,
/// the sizing phase also compares the complete opposite Final word.
pub(crate) proof fn clean_leaf_constraint_replays<L>(
    old_local: L, next_local: L, saved: u32, resolved: u32, opposite_state: u32,
    word: u32, measure: spec_fn(L, u32) -> u32,
)
    requires old_local == next_local, word == measure(old_local, saved),
        crate::cycles::kernel::same_intrinsic_constraint(opposite_state, resolved, saved),
    ensures word == measure(next_local, resolved),
{
}

fn empty_log<I>() -> (log: Ghost<Seq<(I, Totals)>>)
    ensures log@ == Seq::<(I, Totals)>::empty(),
    no_unwind
{
    Ghost(Seq::<(I, Totals)>::empty())
}

fn no_preparations<I>() -> (views: Ghost<Seq<sizing_pass::RegionPrepared<I>>>)
    ensures views@ == Seq::<sizing_pass::RegionPrepared<I>>::empty(), no_unwind
{
    Ghost(Seq::empty())
}

fn record_preparation<I>(prior: Ghost<Seq<sizing_pass::RegionPrepared<I>>>, row: Ghost<sizing_pass::RegionPrepared<I>>)
    -> (next: Ghost<Seq<sizing_pass::RegionPrepared<I>>>)
    ensures next@ == prior@.push(row@), no_unwind
{
    Ghost(prior@.push(row@))
}

fn log_mark<I: Copy>(prior: Ghost<Seq<(I, Totals)>>, node: I, totals: Totals) -> (next: Ghost<Seq<(I, Totals)>>)
    ensures next@ == prior@.push((node, totals)),
    no_unwind
{
    Ghost(prior@.push((node, totals)))
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
pub(crate) struct StructuralResult<I> {
    pub outcome: IncrementalRelayoutOutcome,
    #[cfg(verus_keep_ghost)]
    pub work: Ghost<RegionWork<I>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) struct RootWork<I> {
    pub root: I,
    pub enabled: bool,
    pub parent: Option<I>,
    pub pending: Option<IncrementalRelayoutOutcome>,
    pub direct: Option<Result<u32, ()>>,
    pub general: Option<Totals>,
    pub prepared: Option<sizing_pass::RegionPrepared<I>>,
}

impl<I> RootWork<I> {
    pub(crate) open spec fn valid(self, replay: RootReplay, outcome: IncrementalRelayoutOutcome) -> bool {
        &&& self.prepared.is_some() == self.general.is_some()
        &&& if !self.enabled || self.parent.is_some() || !request_matches(self.pending, replay) {
            self.direct.is_none() && self.general.is_none() && outcome == replay.fallback()
        } else {
            match self.direct {
                Some(Ok(computed)) => computed >= 4 && self.general.is_none()
                    && outcome == (IncrementalRelayoutOutcome::Success { computed }),
                Some(Err(())) => self.general.is_none() && outcome == replay.fallback(),
                None => match self.general {
                    Some(totals) => outcome == (IncrementalRelayoutOutcome::Success { computed: totals.slots }),
                    None => false,
                },
            }
        }
    }

    pub(crate) open spec fn prepared_in(self, order: Order<I>) -> bool {
        self.prepared.is_some() ==> self.prepared.unwrap().valid(order, self.root, true)
    }
}

pub(crate) open spec fn request_matches(pending: Option<IncrementalRelayoutOutcome>, replay: RootReplay) -> bool {
    match replay {
        RootReplay::RegisteredEdits => pending == Some(IncrementalRelayoutOutcome::FallbackFlow),
        RootReplay::IntakeBudget => pending == Some(IncrementalRelayoutOutcome::FallbackTooMuchWork),
        RootReplay::Viewport => pending.is_none(),
    }
}

fn observe_request(pending: &Option<IncrementalRelayoutOutcome>)
    -> (before: Ghost<Option<IncrementalRelayoutOutcome>>)
    ensures before@ == *pending,
    no_unwind
{
    Ghost(*pending)
}

fn no_root_preparation<I>() -> (view: Ghost<Option<sizing_pass::RegionPrepared<I>>>)
    ensures view@.is_none(), no_unwind
{
    Ghost(None)
}

fn root_preparation<I>(prepared: Ghost<sizing_pass::RegionPrepared<I>>)
    -> (view: Ghost<Option<sizing_pass::RegionPrepared<I>>>)
    ensures view@ == Some(prepared@), no_unwind
{
    Ghost(Some(prepared@))
}

fn root_work<I: Copy>(root: I, enabled: bool, parent: Option<I>, pending: Ghost<Option<IncrementalRelayoutOutcome>>,
    direct: Option<Result<u32, ()>>, general: Option<Totals>, prepared: Ghost<Option<sizing_pass::RegionPrepared<I>>>,
) -> (work: Ghost<RootWork<I>>)
    ensures work@ == (RootWork { root, enabled, parent, pending: pending@, direct, general, prepared: prepared@ }),
    no_unwind
{
    Ghost(RootWork { root, enabled, parent, pending: pending@, direct, general, prepared: prepared@ })
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct RootResult<I> {
    pub outcome: IncrementalRelayoutOutcome,
    #[cfg(verus_keep_ghost)]
    pub work: Ghost<RootWork<I>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.outcome == outcome, result.work == work,
    no_unwind
))]
fn root_result<I>(outcome: IncrementalRelayoutOutcome, #[cfg(verus_keep_ghost)] work: Ghost<RootWork<I>>) -> RootResult<I> {
    RootResult {
        outcome,
        #[cfg(verus_keep_ghost)]
        work,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.outcome == outcome, result.work == work,
    no_unwind
))]
fn structural_result<I>(outcome: IncrementalRelayoutOutcome, #[cfg(verus_keep_ghost)] work: Ghost<RegionWork<I>>)
    -> StructuralResult<I>
{
    StructuralResult {
        outcome,
        #[cfg(verus_keep_ghost)]
        work,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Measured<I> {
    totals: Option<Totals>,
    tickets: bool,
    #[cfg(verus_keep_ghost)]
    log: Ghost<Seq<(I, Totals)>>,
    #[cfg(verus_keep_ghost)]
    prepared: Ghost<Seq<sizing_pass::RegionPrepared<I>>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    ensures out.totals == totals, out.tickets == tickets, out.log == log, out.prepared == prepared,
    no_unwind
))]
fn measured<I>(totals: Option<Totals>, tickets: bool, #[cfg(verus_keep_ghost)] log: Ghost<Seq<(I, Totals)>>,
    #[cfg(verus_keep_ghost)] prepared: Ghost<Seq<sizing_pass::RegionPrepared<I>>>,
) -> Measured<I> {
    Measured {
        totals, tickets,
        #[cfg(verus_keep_ghost)]
        log,
        #[cfg(verus_keep_ghost)]
        prepared,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

/// The first unavailable region ends the attempt. Only completely measured
/// regions have their placement marked, and a successful pass covers the list.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires old(scene).order().ordered(), old(scene).order().closed_subtrees(),
        forall |i: int| 0 <= i < regions.len() ==> live(old(scene), #[trigger] regions@[i]),
    ensures final(scene).order() == old(scene).order(),
        out.log@.len() <= regions.len(), ids(out.log@) == regions@.take(out.log@.len() as int),
        out.prepared@.len() == out.log@.len(),
        forall |i: int| 0 <= i < out.log@.len() ==>
            (#[trigger] out.prepared@[i]).valid(old(scene).order(), out.log@[i].0, false),
        match out.totals {
            Some(totals) => out.log@.len() == regions.len() && totals == included(initial, out.log@),
            None => out.log@.len() < regions.len(),
        },
    no_unwind
))]
fn measure_regions<A: Scene + ?Sized>(
    scene: &mut A, regions: &[A::Id], initial: Totals, snapshot: Option<&A::Snapshot>,
) -> Measured<A::Id> {
    let mut index = 0;
    let mut totals = initial;
    let mut tickets = true;
    #[cfg(verus_keep_ghost)]
    let mut log = empty_log();
    #[cfg(verus_keep_ghost)]
    let mut prepared = no_preparations();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= regions.len(), scene.order() == old(scene).order(),
            scene.order().ordered(), scene.order().closed_subtrees(),
            forall |i: int| 0 <= i < regions.len() ==> live(old(scene), #[trigger] regions@[i]),
            log@.len() == index, ids(log@) == regions@.take(index as int),
            prepared@.len() == log@.len(),
            forall |i: int| 0 <= i < log@.len() ==> (#[trigger] prepared@[i]).valid(old(scene).order(), log@[i].0, false),
            totals == included(initial, log@),
        decreases regions.len() - index,
    ))]
    while index < regions.len() {
        let node = regions[index];
        let ticket = if snapshot.is_some() { Some(scene.record(node).topology_index()) } else { None };
        let Some(region_measure) = sizing_pass::measure_region::<_, A::Memory, false>(scene, node) else {
            return measured(None, tickets, #[cfg(verus_keep_ghost)] log, #[cfg(verus_keep_ghost)] prepared);
        };
        let region = Totals { nodes: region_measure.nodes, slots: region_measure.slots, blocks: region_measure.blocks };
        if tickets {
            if let (Some(snapshot), Some(ticket)) = (snapshot, ticket) {
                tickets = scene.restore_tickets(snapshot, node, ticket);
            }
        }
        scene.edit(node).placement = PlacementWork::Subtree;
        totals = totals.include(region);
        #[cfg(verus_keep_ghost)]
        {
            let prior = log;
            let views = prepared;
            log = log_mark(log, node, region);
            prepared = record_preparation(prepared, region_measure.prepared);
            proof! {
                assert forall |i: int| 0 <= i < log@.len() implies
                    (#[trigger] prepared@[i]).valid(old(scene).order(), log@[i].0, false) by {
                    if i < prior@.len() {
                        assert(log@[i] == prior@[i] && prepared@[i] == views@[i]);
                    } else {
                        assert(log@[i] == (node, region) && prepared@[i] == region_measure.prepared@);
                    }
                }
                assert(log@.drop_last() =~= prior@);
                assert(log@.last() == (node, region));
                assert(ids(log@) =~= ids(prior@).push(node));
                assert(regions@.take((index + 1) as int) =~= regions@.take(index as int).push(node));
            }
        }
        index += 1;
    }
    measured(Some(totals), tickets, #[cfg(verus_keep_ghost)] log, #[cfg(verus_keep_ghost)] prepared)
}

/// Records, the parent viewport, retained topology, and publication counters
/// are borrowed independently during a structural sizing attempt.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Scene: plan::Source + sizing_pass::Access + block::Access {
    type Window: Copy;
    type Snapshot;

    #[cfg_attr(verus_keep_ghost, verus_spec(root =>
        ensures document_root(self.order(), root), no_unwind
    ))]
    fn scene_root(&self) -> Self::Id;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn pending_full(&mut self) -> &mut Option<IncrementalRelayoutOutcome>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn viewport(&mut self) -> &mut Self::Window;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn viewport_changes(&mut self, window: Self::Window) -> (bool, bool);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(self, node), no_unwind
    ))]
    fn declared_size(&self, node: Self::Id, axis: Axis, kind: Kind) -> Option<Size>;

    #[cfg_attr(verus_keep_ghost, verus_spec(regions =>
        ensures regions.len() == 0, final(self).order() == old(self).order(), no_unwind
    ))]
    fn take_regions(&mut self) -> Vec<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires regions.len() == 0,
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn recycle_regions(&mut self, regions: Vec<Self::Id>);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn take_plan_spill(&mut self) -> Vec<plan::Suspended<Self::Id>>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(),
            plan::sizing_cache(final(self)) == plan::sizing_cache(old(self)), no_unwind
    ))]
    fn keep_plan_spill(&mut self, spill: Vec<plan::Suspended<Self::Id>>);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(),
            plan::sizing_cache(final(self)) == plan::sizing_cache(old(self)), no_unwind
    ))]
    fn reset_edits(&mut self, retained: plan::SubtreeCounts);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), root),
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn restore_tickets(&mut self, snapshot: &Self::Snapshot, root: Self::Id, ticket: u64) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn update_population(&mut self, totals: Totals);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn unknown_topology(&mut self) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), final(styles).len() == 0, no_unwind
    ))]
    fn reconcile(&mut self, styles: &mut Vec<Self::Id>) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn take_topology(&mut self) -> Option<Self::Snapshot>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn keep_topology(&mut self, snapshot: Self::Snapshot);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).order() == old(self).order(), no_unwind
    ))]
    fn refresh_topology(&mut self, obsolete: Option<Self::Snapshot>);
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(requires live(scene, node), no_unwind))]
fn depends_on_viewport<A: Scene + ?Sized>(scene: &A, node: A::Id, axis: Axis) -> bool {
    matches!(scene.declared_size(node, axis, Kind::Regular), Some(Size::Fill | Size::Frac(_)))
        || matches!(scene.declared_size(node, axis, Kind::Min), Some(Size::Fill | Size::Frac(_)))
        || matches!(scene.declared_size(node, axis, Kind::Max), Some(Size::Fill | Size::Frac(_)))
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires old(scene).order().ordered(), old(scene).order().closed_subtrees(), regions.len() == 0,
    ensures final(scene).order() == old(scene).order(), out.0.work@.valid(out.0.outcome),
        forall |i: int| 0 <= i < out.0.work@.chosen.len() ==> live(old(scene), #[trigger] out.0.work@.chosen[i]),
        plan::ordered_cuts(out.0.work@.chosen, old(scene).order()), out.0.work@.prepared_in(old(scene).order()),
    no_unwind
))]
fn attempt<A: Scene + ?Sized>(
    scene: &mut A, window: A::Window, regions: Vec<A::Id>, snapshot: Option<&A::Snapshot>,
) -> (StructuralResult<A::Id>, bool) {
    let root = scene.scene_root();
    let (x_changed, y_changed) = scene.viewport_changes(window);
    if x_changed && depends_on_viewport(scene, root, X) || y_changed && depends_on_viewport(scene, root, Y) {
        scene.edit(root).mark_subtree_changed();
    }
    let plan = plan::Plan { regions, retained: plan::empty_counts(), complete: true };
    let mut spill = scene.take_plan_spill();
    #[cfg(verus_keep_ghost)]
    let planning = planning_observation(scene);
    let mut plan = plan::run(scene, root, plan, &mut spill);
    #[cfg(verus_keep_ghost)]
    proof! { assert(plan::sizing_cache(scene) == planning@); }
    scene.keep_plan_spill(spill);
    let initial = Totals { nodes: plan.retained.nodes, slots: 0, blocks: plan.retained.blocks };
    if !plan.complete {
        #[cfg(verus_keep_ghost)]
        let work = {
            let log = empty_log();
            proof! { assert(ids(log@) =~= plan.regions@.take(0)); }
            region_work(false, plan.regions.as_slice(), initial, log, no_preparations(), planning)
        };
        A::Memory::clear(&mut plan.regions);
        scene.recycle_regions(plan.regions);
        return (structural_result(IncrementalRelayoutOutcome::FallbackTooMuchWork,
            #[cfg(verus_keep_ghost)] work), true);
    }
    scene.reset_edits(plan.retained);
    #[cfg(verus_keep_ghost)]
    proof! { assert(plan::sizing_cache(scene) == planning@); }
    let measured = measure_regions(scene, plan.regions.as_slice(), initial, snapshot);
    #[cfg(verus_keep_ghost)]
    let work = region_work(true, plan.regions.as_slice(), initial, measured.log, measured.prepared, planning);
    let outcome = if let Some(totals) = measured.totals {
        scene.update_population(totals);
        IncrementalRelayoutOutcome::Success { computed: totals.slots }
    } else {
        IncrementalRelayoutOutcome::FallbackFlow
    };
    A::Memory::clear(&mut plan.regions);
    scene.recycle_regions(plan.regions);
    (structural_result(outcome, #[cfg(verus_keep_ghost)] work), measured.tickets)
}

/// Reconcile retained topology and measure the selected regions before any
/// placement. A rejected attempt leaves publication to the full solver.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires old(scene).order().ordered(), old(scene).order().closed_subtrees(),
    ensures final(scene).order() == old(scene).order(), out.work@.valid(out.outcome),
        forall |i: int| 0 <= i < out.work@.chosen.len() ==> live(old(scene), #[trigger] out.work@.chosen[i]),
        plan::ordered_cuts(out.work@.chosen, old(scene).order()), out.work@.prepared_in(old(scene).order()),
    no_unwind
))]
pub(crate) fn relayout<A: Scene + ?Sized>(scene: &mut A, window: A::Window) -> StructuralResult<A::Id> {
    let mut regions = scene.take_regions();
    if scene.unknown_topology() && scene.reconcile(&mut regions) {
        if let Some(snapshot) = scene.take_topology() {
            let (outcome, tickets) = attempt(scene, window, regions, Some(&snapshot));
            if tickets || !matches!(outcome.outcome, IncrementalRelayoutOutcome::Success { .. }) {
                scene.keep_topology(snapshot);
            } else {
                scene.refresh_topology(Some(snapshot));
            }
            return outcome;
        }
    }
    let (outcome, _) = attempt(scene, window, regions, None);
    if matches!(outcome.outcome, IncrementalRelayoutOutcome::Success { .. }) {
        scene.refresh_topology(None);
    }
    outcome
}

/// A registered size edit retains live dirty marks. A viewport-only replay
/// instead starts with an empty pending-full field.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub(crate) enum RootReplay {
    RegisteredEdits,
    IntakeBudget,
    Viewport,
}

impl RootReplay {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.fallback(), no_unwind))]
    pub(crate) fn fallback(self) -> IncrementalRelayoutOutcome {
        match self {
            Self::IntakeBudget => IncrementalRelayoutOutcome::FallbackTooMuchWork,
            Self::RegisteredEdits | Self::Viewport => IncrementalRelayoutOutcome::FallbackFlow,
        }
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns root_replay(pending, registered, resized, has_flow, stable_tree), no_unwind))]
pub(crate) fn root_replay(
    pending: Option<IncrementalRelayoutOutcome>, registered: bool, resized: bool, has_flow: bool, stable_tree: bool,
) -> Option<RootReplay> {
    if stable_tree {
        match pending {
            Some(IncrementalRelayoutOutcome::FallbackFlow) if registered && has_flow => Some(RootReplay::RegisteredEdits),
            Some(IncrementalRelayoutOutcome::FallbackTooMuchWork) if registered => Some(RootReplay::IntakeBudget),
            None if resized && has_flow => Some(RootReplay::Viewport),
            _ => None,
        }
    } else {
        None
    }
}

/// Leave every unrelated full-solve reason in place, including explicit invalidation.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(taken =>
    ensures taken == request_matches(*old(pending), replay),
        *final(pending) == if taken { None } else { *old(pending) },
    no_unwind
))]
fn take_replay_request(pending: &mut Option<IncrementalRelayoutOutcome>, replay: RootReplay) -> bool {
    let ready = match replay {
        RootReplay::RegisteredEdits => matches!(*pending, Some(IncrementalRelayoutOutcome::FallbackFlow)),
        RootReplay::IntakeBudget => matches!(*pending, Some(IncrementalRelayoutOutcome::FallbackTooMuchWork)),
        RootReplay::Viewport => return pending.is_none(),
    };
    if ready { *pending = None; }
    ready
}

/// Replay sizing from the document root after a viewport or registered sizing
/// edit. New viewport words are installed before any retained leaf is read.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires old(scene).order().ordered(), old(scene).order().closed_subtrees(),
    ensures final(scene).order() == old(scene).order(),
        out.work@.valid(replay, out.outcome), document_root(old(scene).order(), out.work@.root),
        out.work@.prepared_in(old(scene).order()),
    no_unwind
))]
pub(crate) fn replay_root<A: Scene + ?Sized>(
    scene: &mut A, window: A::Window, replay: RootReplay,
) -> RootResult<A::Id> {
    let root = scene.scene_root();
    if scene.params(root).disabled {
        return root_result(replay.fallback(),
            #[cfg(verus_keep_ghost)] root_work(root, false, None, observe_request(&None), None, None, no_root_preparation()));
    }
    if let Some(_parent) = plan::Source::parent_id(scene, root) {
        return root_result(replay.fallback(),
            #[cfg(verus_keep_ghost)] root_work(root, true, Some(_parent), observe_request(&None), None, None, no_root_preparation()));
    }
    let pending = scene.pending_full();
    #[cfg(verus_keep_ghost)]
    let before = observe_request(pending);
    if !take_replay_request(pending, replay) {
        return root_result(replay.fallback(),
            #[cfg(verus_keep_ghost)] root_work(root, true, None, before, None, None, no_root_preparation()));
    }
    #[cfg(verus_keep_ghost)]
    proof! { document_root_closes_region(scene.order(), root); }
    *scene.viewport() = window;
    let ticket = scene.record(root).topology_index();
    let snapshot = scene.take_topology();
    if snapshot.is_none() {
        let window = *scene.sizing_window();
        match block::replay(scene, root, window) {
            block::Attempt::Measured(computed) => {
                scene.reset_edits(plan::empty_counts());
                scene.note_flow(true);
                return root_result(IncrementalRelayoutOutcome::Success { computed },
                    #[cfg(verus_keep_ghost)] root_work(root, true, None, before, Some(Ok(computed)), None, no_root_preparation()));
            }
            block::Attempt::Rejected => return root_result(replay.fallback(),
                #[cfg(verus_keep_ghost)] root_work(root, true, None, before, Some(Err(())), None, no_root_preparation())),
            block::Attempt::Unsupported => {}
        }
    }
    scene.reset_edits(plan::empty_counts());
    let Some(measured) = sizing_pass::measure_region::<_, A::Memory, true>(scene, root) else {
        #[cfg(verus_keep_ghost)]
        proof! { assert(false); }
        if let Some(snapshot) = snapshot { scene.keep_topology(snapshot); }
        return root_result(replay.fallback(),
            #[cfg(verus_keep_ghost)] root_work(root, true, None, before, None, None, no_root_preparation()));
    };
    let sizing_pass::RegionMeasure { nodes, slots, blocks, .. } = measured;
    if let Some(snapshot) = snapshot {
        if scene.restore_tickets(&snapshot, root, ticket) {
            scene.keep_topology(snapshot);
        } else {
            scene.refresh_topology(Some(snapshot));
        }
    }
    let totals = Totals { nodes, slots, blocks };
    scene.update_population(totals);
    root_result(IncrementalRelayoutOutcome::Success { computed: slots },
        #[cfg(verus_keep_ghost)] root_work(root, true, None, before, None, Some(totals), root_preparation(measured.prepared)))
}
