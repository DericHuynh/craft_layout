//! Full and regional sizing passes over a prepared tree.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, ChildrenLayout, Size, X, Xy, Y};
use crate::prepare_frame::FrameFloat;
use crate::node_flags::NodeFlags;
use crate::prepare_nodes::{self, StartActions};
#[cfg(not(verus_keep_ghost))]
use crate::solve::sizing_fill;
#[cfg(verus_keep_ghost)]
use crate::sizing_fill;
use crate::vec_memory::VecMemory;
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules;
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::margin_storage;
#[cfg(not(verus_keep_ghost))]
use crate::tree_walk::{self as walk, AncestorLinks, LinkModel};
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel as cycle_rules;
#[cfg(verus_keep_ghost)]
use crate::tree_walk::{self, kernel::{self as walk, AncestorLinks, LinkModel}};
use cycle_rules::{Kind, SOLVED};
#[cfg(not(verus_keep_ghost))]
#[path = "root_requests.rs"]
mod root_requests;
#[cfg(not(verus_keep_ghost))]
use root_requests::visit_sizing_roots;
#[cfg(verus_keep_ghost)]
use crate::production_schedule::kernel::visit_sizing_roots;
#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
use crate::{IncrementalRelayoutOutcome, StructuralChange, region_policy, solve::grid_state};
#[cfg(verus_keep_ghost)]
use crate::{grid::frame::state as grid_state, publication::IncrementalRelayoutOutcome,
    margin_storage::kernel as margin_storage, structural_plan::policy as region_policy, structural::kernel::StructuralChange};
#[cfg(verus_keep_ghost)]
use crate::prepare_nodes::live;
#[cfg(verus_keep_ghost)]
use crate::prepare_nodes::RecordModel;
#[cfg(verus_keep_ghost)]
use crate::declarations::LayoutParams;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {
use crate::prepare_frame::Order;

pub(crate) open spec fn inside<I>(order: Order<I>, root: I, node: I) -> bool {
    order.inside(root, node)
}

pub(crate) open spec fn remaining<I>(order: Order<I>, root: I, next: Option<I>) -> int {
    match next {
        Some(node) => (order.interval)(root).1 - (order.interval)(node).0,
        None => 0,
    }
}

pub(crate) type RootCall<I> = (I, Axis, Kind);

pub(crate) enum FinalRoute<I> {
    Request,
    Prepared,
    Wrapped(sizing_fill::WrappedFill<I>),
}

impl<I> FinalRoute<I> {
    pub(crate) open spec fn valid(self, flags: NodeFlags, axis: Axis) -> bool {
        (self is Prepared) == (sizing_fill::phase(flags, axis, Kind::Final) == SOLVED)
    }

    pub(crate) open spec fn valid_wrapped<F: FrameFloat>(self, axis: Axis) -> bool {
        match self {
            Self::Wrapped(work) => work.valid::<F>(axis),
            _ => true,
        }
    }
}

pub(crate) struct RootVisit<I> {
    pub node: I,
    pub before: NodeFlags,
    pub horizontal_final: FinalRoute<I>,
    pub vertical_final: FinalRoute<I>,
    pub block_flow: bool,
    pub wrap_share: Option<Axis>,
}

impl<I> RootVisit<I> {
    pub(crate) open spec fn calls(self) -> Seq<RootCall<I>> {
        (if self.horizontal_final is Request { seq![(self.node, X, Kind::Final)] } else { Seq::empty() })
        + (if self.vertical_final is Request { seq![(self.node, Y, Kind::Final)] } else { Seq::empty() })
        + (if self.block_flow { seq![(self.node, Y, Kind::Flow)] } else { Seq::empty() })
        + (if let Some(axis) = self.wrap_share { seq![(self.node, axis, Kind::EvenShare)] } else { Seq::empty() })
    }

    pub(crate) open spec fn valid(self) -> bool {
        self.horizontal_final.valid(self.before, X) && self.vertical_final.valid(self.before, Y)
    }

    pub(crate) open spec fn valid_wrapped<F: FrameFloat>(self) -> bool {
        self.horizontal_final.valid_wrapped::<F>(X) && self.vertical_final.valid_wrapped::<F>(Y)
    }
}

pub(crate) closed spec fn wrapped_visits_are_valid<F: FrameFloat, I>(visits: Seq<RootVisit<I>>) -> bool {
    forall |i: int| 0 <= i < visits.len() ==> (#[trigger] visits[i]).valid_wrapped::<F>()
}

pub(crate) proof fn wrap_receipt_at<F: FrameFloat, I>(visits: Seq<RootVisit<I>>, at: int)
    requires wrapped_visits_are_valid::<F, I>(visits), 0 <= at < visits.len(),
    ensures visits[at].valid_wrapped::<F>(),
{ reveal(wrapped_visits_are_valid); }

proof fn empty_wrap_receipts<F: FrameFloat, I>()
    ensures wrapped_visits_are_valid::<F, I>(Seq::empty()),
{ reveal(wrapped_visits_are_valid); }

proof fn append_wrap_receipt<F: FrameFloat, I>(visits: Seq<RootVisit<I>>, visit: RootVisit<I>)
    requires wrapped_visits_are_valid::<F, I>(visits), visit.valid_wrapped::<F>(),
    ensures wrapped_visits_are_valid::<F, I>(visits.push(visit)),
{
    reveal(wrapped_visits_are_valid);
    let receipts = visits.push(visit);
    assert forall |i: int| 0 <= i < receipts.len() implies (#[trigger] receipts[i]).valid_wrapped::<F>() by {
        if i == visits.len() {
            assert(receipts[i] == visit);
        } else {
            assert(receipts[i] == visits[i]);
        }
    };
}

pub(crate) open spec fn visit_calls<I>(visits: Seq<RootVisit<I>>) -> Seq<RootCall<I>>
    decreases visits.len(),
{
    if visits.len() == 0 { Seq::empty() } else {
        visit_calls(visits.drop_last()) + visits.last().calls()
    }
}

pub(crate) open spec fn ordered_visits<I>(order: Order<I>, root: I, visits: Seq<RootVisit<I>>) -> bool {
    &&& forall |i: int| 0 <= i < visits.len() ==> inside(order, root, (#[trigger] visits[i]).node) && visits[i].valid()
    &&& forall |i: int, j: int| 0 <= i < j < visits.len()
        ==> (order.interval)((#[trigger] visits[i]).node).0 < (order.interval)((#[trigger] visits[j]).node).0
}

pub(crate) enum FullMeasurement<I> {
    Prepared(I),
    Viewport { root: I, params: LayoutParams, record: crate::node_data::NodeLayoutData },
    Walk { root: I, before: Seq<RootCall<I>>, visits: Seq<RootVisit<I>>, after: Seq<RootCall<I>> },
}

impl<I> FullMeasurement<I> {
    pub(crate) open spec fn valid(self, order: Order<I>, window: Xy<f32>) -> bool {
        match self {
            Self::Prepared(root) => (order.live)(root),
            Self::Viewport { root, params, record } => (order.live)(root) && (order.parent)(root).is_none()
                && unbounded_viewport_fill(params) && seeded_viewport(record, window),
            Self::Walk { root, before, visits, after } => (order.live)(root)
                && ordered_visits(order, root, visits)
                && after == before + visit_calls(visits),
        }
    }

    pub(crate) open spec fn valid_wrapped<F: FrameFloat>(self) -> bool {
        match self {
            Self::Walk { visits, .. } => wrapped_visits_are_valid::<F, I>(visits),
            _ => true,
        }
    }
}

fn before_walk<T: RecordModel + ?Sized>(tree: &T) -> (calls: Ghost<Seq<RootCall<T::Id>>>)
    ensures calls@ == tree.root_calls(), no_unwind
{
    Ghost(tree.root_calls())
}

fn prepared_evidence<I>(root: I) -> (evidence: Ghost<FullMeasurement<I>>)
    ensures evidence@ == FullMeasurement::Prepared(root), no_unwind
{
    Ghost(FullMeasurement::Prepared(root))
}

fn viewport_evidence<T: RecordModel + ?Sized>(tree: &T, root: T::Id)
    -> (evidence: Ghost<FullMeasurement<T::Id>>)
    ensures evidence@ == (FullMeasurement::Viewport {
        root, params: tree.layout_params(root), record: tree.layout_record(root),
    }), no_unwind
{
    Ghost(FullMeasurement::Viewport { root, params: tree.layout_params(root), record: tree.layout_record(root) })
}

fn walk_evidence<T: RecordModel + ?Sized>(
    tree: &T, root: T::Id, before: Ghost<Seq<RootCall<T::Id>>>, walk: &SizingWalk<T::Id>,
) -> (evidence: Ghost<FullMeasurement<T::Id>>)
    ensures evidence@ == (FullMeasurement::Walk {
        root, before: before@, visits: walk.visits@, after: tree.root_calls(),
    }),
    no_unwind
{
    Ghost(FullMeasurement::Walk { root, before: before@, visits: walk.visits@, after: tree.root_calls() })
}

pub(crate) open spec fn unbounded_viewport_fill(params: LayoutParams) -> bool {
    &&& !params.disabled
    &&& matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
    &&& matches!(params.size, Xy { x: Size::Fill, y: Size::Fill })
    &&& params.min_size.x.is_none() && params.min_size.y.is_none()
    &&& params.max_size.x.is_none() && params.max_size.y.is_none()
}

pub(crate) open spec fn seeded_viewport(record: crate::node_data::NodeLayoutData, window: Xy<f32>) -> bool {
    let rx = cycle_rules::slot_index(X.index(), Kind::Regular) as int;
    let ry = cycle_rules::slot_index(Y.index(), Kind::Regular) as int;
    let fx = cycle_rules::slot_index(X.index(), Kind::Final) as int;
    let fy = cycle_rules::slot_index(Y.index(), Kind::Final) as int;
    &&& record.values@[rx] == window.x && record.values@[fx] == window.x
    &&& record.values@[ry] == window.y && record.values@[fy] == window.y
    &&& record.levels@[rx] == 0 && record.levels@[ry] == 0
    &&& record.levels@[fx] == 1 && record.levels@[fy] == 1
    &&& !record.flags.is_block_item()
    &&& record.flags.0 & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT == 0
    &&& cycle_rules::read_state(record.flags.0, rx as u32) == SOLVED
    &&& cycle_rules::read_state(record.flags.0, ry as u32) == SOLVED
    &&& cycle_rules::read_state(record.flags.0, fx as u32) == SOLVED
    &&& cycle_rules::read_state(record.flags.0, fy as u32) == SOLVED
}

fn no_visits<I>() -> (visits: Ghost<Seq<RootVisit<I>>>)
    ensures visits@ == Seq::<RootVisit<I>>::empty(), no_unwind
{
    Ghost(Seq::empty())
}

fn record_visits_at_node<I>(node: I, flags: NodeFlags, x: Ghost<FinalRoute<I>>, y: Ghost<FinalRoute<I>>, flow: bool, share: Option<Axis>)
    -> (visit: Ghost<RootVisit<I>>)
    ensures visit@ == (RootVisit {
        node, before: flags, horizontal_final: x@, vertical_final: y@, block_flow: flow, wrap_share: share,
    }),
    no_unwind
{
    Ghost(RootVisit {
        node, before: flags, horizontal_final: x@, vertical_final: y@, block_flow: flow, wrap_share: share,
    })
}

fn record_visit<I>(prior: Ghost<Seq<RootVisit<I>>>, visit: Ghost<RootVisit<I>>) -> (visits: Ghost<Seq<RootVisit<I>>>)
    ensures visits@ == prior@.push(visit@), no_unwind
{
    Ghost(prior@.push(visit@))
}

proof fn append_ordered_visit<I>(order: Order<I>, root: I, prior: Seq<RootVisit<I>>, visit: RootVisit<I>)
    requires ordered_visits(order, root, prior), inside(order, root, visit.node), visit.valid(),
        forall |i: int| 0 <= i < prior.len() ==>
            (order.interval)((#[trigger] prior[i]).node).0 < (order.interval)(visit.node).0,
    ensures ordered_visits(order, root, prior.push(visit)),
        visit_calls(prior.push(visit)) == visit_calls(prior) + visit.calls(),
{
    let extended = prior.push(visit);
    assert(extended.drop_last() =~= prior);
    assert forall |i: int| 0 <= i < extended.len() implies inside(order, root, (#[trigger] extended[i]).node)
        && extended[i].valid() by {
        if i < prior.len() { assert(extended[i] == prior[i]); }
        else { assert(extended[i] == visit); }
    }
    assert forall |i: int, j: int| 0 <= i < j < extended.len() implies
        (order.interval)((#[trigger] extended[i]).node).0 < (order.interval)((#[trigger] extended[j]).node).0 by {
        if j < prior.len() { assert(extended[i] == prior[i] && extended[j] == prior[j]); }
        else { assert(extended[i] == prior[i] && extended[j] == visit); }
    }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct SizingWalk<I> {
    #[cfg(verus_keep_ghost)]
    pub(crate) visits: Ghost<Seq<RootVisit<I>>>,
    #[cfg(not(verus_keep_ghost))]
    id: core::marker::PhantomData<I>,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct FullSizing<I> {
    #[cfg(verus_keep_ghost)]
    pub(crate) evidence: Ghost<FullMeasurement<I>>,
    #[cfg(not(verus_keep_ghost))]
    id: core::marker::PhantomData<I>,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(work =>
    ensures work.evidence == evidence, no_unwind
))]
fn full_sizing<I>(#[cfg(verus_keep_ghost)] evidence: Ghost<FullMeasurement<I>>) -> FullSizing<I> {
    FullSizing {
        #[cfg(verus_keep_ghost)]
        evidence,
        #[cfg(not(verus_keep_ghost))]
        id: core::marker::PhantomData,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: StartActions {
    type Margin: Copy;

    #[cfg_attr(verus_keep_ghost, verus_spec(root => ensures live(self, root), no_unwind))]
    fn root_id(&self) -> Self::Id;

    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).order() == old(self).order(), no_unwind))]
    fn sizing_window(&mut self) -> &mut Xy<f32>;

    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).order() == old(self).order(), no_unwind))]
    fn margins(&mut self) -> &mut Vec<Self::Margin>;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).order() == old(self).order(), no_unwind))]
    fn margin_scratch(&mut self) -> &mut Vec<Self::Margin>;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).order() == old(self).order(), no_unwind))]
    fn sizing_flags(&mut self) -> (&mut bool, &mut bool, &mut Option<IncrementalRelayoutOutcome>);

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(ensures final(self).order() == old(self).order(), no_unwind))]
    fn prepared_nodes(&mut self) -> &mut u32;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node),
        ensures final(self).order() == old(self).order(),
            final(self).root_calls() == old(self).root_calls().push((node, axis, kind)),
        no_unwind
    ))]
    fn slot(&mut self, node: Self::Id, axis: Axis, kind: Kind);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires live(old(self), node),
        ensures final(self).order() == old(self).order(), final(self).root_calls() == old(self).root_calls(),
        no_unwind
    ))]
    fn fill_children(&mut self, node: Self::Id) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(parent =>
        requires live(self, node),
        ensures parent == (self.order().parent)(node), parent.is_some() ==> live(self, parent.unwrap()),
        no_unwind
    ))]
    fn parent_id(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(same => ensures same == (left == right), no_unwind))]
    fn same_id(&self, left: Self::Id, right: Self::Id) -> bool;

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out <= 32, no_unwind))]
    fn ones(word: u32) -> u32;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct Links<'a, T: Access + ?Sized>(&'a T);

#[cfg(not(verus_keep_ghost))]
impl<T: Access + ?Sized> LinkModel for Links<'_, T> { type Id = T::Id; }

#[cfg(verus_keep_ghost)]
verus! {
impl<T: Access + ?Sized> LinkModel for Links<'_, T> {
    type Id = T::Id;
    closed spec fn live(&self, node: Self::Id) -> bool { live(self.0, node) }
    closed spec fn sibling(&self, node: Self::Id) -> Option<Self::Id> { (self.0.order().sibling)(node) }
    closed spec fn parent(&self, node: Self::Id) -> Option<Self::Id> { (self.0.order().parent)(node) }
}

proof fn after_path<T: Access + ?Sized>(links: &Links<T>, root: T::Id, chain: Seq<(T::Id, Option<T::Id>)>, i: int)
    requires
        links.0.order().ordered(), links.0.order().closed_subtrees(), live(links.0, root),
        tree_walk::ancestor_links(links, root, chain), 0 <= i < chain.len(),
        forall |j: int| 0 <= j < chain.len() ==> inside(links.0.order(), root, (#[trigger] chain[j]).0),
        forall |j: int| 0 <= j && j + 1 < chain.len() ==> links.parent((#[trigger] chain[j]).0) == Some(chain[j + 1].0),
    ensures match tree_walk::after(chain, i) {
        Some(next) => inside(links.0.order(), root, next)
            && (links.0.order().interval)(chain[i].0).1 <= (links.0.order().interval)(next).0,
        None => true,
    },
    decreases chain.len() - i,
{
    if i + 1 < chain.len() {
        let order = links.0.order();
        let here = chain[i].0;
        assert(here != root);
        order.node_facts(here);
        assert(inside(order, root, here));
        let parent = chain[i + 1].0;
        assert((order.parent)(here) == Some(parent));
        if let Some(next) = chain[i].1 {
            assert((order.sibling)(here) == Some(next));
        } else {
            assert(order.child(parent, here));
            after_path(links, root, chain, i + 1);
        }
    }
}

fn sibling_path<T: Access + ?Sized>(links: &Links<T>, root: T::Id, node: T::Id) -> (path: Ghost<Seq<(T::Id, Option<T::Id>)>>)
    requires
        live(links.0, root), inside(links.0.order(), root, node),
        links.0.order().ordered(), links.0.order().closed_subtrees(),
    ensures path@.len() > 0, path@[0].0 == node, tree_walk::ancestor_links(links, root, path@),
        match tree_walk::after(path@, 0) {
            Some(next) => inside(links.0.order(), root, next)
                && (links.0.order().interval)(node).1 <= (links.0.order().interval)(next).0,
            None => true,
        },
    no_unwind
{
    proof! {
        let order = links.0.order();
        let scope = |other: T::Id| inside(order, root, other);
        assert forall |other: T::Id| #[trigger] scope(other) implies {
            &&& links.live(other)
            &&& other != root ==> match links.parent(other) {
                Some(parent) => scope(parent) && (order.depth)(parent) < (order.depth)(other),
                None => false,
            }
        } by {
            if other != root {
                order.node_facts(other);
                assert(order.inside(root, other));
                let parent = links.parent(other).unwrap();
                assert(order.child(parent, other));
            }
        }
        tree_walk::build_ancestor_path(links, root, node, scope, order.depth, (order.depth)(node));
        after_path(links, root, tree_walk::ancestor_path(links, root, node, (order.depth)(node)), 0);
    }
    Ghost(tree_walk::ancestor_path(links, root, node, (links.0.order().depth)(node)))
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<T: Access + ?Sized> AncestorLinks for Links<'_, T> {
    #[inline(always)]
    fn following(&self, node: Self::Id) -> Option<Self::Id> {
        self.0.sibling(node)
    }

    #[inline(always)]
    fn enclosing(&self, node: Self::Id) -> Option<Self::Id> {
        self.0.parent_id(node)
    }

    #[inline(always)]
    fn same(&self, node: Self::Id, root: Self::Id) -> bool { self.0.same_id(node, root) }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(next =>
    requires live(tree, root), inside(tree.order(), root, node), tree.order().ordered(), tree.order().closed_subtrees(),
    ensures next.is_some() ==> inside(tree.order(), root, next.unwrap()),
        remaining(tree.order(), root, next) < remaining(tree.order(), root, Some(node)),
    no_unwind
))]
fn following_in_subtree<T: Access + ?Sized>(tree: &T, root: T::Id, node: T::Id, descend: bool) -> Option<T::Id> {
    let child = if descend { tree.first(node) } else { None };
    let links = Links(tree);
    #[cfg(verus_keep_ghost)]
    let path = sibling_path(&links, root, node);
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(node); }
    walk::next(&links, root, node, child, #[cfg(verus_keep_ghost)] path)
}

/// A simple wrapping parent has no in-flow child reading its line share or
/// cross metric. Its remaining sizing dependencies keep the same ranks when
/// the line boundaries move.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires live(tree, wrap), tree.order().ordered(), tree.order().closed_subtrees(),
    no_unwind
))]
fn independent_wrap_items<T: Access + ?Sized>(tree: &T, wrap: T::Id) -> bool {
    let mut child = tree.first(wrap);
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(wrap); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant child.is_some() ==> inside(tree.order(), wrap, child.unwrap()),
          live(tree, wrap), tree.order().ordered(), tree.order().closed_subtrees(),
        decreases remaining(tree.order(), wrap, child),
    ))]
    while let Some(node) = child {
        let p = tree.params(node);
        if !p.disabled && !p.free_placement
            && (p.size.x.is_flex() || p.size.y.is_flex()
                || matches!(p.min_size.x, Some(Size::Fill | Size::Frac(_)))
                || matches!(p.min_size.y, Some(Size::Fill | Size::Frac(_)))
                || matches!(p.max_size.x, Some(Size::Fill | Size::Frac(_)))
                || matches!(p.max_size.y, Some(Size::Fill | Size::Frac(_))))
        {
            return false;
        }
        child = following_in_subtree(tree, wrap, node, false);
    }
    true
}

/// Inspect only live, enabled branches. The result can be retained until a
/// registered change alters the declaration forms or child membership.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires tree.order().ordered(), tree.order().closed_subtrees(),
    no_unwind
))]
pub(crate) fn numeric_wrap_shape<T: Access + ?Sized>(tree: &T) -> bool {
    let root = tree.root_id();
    let mut next = Some(root);
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(root); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant next.is_some() ==> inside(tree.order(), root, next.unwrap()),
            live(tree, root), tree.order().ordered(), tree.order().closed_subtrees(),
        decreases remaining(tree.order(), root, next),
    ))]
    while let Some(node) = next {
        let params = tree.params(node);
        let enabled = !params.disabled;
        if enabled {
            match params.children_layout {
                ChildrenLayout::Block | ChildrenLayout::Grid { .. } => return false,
                ChildrenLayout::Wrap { .. } if !independent_wrap_items(tree, node) => return false,
                _ => {}
            }
        }
        next = following_in_subtree(tree, root, node, enabled);
    }
    true
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct ResetWrap<I> {
    #[cfg(verus_keep_ghost)]
    pub(crate) children: Ghost<Seq<I>>,
    #[cfg(verus_keep_ghost)]
    pub(crate) reset: Ghost<Set<I>>,
    #[cfg(not(verus_keep_ghost))]
    marker: core::marker::PhantomData<I>,
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) open spec fn cleared_wrap(record: crate::node_data::NodeLayoutData) -> crate::node_data::NodeLayoutData {
    crate::node_data::NodeLayoutData {
        flags: NodeFlags(record.flags.0 & !NodeFlags::WRAP_LINE_START),
        parent_flow: [0u32, 0u32],
        ..record
    }
}

/// The complete immediate-child chain when next is None.
pub(crate) open spec fn child_prefix<I>(order: Order<I>, parent: I, done: Seq<I>, next: Option<I>) -> bool {
    &&& (order.first)(parent) == if done.len() == 0 { next } else { Some(done.first()) }
    &&& forall |i: int| 0 <= i < done.len() ==> {
        let child = #[trigger] done[i];
        &&& order.child(parent, child)
        &&& (order.sibling)(child) == if i + 1 == done.len() { next } else { Some(done[i+1]) }
    }
}

type RecordWords<I> = spec_fn(I) -> crate::node_data::NodeLayoutData;

#[verifier::opaque]
pub(crate) open spec fn reset_records<I>(before: RecordWords<I>, after: RecordWords<I>, seen: Set<I>) -> bool {
    forall |node: I| #[trigger] after(node) ==
        if seen.contains(node) { cleared_wrap(before(node)) } else { before(node) }
}

pub(crate) open spec fn record_book<T: RecordModel + ?Sized>(tree: &T) -> RecordWords<T::Id> {
    |node: T::Id| tree.layout_record(node)
}

fn reset_snapshot<T: RecordModel + ?Sized>(tree: &T) -> (saved: Ghost<RecordWords<T::Id>>)
    ensures saved@ == record_book(tree),
    no_unwind
{ Ghost(record_book(tree)) }

proof fn initialize_resets<I>(before: RecordWords<I>)
    ensures reset_records(before, before, Set::empty()),
{
    reveal(reset_records);
}

proof fn apply_wrap_reset<I>(
    before: RecordWords<I>, previous: RecordWords<I>, after: RecordWords<I>, seen: Set<I>, node: I,
)
    requires reset_records(before, previous, seen), !seen.contains(node), after(node) == cleared_wrap(previous(node)),
        forall |row: I| row != node ==> #[trigger] after(row) == previous(row),
    ensures reset_records(before, after, seen.insert(node)),
{
    reveal(reset_records);
    let next = seen.insert(node);
    assert forall |row: I| #[trigger] after(row) ==
        (if next.contains(row) { cleared_wrap(before(row)) } else { before(row) }) by {
        if row == node { assert(next.contains(row)); }
        else { assert(next.contains(row) == seen.contains(row)); }
    }
}

fn reset_set<I>(seen: Ghost<Seq<I>>) -> (nodes: Ghost<Set<I>>)
    ensures nodes@ == seen@.to_set(),
    no_unwind
{ Ghost(seen@.to_set()) }

fn no_resets<I>() -> (seen: Ghost<Seq<I>>)
    ensures seen@ == Seq::<I>::empty(),
    no_unwind
{ Ghost(Seq::empty()) }

fn reset_one<I>(seen: Ghost<Seq<I>>, child: I) -> (next: Ghost<Seq<I>>)
    ensures next@ == seen@.push(child),
    no_unwind
{ Ghost(seen@.push(child)) }

proof fn extend_child_prefix<I>(order: Order<I>, parent: I, old: Seq<I>, child: I)
    requires child_prefix(order, parent, old, Some(child)), order.child(parent, child),
    ensures child_prefix(order, parent, old.push(child), (order.sibling)(child)),
{
    let next = old.push(child);
    if old.len() == 0 { assert(next.first() == child); }
    else { assert(next.first() == old.first()); }
    assert forall |i: int| 0 <= i < next.len() implies {
        let row = #[trigger] next[i];
        &&& order.child(parent, row)
        &&& (order.sibling)(row)
            == if i + 1 == next.len() { (order.sibling)(child) } else { Some(next[i+1]) }
    } by {
        if i == old.len() { assert(next[i] == child); }
        else if i + 1 == old.len() { assert(next[i + 1] == child); }
        else { assert(next[i] == old[i] && next[i + 1] == old[i + 1]); }
    }
}
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(reset =>
    requires live(old(tree), wrap), old(tree).order().ordered(),
    ensures final(tree).order() == old(tree).order(),
        child_prefix(old(tree).order(), wrap, reset.children@, None),
        reset.reset@ == reset.children@.to_set(),
        reset_records(record_book(old(tree)), record_book(final(tree)), reset.reset@),
    no_unwind
))]
pub(crate) fn reset_wrap_items<T: prepare_nodes::Records + ?Sized>(tree: &mut T, wrap: T::Id) -> ResetWrap<T::Id> {
    let mut child = tree.first(wrap);
    #[cfg(verus_keep_ghost)]
    let mut children = no_resets::<T::Id>();
    #[cfg(verus_keep_ghost)]
    let mut reset = reset_set(children);
    #[cfg(verus_keep_ghost)]
    let initial = reset_snapshot(tree);
    #[cfg(verus_keep_ghost)]
    let mut current = initial;
    #[cfg(verus_keep_ghost)]
    proof! {
        tree.order().node_facts(wrap);
        children@.to_set_ensures();
        assert(reset@ =~= Set::<T::Id>::empty());
        initialize_resets(initial@);
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant child.is_some() ==> tree.order().child(wrap, child.unwrap()),
            tree.order() == old(tree).order(), live(tree, wrap), tree.order().ordered(),
            child_prefix(tree.order(), wrap, children@, child),
            initial@ == record_book(old(tree)), current@ == record_book(tree),
            reset@ == children@.to_set(), reset_records(initial@, current@, reset@),
            child.is_some() ==> forall |i: int| 0 <= i < children@.len()
                ==> (tree.order().interval)(#[trigger] children@[i]).0
                    < (tree.order().interval)(child.unwrap()).0,
        decreases remaining(tree.order(), wrap, child),
    ))]
    loop {
        let Some(node) = child else {
            return ResetWrap {
                #[cfg(verus_keep_ghost)]
                children,
                #[cfg(verus_keep_ghost)]
                reset,
                #[cfg(not(verus_keep_ghost))]
                marker: core::marker::PhantomData,
            };
        };
        #[cfg(verus_keep_ghost)]
        let prior = children;
        #[cfg(verus_keep_ghost)]
        let previous = current;
        #[cfg(verus_keep_ghost)]
        let before_reset = reset;
        #[cfg(verus_keep_ghost)]
        proof! {
            tree.order().node_facts(node);
            prior@.to_set_ensures();
            assert(!prior@.contains(node)) by {
                if prior@.contains(node) {
                    let i = choose |i: int| 0 <= i < prior@.len() && #[trigger] prior@[i] == node;
                    assert((tree.order().interval)(prior@[i]).0 < (tree.order().interval)(node).0);
                }
            }
        }
        child = tree.sibling(node);
        let data = tree.edit(node);
        clear_line(data);
        #[cfg(verus_keep_ghost)]
        {
            children = reset_one(prior, node);
            reset = reset_set(children);
            current = reset_snapshot(tree);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            extend_child_prefix(tree.order(), wrap, prior@, node);
            prior@.lemma_push_to_set_commute(node);
            assert(reset@ =~= before_reset@.insert(node));
            apply_wrap_reset(initial@, previous@, current@, before_reset@, node);
            if let Some(next) = child {
                assert forall |i: int| 0 <= i < children@.len()
                    implies (tree.order().interval)(#[trigger] children@[i]).0
                        < (tree.order().interval)(next).0 by {
                    if i == prior@.len() { assert(children@[i] == node); }
                    else { assert(children@[i] == prior@[i]); }
                }
            }
        }
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(ensures *final(data) == cleared_wrap(*old(data)), no_unwind))]
fn clear_line(data: &mut crate::node_data::NodeLayoutData) {
    #[cfg(not(verus_keep_ghost))]
    use crate::flow::wrap_metrics;
    #[cfg(verus_keep_ghost)]
    use crate::wrap_metrics::kernel as wrap_metrics;
    wrap_metrics::clear_parent_line(&mut data.flags.0, NodeFlags::WRAP_LINE_START, &mut data.parent_flow);
    #[cfg(verus_keep_ghost)]
    proof! { assert(data.parent_flow =~= [0u32, 0u32]); }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::reject_recursive_types(I))]
struct FinalSizing<I> {
    #[cfg(verus_keep_ghost)]
    route: Ghost<FinalRoute<I>>,
    #[cfg(not(verus_keep_ghost))]
    node: core::marker::PhantomData<I>,
}

#[cfg(verus_keep_ghost)]
verus! {
fn predict_wrap<T: Access + ?Sized>(tree: &T, node: T::Id, axis: Axis)
    -> (work: Ghost<Option<sizing_fill::WrappedFill<T::Id>>>)
    ensures work@ == sizing_fill::wrapped_fill_at(tree, node, axis), no_unwind
{
    Ghost(sizing_fill::wrapped_fill_at(tree, node, axis))
}

fn selected_wrap<I>(work: Ghost<Option<sizing_fill::WrappedFill<I>>>) -> (route: Ghost<FinalRoute<I>>)
    requires work@.is_some(),
    ensures route@ == FinalRoute::Wrapped(work@.unwrap()), no_unwind
{
    Ghost(FinalRoute::Wrapped(work@.unwrap()))
}

fn prepared_final<I>() -> (route: Ghost<FinalRoute<I>>)
    ensures route@ is Prepared, no_unwind
{
    Ghost(FinalRoute::Prepared)
}

fn requested_final<I>() -> (route: Ghost<FinalRoute<I>>)
    ensures route@ is Request, no_unwind
{
    Ghost(FinalRoute::Request)
}
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    ensures result.route@ == route@, no_unwind
))]
fn final_sizing<I>(#[cfg(verus_keep_ghost)] route: Ghost<FinalRoute<I>>) -> FinalSizing<I> {
    FinalSizing {
        #[cfg(verus_keep_ghost)]
        route,
        #[cfg(not(verus_keep_ghost))]
        node: core::marker::PhantomData,
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), node),
    ensures final(tree).order() == old(tree).order(),
        result.route@.valid(flags, axis),
        result.route@.valid_wrapped::<T::Float>(axis),
        final(tree).root_calls() == if result.route@ is Request { old(tree).root_calls().push((node, axis, Kind::Final)) }
            else { old(tree).root_calls() },
        match result.route@ {
            FinalRoute::Prepared => final(tree).layout_record(node) == old(tree).layout_record(node),
            FinalRoute::Wrapped(work) => sizing_fill::wrapped_fill_at(old(tree), node, axis) == Some(work)
                && sizing_fill::published_line_fill(final(tree).layout_record(node), axis, work),
            FinalRoute::Request => sizing_fill::wrapped_fill_at(old(tree), node, axis).is_none(),
        },
    no_unwind
))]
fn solve_final<T: Access + ?Sized>(tree: &mut T, node: T::Id, axis: Axis, flags: NodeFlags) -> FinalSizing<T::Id> {
    if flags.check_state(axis, Kind::Final) == SOLVED {
        return final_sizing(#[cfg(verus_keep_ghost)] prepared_final());
    }
    #[cfg(verus_keep_ghost)]
    let work = predict_wrap(tree, node, axis);
    if sizing_fill::wrapped(tree, node, axis) {
        return final_sizing(#[cfg(verus_keep_ghost)] selected_wrap(work));
    }
    tree.slot(node, axis, Kind::Final);
    final_sizing(#[cfg(verus_keep_ghost)] requested_final())
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct NodeSizing<I> {
    descend: bool,
    #[cfg(verus_keep_ghost)]
    visit: Ghost<RootVisit<I>>,
    #[cfg(not(verus_keep_ghost))]
    id: core::marker::PhantomData<I>,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires live(old(tree), node),
    ensures final(tree).order() == old(tree).order(), result.visit@.node == node,
        result.visit@.before == flags, result.visit@.valid(),
        result.visit@.valid_wrapped::<T::Float>(),
        final(tree).root_calls() == old(tree).root_calls() + result.visit@.calls(),
    no_unwind
))]
fn visit_sizing_slots<T: Access + ?Sized>(tree: &mut T, node: T::Id, flags: NodeFlags) -> NodeSizing<T::Id> {
    let [first, second] = cycle_rules::canonical_axes(X, Y);
    #[cfg(verus_keep_ghost)]
    let mut x_path = final_sizing::<T::Id>(requested_final());
    #[cfg(verus_keep_ghost)]
    let mut y_path = final_sizing::<T::Id>(requested_final());
    #[cfg(verus_keep_ghost)]
    let mut share = None;
    let flow = flags.0 & NodeFlags::BLOCK_CONTAINER != 0;
    visit_sizing_roots!(
        first, second;
        axis => {
            let _path = solve_final(tree, node, axis, flags);
            #[cfg(verus_keep_ghost)]
            if matches!(axis, X) { x_path = _path; } else { y_path = _path; }
        };
        flow => { tree.slot(node, Y, Kind::Flow); };
        flags.0 & NodeFlags::WRAP_CONTAINER != 0 => {
            if let ChildrenLayout::Stack { axis, .. } | ChildrenLayout::Wrap { axis, .. } = tree.params(node).children_layout {
                tree.slot(node, axis, Kind::EvenShare);
                #[cfg(verus_keep_ghost)]
                { share = Some(axis); }
            }
        }
    );
    let descend = flags.0 & NodeFlags::DESCENDANTS_NEED_SOLVE != 0 && !tree.fill_children(node);
    #[cfg(verus_keep_ghost)]
    let visit = record_visits_at_node(node, flags, x_path.route, y_path.route, flow, share);
    NodeSizing {
        descend,
        #[cfg(verus_keep_ghost)]
        visit,
        #[cfg(not(verus_keep_ghost))]
        id: core::marker::PhantomData,
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(walk =>
    requires live(old(tree), root), old(tree).order().ordered(), old(tree).order().closed_subtrees(),
    ensures final(tree).order() == old(tree).order(),
        ordered_visits(old(tree).order(), root, walk.visits@),
        wrapped_visits_are_valid::<T::Float, T::Id>(walk.visits@),
        final(tree).root_calls() == old(tree).root_calls() + visit_calls(walk.visits@),
    no_unwind
))]
pub(crate) fn solve_subtree<T: Access + ?Sized, const RETAIN: bool>(tree: &mut T, root: T::Id) -> SizingWalk<T::Id> {
    let mut next = Some(root);
    #[cfg(verus_keep_ghost)]
    let mut visits = no_visits();
    #[cfg(verus_keep_ghost)]
    proof! {
        tree.order().node_facts(root);
        empty_wrap_receipts::<T::Float, T::Id>();
    }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), live(tree, root), tree.order().ordered(), tree.order().closed_subtrees(),
            next.is_some() ==> inside(tree.order(), root, next.unwrap()),
            ordered_visits(tree.order(), root, visits@),
            wrapped_visits_are_valid::<T::Float, T::Id>(visits@),
            tree.root_calls() == old(tree).root_calls() + visit_calls(visits@),
            next.is_some() ==> forall |i: int| 0 <= i < visits@.len() ==>
                (tree.order().interval)((#[trigger] visits@[i]).node).0 < (tree.order().interval)(next.unwrap()).0,
        decreases remaining(tree.order(), root, next),
    ))]
    while let Some(node) = next {
        #[cfg(any(feature = "incremental", verus_keep_ghost))]
        if RETAIN && matches!(tree.record(node).structural_change, StructuralChange::Retained) {
            next = following_in_subtree(tree, root, node, false);
            continue;
        }
        let flags = tree.record(node).flags;
        if flags.0 == NodeFlags::EMPTY.0 && tree.params(node).disabled {
            next = following_in_subtree(tree, root, node, false);
            continue;
        }
        let work = visit_sizing_slots(tree, node, flags);
        #[cfg(verus_keep_ghost)]
        proof! {
            append_ordered_visit(tree.order(), root, visits@, work.visit@);
            append_wrap_receipt::<T::Float, T::Id>(visits@, work.visit@);
            assert(tree.root_calls() =~= old(tree).root_calls() + visit_calls(visits@.push(work.visit@)));
        }
        #[cfg(verus_keep_ghost)]
        { visits = record_visit(visits, work.visit); }
        next = following_in_subtree(tree, root, node, work.descend);
    }
    SizingWalk {
        #[cfg(verus_keep_ghost)]
        visits,
        #[cfg(not(verus_keep_ghost))]
        id: core::marker::PhantomData,
    }
}

#[inline(never)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(finished =>
    requires live(old(tree), root),
    ensures final(tree).order() == old(tree).order(),
        finished ==> seeded_viewport(final(tree).layout_record(root), window)
            && unbounded_viewport_fill(final(tree).layout_params(root)) && (final(tree).order().parent)(root).is_none(),
        !finished ==> final(tree).layout_record(root) == old(tree).layout_record(root),
    no_unwind
))]
fn finish_viewport<T: Access + ?Sized>(tree: &mut T, root: T::Id, window: Xy<f32>) -> bool {
    let flags = tree.record(root).flags.0;
    const BLOCK_FLAGS: u32 = NodeFlags::BLOCK_ITEM | NodeFlags::BLOCK_PARENT_AUTO_HEIGHT;
    const NEEDS_SIZING: u32 = NodeFlags::DESCENDANTS_NEED_SOLVE | BLOCK_FLAGS | NodeFlags::BLOCK_CONTAINER | NodeFlags::WRAP_CONTAINER;
    if flags & NEEDS_SIZING != 0 {
        return false;
    }
    let params = tree.params(root);
    if params.disabled || !matches!(params.children_layout, ChildrenLayout::Free | ChildrenLayout::Stack { .. })
        || !matches!(params.size, Xy { x: Size::Fill, y: Size::Fill })
        || params.min_size.x.is_some() || params.min_size.y.is_some()
        || params.max_size.x.is_some() || params.max_size.y.is_some()
        || !T::Float::finite(window.x) || !T::Float::finite(window.y) || tree.parent_id(root).is_some()
    {
        return false;
    }
    let data = tree.edit(root);
    data.publish_axis(X, window.x, window.x, 0);
    data.publish_axis(Y, window.y, window.y, 0);
    #[cfg(verus_keep_ghost)]
    proof! {
        let after = data.flags.0;
        assert(after & NodeFlags::BLOCK_ITEM == 0 && after & NodeFlags::BLOCK_PARENT_AUTO_HEIGHT == 0)
            by(bit_vector) requires flags & NEEDS_SIZING == 0, after & 0xfff0_0000u32 == flags & 0xfff0_0000u32;
    }
    true
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(work =>
    requires old(tree).order().ordered(), old(tree).order().closed_subtrees(),
    ensures final(tree).order() == old(tree).order(),
        work.evidence@.valid(final(tree).order(), window),
        work.evidence@.valid_wrapped::<T::Float>(),
    no_unwind
))]
pub(crate) fn measure_full<T: Access + ?Sized, M: VecMemory, const REGISTERED_PIXELS: bool>(
    tree: &mut T, window: Xy<f32>,
) -> FullSizing<T::Id> {
    *tree.sizing_window() = window;
    M::clear(tree.margins());
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    {
        let (cycle, flow, pending) = tree.sizing_flags();
        *cycle = false;
        *flow = false;
        *pending = None;
    }
    let root = tree.root_id();
    let _summary = prepare_nodes::prepare::<T, M, false, REGISTERED_PIXELS>(tree, root, None, &mut prepare_nodes::empty_retained());
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    { *tree.prepared_nodes() = _summary.0; }
    if !_summary.1 {
        return full_sizing(#[cfg(verus_keep_ghost)] prepared_evidence(root));
    }
    if finish_viewport(tree, root, window) {
        return full_sizing(#[cfg(verus_keep_ghost)] viewport_evidence(tree, root));
    }
    #[cfg(verus_keep_ghost)]
    let previous = before_walk(tree);
    let _walk = solve_subtree::<T, false>(tree, root);
    full_sizing(#[cfg(verus_keep_ghost)] walk_evidence(tree, root, previous, &_walk))
}

/// Reindex explicit margins in visible preorder after a regional solve.
#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(tree).order().ordered(), old(tree).order().closed_subtrees(),
    ensures final(tree).order() == old(tree).order(),
    no_unwind
))]
pub(crate) fn compact_margins<T: Access + ?Sized, M: VecMemory>(tree: &mut T, blocks: usize) {
    if blocks == 0 {
        M::clear(tree.margins());
        return;
    }
    if tree.margins().len() <= blocks.saturating_mul(2) { return; }
    let previous = M::take(tree.margins());
    let mut retained = M::take(tree.margin_scratch());
    let root = tree.root_id();
    let mut next = Some(root);
    #[cfg(verus_keep_ghost)]
    proof! { tree.order().node_facts(root); }
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant tree.order() == old(tree).order(), live(tree, root), tree.order().ordered(), tree.order().closed_subtrees(),
            next.is_some() ==> inside(tree.order(), root, next.unwrap()),
        decreases remaining(tree.order(), root, next),
    ))]
    while let Some(node) = next {
        let enabled = !tree.params(node).disabled;
        next = following_in_subtree(tree, root, node, enabled);
        if !enabled { continue; }
        let Some(index) = tree.record(node).block_margin_index::<T::Float>() else { continue; };
        let next_index = margin_storage::copy_margin::<_, M>(previous.as_slice(), &mut retained, index);
        tree.edit(node).set_block_margin_index::<T::Float>(next_index);
    }
    *tree.margins() = retained;
    *tree.margin_scratch() = previous;
    M::clear(tree.margin_scratch());
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) struct RegionPrepared<I> {
    pub root: I,
    pub parent: Option<I>,
    pub parent_layout: Option<ChildrenLayout>,
    pub in_flow: bool,
    pub parent_cell_before: [u32; 2],
    pub restored_parent_cell: Option<[u32; 2]>,
    pub prepared_parent_flow: [u32; 2],
    pub leaf_only: bool,
    pub needed_sizing: bool,
    pub visits: Seq<RootVisit<I>>,
}

impl<I> RegionPrepared<I> {
    pub(crate) open spec fn valid(self, order: Order<I>, root: I, leaf_only: bool) -> bool {
        &&& self.root == root && self.parent == (order.parent)(root) && self.leaf_only == leaf_only
        &&& self.parent.is_none() == self.parent_layout.is_none()
        &&& !region_policy::attached_flow_child(self.in_flow,
            matches!(self.parent_layout, Some(ChildrenLayout::Wrap { .. } | ChildrenLayout::Block)))
        &&& self.restored_parent_cell == grid_state::preserve_parent_cell(self.in_flow,
            matches!(self.parent_layout, Some(ChildrenLayout::Grid { .. })), self.parent_cell_before)
        &&& self.restored_parent_cell.is_some() ==> self.prepared_parent_flow == self.restored_parent_cell.unwrap()
        &&& ordered_visits(order, root, self.visits)
        &&& !self.needed_sizing ==> self.visits.len() == 0
    }
}

fn observe_parent_flow<T: RecordModel + ?Sized>(tree: &T, root: T::Id) -> (record: Ghost<[u32; 2]>)
    ensures record@ == tree.layout_record(root).parent_flow, no_unwind
{
    Ghost(tree.layout_record(root).parent_flow)
}

fn region_prepared<I: Copy>(root: I, parent: Option<I>, parent_layout: Option<ChildrenLayout>, in_flow: bool,
    parent_cell_before: [u32; 2], restored_parent_cell: Option<[u32; 2]>, prepared_parent_flow: Ghost<[u32; 2]>,
    leaf_only: bool, needed_sizing: bool, visits: Ghost<Seq<RootVisit<I>>>,
) -> (prepared: Ghost<RegionPrepared<I>>)
    ensures prepared@ == (RegionPrepared { root, parent, parent_layout, in_flow, parent_cell_before,
        restored_parent_cell, prepared_parent_flow: prepared_parent_flow@, leaf_only, needed_sizing, visits: visits@ }),
    no_unwind
{
    Ghost(RegionPrepared { root, parent, parent_layout, in_flow, parent_cell_before, restored_parent_cell,
        prepared_parent_flow: prepared_parent_flow@, leaf_only, needed_sizing, visits: visits@ })
}
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct RegionMeasure<I> {
    pub nodes: u32,
    pub slots: u32,
    pub blocks: usize,
    #[cfg(verus_keep_ghost)]
    pub prepared: Ghost<RegionPrepared<I>>,
    #[cfg(not(verus_keep_ghost))]
    id: core::marker::PhantomData<I>,
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(out =>
    requires live(old(tree), root), old(tree).order().ordered(), old(tree).order().closed_subtrees(),
        LEAF_ONLY ==> (old(tree).order().parent)(root).is_none(),
    ensures final(tree).order() == old(tree).order(), LEAF_ONLY ==> out.is_some(),
        out.is_some() ==> out.unwrap().prepared@.valid(old(tree).order(), root, LEAF_ONLY),
    no_unwind
))]
pub(crate) fn measure_region<T: Access + ?Sized, M: VecMemory, const LEAF_ONLY: bool>(
    tree: &mut T, root: T::Id,
) -> Option<RegionMeasure<T::Id>> {
    let parent = tree.parent_id(root);
    let parent_layout = match parent {
        Some(parent) => Some(tree.params(parent).children_layout),
        None => None,
    };
    let params = tree.params(root);
    let in_flow = !params.disabled && !params.free_placement;
    if region_policy::attached_flow_child(in_flow, matches!(parent_layout, Some(ChildrenLayout::Wrap { .. } | ChildrenLayout::Block))) {
        return None;
    }
    let parent_cell = tree.record(root).parent_flow;
    let grid_cell = grid_state::preserve_parent_cell(in_flow, matches!(parent_layout, Some(ChildrenLayout::Grid { .. })), parent_cell);
    if LEAF_ONLY {
        // The document replay rebuilds every flow producer. The retained
        // leaf path keeps only declaration and Final words, never margins.
        M::clear(tree.margins());
    }
    let mut retained = prepare_nodes::empty_retained();
    retained.leaf_only = LEAF_ONLY;
    let (nodes, needs_solve) = prepare_nodes::prepare::<T, M, true, false>(tree, root, None, &mut retained);
    if let Some(cell) = grid_cell { tree.edit(root).parent_flow = cell; }
    #[cfg(verus_keep_ghost)]
    let prepared_parent_flow = observe_parent_flow(tree, root);

    let mut slots = nodes.saturating_mul(4);
    let mut blocks = retained.blocks;
    #[cfg(verus_keep_ghost)]
    let mut visits = no_visits();
    if needs_solve {
        let _walk = solve_subtree::<T, true>(tree, root);
        #[cfg(verus_keep_ghost)]
        { visits = _walk.visits; }
        if !retained.inspect_descendants { slots = slots.saturating_add(retained.leaf_bounds); }
        let mut next = Some(root);
        #[cfg(verus_keep_ghost)]
        proof! { tree.order().node_facts(root); }
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant tree.order() == old(tree).order(), live(tree, root), tree.order().ordered(), tree.order().closed_subtrees(),
                next.is_some() ==> inside(tree.order(), root, next.unwrap()),
            decreases remaining(tree.order(), root, next),
        ))]
        while let Some(node) = next {
            if matches!(tree.record(node).structural_change, StructuralChange::Retained) {
                tree.edit(node).structural_change = StructuralChange::Clean;
                next = following_in_subtree(tree, root, node, false);
                continue;
            }
            let flags = tree.record(node).flags;
            const SOLVED_BITS: u32 = 0xaaaa_aaaa & (u32::MAX >> (32 - 2 * cycle_rules::N_SLOTS));
            slots = slots.saturating_add(T::ones(flags.0 & SOLVED_BITS).saturating_sub(4));
            blocks = blocks.saturating_add(if flags.is_block_container() { 1 } else { 0 });
            next = following_in_subtree(tree, root, node, retained.inspect_descendants
                && flags.0 & NodeFlags::DESCENDANTS_NEED_SOLVE != 0);
        }
    }
    Some(RegionMeasure {
        nodes, slots: slots.saturating_sub(retained.slots), blocks,
        #[cfg(verus_keep_ghost)]
        prepared: region_prepared(root, parent, parent_layout, in_flow, parent_cell, grid_cell, prepared_parent_flow,
            LEAF_ONLY, needs_solve, visits),
        #[cfg(not(verus_keep_ghost))]
        id: core::marker::PhantomData,
    })
}
