//! Publish one rectangle and identify its first descendant cursor.
#![allow(unexpected_cfgs)]

use crate::prepare_frame::FrameFloat;
#[cfg(not(verus_keep_ghost))]
use crate::placement_work::PlacementWork;
#[cfg(verus_keep_ghost)]
use super::PlacementWork;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

pub(crate) type Edges = [[f32; 2]; 2];

#[cfg(verus_keep_ghost)]
verus! {
/// The finite sibling suffix includes the current node's entire subtree.
#[verifier::reject_recursive_types(I)]
pub struct PlacementLinks<I> {
    pub child: spec_fn(I) -> Option<I>,
    pub sibling: spec_fn(I) -> Option<I>,
    pub suffix: spec_fn(I) -> nat,
    pub interval: spec_fn(I) -> (nat, nat),
    pub ceiling: spec_fn(I) -> nat,
}

impl<I> PlacementLinks<I> {
    pub(crate) open spec fn from_order(order: crate::prepare_frame::Order<I>) -> Self {
        Self {
            child: order.first,
            sibling: order.sibling,
            interval: order.interval,
            ceiling: |node: I| match (order.parent)(node) {
                Some(parent) => (order.interval)(parent).1,
                None => (order.interval)(node).1,
            },
            suffix: |node: I| {
                if !(order.live)(node) {
                    0
                } else {
                    let end = match (order.parent)(node) {
                        Some(parent) => (order.interval)(parent).1,
                        None => (order.interval)(node).1,
                    };
                    (end - (order.interval)(node).0) as nat
                }
            },
        }
    }

    pub open spec fn cost(self, cursor: Option<I>) -> nat {
        match cursor { Some(node) => (self.suffix)(node), None => 0 }
    }

    pub open spec fn first(self, node: I) -> Option<I> { (self.child)(node) }
    pub open spec fn next(self, node: I) -> Option<I> { (self.sibling)(node) }

    /// Exactly two physical children, with no descendants in either branch.
    pub open spec fn leaf_pair(self, parent: I) -> Option<(I, I)> {
        match self.first(parent) {
            Some(first) => match self.next(first) {
                Some(second) if self.next(second).is_none() && self.first(first).is_none()
                    && self.first(second).is_none() => Some((first, second)),
                _ => None,
            },
            None => None,
        }
    }

    pub open spec fn rank(self, node: I) -> nat { (self.interval)(node).0 }
    pub open spec fn end(self, node: I) -> nat { (self.interval)(node).1 }
    pub open spec fn limit(self, node: I) -> nat { (self.ceiling)(node) }

    pub open spec fn covers(self, node: I) -> bool {
        &&& self.cost(self.first(node)) + self.cost(self.next(node)) < self.cost(Some(node))
        &&& self.first(node).is_some() ==> self.cost(self.first(node)) > 0
        &&& self.next(node).is_some() ==> self.cost(self.next(node)) > 0
        &&& self.rank(node) < self.end(node) <= self.limit(node)
        &&& match self.first(node) {
            Some(child) => self.rank(node) < self.rank(child) < self.end(node)
                && self.limit(child) == self.end(node),
            None => true,
        }
        &&& match self.next(node) {
            Some(next) => self.end(node) <= self.rank(next) < self.limit(node)
                && self.limit(next) == self.limit(node),
            None => true,
        }
    }

    pub open spec fn finite(self) -> bool {
        forall |node: I| #[trigger] self.cost(Some(node)) > 0 ==> self.covers(node)
    }
}

/// A sibling's remaining interval ends at its parent. The current subtree
/// and any later siblings have disjoint intervals, even when ranks have gaps.
pub(crate) proof fn finite_from_order<I>(order: crate::prepare_frame::Order<I>)
    requires order.ordered(),
    ensures
        PlacementLinks::from_order(order).finite(),
        forall |node: I| #[trigger] PlacementLinks::from_order(order).cost(Some(node)) > 0
            <==> (order.live)(node),
{
    let links = PlacementLinks::from_order(order);
    assert forall |node: I| #[trigger] links.cost(Some(node)) > 0 <==> (order.live)(node) by {
        if (order.live)(node) {
            order.node_facts(node);
            if let Some(parent) = (order.parent)(node) {
                assert(order.child(parent, node));
            }
        }
    }
    assert forall |node: I| #[trigger] links.cost(Some(node)) > 0 implies links.covers(node) by {
        order.node_facts(node);
        assert(links.rank(node) < links.end(node) <= links.limit(node));
        if let Some(child) = links.first(node) {
            let start = (order.interval)(child).0;
            assert((order.live)(child));
            assert(links.cost(Some(child)) == (order.interval)(node).1 - start);
            assert(links.limit(child) == links.end(node));
        }
        if let Some(next) = links.next(node) {
            let parent = (order.parent)(node).unwrap();
            let start = (order.interval)(next).0;
            assert((order.live)(next));
            assert(links.cost(Some(next)) == (order.interval)(parent).1 - start);
            assert(links.limit(next) == links.limit(node));
        }
    }
}

/// In preorder, the unvisited suffix is split into the selected node, its
/// children and its later siblings. The ranks are mathematical, so this
/// witness adds no storage or arithmetic to a native cursor.
pub proof fn finite_from_preorder<I>(
    links: PlacementLinks<I>, start: spec_fn(I) -> nat,
    subtree_end: spec_fn(I) -> nat, sibling_end: spec_fn(I) -> nat,
)
    requires
        forall |id: I| #[trigger] links.rank(id) == start(id),
        forall |id: I| #[trigger] links.end(id) == subtree_end(id),
        forall |id: I| #[trigger] links.limit(id) == sibling_end(id),
        forall |id: I| #[trigger] links.cost(Some(id))
            == if start(id) < sibling_end(id) { (sibling_end(id) - start(id)) as nat } else { 0 },
        forall |id: I| #[trigger] links.cost(Some(id)) > 0 ==> {
            &&& start(id) < subtree_end(id) <= sibling_end(id)
            &&& match links.first(id) {
                Some(child) => start(child) == start(id) + 1 && start(child) < subtree_end(id)
                    && sibling_end(child) == subtree_end(id),
                None => subtree_end(id) == start(id) + 1,
            }
            &&& match links.next(id) {
                Some(sibling) => start(sibling) == subtree_end(id) && start(sibling) < sibling_end(id)
                    && sibling_end(sibling) == sibling_end(id),
                None => subtree_end(id) == sibling_end(id),
            }
        },
    ensures links.finite(),
{
    assert forall |id: I| #[trigger] links.cost(Some(id)) > 0 implies links.covers(id) by {
        if let Some(child) = links.first(id) {
            assert(links.cost(Some(child)) == sibling_end(child) - start(child));
        }
        if let Some(sibling) = links.next(id) {
            assert(links.cost(Some(sibling)) == sibling_end(sibling) - start(sibling));
        }
    }
}

#[allow(private_bounds)]
pub trait NodeModel<I> {
    type PublicationFloat: FrameFloat;
    spec fn solved_size(&self, node: I) -> [f32; 2];
    spec fn start_aligned(&self) -> spec_fn(I, bool) -> bool;
    spec fn configured_scale(&self) -> Option<f32>;
    spec fn mark(&self, node: I) -> Option<PlacementWork>;
    spec fn links(&self) -> PlacementLinks<I>;
    spec fn hidden(&self) -> spec_fn(I) -> bool;
    spec fn plain(&self) -> bool;
    spec fn root_key(&self) -> I;
    spec fn written(&self) -> Seq<I>;
    spec fn rectangles(&self) -> Map<I, (Edges, Edges)>;
    spec fn rounding(&self) -> spec_fn(Edges) -> Edges;
    spec fn edge_difference(left: f32, right: f32) -> f32;
}
}

#[cfg(not(verus_keep_ghost))]
#[allow(private_bounds)]
pub trait NodeModel<I> { type PublicationFloat: FrameFloat; }

/// Primitive operations on one layout node. A missing mark means that this host
/// does not keep incremental placement state.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait NodeTarget<I>: NodeModel<I> {
    #[cfg_attr(verus_keep_ghost, verus_spec(work => ensures work == self.mark(node), no_unwind))]
    fn read_work(&self, node: I) -> Option<PlacementWork>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).mark(node) == Some(PlacementWork::Clean),
            forall|other: I| other != node ==> #[trigger] final(self).mark(other) == old(self).mark(other),
            final(self).links() == old(self).links(),
            final(self).hidden() == old(self).hidden(),
                final(self).plain() == old(self).plain(),
            final(self).written() == old(self).written(),
            final(self).rectangles() == old(self).rectangles(),
            final(self).rounding() == old(self).rounding(),
            forall|id: I| #[trigger] final(self).solved_size(id) == old(self).solved_size(id),
            final(self).start_aligned() == old(self).start_aligned(),
        no_unwind
    ))]
    fn clear_work(&mut self, node: I);

    #[cfg_attr(verus_keep_ghost, verus_spec(rounded => ensures rounded == (self.rounding())(rect), no_unwind))]
    fn snap(&self, rect: Edges) -> Edges;

    #[cfg_attr(verus_keep_ghost, verus_spec(returns Self::edge_difference(left, right), no_unwind))]
    fn subtract_edges(left: f32, right: f32) -> f32;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).written() == old(self).written().push(node),
            final(self).rectangles() == old(self).rectangles().insert(node, (rect, local)),
            final(self).links() == old(self).links(),
            final(self).hidden() == old(self).hidden(),
                final(self).plain() == old(self).plain(),
            final(self).rounding() == old(self).rounding(),
            forall|other: I| #[trigger] final(self).mark(other) == old(self).mark(other),
            forall|id: I| #[trigger] final(self).solved_size(id) == old(self).solved_size(id),
            final(self).start_aligned() == old(self).start_aligned(),
        no_unwind
    ))]
    fn write(&mut self, node: I, rect: Edges, local: Edges);

    #[cfg_attr(verus_keep_ghost, verus_spec(first => ensures first == self.links().first(node), no_unwind))]
    fn first_child(&self, node: I) -> Option<I>;
}

#[cfg(verus_keep_ghost)]
verus! {
pub open spec fn visits(work: Option<PlacementWork>, partial: bool) -> bool {
    match work { Some(mark) => mark.visits(!partial), None => true }
}

pub open spec fn writes(work: Option<PlacementWork>, partial: bool) -> bool {
    match work { Some(mark) => mark.writes(!partial), None => true }
}

pub(crate) open spec fn relative_edges<I, T: NodeModel<I>>(rect: Edges, origin: [f32; 2]) -> Edges {
    let [[left, right], [top, bottom]] = rect;
    let [x, y] = origin;
    [[T::edge_difference(left, x), T::edge_difference(right, x)],
        [T::edge_difference(top, y), T::edge_difference(bottom, y)]]
}

/// Representation at the host sink. Descent still uses the raw snapped origin.
pub(crate) open spec fn published_edges<I, T: NodeModel<I> + ?Sized>(rect: Edges) -> Edges {
    crate::placement_adapter::stable_rectangle_value::<T::PublicationFloat>(rect)
}

pub(crate) open spec fn resulting_rectangles<I, T: NodeModel<I>>(
    target: &T, node: I, rect: Edges, origin: [f32; 2], partial: bool,
) -> Map<I, (Edges, Edges)> {
    if writes(target.mark(node), partial) {
        let absolute = (target.rounding())(rect);
        target.rectangles().insert(node, (published_edges::<I, T>(absolute),
            published_edges::<I, T>(relative_edges::<I, T>(absolute, origin))))
    } else {
        target.rectangles()
    }
}
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(visit => ensures visit == visits(work, PARTIAL), no_unwind))]
fn visits_work<const PARTIAL: bool>(work: Option<PlacementWork>) -> bool {
    match work { Some(mark) => mark.visits(!PARTIAL), None => true }
}

/// A mode can skip computing a rectangle when publication would leave its
/// mark and retained output intact and would not visit any descendants.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(skip =>
    ensures skip == !visits(target.mark(node), PARTIAL),
        skip ==> !writes(target.mark(node), PARTIAL) && target.mark(node) == Some(PlacementWork::Clean),
    no_unwind
))]
pub(crate) fn skip_clean<I, T: NodeTarget<I>, const PARTIAL: bool>(target: &T, node: I) -> bool {
    PARTIAL && !visits_work::<PARTIAL>(target.read_work(node))
}

/// Subtract the snapped parent's origin after rounding the absolute edges.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(returns relative_edges::<I, T>(rect, origin), no_unwind))]
fn local_edges<I, T: NodeTarget<I>>(rect: Edges, origin: [f32; 2]) -> Edges {
    let [[left, right], [top, bottom]] = rect;
    let [x, y] = origin;
    [[T::subtract_edges(left, x), T::subtract_edges(right, x)],
        [T::subtract_edges(top, y), T::subtract_edges(bottom, y)]]
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns snapped_origin(rect), no_unwind))]
pub(crate) fn snapped_origin(rect: Edges) -> [f32; 2] {
    let [[left, _], [top, _]] = rect;
    [left, top]
}

/// Publish edges that have already been rounded by either snapper.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(target).links() == old(target).links(),
        final(target).hidden() == old(target).hidden(),
            final(target).plain() == old(target).plain(),
        final(target).rounding() == old(target).rounding(),
        final(target).written() == old(target).written().push(node),
        final(target).rectangles() == old(target).rectangles().insert(node, (published_edges::<I, T>(rect),
            published_edges::<I, T>(relative_edges::<I, T>(rect, origin)))),
        forall|id: I| #[trigger] final(target).mark(id) ==
            if reset && id == node { Some(PlacementWork::Clean) } else { old(target).mark(id) },
        forall|id: I| #[trigger] final(target).solved_size(id) == old(target).solved_size(id),
        final(target).start_aligned() == old(target).start_aligned(),
    no_unwind
))]
pub(crate) fn write_snapped<I: Copy, T: NodeTarget<I>>(
    target: &mut T, node: I, rect: Edges, origin: [f32; 2], reset: bool,
) {
    if reset { target.clear_work(node); }
    let local = local_edges::<I, T>(rect, origin);
    let absolute = crate::placement_adapter::stable_edges::<T::PublicationFloat>(rect);
    let local = crate::placement_adapter::stable_edges::<T::PublicationFloat>(local);
    target.write(node, absolute, local);
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(branch =>
    ensures final(target).links() == old(target).links(),
        final(target).hidden() == old(target).hidden(),
            final(target).plain() == old(target).plain(),
        final(target).rounding() == old(target).rounding(),
        final(target).rectangles() == resulting_rectangles(old(target), node, rect, parent_origin, PARTIAL),
        final(target).written() == (if writes(old(target).mark(node), PARTIAL) {
        old(target).written().push(node)
    } else { old(target).written() }),
        final(target).mark(node) == (if visits(old(target).mark(node), PARTIAL) && old(target).mark(node).is_some() {
            Some(PlacementWork::Clean)
        } else { old(target).mark(node) }),
        forall|other: I| other != node ==> #[trigger] final(target).mark(other) == old(target).mark(other),
        match branch {
            Some((first, origin, partial)) => visits(old(target).mark(node), PARTIAL)
                && Some(first) == old(target).links().first(node)
                && origin == snapped_origin((old(target).rounding())(rect))
                && partial == (PARTIAL && !writes(old(target).mark(node), PARTIAL)),
            None => !visits(old(target).mark(node), PARTIAL) || old(target).links().first(node).is_none(),
        },
    no_unwind
))]
pub(crate) fn publish<I: Copy, T: NodeTarget<I>, const PARTIAL: bool>(
    target: &mut T, node: I, rect: Edges, parent_origin: [f32; 2],
) -> Option<(I, [f32; 2], bool)> {
    let work = target.read_work(node);
    if !visits_work::<PARTIAL>(work) { return None; }
    let write = if let Some(work) = work {
        if !matches!(work, PlacementWork::Clean) { target.clear_work(node); }
        work.writes(!PARTIAL)
    } else { true };

    let output = target.snap(rect);
    if write {
        write_snapped(target, node, output, parent_origin, false);
    }
    let Some(first) = target.first_child(node) else { return None };
    // A changed frame forces all its descendants to publish.
    Some((first, snapped_origin(output), PARTIAL && !write))
}
