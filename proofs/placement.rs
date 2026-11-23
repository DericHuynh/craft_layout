use vstd::prelude::*;

#[path = "../src/placement_work.rs"]
pub(crate) mod kernel;
pub use kernel::PlacementWork;

verus! {

/// The child summary pairs its placement mark with whether its size can reposition siblings.
pub open spec fn fold_children(initial: PlacementWork, children: Seq<(PlacementWork, bool)>) -> PlacementWork
    decreases children.len(),
{
    if children.len() == 0 {
        initial
    } else {
        let child = children.last();
        fold_children(initial, children.drop_last()).with_child(child.0, child.1)
    }
}

pub open spec fn any_coupled_size_change(children: Seq<(PlacementWork, bool)>) -> bool {
    exists|i: int| 0 <= i < children.len() && (#[trigger] children[i]).1
}

pub open spec fn any_child_work(children: Seq<(PlacementWork, bool)>) -> bool {
    exists|i: int| 0 <= i < children.len() && (#[trigger] children[i]).0 != PlacementWork::Clean
}

/// The planner skips clean leaves and stops updating a mark once it covers the entire subtree.
pub proof fn lemma_skipped_child(previous: PlacementWork, child: PlacementWork, coupled_size_change: bool)
    ensures
        previous.with_child(PlacementWork::Clean, false) == previous,
        PlacementWork::Subtree.with_child(child, coupled_size_change) == PlacementWork::Subtree,
{}

proof fn lemma_fold(initial: PlacementWork, children: Seq<(PlacementWork, bool)>, force: bool)
    ensures
        fold_children(initial, children).writes(force) == (initial.writes(force) || any_coupled_size_change(children)),
        fold_children(initial, children).visits(force) == (initial.visits(force)
            || any_coupled_size_change(children) || any_child_work(children)),
    decreases children.len(),
{
    if children.len() > 0 {
        let rest = children.drop_last();
        let last = children.last();
        lemma_fold(initial, rest, force);
        assert(last == children[children.len() - 1]);
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] children[i] == rest[i] by {};
        assert forall|i: int| 0 <= i < rest.len() implies #[trigger] rest[i] == children[i] by {};
        assert(any_coupled_size_change(children) == (any_coupled_size_change(rest) || last.1));
        assert(any_child_work(children) == (any_child_work(rest) || last.0 != PlacementWork::Clean));
    }
}

/// Summarizing any number of children preserves every reason to visit or rewrite.
pub proof fn lemma_parent_fold(
    previous: PlacementWork, children_changed: bool, coupled: bool, children: Seq<(PlacementWork, bool)>, force: bool,
)
    ensures
        fold_children(previous.for_parent(children_changed, coupled), children).writes(force)
            == (force || previous == PlacementWork::Subtree || children_changed && coupled || any_coupled_size_change(children)),
        fold_children(previous.for_parent(children_changed, coupled), children).visits(force)
            == (force || previous == PlacementWork::Subtree || children_changed && coupled
                || any_coupled_size_change(children) || any_child_work(children)),
{
    lemma_fold(previous.for_parent(children_changed, coupled), children, force);
}

/// A partial pass reaches each child that requested work. A coupled change forces
/// placement for every sibling, including siblings whose own marks are clean.
pub proof fn lemma_child_reached(
    previous: PlacementWork, children_changed: bool, coupled: bool,
    children: Seq<(PlacementWork, bool)>, i: int, force: bool,
)
    requires 0 <= i < children.len(),
    ensures ({
        let parent = fold_children(previous.for_parent(children_changed, coupled), children);
        let child = children[i].0;
        &&& child.visits(false) ==> (parent.visits(force) && child.visits(parent.writes(force)))
        &&& child.writes(false) ==> (parent.visits(force) && child.writes(parent.writes(force)))
        &&& (force || previous == PlacementWork::Subtree || children_changed && coupled
                || any_coupled_size_change(children))
            ==> (parent.visits(force) && child.writes(parent.writes(force)))
    }),
{
    lemma_parent_fold(previous, children_changed, coupled, children, force);
    if children[i].0 != PlacementWork::Clean {
        assert(any_child_work(children));
    }
}

/// One edge on a path through the current tree. The same parent summary is used
/// for each sibling. The index identifies the child on this path.
pub struct PathEdge {
    pub previous: PlacementWork,
    pub children_changed: bool,
    pub coupled: bool,
    pub children: Seq<(PlacementWork, bool)>,
    pub index: int,
}

impl PathEdge {
    pub open spec fn parent_mark(self) -> PlacementWork {
        fold_children(self.previous.for_parent(self.children_changed, self.coupled), self.children)
    }
}

/// Adjacent summaries agree on the mark of their shared node, with the final
/// child carrying the target mark. The empty path describes the root itself.
pub open spec fn routes_to(path: Seq<PathEdge>, target: PlacementWork) -> bool
    decreases path.len(),
{
    if path.len() == 0 {
        true
    } else {
        let edge = path.last();
        &&& 0 <= edge.index < edge.children.len()
        &&& edge.children[edge.index].0 == target
        &&& routes_to(path.drop_last(), edge.parent_mark())
    }
}

pub struct Route {
    pub visited: bool,
    pub force: bool,
}

/// Follow placement from the root. Rewriting a parent forces all of its children.
pub open spec fn placement_route(path: Seq<PathEdge>, root_force: bool) -> Route
    decreases path.len(),
{
    if path.len() == 0 {
        Route { visited: true, force: root_force }
    } else {
        let edge = path.last();
        let prior = placement_route(path.drop_last(), root_force);
        let force = edge.parent_mark().writes(prior.force);
        let child = edge.children[edge.index].0;
        Route {
            visited: prior.visited && edge.parent_mark().visits(prior.force) && child.visits(force),
            force,
        }
    }
}

pub open spec fn ancestor_writes(path: Seq<PathEdge>) -> bool {
    exists|i: int| 0 <= i < path.len() && (#[trigger] path[i]).parent_mark() == PlacementWork::Subtree
}

/// Dirty targets are reachable regardless of path length. Full traversal or a
/// rewritten ancestor also reaches and rewrites every clean descendant on its path.
pub proof fn lemma_path_reached(path: Seq<PathEdge>, target: PlacementWork, root_force: bool)
    requires routes_to(path, target),
    ensures ({
        let route = placement_route(path, root_force);
        &&& route.force == (root_force || ancestor_writes(path))
        &&& target.visits(route.force) ==> route.visited
        &&& (target == PlacementWork::Subtree || root_force || ancestor_writes(path))
            ==> (route.visited && target.writes(route.force))
    }),
    decreases path.len(),
{
    if path.len() > 0 {
        let edge = path.last();
        let prefix = path.drop_last();
        let prior = placement_route(prefix, root_force);
        lemma_path_reached(prefix, edge.parent_mark(), root_force);
        lemma_child_reached(edge.previous, edge.children_changed, edge.coupled,
            edge.children, edge.index, prior.force);
        assert(edge == path[path.len() - 1]);
        assert forall|i: int| 0 <= i < prefix.len() implies #[trigger] prefix[i] == path[i] by {};
        assert forall|i: int| 0 <= i < prefix.len() implies #[trigger] path[i] == prefix[i] by {};
        assert(ancestor_writes(path) == (ancestor_writes(prefix) || edge.parent_mark() == PlacementWork::Subtree));
    }
}

}
