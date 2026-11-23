//! Placement order through first-child/next-sibling links.
use vstd::prelude::*;
#[path = "../src/child_walk.rs"]
mod kernel;

verus! {

pub open spec fn at<I>(links: Seq<(I, bool)>, stop: Option<I>, i: int) -> Option<I> {
    if i == links.len() { stop } else { Some(links[i].0) }
}

pub open spec fn position<I>(links: Seq<(I, bool)>, stop: Option<I>, cursor: Option<I>) -> int {
    choose |i: int| 0 <= i <= links.len() && at(links, stop, i) == cursor
}

// The adapter supplies a finite sibling chain of distinct IDs. Its last link is
// either the end of the siblings, or the first child of the next wrapping line.
pub open spec fn chain<I, F: Fn(I) -> Option<(Option<I>, bool)>>(
    links: Seq<(I, bool)>, stop: Option<I>, read: F,
) -> bool {
    &&& forall |i: int, j: int| 0 <= i <= links.len() && 0 <= j <= links.len() &&
        #[trigger] at(links, stop, i) == #[trigger] at(links, stop, j) ==> i == j
    &&& forall |i: int| 0 <= i < links.len() ==> #[trigger] call_requires(read, (links[i].0,))
    &&& forall |i: int, r: Option<(Option<I>, bool)>| 0 <= i < links.len() &&
        #[trigger] call_ensures(read, (links[i].0,), r) ==> r == Some((at(links, stop, i + 1), !links[i].1))
    &&& stop.is_some() ==> call_requires(read, (stop.unwrap(),))
    &&& forall |r: Option<(Option<I>, bool)>| stop.is_some() && #[trigger] call_ensures(read, (stop.unwrap(),), r)
        ==> r == None
}

proof fn locate<I>(links: Seq<(I, bool)>, stop: Option<I>, i: int)
    requires 0 <= i <= links.len(), forall |j: int, k: int| 0 <= j <= links.len() && 0 <= k <= links.len()
        && #[trigger] at(links, stop, j) == #[trigger] at(links, stop, k) ==> j == k,
    ensures position(links, stop, at(links, stop, i)) == i,
{
    assert(exists |k: int| 0 <= k <= links.len() && at(links, stop, k) == at(links, stop, i));
}

pub open spec fn advanced<I>(links: Seq<(I, bool)>, stop: Option<I>, result: Option<I>, cursor: Option<I>) -> bool {
    match result {
        None => cursor == stop && forall |i: int| 0 <= i < links.len() ==> !(#[trigger] links[i]).1,
        Some(id) => exists |i: int| 0 <= i < links.len() && #[trigger] at(links, stop, i) == Some(id)
            && links[i].1 && cursor == at(links, stop, i + 1) &&
            forall |j: int| 0 <= j < i ==> !(#[trigger] links[j]).1,
    }
}

}

use super::{Key, Phase, Rule, Step, Work, writes};
use super::placement::{PathEdge, PlacementWork, Route, placement_route};
use super::retained_view::visible_keys;

verus! {

/// The payload is the output of recursively visiting this child. Absolute
/// positioning (a free child) affects wrap fitting, but never hides the child.
pub struct Child<A> {
    pub output: Seq<A>,
    pub enabled: bool,
    pub free: bool,
    pub marked_break: bool,
}

pub open spec fn walk<A>(children: Seq<Child<A>>) -> Seq<A>
    decreases children.len(),
{
    if children.len() == 0 { Seq::empty() } else {
        let child = children.first();
        (if child.enabled { child.output } else { Seq::empty() }) + walk(children.drop_first())
    }
}

// This postcondition is the same one established by the executable cursor. Its
// returned child can be consumed immediately, before borrowing the adapter again.
pub proof fn cursor_emits_first_visible<A>(
    children: Seq<Child<A>>, stop: Option<int>, result: Option<int>, next: Option<int>,
)
    requires advanced(Seq::new(children.len(), |i: int| (i, children[i].enabled)), stop, result, next),
    ensures match result {
        None => walk(children) == Seq::<A>::empty() && next == stop,
        Some(i) => 0 <= i < children.len() && children[i].enabled &&
            walk(children) == children[i].output + walk(children.skip(i+1)) &&
            next == if i+1 == children.len() { stop } else { Some(i+1) },
    },
{
    let links = Seq::new(children.len(), |i: int| (i, children[i].enabled));
    if let Some(id) = result {
        let i = choose |i: int| 0 <= i < links.len() && #[trigger] at(links, stop, i) == Some(id)
            && links[i].1 && next == at(links, stop, i+1) &&
            forall |j: int| 0 <= j < i ==> !(#[trigger] links[j]).1;
        assert(i == id);
        walk_split(children, i);
        assert forall |j: int| 0 <= j < children.take(i).len() implies !(#[trigger] children.take(i)[j]).enabled by {
            assert(!links[j].1);
        }
        empty_walk(children.take(i));
        assert(children.skip(i).drop_first() =~= children.skip(i+1));
    } else {
        assert forall |i:int| 0 <= i < children.len() implies !(#[trigger] children[i]).enabled by {
            assert(!links[i].1);
        }
        empty_walk(children);
    }
}

proof fn empty_walk<A>(children: Seq<Child<A>>)
    requires forall |i:int| 0 <= i < children.len() ==> !(#[trigger] children[i]).enabled,
    ensures walk(children) == Seq::<A>::empty(),
    decreases children.len(),
{
    if children.len() > 0 {
        assert forall |i:int| 0 <= i < children.drop_first().len() implies !(#[trigger] children.drop_first()[i]).enabled by {
            assert(!children[i+1].enabled);
        }
        empty_walk(children.drop_first());
    }
}

proof fn walk_split<A>(children: Seq<Child<A>>, cut: int)
    requires 0 <= cut <= children.len(),
    ensures walk(children) == walk(children.take(cut)) + walk(children.skip(cut)),
    decreases cut,
{
    if cut > 0 {
        walk_split(children.drop_first(), cut-1);
        assert(children.take(cut).drop_first() =~= children.drop_first().take(cut-1));
        assert(children.skip(cut) =~= children.drop_first().skip(cut-1));
    } else { assert(children.skip(0) =~= children); }
}

// At placement time wrap_line(None) uses cached breaks and accepts at least one
// in-flow item before it can stop. Trailing disabled/free children still advance.
pub open spec fn line_len<A>(children: Seq<Child<A>>, has_item: bool) -> nat
    decreases children.len(),
{
    if children.len() == 0 { 0 }
    else {
        let child = children.first();
        let flows = child.enabled && !child.free;
        if flows && has_item && child.marked_break { 0 }
        else { 1 + line_len(children.drop_first(), has_item || flows) }
    }
}

proof fn line_progress<A>(children: Seq<Child<A>>, has_item: bool)
    ensures line_len(children, has_item) <= children.len(),
        !has_item && children.len() > 0 ==> line_len(children, has_item) > 0,
    decreases children.len(),
{
    if children.len() > 0 {
        let first = children.first();
        line_progress(children.drop_first(), has_item || (first.enabled && !first.free));
    }
}

// A cached boundary points to an in-flow sibling. The first in-flow item in
// the current line can itself have a mark and must still be consumed.
pub open spec fn in_flow<A>(child: Child<A>) -> bool {
    child.enabled && !child.free
}

pub open spec fn eligible_boundary<A>(children: Seq<Child<A>>, at: int) -> bool {
    0 <= at < children.len() && in_flow(children[at])
        && (exists |prior: int| 0 <= prior < at && in_flow(#[trigger] children[prior]))
}

pub open spec fn cached_boundaries_match<A>(children: Seq<Child<A>>, cut: nat, seen: bool) -> bool {
    &&& cut <= children.len()
    &&& cut < children.len() && in_flow(children[cut as int]) && children[cut as int].marked_break
        && (seen || eligible_boundary(children, cut as int)) || cut == children.len()
    &&& forall |j:int| 0 <= j < cut && (seen || eligible_boundary(children,j))
        ==> !(#[trigger] children[j]).marked_break || !in_flow(children[j])
}

/// `cut` is the next endpoint selected during sizing. Replaying the marks
/// reads the same run, regardless of the now-resolved main-axis Fill sizes.
pub proof fn recorded_wrap_boundary_is_replayed<A>(children: Seq<Child<A>>, cut: nat, seen: bool)
    requires cached_boundaries_match(children,cut,seen),
    ensures line_len(children,seen) == cut,
    decreases children.len(),
{
    if children.len() > 0 {
        let first = children.first();
        assert(first == children[0]);
        let flows = in_flow(first);
        if cut == 0 {
            assert(seen);
        } else {
            assert(!(flows && seen && first.marked_break));
            let rest = children.drop_first();
            let any = seen || flows;
            assert forall |j:int| 0 <= j < rest.len() implies
                (eligible_boundary(rest,j) || any && in_flow(#[trigger] rest[j]))
                    == (eligible_boundary(children,j+1) || seen && in_flow(children[j+1])) by {
                assert(rest[j] == children[j+1]);
                if eligible_boundary(rest,j) {
                    let prev = choose |p:int| 0 <= p < j && in_flow(#[trigger] rest[p]);
                    assert(rest[prev] == children[prev+1]);
                }
                if eligible_boundary(children,j+1) {
                    let prev = choose |p:int| 0 <= p < j+1 && in_flow(#[trigger] children[p]);
                    if prev > 0 { assert(rest[prev-1] == children[prev]); }
                }
            }
            assert(forall |j:int| 0 <= j < cut - 1 && (any || eligible_boundary(rest,j))
                ==> !(#[trigger] rest[j]).marked_break || !in_flow(rest[j]));
            if cut < children.len() { assert(rest[cut - 1] == children[cut as int]); }
            recorded_wrap_boundary_is_replayed(rest,(cut-1) as nat,any);
        }
    }
}

pub open spec fn matches_partition<A>(children: Seq<Child<A>>, lengths: Seq<nat>) -> bool
    decreases lengths.len(),
{
    if lengths.len() == 0 { children.len() == 0 } else {
        let cut = lengths.first();
        cut > 0 && cached_boundaries_match(children,cut,false)
            && matches_partition(children.skip(cut as int),lengths.drop_first())
    }
}

pub open spec fn cached_partition<A>(children: Seq<Child<A>>) -> Seq<nat>
    decreases children.len(),
{
    let cut = line_len(children,false);
    if 0 < cut <= children.len() {
        seq![cut] + cached_partition(children.skip(cut as int))
    } else { Seq::empty() }
}

/// This separates parity of line membership from the earlier theorem on
/// callback order, which holds for any layout-consistent sequence of breaks.
pub proof fn cached_wrap_replays_sized_partition<A>(children: Seq<Child<A>>, lengths: Seq<nat>)
    requires matches_partition(children,lengths),
    ensures cached_partition(children) == lengths,
    decreases lengths.len(),
{
    if lengths.len() > 0 {
        let cut = lengths.first();
        recorded_wrap_boundary_is_replayed(children,cut,false);
        cached_wrap_replays_sized_partition(children.skip(cut as int),lengths.drop_first());
        assert(lengths =~= seq![cut] + lengths.drop_first());
    }
}

pub open spec fn wrapped<A>(children: Seq<Child<A>>) -> Seq<A>
    decreases children.len(),
{
    let n = line_len(children, false) as int;
    if 0 < n <= children.len() { walk(children.take(n)) + wrapped(children.skip(n)) }
    else { Seq::empty() }
}

pub proof fn wrapping_preserves_order<A>(children: Seq<Child<A>>)
    ensures wrapped(children) == walk(children),
    decreases children.len(),
{
    if children.len() > 0 {
        line_progress(children, false);
        let cut = line_len(children, false) as int;
        walk_split(children, cut);
        wrapping_preserves_order(children.skip(cut));
    }
}

// The four single-pass modes (free, stack, block and grid) share the same loop.
// Wrapping consumes a sequence of ranges using that loop with a stop sentinel.
pub open spec fn layout_order<A>(children: Seq<Child<A>>, wrapping: bool) -> Seq<A> {
    if wrapping { wrapped(children) } else { walk(children) }
}

pub struct Node {
    pub incarnation: nat,
    pub enabled: bool,
    pub free: bool,
    pub starts_line: bool,
    pub wrapping: bool,
    pub rule: Rule,
    pub mark: PlacementWork,
    pub previous: PlacementWork,
    pub changed_children: bool,
    pub coupled: bool,
    pub affects_siblings: bool,
    pub children: Seq<Node>,
}

impl Node {
    pub open spec fn key(self) -> Key { Key { incarnation: self.incarnation, phase: Phase::Placement } }

    pub open spec fn edge(self, i: int) -> PathEdge {
        PathEdge {
            previous: self.previous, children_changed: self.changed_children, coupled: self.coupled,
            children: Seq::new(self.children.len(), |j: int| (self.children[j].mark, self.children[j].affects_siblings)),
            index: i,
        }
    }
}

pub open spec fn trace_children(n: Node, path: Seq<PathEdge>, force: bool) -> Seq<Child<Step>>
    decreases n, 0nat,
{
    Seq::new(n.children.len(), |i: int| {
        let child = n.children[i];
        Child { enabled: child.enabled, free: child.free, marked_break: child.starts_line,
            output: if 0 <= i < n.children.len() {trace(child, path.push(n.edge(i)), force)} else {Seq::empty()} }
    })
}

pub open spec fn trace(n: Node, path: Seq<PathEdge>, force: bool) -> Seq<Step>
    decreases n, 1nat,
{
    if !n.enabled { Seq::empty() } else {
        seq![Step { key: n.key(), rule: n.rule, work: Work::Place { path, root_force: force, mark: n.mark } }]
            + layout_order(trace_children(n, path, force), n.wrapping)
    }
}

// Document order is defined independently from wrap boundaries and placement marks.
pub open spec fn flatten<A>(chunks: Seq<Seq<A>>) -> Seq<A>
    decreases chunks.len(),
{
    if chunks.len() == 0 { Seq::empty() } else { chunks.first() + flatten(chunks.drop_first()) }
}

pub open spec fn document_children(n: Node) -> Seq<Seq<Key>>
    decreases n, 0nat,
{
    Seq::new(n.children.len(), |i:int| if 0 <= i < n.children.len() {document(n.children[i])} else {Seq::empty()})
}

pub open spec fn document(n: Node) -> Seq<Key>
    decreases n, 1nat,
{
    if !n.enabled { Seq::empty() } else { seq![n.key()] + flatten(document_children(n)) }
}

pub open spec fn keys(steps: Seq<Step>, only_writes: bool) -> Seq<Key>
    decreases steps.len(),
{
    if !only_writes { visible_keys(steps) } else if steps.len() == 0 { Seq::empty() } else {
        let step = steps.last();
        let prior = keys(steps.drop_last(), true);
        if step.work is Place && writes(step.work) { prior.push(step.key) } else { prior }
    }
}

proof fn keys_append(before: Seq<Step>, tail: Seq<Step>, only: bool)
    ensures keys(before + tail, only) == keys(before, only) + keys(tail, only),
    decreases tail.len(),
{
    if tail.len() > 0 {
        keys_append(before, tail.drop_last(), only);
        assert((before + tail).drop_last() =~= before + tail.drop_last());
        assert((before + tail).last() == tail.last());
        assert(keys(before + tail, only) =~= keys(before, only) + keys(tail, only));
    }
}

proof fn child_keys(cells: Seq<Child<Step>>, order: Seq<Seq<Key>>, only: bool)
    requires cells.len() == order.len(), forall |i:int| 0 <= i < cells.len() ==>
        #[trigger] order[i] == if cells[i].enabled {keys(cells[i].output, only)} else {Seq::<Key>::empty()},
    ensures keys(walk(cells), only) == flatten(order),
    decreases cells.len(),
{
    if cells.len() > 0 {
        assert forall |i:int| 0 <= i < cells.drop_first().len() implies #[trigger] order.drop_first()[i] ==
            if cells.drop_first()[i].enabled { keys(cells.drop_first()[i].output, only) } else { Seq::<Key>::empty() } by {
            assert(order[i+1] == if cells[i+1].enabled {keys(cells[i+1].output, only)} else {Seq::<Key>::empty()});
        }
        child_keys(cells.drop_first(), order.drop_first(), only);
        keys_append(if cells.first().enabled { cells.first().output } else {Seq::empty()}, walk(cells.drop_first()), only);
    }
}

pub proof fn placement_keys_follow_document(n: Node, path: Seq<PathEdge>, force: bool)
    ensures visible_keys(trace(n, path, force)) == document(n),
    decreases n,
{
    if n.enabled {
        reveal_with_fuel(visible_keys, 2);
        let cells = trace_children(n, path, force);
        let order = document_children(n);
        assert forall |i:int| 0 <= i < cells.len() implies #[trigger] order[i] ==
            if cells[i].enabled {visible_keys(cells[i].output)} else {Seq::<Key>::empty()} by {
            placement_keys_follow_document(n.children[i], path.push(n.edge(i)), force);
        }
        child_keys(cells, order, false);
        wrapping_preserves_order(cells);
        let own = Step {key: n.key(), rule: n.rule, work: Work::Place {path, root_force:force, mark:n.mark}};
        keys_append(seq![own], layout_order(cells, n.wrapping), false);
        assert(seq![own].drop_last() =~= Seq::<Step>::empty());
        assert(seq![own].last() == own);
        assert(visible_keys(seq![own]) =~= seq![n.key()]);
        assert(trace(n, path, force) == seq![own] + layout_order(cells, n.wrapping));
        assert(document(n) == seq![n.key()] + flatten(order));
    }
}

}

verus! {

proof fn child_force_steps(cells: Seq<Child<Step>>, force: bool)
    requires forall |i:int, j:int| 0 <= i < cells.len() && 0 <= j < cells[i].output.len() ==>
        (#[trigger] cells[i].output[j]).work is Place && cells[i].output[j].work->Place_root_force == force,
    ensures forall |j:int| 0 <= j < walk(cells).len() ==> (#[trigger] walk(cells)[j]).work is Place &&
        walk(cells)[j].work->Place_root_force == force,
    decreases cells.len(),
{
    if cells.len() > 0 {
        let rest = cells.drop_first();
        assert forall |i:int,j:int| 0 <= i < rest.len() && 0 <= j < rest[i].output.len() implies
            (#[trigger] rest[i].output[j]).work is Place && rest[i].output[j].work->Place_root_force == force by {
            assert(cells[i+1].output[j].work is Place && cells[i+1].output[j].work->Place_root_force == force);
        }
        child_force_steps(rest, force);
        let head = if cells.first().enabled {cells.first().output} else {Seq::empty()};
        assert forall |j:int| 0 <= j < walk(cells).len() implies (#[trigger] walk(cells)[j]).work is Place &&
            walk(cells)[j].work->Place_root_force == force by {
            if j < head.len() {assert(head[j] == cells[0].output[j]);}
            else {assert(walk(cells)[j] == walk(rest)[j-head.len()]);}
        }
    }
}

pub proof fn trace_force_steps(n: Node, path: Seq<PathEdge>, force: bool)
    ensures forall |i:int| 0 <= i < trace(n,path,force).len() ==> (#[trigger] trace(n,path,force)[i]).work is Place &&
        trace(n,path,force)[i].work->Place_root_force == force,
    decreases n,
{
    if n.enabled {
        let cells = trace_children(n,path,force);
        assert forall |i:int,j:int| 0 <= i < cells.len() && 0 <= j < cells[i].output.len() implies
            (#[trigger] cells[i].output[j]).work is Place && cells[i].output[j].work->Place_root_force == force by {
            trace_force_steps(n.children[i],path.push(n.edge(i)),force);
        }
        child_force_steps(cells,force);
        wrapping_preserves_order(cells);
        assert forall |j:int| 0 <= j < trace(n,path,force).len() implies (#[trigger] trace(n,path,force)[j]).work is Place &&
            trace(n,path,force)[j].work->Place_root_force == force by {
            if j > 0 { assert(trace(n,path,force)[j] == walk(cells)[j-1]); }
        }
    }
}

// Snapshot of the planner's bottom-up parent/child marks. The path carried by
// each trace step is constructed from these sibling indices as the tree is read.
pub open spec fn consistent(n: Node) -> bool
    decreases n,
{
    forall |i:int| 0 <= i < n.children.len() ==> #[trigger] n.edge(i).parent_mark() == n.mark &&
        consistent(n.children[i])
}

pub open spec fn physical_children(n: Node, entered: bool, force: bool) -> Seq<Seq<Key>>
    decreases n, 0nat,
{
    Seq::new(n.children.len(), |i:int| if 0 <= i < n.children.len() {physical(n.children[i], entered, force)}
        else {Seq::empty()})
}

pub open spec fn physical(n: Node, entered: bool, force: bool) -> Seq<Key>
    decreases n, 1nat,
{
    if !entered || !n.enabled || !n.mark.visits(force) { Seq::empty() } else {
        let write = n.mark.writes(force);
        (if write {seq![n.key()]} else {Seq::empty()}) + flatten(physical_children(n,true,write))
    }
}

proof fn flattened_empty<A>(chunks: Seq<Seq<A>>)
    requires forall |i:int| 0 <= i < chunks.len() ==> (#[trigger] chunks[i]).len() == 0,
    ensures flatten(chunks).len() == 0,
    decreases chunks.len(),
{
    if chunks.len() > 0 {
        assert forall |i:int| 0 <= i < chunks.drop_first().len() implies (#[trigger] chunks.drop_first()[i]).len() == 0 by {
            assert(chunks[i+1].len() == 0);
        }
        flattened_empty(chunks.drop_first());
    }
}

// Compare the physical callbacks to the trace's retained-write predicate. A clean
// parent returns immediately in Place::place, a descendants-only parent writes
// nothing and visits its children, and a rewritten parent forces its subtree.
pub proof fn callbacks_follow_trace(n: Node, path: Seq<PathEdge>, force: bool)
    requires consistent(n),
    ensures ({
        let route = placement_route(path,force);
        keys(trace(n,path,force), true) == physical(n,route.visited,route.force)
    }),
    decreases n,
{
    if n.enabled {
        reveal_with_fuel(keys,2);
        let parent = placement_route(path,force);
        let enter = parent.visited && n.mark.visits(parent.force);
        let write = n.mark.writes(parent.force);
        let cells = trace_children(n,path,force);
        let order = physical_children(n,enter,write);
        assert forall |i:int| 0 <= i < cells.len() implies #[trigger] order[i] ==
            if cells[i].enabled {keys(cells[i].output,true)} else {Seq::<Key>::empty()} by {
            let child = n.children[i];
            let edge = n.edge(i);
            let child_path = path.push(edge);
            assert(child_path.drop_last() =~= path);
            assert(child_path.last() == edge);
            assert(edge.parent_mark() == n.mark);
            assert(placement_route(child_path,force) == Route {visited: enter && child.mark.visits(write), force:write});
            callbacks_follow_trace(child,child_path,force);
        }
        child_keys(cells,order,true);
        wrapping_preserves_order(cells);
        let own = Step {key:n.key(),rule:n.rule,work:Work::Place {path,root_force:force,mark:n.mark}};
        assert(seq![own].drop_last() =~= Seq::<Step>::empty());
        assert(seq![own].last() == own);
        let prefix: Seq<Key> = if parent.visited && write { seq![n.key()] } else { Seq::empty() };
        assert(keys(seq![own],true) =~= prefix);
        keys_append(seq![own],layout_order(cells,n.wrapping),true);
        if !enter {
            assert forall |i:int| 0 <= i < order.len() implies (#[trigger] order[i]).len() == 0 by {}
            flattened_empty(order);
        }
    }
}

}

use super::{Eval, retained_view::{Coverage, Frames, after, emitted_view, publish_frame, same_view_after_edits, valid_frames}};

verus! {

proof fn sizes_have_no_visible_keys(steps: Seq<Step>)
    requires forall |i:int| 0 <= i < steps.len() ==> (#[trigger] steps[i]).work is Size,
    ensures visible_keys(steps).len() == 0,
    decreases steps.len(),
{
    if steps.len() > 0 {
        assert forall |i:int| 0 <= i < steps.drop_last().len() implies (#[trigger] steps.drop_last()[i]).work is Size by {
            assert(steps[i].work is Size);
        }
        sizes_have_no_visible_keys(steps.drop_last());
    }
}

// Start the current frame from its adapter tree and previous host storage. Both
// views are compared in the new document order, including skipped callbacks.
pub proof fn retained_tree_matches_full(
    n: Node, sizes: Seq<Step>, previous: Frames, eval: Eval, coverage: Coverage, force: bool,
)
    requires
        forall |i:int| 0 <= i < sizes.len() ==> (#[trigger] sizes[i]).work is Size,
        valid_frames(previous.push(sizes + trace(n,Seq::empty(),force)),eval,coverage),
    ensures ({
        let frame = sizes + trace(n,Seq::empty(),force);
        let host = after(previous.push(frame),eval).1;
        let full = publish_frame(frame,Map::empty(),Map::empty(),eval,true);
        emitted_view(document(n),host) == emitted_view(document(n),full)
    }),
{
    let placed = trace(n,Seq::empty(),force);
    let frame = sizes + placed;
    let history = previous.push(frame);
    sizes_have_no_visible_keys(sizes);
    keys_append(sizes,placed,false);
    placement_keys_follow_document(n,Seq::empty(),force);
    assert(history.last() == frame);
    same_view_after_edits(history,eval,coverage);
}

}
