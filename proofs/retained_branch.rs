//! Verify every accepted node of the actual retained fixed-size branch walk.
use vstd::prelude::*;
#[path = "../src/retained_branch.rs"]
pub(crate) mod kernel;
use kernel::CachedBranch;

verus! {

pub struct Links<I> {
    pub status: CachedBranch,
    pub first: Option<I>,
    pub next: Option<I>,
}

pub struct Branch<I> {
    pub id: I,
    pub status: CachedBranch,
    pub children: Seq<Branch<I>>,
}

pub closed spec fn at<I>(trees: Seq<Branch<I>>, i: int) -> Option<I> {
    if 0 <= i < trees.len() { Some(trees[i].id) } else { None }
}

pub proof fn sibling_cursor<I>(trees: Seq<Branch<I>>, i: int)
    requires 0 <= i <= trees.len(),
    ensures at(trees,i).is_some() == (i < trees.len()),
        i < trees.len() ==> at(trees,i) == Some(trees[i].id),
{
    reveal(at);
}
/// Adapter links describe a finite tree. Only Ready nodes read child links.
/// The statically smaller child witness proves termination without a worklist.
pub closed spec fn rooted<I>(map: Map<I,Links<I>>, t: Branch<I>) -> bool
    decreases t, 0nat,
{
    &&& map.contains_key(t.id)
    &&& map[t.id].status == t.status
    &&& t.status is Ready ==> ({
        &&& map[t.id].first == at(t.children,0)
        &&& rooted_children(map,t.children,0)
    })
}

pub closed spec fn rooted_children<I>(map: Map<I,Links<I>>, trees: Seq<Branch<I>>, i: int) -> bool
    decreases trees, trees.len() - i,
{
    i == trees.len() || (0 <= i < trees.len() && {
        let child = trees[i];
        &&& rooted(map,child)
        &&& map[child.id].next == at(trees,i+1)
        &&& rooted_children(map,trees,i+1)
    })
}

pub closed spec fn ready_prefix<I>(trees: Seq<Branch<I>>, end: nat) -> bool
    decreases trees, end,
{
    end == 0 || (ready_prefix(trees,(end-1) as nat) && (end <= trees.len() && all_ready(trees[end-1])))
}

pub open spec fn all_ready<I>(t: Branch<I>) -> bool
    decreases t, 0nat,
{
    match t.status {
        CachedBranch::Ready => ready_prefix(t.children,t.children.len()),
        CachedBranch::Hidden => true,
        CachedBranch::Reject => false,
    }
}

pub closed spec fn ready_within<I>(tree: Branch<I>, depth: nat) -> bool
    decreases depth, 0nat,
{
    depth != 0 && match tree.status {
        CachedBranch::Ready => children_ready_within(tree.children, (depth - 1) as nat, tree.children.len()),
        CachedBranch::Hidden => true,
        CachedBranch::Reject => false,
    }
}

closed spec fn children_ready_within<I>(children: Seq<Branch<I>>, depth: nat, end: nat) -> bool
    decreases depth, end + 1,
{
    end == 0 || (end <= children.len()
        && ready_within(children[end - 1], depth)
        && children_ready_within(children, depth, (end - 1) as nat))
}

pub proof fn ready_depth_facts<I>(tree: Branch<I>, depth: nat)
    requires ready_within(tree, depth),
    ensures depth > 0, !(tree.status is Reject),
{
    reveal(ready_within);
}

pub proof fn child_within<I>(tree: Branch<I>, depth: nat, i: int)
    requires ready_within(tree, depth), tree.status is Ready, 0 <= i < tree.children.len(),
    ensures ready_within(tree.children[i], (depth - 1) as nat),
{
    reveal(ready_within);
    child_prefix_within(tree.children, (depth - 1) as nat, tree.children.len(), i);
}

proof fn child_prefix_within<I>(children: Seq<Branch<I>>, depth: nat, end: nat, i: int)
    requires 0 <= i < end, children_ready_within(children, depth, end),
    ensures ready_within(children[i], depth),
    decreases end,
{
    reveal(children_ready_within);
    if i < end - 1 {
        child_prefix_within(children, depth, (end - 1) as nat, i);
    }
}

pub closed spec fn visible_prefix<I>(trees: Seq<Branch<I>>, end: nat) -> Seq<I>
    decreases trees, end,
{
    if end == 0 || end > trees.len() { Seq::empty() }
    else { visible_prefix(trees,(end-1) as nat) + visible(trees[end-1]) }
}

pub open spec fn visible<I>(t: Branch<I>) -> Seq<I>
    decreases t, 0nat,
{
    if t.status is Ready { seq![t.id] + visible_prefix(t.children,t.children.len()) } else { Seq::empty() }
}

pub proof fn root_facts<I>(map: Map<I,Links<I>>, t: Branch<I>)
    requires rooted(map,t),
    ensures map.contains_key(t.id), map[t.id].status == t.status,
        t.status is Ready ==> map[t.id].first == at(t.children,0),
        t.status is Ready ==> rooted_children(map,t.children,0),
{
    reveal(rooted);
}

pub proof fn child_facts<I>(map: Map<I,Links<I>>, trees: Seq<Branch<I>>, i: int)
    requires rooted_children(map,trees,i), 0 <= i < trees.len(),
    ensures rooted(map,trees[i]), map.contains_key(trees[i].id),
        map[trees[i].id].next == at(trees,i+1),
        rooted_children(map,trees,i+1),
{
    reveal(rooted_children);
    root_facts(map,trees[i]);
}

pub proof fn empty_prefix<I>(trees: Seq<Branch<I>>)
    ensures ready_prefix(trees,0), visible_prefix(trees,0) == Seq::<I>::empty(),
{
    reveal(ready_prefix);
    reveal(visible_prefix);
}

pub proof fn accept_child<I>(trees: Seq<Branch<I>>, current: int)
    requires 0 <= current < trees.len(), ready_prefix(trees, current as nat), all_ready(trees[current]),
    ensures ready_prefix(trees, (current + 1) as nat),
        visible_prefix(trees, (current + 1) as nat) == visible_prefix(trees, current as nat) + visible(trees[current]),
{
    reveal(ready_prefix);
    reveal(visible_prefix);
}

pub proof fn reject_at<I>(trees: Seq<Branch<I>>, end: nat, bad: int)
    requires 0 <= bad < end <= trees.len(), !all_ready(trees[bad]),
    ensures !ready_prefix(trees,end),
    decreases end,
{
    reveal(ready_prefix);
    if bad < end - 1 {
        reject_at(trees,(end-1) as nat,bad);
    }
}

}
