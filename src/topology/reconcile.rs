//! Project retained pixel boxes onto the live, possibly edited tree.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum Projection<C> {
    Retain(C),
    RefreshChildren(C),
    Rebuild,
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns classify(fixed, has_children), no_unwind))]
pub(crate) fn classify<C: Copy>(fixed: Option<C>, has_children: bool) -> Projection<C> {
    match fixed {
        Some(record) if has_children => Projection::RefreshChildren(record),
        Some(record) => Projection::Retain(record),
        None => Projection::Rebuild,
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait Model {
    type Id: Copy;
    type Cache: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait Model {
    type Id: Copy;
    type Cache: Copy;

    spec fn live(&self, node: Self::Id) -> bool;
    spec fn preorder(&self, root: Self::Id) -> Seq<Self::Id>;
    spec fn first(&self, node: Self::Id) -> Option<Self::Id>;
    spec fn disabled(&self, node: Self::Id) -> bool;
    spec fn fixed_box(&self, node: Self::Id) -> Option<Self::Cache>;
    spec fn projection_log(&self) -> Seq<(Self::Id, Projection<Self::Cache>)>;
}

pub(crate) open spec fn entry<I>(nodes: Seq<I>, position: int) -> Option<I> {
    if 0 <= position < nodes.len() { Some(nodes[position]) } else { None }
}

pub(crate) open spec fn all_live<S: Model + ?Sized>(source: &S, nodes: Seq<S::Id>) -> bool {
    forall |i: int| 0 <= i < nodes.len() ==> source.live(#[trigger] nodes[i])
}

fn origin() -> (position: Ghost<int>)
    ensures position@ == 0,
    no_unwind
{
    Ghost(0int)
}

fn step(position: Ghost<int>) -> (next: Ghost<int>)
    ensures next@ == position@ + 1,
    no_unwind
{
    Ghost(position@ + 1)
}

fn save_log<S: Model + ?Sized>(source: &S) -> (log: Ghost<Seq<(S::Id, Projection<S::Cache>)>>)
    ensures log@ == source.projection_log(),
    no_unwind
{
    Ghost(source.projection_log())
}
}

/// The successor reads only links. Updating a cache leaves the tree and all
/// other nodes' projection inputs unchanged.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: Model {
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        requires self.live(node),
        ensures result == (self.first(node), self.disabled(node), self.fixed_box(node)),
        no_unwind
    ))]
    fn inspect(&self, node: Self::Id) -> (Option<Self::Id>, bool, Option<Self::Cache>);

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).live(node),
        ensures final(self).projection_log() == old(self).projection_log().push((node, projection)),
            forall |id: Self::Id| #[trigger] final(self).live(id) == old(self).live(id),
            forall |root: Self::Id| #[trigger] final(self).preorder(root) == old(self).preorder(root),
            forall |id: Self::Id| #[trigger] final(self).first(id) == old(self).first(id)
                && final(self).disabled(id) == old(self).disabled(id),
            forall |id: Self::Id| id != node ==>
                #[trigger] final(self).fixed_box(id) == old(self).fixed_box(id),
        no_unwind
    ))]
    fn apply(&mut self, node: Self::Id, projection: Projection<Self::Cache>);

    #[cfg_attr(verus_keep_ghost, verus_spec(next =>
        requires self.live(root), self.live(node), entry(self.preorder(root), position@) == Some(node),
            child == (if self.disabled(node) { None } else { self.first(node) }),
        ensures next == entry(self.preorder(root), position@ + 1),
        no_unwind
    ))]
    fn successor(
        &self, root: Self::Id, node: Self::Id, child: Option<Self::Id>,
        #[cfg(verus_keep_ghost)] position: Ghost<int>,
    ) -> Option<Self::Id>;
}

/// Visit every enabled link in preorder, retaining provably fixed pixel
/// boxes and marking any uncertain sizing state for rebuilding.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires
        old(source).preorder(root).len() > 0,
        old(source).preorder(root)[0] == root,
        all_live(old(source), old(source).preorder(root)),
        old(source).preorder(root).no_duplicates(),
    ensures ({
        let before = old(source).projection_log();
        let nodes = old(source).preorder(root);
        let after = final(source).projection_log();
        &&& after.len() == before.len() + nodes.len()
        &&& after.take(before.len() as int) == before
        &&& forall |i: int| 0 <= i < nodes.len() ==> {
            let id = nodes[i];
            #[trigger] after[before.len() + i]
                == (id, classify(old(source).fixed_box(id), old(source).first(id).is_some()))
        }
    }),
    no_unwind
))]
pub(crate) fn project<S: Access + ?Sized>(source: &mut S, root: S::Id) {
    let mut next = Some(root);
    #[cfg(verus_keep_ghost)]
    let mut position = origin();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            0 <= position@ <= old(source).preorder(root).len(),
            next == entry(old(source).preorder(root), position@),
            source.preorder(root) == old(source).preorder(root),
            old(source).preorder(root).no_duplicates(),
            all_live(source, old(source).preorder(root)),
            source.live(root),
            forall |id: S::Id| #[trigger] source.first(id) == old(source).first(id)
                && source.disabled(id) == old(source).disabled(id),
            forall |i: int| position@ <= i < old(source).preorder(root).len() ==>
                #[trigger] source.fixed_box(old(source).preorder(root)[i])
                    == old(source).fixed_box(old(source).preorder(root)[i]),
            source.projection_log().len() == old(source).projection_log().len() + position@,
            source.projection_log().take(old(source).projection_log().len() as int) == old(source).projection_log(),
            forall |i: int| 0 <= i < position@ ==> {
                let id = old(source).preorder(root)[i];
                #[trigger] source.projection_log()[old(source).projection_log().len() + i]
                    == (id, classify(old(source).fixed_box(id), old(source).first(id).is_some()))
            },
        decreases old(source).preorder(root).len() - position@,
    ))]
    loop {
        let Some(node) = next else {
            #[cfg(verus_keep_ghost)]
            proof! { assert(position@ == old(source).preorder(root).len()); }
            return;
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            let nodes = old(source).preorder(root);
            assert(node == nodes[position@]);
            assert(source.live(node));
            assert(source.live(root));
            assert(source.fixed_box(node) == old(source).fixed_box(node));
        }
        let (first, disabled, fixed) = source.inspect(node);
        let projection = classify(fixed, first.is_some());
        #[cfg(verus_keep_ghost)]
        let prior = save_log(source);
        source.apply(node, projection);
        #[cfg(verus_keep_ghost)]
        proof! {
            let old_len = old(source).projection_log().len() as int;
            let nodes = old(source).preorder(root);
            let expected = (node, classify(old(source).fixed_box(node), old(source).first(node).is_some()));
            assert(source.projection_log() == prior@.push(expected));
            assert(source.projection_log().take(old_len) =~= old(source).projection_log());
            assert forall |i: int| position@ < i < nodes.len()
                implies #[trigger] source.fixed_box(nodes[i]) == old(source).fixed_box(nodes[i]) by {
                assert(nodes[i] != nodes[position@]);
            }
            assert forall |i: int| 0 <= i <= position@ implies
                #[trigger] source.projection_log()[old_len + i]
                    == (nodes[i], classify(old(source).fixed_box(nodes[i]), old(source).first(nodes[i]).is_some()))
                by {
                    if i == position@ {
                        assert(source.projection_log()[old_len + i] == expected);
                    } else {
                        assert(source.projection_log()[old_len + i] == prior@[old_len + i]);
                    }
                }
        }
        let child = if disabled { None } else { first };
        next = source.successor(
            root, node, child,
            #[cfg(verus_keep_ghost)]
            position,
        );
        #[cfg(verus_keep_ghost)]
        {
            position = step(position);
        }
    }
}
