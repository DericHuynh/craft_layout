use super::NodeKey;
pub use super::structural_guard::TreeError;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::Arc;

#[derive(Debug)]
pub(super) struct TreeIdentity {
    pub(super) root: NodeKey,
}

/// An opaque handle to a particular node in one layout tree.
///
/// Removing a node invalidates all of its handles. A cloned tree has
/// its own handles, including for nodes shared with the original snapshot.
#[derive(Clone)]
pub struct NodeId {
    owner: Arc<TreeIdentity>,
    key: NodeKey,
    incarnation: u64,
}

impl NodeId {
    pub(super) fn new(owner: &Arc<TreeIdentity>, key: NodeKey, incarnation: u64) -> Self {
        Self { owner: Arc::clone(owner), key, incarnation }
    }

    pub(super) fn belongs_to(&self, owner: &Arc<TreeIdentity>) -> bool {
        Arc::ptr_eq(&self.owner, owner)
    }

    pub(crate) fn key(&self) -> NodeKey { self.key }

    pub(super) fn incarnation(&self) -> u64 { self.incarnation }

    /// Use this node as a child when it is structurally eligible.
    ///
    /// The root has no child handle. A handle can still go stale, so edit
    /// operations separately validate that the child remains in the tree.
    pub fn as_child(&self) -> Option<ChildId> {
        (self.key != self.owner.root).then(|| ChildId(self.clone()))
    }
}

impl PartialEq for NodeId {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key && self.incarnation == other.incarnation && self.belongs_to(&other.owner)
    }
}

impl Eq for NodeId {}

impl Hash for NodeId {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(Arc::as_ptr(&self.owner), state);
        self.key.hash(state);
        self.incarnation.hash(state);
    }
}

impl fmt::Debug for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("NodeId").field("key", &self.key)
            .field("incarnation", &self.incarnation).finish_non_exhaustive()
    }
}

/// A handle to a non-root node that can be moved or removed.
///
/// ```compile_fail
/// use keru_layout::LayoutTree;
///
/// let mut tree = LayoutTree::<()>::new();
/// let root = tree.root();
/// tree.remove(&root);
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ChildId(pub(super) NodeId);

impl Deref for ChildId {
    type Target = NodeId;

    fn deref(&self) -> &NodeId { &self.0 }
}

impl From<ChildId> for NodeId {
    fn from(child: ChildId) -> Self { child.0 }
}

/// Where to place a node when moving it.
#[derive(Debug, Clone, Copy)]
pub enum Destination<'a> {
    /// Append to the given parent's children.
    LastChildOf(&'a NodeId),
    /// Insert just before this sibling under its current parent.
    Before(&'a ChildId),
}

impl fmt::Display for TreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::ForeignNode => "the node belongs to another layout tree",
            Self::StaleNode => "the node was removed",
            Self::WouldCreateCycle => "the move would create a cycle",
            Self::BeforeSelf => "a node cannot be moved before itself",
            Self::LayoutUnavailable => "the node has no published rectangle",
            Self::Capacity => "layout tree capacity could not be reserved",
        })
    }
}

impl std::error::Error for TreeError {}
