//! Retain the identity permutation implicitly until an edge moves a slot.

use crate::batch_order::{Adjacency, RepairError, RepairScratch, RepairStats, TopologicalOrder};

#[derive(Debug, Default)]
pub(super) struct Order {
    vertices: usize,
    ranked: Option<TopologicalOrder>,
}

impl Order {
    pub(super) fn len(&self) -> usize {
        self.vertices
    }

    /// Packing interprets an empty rank slice as the identity permutation.
    pub(super) fn positions(&self) -> &[usize] {
        self.ranked
            .as_ref()
            .map_or(&[], TopologicalOrder::positions)
    }

    pub(super) fn suffix(&self, start: usize) -> impl Iterator<Item = usize> + '_ {
        let (identity, order) = match &self.ranked {
            Some(ranked) => (0..0, &ranked.order()[start..]),
            None => (start..self.vertices, &[][..]),
        };
        identity.chain(order.iter().copied())
    }

    pub(super) fn repair_with_appended(
        &mut self,
        graph: &impl Adjacency,
        backward: &[(usize, usize)],
        scratch: &mut RepairScratch,
    ) -> Result<RepairStats, RepairError> {
        let total = graph.vertex_count();
        if total < self.vertices {
            return Err(RepairError::WrongVertexCount {
                expected: self.vertices,
                actual: total,
            });
        }
        let stats = match &mut self.ranked {
            Some(order) => order.repair_with_appended(graph, backward, scratch)?,
            // Capture has already checked every endpoint and collected every
            // edge whose old tail does not precede its old head.
            None if backward.is_empty() => RepairStats::default(),
            None => {
                let mut order = TopologicalOrder::default();
                let stats = order.repair_with_appended(graph, backward, scratch)?;
                self.ranked = Some(order);
                stats
            }
        };
        self.vertices = total;
        Ok(stats)
    }
}
