//! Pearce–Kelly batch ordering for an existing directed acyclic graph.
//!
//! The caller owns adjacency storage and supplies the graph after deleting old
//! constraints and applying the complete batch of added edges. Vertex IDs are
//! dense and remain stable across batches. A failed repair leaves the order
//! intact, so the caller can discard or rebuild the rejected graph.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RepairError {
    InvalidOrder { vertex: usize, position: usize },
    WrongVertexCount { expected: usize, actual: usize },
    UnknownVertex(usize),
    OrderViolation { from: usize, to: usize },
    Cycle,
    Allocation,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct RepairStats {
    pub backward_edges: usize,
    pub regions: usize,
    pub interval_vertices: usize,
    pub discovered_vertices: usize,
    pub examined_edges: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TopologicalOrder {
    order: Vec<usize>,
    positions: Vec<usize>,
}

#[derive(Debug, Clone, Copy)]
struct Interval {
    first: usize,
    last: usize,
}

#[derive(Debug, Clone, Copy)]
struct Region {
    interval: Interval,
    replacement_start: usize,
}

#[derive(Debug, Clone, Copy)]
struct WalkFrame {
    vertex: usize,
    next_edge: usize,
}

#[derive(Debug, Clone, Copy)]
struct Shift {
    vertex: usize,
    destination: usize,
}

#[derive(Debug, Default)]
pub struct RepairScratch {
    backward: Vec<Interval>,
    regions: Vec<Region>,
    replacement: Vec<usize>,
    walk: Vec<WalkFrame>,
    shifts: Vec<Shift>,
    marks: Vec<u32>,
    generation: u32,
}

impl TopologicalOrder {
    /// Install a permutation of `0..order.len()`. Call [Self::validate_graph]
    /// to check it against initial adjacency that does not already have a proof.
    pub fn new(order: Vec<usize>) -> Result<Self, RepairError> {
        let mut positions = Vec::new();
        positions
            .try_reserve_exact(order.len())
            .map_err(|_| RepairError::Allocation)?;
        positions.resize(order.len(), usize::MAX);
        for (position, &vertex) in order.iter().enumerate() {
            let Some(entry) = positions.get_mut(vertex) else {
                return Err(RepairError::InvalidOrder { vertex, position });
            };
            if *entry != usize::MAX {
                return Err(RepairError::InvalidOrder { vertex, position });
            }
            *entry = position;
        }
        Ok(Self { order, positions })
    }

    pub fn order(&self) -> &[usize] {
        &self.order
    }

    pub fn positions(&self) -> &[usize] {
        &self.positions
    }

    /// Check every edge against the current order in linear time.
    pub fn validate_graph(&self, outgoing: &[impl AsRef<[usize]>]) -> Result<(), RepairError> {
        self.check_vertex_count(outgoing.len())?;
        for (position, &from) in self.order.iter().enumerate() {
            for &to in outgoing[from].as_ref() {
                if self.position(to)? <= position {
                    return Err(RepairError::OrderViolation { from, to });
                }
            }
        }
        Ok(())
    }

    /// Repair the order after a batch of changes.
    ///
    /// `outgoing` must contain the complete post-edit graph. Its unreported
    /// edges must respect the old order, and every reported edge must exist
    /// in this graph. Duplicate reports are harmless. Out-of-range endpoints,
    /// self-loops and cycles encountered by the repair are errors.
    ///
    /// A forward-only batch checks only its endpoints. For a backward batch,
    /// searches visit the graph through bounded, merged old-order intervals.
    /// Ties use the old head rank and then the supplied adjacency order.
    pub fn repair(
        &mut self,
        outgoing: &[impl AsRef<[usize]>],
        additions: &[(usize, usize)],
        scratch: &mut RepairScratch,
    ) -> Result<RepairStats, RepairError> {
        self.check_vertex_count(outgoing.len())?;
        scratch.clear_batch();
        for &(from, to) in additions {
            let last = self.position(from)?;
            let first = self.position(to)?;
            if last == first {
                return Err(RepairError::Cycle);
            }
            if first < last {
                push(&mut scratch.backward, Interval { first, last })?;
            }
        }

        let mut stats = RepairStats {
            backward_edges: scratch.backward.len(),
            ..RepairStats::default()
        };
        if scratch.backward.is_empty() {
            return Ok(stats);
        }

        scratch.begin_search(self.order.len())?;
        scratch.backward.sort_unstable_by(|left, right| {
            right
                .last
                .cmp(&left.last)
                .then(left.first.cmp(&right.first))
        });

        // Use old positions throughout discovery, including for intervals
        // considered after another interval has already prepared a shift.
        let mut start = 0;
        while start < scratch.backward.len() {
            let mut interval = scratch.backward[start];
            let mut end = start + 1;
            while let Some(next) = scratch.backward.get(end) {
                if next.last < interval.first {
                    break;
                }
                interval.first = interval.first.min(next.first);
                end += 1;
            }
            for index in start..end {
                let edge = scratch.backward[index];
                self.discover(outgoing, interval.first, edge, scratch, &mut stats)?;
            }
            self.stage_region(interval, scratch, &mut stats)?;
            start = end;
        }

        // All allocation and rejection are over before the order is changed.
        for region in &scratch.regions {
            let start = region.replacement_start;
            let order = &mut self.order[region.interval.first..=region.interval.last];
            order.copy_from_slice(&scratch.replacement[start..start + order.len()]);
            for (offset, &vertex) in order.iter().enumerate() {
                self.positions[vertex] = region.interval.first + offset;
            }
        }
        Ok(stats)
    }

    fn check_vertex_count(&self, actual: usize) -> Result<(), RepairError> {
        if actual != self.order.len() {
            return Err(RepairError::WrongVertexCount {
                expected: self.order.len(),
                actual,
            });
        }
        Ok(())
    }

    fn position(&self, vertex: usize) -> Result<usize, RepairError> {
        self.positions
            .get(vertex)
            .copied()
            .ok_or(RepairError::UnknownVertex(vertex))
    }

    // Paper algorithm DISCOVER. A vertex first seen from the highest tail
    // that reaches it is assigned that destination. Postorder lets SHIFT
    // emit vertices assigned to the same destination in reverse postorder.
    fn discover(
        &self,
        outgoing: &[impl AsRef<[usize]>],
        lower: usize,
        edge: Interval,
        scratch: &mut RepairScratch,
        stats: &mut RepairStats,
    ) -> Result<(), RepairError> {
        let head = self.order[edge.first];
        if scratch.seen(head) {
            return Ok(());
        }
        scratch.visit(head)?;
        while let Some(frame) = scratch.walk.last_mut() {
            let from = frame.vertex;
            if let Some(&to) = outgoing[from].as_ref().get(frame.next_edge) {
                frame.next_edge += 1;
                stats.examined_edges = stats.examined_edges.saturating_add(1);
                let rank = self.position(to)?;
                if rank == edge.last || scratch.active(to) {
                    // The destination is excluded by the search bound. An
                    // edge reaching it closes a cycle through the seed edge.
                    return Err(RepairError::Cycle);
                }
                if rank < lower {
                    return Err(RepairError::OrderViolation { from, to });
                }
                if rank < edge.last && !scratch.seen(to) {
                    scratch.visit(to)?;
                }
            } else {
                scratch.walk.pop();
                scratch.marks[from] = scratch.generation;
                push(
                    &mut scratch.shifts,
                    Shift {
                        vertex: from,
                        destination: edge.last,
                    },
                )?;
                stats.discovered_vertices += 1;
            }
        }
        Ok(())
    }

    // Paper algorithm SHIFT, staged in a separate contiguous buffer. Skipping
    // vacant rows and inserting each group at its old destination is equivalent
    // to tracking holes while shifting the interval in place.
    fn stage_region(
        &self,
        interval: Interval,
        scratch: &mut RepairScratch,
        stats: &mut RepairStats,
    ) -> Result<(), RepairError> {
        let width = interval.last - interval.first + 1;
        let start = scratch.replacement.len();
        scratch
            .replacement
            .try_reserve(width)
            .map_err(|_| RepairError::Allocation)?;
        for rank in interval.first..=interval.last {
            let vertex = self.order[rank];
            if !scratch.seen(vertex) {
                scratch.replacement.push(vertex);
            }
            while let Some(shift) = scratch.shifts.last().copied() {
                if shift.destination != rank {
                    break;
                }
                if scratch.seen(vertex) {
                    return Err(RepairError::OrderViolation {
                        from: vertex,
                        to: shift.vertex,
                    });
                }
                scratch.replacement.push(shift.vertex);
                scratch.shifts.pop();
            }
        }
        if let Some(shift) = scratch.shifts.last() {
            return Err(RepairError::OrderViolation {
                from: self.order[shift.destination],
                to: shift.vertex,
            });
        }
        push(
            &mut scratch.regions,
            Region {
                interval,
                replacement_start: start,
            },
        )?;
        stats.regions += 1;
        stats.interval_vertices += width;
        Ok(())
    }
}

impl RepairScratch {
    fn clear_batch(&mut self) {
        self.backward.clear();
        self.regions.clear();
        self.replacement.clear();
        self.walk.clear();
        self.shifts.clear();
    }

    fn begin_search(&mut self, vertices: usize) -> Result<(), RepairError> {
        if vertices > self.marks.len() {
            self.marks
                .try_reserve(vertices - self.marks.len())
                .map_err(|_| RepairError::Allocation)?;
            self.marks.resize(vertices, 0);
        }
        self.generation = self.generation.wrapping_add(2);
        if self.generation == 0 {
            self.marks.fill(0);
            self.generation = 2;
        }
        Ok(())
    }

    fn seen(&self, vertex: usize) -> bool {
        self.marks[vertex] & !1 == self.generation
    }

    fn active(&self, vertex: usize) -> bool {
        self.marks[vertex] == self.generation | 1
    }

    fn visit(&mut self, vertex: usize) -> Result<(), RepairError> {
        push(
            &mut self.walk,
            WalkFrame {
                vertex,
                next_edge: 0,
            },
        )?;
        self.marks[vertex] = self.generation | 1;
        Ok(())
    }
}

fn push<T>(buffer: &mut Vec<T>, value: T) -> Result<(), RepairError> {
    buffer.try_reserve(1).map_err(|_| RepairError::Allocation)?;
    buffer.push(value);
    Ok(())
}
