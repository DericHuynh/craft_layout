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

/// Read outgoing edges from either packed rows or an adjacency list.
pub trait Adjacency {
    fn vertex_count(&self) -> usize;
    fn successors(&self, vertex: usize) -> &[usize];
}

impl<R: AsRef<[usize]>> Adjacency for [R] {
    fn vertex_count(&self) -> usize {
        self.len()
    }

    fn successors(&self, vertex: usize) -> &[usize] {
        self[vertex].as_ref()
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
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
    moved: Vec<usize>,
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
        self.validate(outgoing)
    }

    pub fn validate(&self, outgoing: &(impl Adjacency + ?Sized)) -> Result<(), RepairError> {
        self.check_vertex_count(outgoing.vertex_count())?;
        for (position, &from) in self.order.iter().enumerate() {
            for &to in outgoing.successors(from) {
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
        self.repair_graph::<false>(outgoing, additions, scratch)
    }

    /// Extend the old permutation with isolated slots before applying a batch.
    /// A rejected batch restores both maps to their pre-edit lengths.
    pub fn repair_with_appended(
        &mut self,
        outgoing: &(impl Adjacency + ?Sized),
        additions: &[(usize, usize)],
        scratch: &mut RepairScratch,
    ) -> Result<RepairStats, RepairError> {
        let before = self.order.len();
        let total = outgoing.vertex_count();
        let added = total
            .checked_sub(before)
            .ok_or(RepairError::WrongVertexCount {
                expected: before,
                actual: total,
            })?;
        self.order
            .try_reserve(added)
            .map_err(|_| RepairError::Allocation)?;
        self.positions
            .try_reserve(added)
            .map_err(|_| RepairError::Allocation)?;
        self.order.extend(before..total);
        self.positions.extend(before..total);
        let result = if before == 0 {
            self.repair_graph::<true>(outgoing, additions, scratch)
        } else {
            self.repair_graph::<false>(outgoing, additions, scratch)
        };
        if result.is_err() {
            self.order.truncate(before);
            self.positions.truncate(before);
        }
        result
    }

    fn repair_graph<const IDENTITY: bool>(
        &mut self,
        outgoing: &(impl Adjacency + ?Sized),
        additions: &[(usize, usize)],
        scratch: &mut RepairScratch,
    ) -> Result<RepairStats, RepairError> {
        self.check_vertex_count(outgoing.vertex_count())?;
        scratch.clear_batch();
        let mut ascending = true;
        for &(from, to) in additions {
            let last = self.old_position::<IDENTITY>(from)?;
            let first = self.old_position::<IDENTITY>(to)?;
            if last == first {
                return Err(RepairError::Cycle);
            }
            if first < last {
                ascending &= scratch.backward.last().is_none_or(|edge| edge.last <= last);
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
        if ascending {
            // Graph capture emits adjacent groups in increasing old tail rank
            // on the initial identity order. Sort only the heads in each group.
            let mut rows = scratch.backward.as_mut_slice();
            while let Some(first) = rows.first() {
                let tail = first.last;
                let length = rows.iter().take_while(|edge| edge.last == tail).count();
                let (group, rest) = rows.split_at_mut(length);
                if group.len() > 1 {
                    group.sort_unstable_by(|left, right| right.first.cmp(&left.first));
                }
                rows = rest;
            }
        } else {
            scratch.backward.sort_unstable_by(|left, right| {
                left.last
                    .cmp(&right.last)
                    .then(right.first.cmp(&left.first))
            });
        }

        // Visit decreasing old tail rank and increasing head rank on ties.
        // No region publishes before every bounded search has succeeded.
        let mut end = scratch.backward.len();
        while end > 0 {
            let mut start = end - 1;
            let mut interval = scratch.backward[start];
            while start > 0 {
                let next = scratch.backward[start - 1];
                if next.last < interval.first {
                    break;
                }
                interval.first = interval.first.min(next.first);
                start -= 1;
            }
            for index in (start..end).rev() {
                let edge = scratch.backward[index];
                self.discover::<IDENTITY>(outgoing, interval.first, edge, scratch, &mut stats)?;
            }
            self.stage_region::<IDENTITY>(interval, scratch, &mut stats)?;
            end = start;
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

    #[inline(always)]
    fn old_position<const IDENTITY: bool>(&self, vertex: usize) -> Result<usize, RepairError> {
        if IDENTITY {
            if vertex < self.order.len() {
                Ok(vertex)
            } else {
                Err(RepairError::UnknownVertex(vertex))
            }
        } else {
            self.position(vertex)
        }
    }

    // Paper algorithm DISCOVER. A vertex first seen from the highest tail
    // that reaches it is assigned that destination. Postorder lets SHIFT
    // emit vertices assigned to the same destination in reverse postorder.
    fn discover<const IDENTITY: bool>(
        &self,
        outgoing: &(impl Adjacency + ?Sized),
        lower: usize,
        edge: Interval,
        scratch: &mut RepairScratch,
        stats: &mut RepairStats,
    ) -> Result<(), RepairError> {
        let head = if IDENTITY {
            edge.first
        } else {
            self.order[edge.first]
        };
        if scratch.seen(head) {
            return Ok(());
        }
        scratch.visit(head)?;
        'resume: while let Some(frame) = scratch.walk.last_mut() {
            let from = frame.vertex;
            let outgoing = outgoing.successors(from);
            let remaining = outgoing.get(frame.next_edge..).unwrap_or_default();
            for &to in remaining {
                frame.next_edge += 1;
                stats.examined_edges = stats.examined_edges.saturating_add(1);
                let rank = self.old_position::<IDENTITY>(to)?;
                let mark = scratch.marks[to];
                if rank == edge.last || mark == scratch.generation | 1 {
                    // The destination is excluded by the search bound. An
                    // edge reaching it closes a cycle through the seed edge.
                    return Err(RepairError::Cycle);
                }
                if rank < lower {
                    return Err(RepairError::OrderViolation { from, to });
                }
                if rank < edge.last && mark & !1 != scratch.generation {
                    scratch.visit(to)?;
                    continue 'resume;
                }
            }
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
        Ok(())
    }

    // Paper algorithm SHIFT, staged in a separate contiguous buffer. Skipping
    // vacant rows and inserting each group at its old destination is equivalent
    // to tracking holes while shifting the interval in place.
    fn stage_region<const IDENTITY: bool>(
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
        if IDENTITY && scratch.shifts.len() < width / 8 {
            scratch.stage_sparse_identity(interval.first, interval.first + width)?;
        } else {
            for rank in interval.first..=interval.last {
                let vertex = if IDENTITY { rank } else { self.order[rank] };
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

    // A wide interval may contain only a few discovered vertices. The other
    // ranks are the identity permutation and can be emitted in contiguous runs.
    fn stage_sparse_identity(&mut self, first: usize, end: usize) -> Result<(), RepairError> {
        self.moved.clear();
        self.moved
            .try_reserve(self.shifts.len())
            .map_err(|_| RepairError::Allocation)?;
        self.moved
            .extend(self.shifts.iter().map(|shift| shift.vertex));
        self.moved.sort_unstable();
        let mut moved = self.moved.iter().copied().peekable();
        let mut cursor = first;
        loop {
            let from = moved.peek().copied().unwrap_or(end);
            let shift = self.shifts.last().copied();
            let next = from.min(shift.map_or(end, |shift| shift.destination));
            self.replacement.extend(cursor..next);
            if next == end {
                return Ok(());
            }
            cursor = next + 1;
            if let Some(shift) = shift.filter(|shift| shift.destination == next) {
                if from == next {
                    return Err(RepairError::OrderViolation {
                        from,
                        to: shift.vertex,
                    });
                }
                self.replacement.push(next);
                while let Some(shift) = self.shifts.last().copied() {
                    if shift.destination != next {
                        break;
                    }
                    self.replacement.push(shift.vertex);
                    self.shifts.pop();
                }
            } else {
                moved.next();
            }
        }
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
