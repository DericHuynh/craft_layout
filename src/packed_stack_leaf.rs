//! Transient placement inputs for freshly sized Stack and Wrap leaves.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct PreparedStackLeaf<I> {
    pub id: I,
    pub size: [f32; 2],
    pub main_leading: f32,
    pub advance: f32,
    pub cross_leading: f32,
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<I> PreparedStackLeaf<I> {
    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(row =>
        ensures row == (Self {
            id, size, main_leading: margin[0], cross_leading,
            advance: F::sum(crate::placement::modes::adjusted::<F>(if horizontal { size[0] } else { size[1] }, margin[1]), gap),
        }),
        no_unwind
    ))]
    pub(crate) fn stack<F: crate::prepare_frame::FrameFloat>(
        id: I, size: [f32; 2], horizontal: bool, margin: [f32; 2], cross_leading: f32, gap: f32,
    ) -> Self {
        let main = if horizontal { size[0] } else { size[1] };
        let footprint = if F::is_zero(margin[1]) { main } else { F::add(main, margin[1]) };
        Self { id, size, main_leading: margin[0], advance: F::add(footprint, gap), cross_leading }
    }

    #[cfg(any(feature = "incremental", verus_keep_ghost))]
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(row =>
        ensures row == (Self { id, size, advance: F::sum(if horizontal { size[0] } else { size[1] }, gap),
            main_leading: if first_on_line { 1.0 } else { 0.0 },
            cross_leading: line_height }),
        no_unwind
    ))]
    pub(crate) fn wrapped<F: crate::prepare_frame::FrameFloat>(
        id: I, size: [f32; 2], horizontal: bool, gap: f32, first_on_line: bool, line_height: f32,
    ) -> Self {
        // The Wrap row shares the Stack row's storage and is decoded by the parent mode.
        let advance = F::add(if horizontal { size[0] } else { size[1] }, gap);
        Self { id, size, advance, main_leading: if first_on_line { 1.0 } else { 0.0 }, cross_leading: line_height }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_spec(height =>
        ensures height == if F::word(self.main_leading) & 0x7fff_ffffu32 == 0 { None } else { Some(self.cross_leading) },
        no_unwind
    ))]
    pub(crate) fn line_height<F: crate::prepare_frame::FrameFloat>(&self) -> Option<f32> {
        if F::is_zero(self.main_leading) { None } else { Some(self.cross_leading) }
    }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
use crate::vec_memory::VecMemory;

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct StackLeafGroup<I> {
    pub parent: I,
    pub span: [u32; 2],
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) struct PackedStackLeaves<I> {
    pub rows: Vec<PreparedStackLeaf<I>>,
    pub groups: Vec<StackLeafGroup<I>>,
    pub cursor: usize,
    pub uniform_ids: Vec<I>,
    pub uniform_run: Option<(I, [f32; 2])>,
    pub uniform_capture_open: bool,
}

#[cfg(feature = "incremental")]
impl<I> PackedStackLeaves<I> {
    #[cfg(not(verus_keep_ghost))]
    pub(crate) const fn new() -> Self {
        Self {
            rows: Vec::new(), groups: Vec::new(), cursor: 0,
            uniform_ids: Vec::new(), uniform_run: None, uniform_capture_open: false,
        }
    }
}

#[cfg(all(feature = "incremental", not(verus_keep_ghost)))]
impl<I> Clone for PackedStackLeaves<I> {
    fn clone(&self) -> Self { Self::new() }
}

#[cfg(any(feature = "incremental", verus_keep_ghost))]
impl<I: Copy> PackedStackLeaves<I> {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(no_unwind))]
    pub(crate) fn clear<M: VecMemory>(&mut self) {
        M::clear(&mut self.rows);
        M::clear(&mut self.groups);
        self.cursor = 0;
        M::clear(&mut self.uniform_ids);
        self.uniform_run = None;
        self.uniform_capture_open = true;
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(parent =>
        ensures parent == if self.cursor < self.groups.len() {
            Some(self.groups@[self.cursor as int].parent)
        } else { None },
        no_unwind
    ))]
    pub(crate) fn next_parent(&self) -> Option<I> {
        if self.cursor < self.groups.len() { Some(self.groups[self.cursor].parent) } else { None }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(span =>
        ensures final(self).groups@ == old(self).groups@, final(self).rows@ == old(self).rows@,
            final(self).uniform_ids@ == old(self).uniform_ids@,
            final(self).uniform_run == old(self).uniform_run,
            final(self).uniform_capture_open == old(self).uniform_capture_open,
            span == if old(self).cursor < old(self).groups.len() {
                let [start, end] = old(self).groups@[old(self).cursor as int].span;
                Some([start as usize, end as usize])
            } else { None },
            final(self).cursor as int == old(self).cursor as int + (if span.is_some() { 1int } else { 0int }),
        no_unwind
    ))]
    pub(crate) fn take_span(&mut self) -> Option<[usize; 2]> {
        let index = self.cursor;
        if index >= self.groups.len() { return None; }
        let [start, end] = self.groups[index].span;
        self.cursor = index + 1;
        Some([start as usize, end as usize])
    }
}
