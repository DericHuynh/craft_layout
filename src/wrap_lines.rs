//! Shared greedy sizing and marked replay of a wrapping line.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel::add_count;
#[cfg(not(verus_keep_ghost))]
use crate::solve::cycle_rules::add_count;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub struct WrapLine<I, M = f32> {
    pub next: Option<I>,
    pub count: u32,
    pub main: M,
    pub cross: M,
    pub has_fill: bool,
}

#[cfg(verus_keep_ghost)]
verus! {
pub trait LineModel {
    type Id: Copy;
    type Metric: Copy;

    spec fn items(&self) -> Seq<Item<Self::Id, Self::Metric>>;
    spec fn zero(&self) -> Self::Metric;
    spec fn summed(&self, main: Self::Metric, extent: Self::Metric) -> Self::Metric;
    spec fn cross_max(&self, cross: Self::Metric, extent: Self::Metric) -> Self::Metric;
    spec fn overflows(&self, main: Self::Metric, limit: Self::Metric) -> bool;
}
}

#[cfg(not(verus_keep_ghost))]
pub trait LineModel {
    type Id: Copy;
    type Metric: Copy;
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub trait LineSource: LineModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires present(self.items(), id),
        ensures out == indexed(self.items(), id).in_flow,
    ))]
    fn in_flow(&self, id: Self::Id) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires present(self.items(), id),
        ensures out == indexed(self.items(), id).marked,
    ))]
    fn marked(&self, id: Self::Id) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires present(self.items(), id),
        ensures out == indexed(self.items(), id).fill,
    ))]
    fn fills(&self, id: Self::Id) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires present(self.items(), id),
        ensures out == at(self.items(), index(self.items(), id) + 1),
    ))]
    fn sibling(&self, id: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires present(self.items(), id),
        ensures out == if base { indexed(self.items(), id).base } else { indexed(self.items(), id).main },
    ))]
    fn extent(&self, id: Self::Id, base: bool) -> Self::Metric;

    #[cfg_attr(verus_keep_ghost, verus_spec(out =>
        requires present(self.items(), id),
        ensures out == indexed(self.items(), id).cross,
    ))]
    fn cross_extent(&self, id: Self::Id) -> Self::Metric;

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == self.zero()))]
    fn empty_extent(&self) -> Self::Metric;

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == self.summed(main, extent)))]
    fn append_extent(&self, main: Self::Metric, extent: Self::Metric) -> Self::Metric;

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == self.cross_max(cross, extent)))]
    fn max_cross(&self, cross: Self::Metric, extent: Self::Metric) -> Self::Metric;

    #[cfg_attr(verus_keep_ghost, verus_spec(out => ensures out == self.overflows(main, limit)))]
    fn exceeds_limit(&self, main: Self::Metric, limit: Self::Metric) -> bool;
}

/// Fresh sizing tests the margin-inclusive, pre-Fill main extent. Replay
/// ignores the fitting limit and uses the marked starts and resolved main sizes.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(line =>
    requires valid_chain(source.items()), start == at(source.items(), 0),
    ensures scanned(source, limit, line),
))]
pub(crate) fn scan_line<S: LineSource>(source: &S, mut start: Option<S::Id>, limit: Option<S::Metric>) -> WrapLine<S::Id, S::Metric> {
    let mut count = 0u32;
    let mut main = source.empty_extent();
    let mut cross = main;
    let mut has_fill = false;
    #[cfg(verus_keep_ghost)]
    let mut consumed = start_scan();
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant
            valid_chain(source.items()),
            consumed@ <= source.items().len(), start == at(source.items(), consumed@ as int),
            count == summary(source, limit, consumed@).count,
            main == summary(source, limit, consumed@).main,
            cross == summary(source, limit, consumed@).cross,
            has_fill == summary(source, limit, consumed@).has_fill,
            forall |j: int| 0 <= j < consumed@ ==> !#[trigger] stop_at(source, limit, j),
        decreases source.items().len() - consumed@,
    ))]
    while start.is_some() {
        let child = start.unwrap();
        #[cfg(verus_keep_ghost)]
        proof! { locate(source.items(), consumed@, child); }
        if source.in_flow(child) {
            if limit.is_none() && count != 0 && source.marked(child) {
                let line = WrapLine { next: start, count, main, cross, has_fill };
                #[cfg(verus_keep_ghost)]
                proof! { finish_scan(source, limit, consumed@, line); }
                return line;
            }
            let fill = limit.is_some() && source.fills(child);
            let extent = source.extent(child, fill);
            let new_main = if count == 0 { extent } else { source.append_extent(main, extent) };
            let overflows = match limit {
                Some(available) if count != 0 => source.exceeds_limit(new_main, available),
                _ => false,
            };
            if overflows {
                let line = WrapLine { next: start, count, main, cross, has_fill };
                #[cfg(verus_keep_ghost)]
                proof! { finish_scan(source, limit, consumed@, line); }
                return line;
            }
            main = new_main;
            has_fill |= fill;
            if limit.is_none() {
                cross = source.max_cross(cross, source.cross_extent(child));
            }
            count = add_count(count, 1);
        }
        start = source.sibling(child);
        #[cfg(verus_keep_ghost)]
        proof! { assert(!stop_at(source, limit, consumed@ as int)); }
        #[cfg(verus_keep_ghost)]
        { consumed = advance(consumed); }
    }
    let line = WrapLine { next: start, count, main, cross, has_fill };
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(start == None);
        assert(consumed@ == source.items().len());
        finish_scan(source, limit, consumed@, line);
    }
    line
}
