//! Keep track of a comparison against an ordered snapshot.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// Once a mismatch is found, subsequent writes cannot make the frame agree.
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
pub struct ViewCheck {
    pub cursor: usize,
    pub agrees: bool,
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(state => ensures state.cursor == 0 && state.agrees))]
pub fn start() -> ViewCheck { ViewCheck { cursor: 0, agrees: true } }

impl ViewCheck {
    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.position()))]
    pub fn position(self) -> usize { self.cursor }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify)]
    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires matches_next ==> old(self).cursor < usize::MAX,
        ensures final(self).agrees == (old(self).agrees && matches_next),
            final(self).cursor == old(self).cursor + if final(self).agrees { 1int } else { 0int },
    ))]
    pub fn compare(&mut self, matches_next: bool) {
        if self.agrees && matches_next {
            self.cursor += 1;
        } else {
            self.agrees = false;
        }
    }

    #[inline]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.finished(expected)))]
    pub fn finished(self, expected: usize) -> bool {
        self.agrees && self.cursor == expected
    }

}
