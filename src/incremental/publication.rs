//! Choose how an incremental attempt publishes geometry.
#![allow(unexpected_cfgs)]

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum Publication {
    /// Finish through the ordinary full solve.
    Rebuild,
    /// Compare complete views and publish the reference result.
    Checked,
    /// Publish every visible output from the new sizing pass.
    All,
    /// Reuse retained output wherever placement permits it.
    Retained,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(action =>
    requires succeeded && !check && partial ==> call_requires(retains_output, ()),
        succeeded && !check && partial ==>
            forall |retained: bool| #[trigger] call_ensures(retains_output, (), retained) ==>
                retained == stable@,
    ensures
        (action is Rebuild) == !succeeded,
        (action is Checked) == (succeeded && check),
        (action is Retained) == (succeeded && !check && partial && stable@),
        (action is All) == (succeeded && !check && (!partial || !stable@)),
))]
pub(crate) fn publication_route<F: Fn() -> bool>(
    succeeded: bool,
    check: bool,
    partial: bool,
    retains_output: F,
    #[cfg(verus_keep_ghost)] stable: Ghost<bool>,
) -> Publication {
    if !succeeded {
        Publication::Rebuild
    } else if check {
        Publication::Checked
    } else if partial && retains_output() {
        Publication::Retained
    } else {
        Publication::All
    }
}
