//! Prove the checked layout's stream comparison, including order and length.
use vstd::prelude::*;
use crate::vec_memory::FallibleVecMemory;
#[path = "../src/view_check.rs"]
pub(crate) mod kernel;
#[path = "../src/incremental/checked_view.rs"]
pub(crate) mod adapter;

verus! {

pub open spec fn agrees_on_prefix<T>(expected: Seq<T>, observed: Seq<T>) -> bool {
    observed.len() <= expected.len() && expected.take(observed.len() as int) == observed
}

/// The capture sink records every callback in sequence until storage rejects a record.
/// Later callbacks may continue the layout walk, but they leave the buffer intact.
pub(crate) fn capture_stream<I: Copy, M: FallibleVecMemory>(
    expected: &mut Vec<kernel::OutputRecord<I>>, observed: &[kernel::OutputRecord<I>],
) -> (complete: bool)
    ensures
        complete ==> final(expected)@ == old(expected)@ + observed@,
        !complete ==> exists |count: int| 0 <= count < observed.len()
            && final(expected)@ == old(expected)@ + #[trigger] observed@.take(count),
    no_unwind
{
    let mut check = kernel::start();
    let mut i = 0;
    proof! { assert((old(expected)@ + observed@.take(0)) =~= old(expected)@); }
    while i < observed.len()
        invariant i <= observed.len(), check.agrees,
            expected@ == old(expected)@ + observed@.take(i as int),
        decreases observed.len() - i,
    {
        check.capture_record::<_, M>(expected, observed[i]);
        if !check.agrees {
            proof! {
                assert(exists |count: int| 0 <= count < observed.len()
                    && expected@ == old(expected)@ + #[trigger] observed@.take(count)) by {
                    assert(expected@ == old(expected)@ + observed@.take(i as int));
                }
            }
            return false;
        }
        proof! {
            assert(observed@.take(i as int).push(observed@[i as int]) =~= observed@.take(i as int + 1));
            assert(expected@ =~= old(expected)@ + observed@.take(i as int + 1));
        }
        i += 1;
    }
    proof! { assert(observed@.take(i as int) =~= observed@); }
    true
}

/// Each callback supplies equality of its node identity and eight rectangle bits
/// with the saved record at the current cursor. A missing or extra callback
/// cannot pass the comparison. The implementation never re-reads host output.
pub fn check_stream<I: kernel::OutputIdentity>(
    expected: &[kernel::OutputRecord<I>], observed: &[kernel::OutputRecord<I>],
) -> (ok: bool)
    ensures ok == (expected@ == observed@),
    no_unwind
{
    let mut check = kernel::start();
    let mut i = 0;
    #[cfg(verus_keep_ghost)]
    proof! { assert(expected@.take(0) =~= observed@.take(0)); }
    while i < observed.len()
        invariant
            i <= observed.len(), check.position() <= expected.len(),
            check.agrees == agrees_on_prefix(expected@,observed@.take(i as int)),
            check.agrees ==> check.position() == i,
        decreases observed.len() - i,
    {
        check.compare_record(expected, observed[i]);
        proof! {
            assert(observed@.take((i + 1) as int).take(i as int) =~= observed@.take(i as int));
            if agrees_on_prefix(expected@,observed@.take((i + 1) as int)) {
                assert(expected@.take((i + 1) as int).take(i as int) =~= expected@.take(i as int));
                assert(expected@.take((i + 1) as int)[i as int] == expected[i as int]);
                assert(observed@.take((i + 1) as int)[i as int] == observed[i as int]);
                assert(expected[i as int] == observed[i as int]);
            } else if check.agrees {
                assert(expected@.take((i + 1) as int) =~= observed@.take((i + 1) as int));
            }
        }
        i += 1;
    }
    proof! {
        assert(observed@.take(i as int) =~= observed@);
        assert(expected@.take(expected.len() as int) =~= expected@);
    }
    check.finished(expected.len())
}

}
