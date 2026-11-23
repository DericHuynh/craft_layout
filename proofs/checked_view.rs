//! Prove the checked layout's stream comparison, including order and length.
use vstd::prelude::*;
#[path = "../src/view_check.rs"]
mod kernel;


verus! {

pub open spec fn agrees_on_prefix<T>(expected: Seq<T>, observed: Seq<T>) -> bool {
    observed.len() <= expected.len() && expected.take(observed.len() as int) == observed
}

/// Each callback supplies equality of its node identity and eight rectangle bits
/// with the saved record at the current cursor. A missing or extra callback
/// cannot pass the comparison. The implementation never re-reads host output.
pub fn check_stream(expected: &[u32], observed: &[u32]) -> (ok: bool)
    ensures ok == (expected@ == observed@),
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
        let j = check.position();
        let equal = j < expected.len() && expected[j] == observed[i];
        check.compare(equal);
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
