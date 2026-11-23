// Shared cursor for layout child lists and bounded wrapping lines.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

// Expand the complete sibling loop at its call site so LLVM can optimize the
// placement body together with the traversal. The bounded form can stop before
// advancing past a wrapping-line boundary.
macro_rules! walk_siblings {
    ($(#[$attr:meta])* ; ($cursor:expr, $id:ident); { $($before:tt)* }; $following:expr; $disabled:expr; $body:block) => {
        $(#[$attr])*
        while let Some($id) = $cursor {
            $($before)*
            $cursor = $following;
            if !$disabled $body
        }
    };
}

// Verify a prefix of the actual loop up to its first emitted child. The cursor
// is already advanced there, so the same contract applies to every remaining
// iteration. The adapter's finite linked list supplies the termination measure.
#[cfg(verus_keep_ghost)]
#[verus_verify]
#[verus_spec(result =>
    requires chain(links@, stop@, read), *old(cursor) == at(links@, stop@, 0),
    ensures advanced(links@, stop@, result, *final(cursor)),
)]
pub fn next_visible<I: Copy, F: Fn(I) -> Option<(Option<I>, bool)>>(
    cursor: &mut Option<I>, read: F, links: Ghost<Seq<(I, bool)>>, stop: Ghost<Option<I>>,
) -> Option<I> {
    proof! { locate(links@, stop@, 0); }
    walk_siblings!(
        #[verus_spec(
            invariant
                chain(links@, stop@, read),
                0 <= position(links@, stop@, *cursor) <= links@.len(),
                *cursor == at(links@, stop@, position(links@, stop@, *cursor)),
                forall |i: int| 0 <= i < position(links@, stop@, *cursor) ==> !(#[trigger] links@[i]).1,
            ensures advanced(links@, stop@, None, *cursor),
            decreases links@.len() - position(links@, stop@, *cursor),
        )]; (*cursor, id); {
            proof! {
                let p = position(links@, stop@, *cursor);
                if p < links@.len() { locate(links@, stop@, p + 1); }
            }
            let Some((following, disabled)) = read(id) else { break };
        }; following; disabled; { return Some(id); }
    );
    None
}
