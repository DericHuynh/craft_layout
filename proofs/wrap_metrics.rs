//! A line's metric word is written once for each in-flow sibling in that line.
use vstd::prelude::*;
use super::wrap_lines;

#[path = "../src/wrap_metrics.rs"]
pub(super) mod kernel;
use kernel::Metric;

verus! {

pub open spec fn cursor<I>(run:Seq<(I,bool)>, stop:Option<I>, i:int) -> Option<I> {
    if i == run.len() { stop } else { Some(run[i].0) }
}

pub open spec fn distinct<I>(run:Seq<(I,bool)>, stop:Option<I>) -> bool {
    forall |i:int,j:int| 0 <= i <= run.len() && 0 <= j <= run.len() &&
        #[trigger] cursor(run,stop,i) == #[trigger] cursor(run,stop,j) ==> i == j
}

pub open spec fn member<I>(run:Seq<(I,bool)>, stop:Option<I>, id:I) -> bool {
    exists |i:int| 0 <= i < run.len() && #[trigger] cursor(run,stop,i) == Some(id)
}

pub open spec fn index<I>(run:Seq<(I,bool)>, stop:Option<I>, id:I) -> int {
    choose |i:int| 0 <= i < run.len() && #[trigger] cursor(run,stop,i) == Some(id)
}

pub proof fn locate<I>(run:Seq<(I,bool)>, stop:Option<I>, i:nat, id:I)
    requires distinct(run,stop), i < run.len(), cursor(run,stop,i as int) == Some(id),
    ensures member(run,stop,id), index(run,stop,id) == i,
{
    assert(exists |j:int| 0 <= j < run.len() && cursor(run,stop,j) == Some(id));
    let j = index(run,stop,id);
    assert(cursor(run,stop,j) == cursor(run,stop,i as int));
}

pub type Words = (u32, u32);

pub open spec fn read_word(words: Words, metric: Metric) -> u32 {
    match metric { Metric::Share => words.0, Metric::Cross => words.1 }
}

pub open spec fn replace_word(words: Words, metric: Metric, bits: u32) -> Words {
    match metric { Metric::Share => (bits,words.1), Metric::Cross => (words.0,bits) }
}

pub open spec fn other(metric: Metric) -> Metric {
    match metric { Metric::Share => Metric::Cross, Metric::Cross => Metric::Share }
}

pub proof fn metric_words_are_distinct()
    ensures Metric::Share.word()==0, Metric::Cross.word()==1,
{}

/// These are the exact machine words. Exponents, signs and NaN payloads have
/// no effect on which field is visible or on the other field's round trip.
pub fn physical_word_update(
    mut words:[u32;2], channel:Metric, bits:u32, producer_solved:bool,
) -> (out:(u32,[u32;2]))
    ensures ({
        let next=replace_word((words[0],words[1]),channel,bits);
        &&& out.0 == if producer_solved {bits} else {0u32}
        &&& out.1[0]==next.0 && out.1[1]==next.1
    }),
{
    proof!{metric_words_are_distinct();}
    kernel::store_metric(&mut words,channel,bits);
    let read=match kernel::ready_metric(producer_solved,channel) {
        Some(metric)=>kernel::read_metric(&words,metric),
        None=>0,
    };
    (read,words)
}

pub open spec fn stamp<I>(run:Seq<(I,bool)>, n:nat, cache:Map<I,Words>, metric:Metric, bits:u32) -> Map<I,Words>
    decreases n,
{
    if n == 0 { cache } else {
        let row = run[n-1];
        let finished = stamp(run,(n-1) as nat,cache,metric,bits);
        if row.1 { finished.insert(row.0,replace_word(finished[row.0],metric,bits)) } else { finished }
    }
}

pub open spec fn receives<I>(run:Seq<(I,bool)>, n:nat, id:I) -> bool {
    exists |i:int| 0 <= i < n && #[trigger] run[i] == (id,true)
}

pub proof fn stamp_preserves_other_words<I>(
    run: Seq<(I,bool)>, n:nat, cache: Map<I,Words>, metric:Metric, bits:u32, id:I,
)
    requires n <= run.len(),
        forall |i:int| 0 <= i < run.len() ==> cache.contains_key((#[trigger] run[i]).0),
    ensures stamp(run,n,cache,metric,bits).contains_key(id) == cache.contains_key(id),
        cache.contains_key(id) ==> read_word(stamp(run,n,cache,metric,bits)[id],other(metric)) == read_word(cache[id],other(metric)),
        cache.contains_key(id) ==> read_word(stamp(run,n,cache,metric,bits)[id],metric) ==
            if receives(run,n,id) { bits } else { read_word(cache[id],metric) },
    decreases n,
{
    if n > 0 {
        stamp_preserves_other_words(run,(n-1) as nat,cache,metric,bits,id);
        let row = run[n-1];
        assert(receives(run,n,id) == (receives(run,(n-1) as nat,id) || row == (id,true))) by {
            if receives(run,n,id) {
                let i = choose |i:int| 0 <= i < n && #[trigger] run[i] == (id,true);
                if i == n - 1 { assert(run[i] == row); }
            } else if row == (id,true) {
                assert(run[n-1] == (id,true));
            }
        }
        match metric { Metric::Share => {}, Metric::Cross => {} }
    }
}

/// A DFS back edge can let Flow finish while EvenShare is still active. Both
/// producers preserve the other channel even when the provisional and final
/// calculations use different line membership.
pub proof fn two_pass_metric<I>(
    main_run:Seq<(I,bool)>, cross_run:Seq<(I,bool)>, cache:Map<I,Words>, share:u32, extent:u32, id:I,
)
    requires cache.contains_key(id),
        forall |i:int| 0 <= i < main_run.len() ==> cache.contains_key((#[trigger] main_run[i]).0),
        forall |i:int| 0 <= i < cross_run.len() ==> cache.contains_key((#[trigger] cross_run[i]).0),
    ensures ({
        let main = stamp(main_run,main_run.len(),cache,Metric::Share,share);
        let cross = stamp(cross_run,cross_run.len(),main,Metric::Cross,extent);
        let reverse_cross = stamp(cross_run,cross_run.len(),cache,Metric::Cross,extent);
        let reverse_main = stamp(main_run,main_run.len(),reverse_cross,Metric::Share,share);
        &&& main.contains_key(id) && cross.contains_key(id)
        &&& reverse_cross.contains_key(id) && reverse_main.contains_key(id)
        &&& cross[id] == reverse_main[id]
        &&& cross[id].0 == if receives(main_run,main_run.len(),id) { share } else { cache[id].0 }
        &&& cross[id].1 == if receives(cross_run,cross_run.len(),id) { extent } else { cache[id].1 }
    }),
{
    stamp_preserves_other_words(main_run,main_run.len(),cache,Metric::Share,share,id);
    stamp_preserves_other_words(cross_run,cross_run.len(),cache,Metric::Cross,extent,id);
    let main = stamp(main_run,main_run.len(),cache,Metric::Share,share);
    let cross = stamp(cross_run,cross_run.len(),cache,Metric::Cross,extent);
    assert forall |i:int| 0 <= i < cross_run.len() implies main.contains_key((#[trigger] cross_run[i]).0) by {
        stamp_preserves_other_words(main_run,main_run.len(),cache,Metric::Share,share,cross_run[i].0);
    }
    assert forall |i:int| 0 <= i < main_run.len() implies cross.contains_key((#[trigger] main_run[i]).0) by {
        stamp_preserves_other_words(cross_run,cross_run.len(),cache,Metric::Cross,extent,main_run[i].0);
    }
    stamp_preserves_other_words(cross_run,cross_run.len(),main,Metric::Cross,extent,id);
    stamp_preserves_other_words(main_run,main_run.len(),cross,Metric::Share,share,id);
}

}
