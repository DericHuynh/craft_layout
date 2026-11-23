//! A back edge reads an in-progress slot's provisional value. This makes DFS
//! entry order observable, even with fully deterministic measurement functions.
use vstd::prelude::*;
#[path = "../src/cycle_rules.rs"]
pub mod kernel;
use kernel::{Entry, Route};

verus! {

/// Different slots never overlap. Share and Flow each name one slot per
/// node, independent of which axis requested it.
proof fn distinct_slot_indices(
    first_axis: usize, first_kind: kernel::Kind, second_axis: usize, second_kind: kernel::Kind,
)
    requires first_axis < 2, second_axis < 2,
    ensures kernel::slot_index(first_axis, first_kind) == kernel::slot_index(second_axis, second_kind)
        <==> first_kind == second_kind &&
            (first_axis == second_axis || first_kind is EvenShare || first_kind is Flow),
{}

pub proof fn production_routes(state:u32, structural:bool, cyclic:bool, flow:bool, resized:bool)
    ensures
        (kernel::enter(state) is BackEdge) == (state == 1),
        (kernel::enter(state) is Reuse) == (state == 2),
        (kernel::enter(state) is CheckIntrinsic) == (state == 3),
        kernel::enter(0) is Compute,
        cyclic && !structural ==> kernel::route(structural,cyclic,flow,resized) is Cycle,
        structural ==> kernel::route(structural,cyclic,flow,resized) is Structural,
        kernel::route(structural,cyclic,flow,resized) is Queue ==> !cyclic && !structural,
{}

/// The same seeds enter both fresh and regional DFS. Cached intrinsic slots
/// expose these bits after the production erase helper and before recursing.
pub proof fn production_slot_defaults_and_order(is_max:bool, regular:int, min:int, max:int)
    ensures
        kernel::provisional_bits(is_max) == if is_max {0x7f80_0000u32} else {0u32},
        kernel::declaration_order(regular,min,max)@ == seq![regular,min,max],
{}

/// An ordinary constrained leaf's stable rule contains its declaration,
/// padding, maximums and the registered content identity. The opposite Final
/// supplies its only dynamic measurement input. Always test the state before
/// trusting its bits, since an in-progress slot holds a provisional value.
pub proof fn matching_constraint_reuses_exact_intrinsic(
    local: Seq<int>, old_bits: u32, new_bits: u32, state: u32,
    eval: spec_fn(Seq<int>, u32) -> u32,
)
    ensures
        kernel::same_intrinsic_constraint(state,new_bits,old_bits)
            ==> eval(local,new_bits) == eval(local,old_bits),
        state == kernel::IN_PROGRESS ==> !kernel::same_intrinsic_constraint(state,new_bits,old_bits),
{}

/// Entering an unsolved slot initializes its provisional bits. Finishing a
/// slot consumes the ordered values currently visible to that invocation. An
/// in-progress read thus sees exactly the same provisional bits as full DFS.
pub enum Event {
    Begin { key:int, provisional:Seq<u32> },
    Finish { key:int, reads:Seq<int> },
}

impl Event {
    pub open spec fn target(self) -> int {
        match self { Self::Begin {key,..} | Self::Finish {key,..} => key }
    }
    pub open spec fn inputs(self) -> Seq<int> {
        match self { Self::Begin {..} => Seq::empty(), Self::Finish {reads,..} => reads }
    }
}

pub type Storage = Map<int,Seq<u32>>;
pub type Compute = spec_fn(int,Seq<Seq<u32>>) -> Seq<u32>;

pub open spec fn arguments(reads:Seq<int>, state:Storage) -> Seq<Seq<u32>> {
    Seq::new(reads.len(),|i:int| state[reads[i]])
}
pub open spec fn replay(events:Seq<Event>, initial:Storage, eval:Compute) -> Storage
    decreases events.len(),
{
    if events.len() == 0 { initial }
    else {
        let prior = replay(events.drop_last(),initial,eval);
        let event = events.last();
        let value = match event {
            Event::Begin { provisional,.. } => provisional,
            Event::Finish { key,reads } => eval(key,arguments(reads,prior)),
        };
        prior.insert(event.target(),value)
    }
}
pub open spec fn wrote(events:Seq<Event>, key:int) -> bool {
    exists|i:int| 0 <= i < events.len() && (#[trigger] events[i]).target() == key
}
/// Slots may differ in the incoming caches. Only an input actually consumed
/// before the region initializes it must have matching incoming bits.
pub open spec fn boundaries_agree(events:Seq<Event>, a:Storage, b:Storage) -> bool
    decreases events.len(),
{
    if events.len() == 0 { true }
    else {
        let prefix = events.drop_last();
        let reads = events.last().inputs();
        boundaries_agree(prefix,a,b) &&
            forall|j:int| 0 <= j < reads.len() && !wrote(prefix,#[trigger] reads[j]) ==>
                a.contains_key(reads[j]) && b.contains_key(reads[j]) && a[reads[j]] == b[reads[j]]
    }
}

pub proof fn canonical_replay_matches_full(events:Seq<Event>, a:Storage, b:Storage, eval:Compute, k:int)
    requires boundaries_agree(events,a,b),
    ensures ({
        let x=replay(events,a,eval); let y=replay(events,b,eval);
        &&& wrote(events,k) ==> x.contains_key(k) && y.contains_key(k) && x[k] == y[k]
        &&& !wrote(events,k) ==> x.contains_key(k) == a.contains_key(k) && y.contains_key(k) == b.contains_key(k)
            && (a.contains_key(k) ==> x[k] == a[k]) && (b.contains_key(k) ==> y[k] == b[k])
    }),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix=events.drop_last();
        let event=events.last();
        canonical_replay_matches_full(prefix,a,b,eval,k);
        assert(wrote(events,k) == (wrote(prefix,k) || event.target() == k)) by {
            assert(event == events[events.len()-1]);
            assert forall|i:int| 0 <= i < prefix.len() implies #[trigger] prefix[i] == events[i] by {};
            assert forall|i:int| 0 <= i < prefix.len() implies #[trigger] events[i] == prefix[i] by {};
        }
        if event.target() == k {
            if let Event::Finish {reads,..} = event {
                let x = replay(prefix,a,eval); let y = replay(prefix,b,eval);
                assert(arguments(reads,x) =~= arguments(reads,y)) by {
                    assert forall|j:int| 0 <= j < reads.len() implies x[#[trigger] reads[j]] == y[reads[j]] by {
                        let read = reads[j];
                        canonical_replay_matches_full(prefix,a,b,eval,read);
                        if !wrote(prefix, read) {
                            assert(read == events.last().inputs()[j]);
                            assert(a.contains_key(read) && b.contains_key(read) && a[read] == b[read]);
                        }
                    }
                }
            }
        }
    } else {
        assert(!wrote(events,k));
    }
}

/// Both slots depend on the other. Swapping which one starts first changes
/// the final geometry for a deterministic rule. A topological queue cannot
/// replace canonical replay in general.
pub proof fn changing_cycle_entry_can_change_results()
{
    let initial:Storage = Map::empty();
    let a = Event::Begin { key:0, provisional:seq![0u32] };
    let b = Event::Begin { key:1, provisional:seq![0u32] };
    let fa = Event::Finish { key:0, reads:seq![1int] };
    let fb = Event::Finish { key:1, reads:seq![0int] };
    let eval:Compute = |k:int, args:Seq<Seq<u32>>| seq![if args[0][0] == 0 { 1u32 } else { 2u32 }];
    let ab = seq![a,b,fb,fa];
    let ba = seq![b,a,fa,fb];
    reveal_with_fuel(replay,5);
    assert(ab.drop_last().drop_last().drop_last().drop_last() =~= Seq::<Event>::empty());
    assert(ba.drop_last().drop_last().drop_last().drop_last() =~= Seq::<Event>::empty());
    assert(replay(ab,initial,eval)[0][0] == 2);
    assert(replay(ba,initial,eval)[0][0] == 1);
}

}

#[path = "cycle_dfs.rs"]
pub mod dfs;

#[path = "cycle_boundary.rs"]
pub mod boundary;
