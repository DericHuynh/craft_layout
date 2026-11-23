//! Embed the change-aware measurement queue in the retained-view trace.
use super::*;
use super::dependencies::{self, Datum, Edge, Graph, Locals, Part, queue_matches_full_prefix, queue_prefix};

verus! {

pub struct Frame {
    pub keys: Seq<Key>,
    pub parts: Seq<Part>,
    pub reads: Seq<Seq<int>>,
    pub near: spec_fn(int, int) -> Edge,
    pub local: Locals,
}

pub open spec fn as_words(values: Seq<Datum>) -> Seq<Value> {
    Seq::new(values.len(), |i:int| Value::Words(values[i]))
}

impl Frame {
    pub open spec fn rule(self, i: int, local: Seq<int>) -> Rule {
        Rule { local, reads: Seq::new(self.reads[i].len(), |j:int| self.keys[self.reads[i][j]]) }
    }
    pub open spec fn graph(self, eval: Eval) -> Graph {
        Graph {
            parts: self.parts, reads: self.reads, neighborhood: self.near,
            eval: |i:int, local:Seq<int>, vs:Seq<Datum>|
                (eval.measure)(self.keys[i], self.rule(i,local), as_words(vs)),
        }
    }
    pub open spec fn values(self, old: Cache) -> Seq<Datum> {
        Seq::new(self.keys.len(), |i:int| old[self.keys[i]].value->Words_0)
    }
    pub open spec fn old_local(self, old: Cache) -> Locals {
        Seq::new(self.keys.len(), |i:int| old[self.keys[i]].rule.local)
    }
    /// Numeric passes keep the old identities and ordered read lists; a rule
    /// shape or identity change is handled by structural measurement instead.
    pub open spec fn stable_graph(self, old: Cache, eval: Eval) -> bool {
        &&& self.graph(eval).valid()
        &&& self.keys.len() == self.parts.len() == self.local.len()
        &&& forall|i:int| 0 <= i < self.keys.len() ==> ({
            let k = #[trigger] self.keys[i];
            &&& k.phase is Measurement
            &&& old.contains_key(k)
            &&& old[k].value is Words
            &&& old[k].rule == self.rule(i,old[k].rule.local)
        })
        &&& forall|i:int,j:int| 0 <= i < j < self.keys.len() ==> self.keys[i] != self.keys[j]
    }
    pub open spec fn valid(self, old: Cache, seeds: Set<int>, eval: Eval) -> bool {
        self.stable_graph(old,eval) && forall|i:int| 0 <= i < self.keys.len()
            && old[self.keys[i]].rule.local != self.local[i] ==> #[trigger] seeds.contains(i)
    }

}

pub open spec fn trace(f:Frame, old:Cache, seeds:Set<int>, eval:Eval, n:nat) -> Seq<Step>
    decreases n,
{
    if n == 0 { Seq::empty() }
    else {
        let i = n-1;
        let q = queue_prefix(f.graph(eval),f.local,f.values(old),seeds,i as nat);
        trace(f,old,seeds,eval,i as nat).push(Step {
            key: f.keys[i], rule: f.rule(i,f.local[i]), work: Work::Size { recompute: (q.pending)(i) }
        })
    }
}

/// This discharges UnchangedReads coverage for the entire numeric prefix. The
/// map built by the actual view theorem contains the queue's values at those keys.
pub proof fn sizing_queue_covers_trace(f: Frame, old: Cache, seeds: Set<int>, eval: Eval, n: nat)
    requires f.valid(old,seeds,eval), sound(old,eval), coherent(old), n <= f.keys.len(),
    ensures ({
        let steps = trace(f,old,seeds,eval,n);
        let q = queue_prefix(f.graph(eval),f.local,f.values(old),seeds,n);
        let built = build(steps,old,eval,false);
        &&& covered(steps,old,eval)
        &&& forall|j:int| 0 <= j < f.keys.len() ==> ({
            let k = #[trigger] f.keys[j];
            &&& built.contains_key(k) == (j < n)
            &&& j < n ==> built[k].value == Value::Words(q.values[j])
        })
    }),
    decreases n,
{
    let g = f.graph(eval);
    let v = f.values(old);
    let l = f.old_local(old);
    assert forall|i:int| 0 <= i < v.len() implies
        #[trigger] v[i] == (g.eval)(i,l[i],g.inputs(i,v)) by {
        let k = f.keys[i];
        let rule = old[k].rule;
        assert(as_words(g.inputs(i,v)) =~= args(rule,old)) by {
            assert forall|j:int| 0 <= j < rule.reads.len() implies
                #[trigger] rule.reads[j] == f.keys[f.reads[i][j]]
                && old[rule.reads[j]].value == Value::Words(v[f.reads[i][j]]) by {
                assert(0 <= f.reads[i][j] < i);
            }
        }
    }
    if n > 0 {
        let i = n-1;
        let key = f.keys[i];
        sizing_queue_covers_trace(f,old,seeds,eval,i as nat);
        queue_matches_full_prefix(g,l,f.local,v,seeds,i as nat);
        let earlier = trace(f,old,seeds,eval,i as nat);
        let prefix = build(earlier,old,eval,false);
        let prior = queue_prefix(g,f.local,v,seeds,i as nat);
        let steps = trace(f,old,seeds,eval,n);
        let rule = f.rule(i,f.local[i]);
        assert(steps.drop_last() == earlier);
        assert forall|j:int| 0 <= j < rule.reads.len() implies #[trigger] prefix.contains_key(rule.reads[j])
            && prefix[rule.reads[j]].value == Value::Words(prior.values[f.reads[i][j]]) by {
            let s = f.reads[i][j];
            assert(0 <= s < i);
            assert(rule.reads[j] == f.keys[s]);
        }
        assert(args(rule,prefix) =~= as_words(g.inputs(i,prior.values)));
        if !(prior.pending)(i) {
            assert(old[key].rule == rule);
            assert(args(rule,prefix) =~= args(rule,old)) by {
                assert forall|j:int| 0 <= j < rule.reads.len() implies
                    #[trigger] prefix[rule.reads[j]].value == old[rule.reads[j]].value by {
                    assert(0 <= f.reads[i][j] < i);
                }
            }
        }
        let q = queue_prefix(g,f.local,v,seeds,n);
        let built = build(steps,old,eval,false);
        assert forall|j:int| 0 <= j < f.keys.len() implies ({
            let k = #[trigger] f.keys[j];
            &&& built.contains_key(k) == (j < n)
            &&& j < n ==> built[k].value == Value::Words(q.values[j])
        }) by {
            if j < i { assert(prior.values[j] == q.values[j]); }
        }
    }
}

/// Compose concrete edit dispatch, change-aware propagation, and the view
/// proof. The adapter supplies which primitive local inputs changed. No seed
/// set, trace coverage, or equality to a fresh solve is required as a premise.
pub proof fn registered_sizing_frame_matches_full(f:Frame, edits:Seq<dependencies::Edit>,
    old:Cache, eval:Eval)
    requires f.stable_graph(old,eval), sound(old,eval), coherent(old),
        forall|i:int| 0 <= i < f.keys.len() && old[f.keys[i]].rule.local != f.local[i]
            ==> #[trigger] dependencies::reader_changed(edits,i),
    ensures ({
        let n=f.keys.len();
        let seeds=dependencies::batch_seeds(edits,n);
        let steps=trace(f,old,seeds,eval,n);
        &&& covered(steps,old,eval)
        &&& build(steps,old,eval,false) == build(steps,Map::empty(),eval,true)
        &&& sound(build(steps,old,eval,false),eval) && coherent(build(steps,old,eval,false))
    }),
{
    let n=f.keys.len();
    let seeds=dependencies::batch_seeds(edits,n);
    assert forall|i:int| 0 <= i < n && old[f.keys[i]].rule.local != f.local[i]
        implies #[trigger] seeds.contains(i) by {
        dependencies::batch_registers_every_reader(edits,n,i);
    }
    sizing_queue_covers_trace(f,old,seeds,eval,n);
    incremental_matches_full(trace(f,old,seeds,eval,n),old,eval);
}

}
