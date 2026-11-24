use vstd::prelude::*;
#[path = "../src/queue_storage.rs"]
mod kernel;
#[path = "../src/incremental/numeric.rs"]
pub(crate) mod numeric;
#[path = "../src/incremental/intake.rs"]
pub(crate) mod intake;
#[path = "../src/incremental/tape.rs"]
pub(crate) mod tape;
#[path = "../src/incremental/tape_plan.rs"]
pub(crate) mod tape_plan;
#[path = "../src/incremental/readers.rs"]
pub(crate) mod readers;
verus! {
#[allow(non_snake_case)]
pub open spec fn BucketCount() -> int { 65536 }
pub open spec fn at_rank(heads:Seq<usize>, base:u16, r:int) -> usize {
    if base <= r < base as int + heads.len() { heads[r-base] } else { 0 }
}

/// The free list is just another owned chain. Ranks use absolute levels, so a
/// physical change of base or extent leaves every abstract chain unchanged.
pub type Chains = spec_fn(int) -> Seq<usize>;
pub type Heads = spec_fn(int) -> usize;
pub type Position = (int,int);

pub open spec fn head(xs:Seq<usize>) -> usize { if xs.len()==0 {0} else {xs[0]} }
pub open spec fn next(xs:Seq<usize>, i:int) -> usize { if i+1<xs.len() {xs[i+1]} else {0} }
pub open spec fn live(w:Chains,p:Position) -> bool { 0 <= p.1 < w(p.0).len() }
pub open spec fn id(w:Chains,p:Position) -> usize { w(p.0)[p.1] }
pub open spec fn owns(w:Chains,e:usize) -> bool { exists|p:Position| live(w,p) && #[trigger] id(w,p)==e }
pub open spec fn valid<T>(es:Seq<(T,usize)>, hs:Heads, w:Chains) -> bool {
    &&& forall|r:int| #[trigger] hs(r)==head(w(r))
    &&& forall|p:Position| #[trigger] live(w,p) ==> ({
        let e=id(w,p);
        &&& 0<e<=es.len()
        &&& es[e-1].1 == next(w(p.0),p.1)
    })
    &&& forall|p:Position,q:Position| live(w,p) && live(w,q)
        && #[trigger] id(w,p) == #[trigger] id(w,q) ==> p==q
    &&& forall|e:usize| 0 < e <= es.len() ==> #[trigger] owns(w,e)
}

pub struct Transfer {
    pub source:Option<int>, // None allocates a new terminal index
    pub dest:int,
}
impl Transfer {
    pub open spec fn ok(self,w:Chains) -> bool {
        match self.source {Some(src) => src!=self.dest && w(src).len()>0, None => true}
    }
    pub open spec fn offset(self, r:int) -> int {
        if r==self.dest {1} else if self.source==Some(r) {-1} else {0}
    }
    pub open spec fn forward(self,p:Position) -> Position {
        if self.source==Some(p.0) && p.1==0 {(self.dest,0)} else {(p.0,p.1+self.offset(p.0))}
    }
    pub open spec fn origin(self,p:Position) -> Option<Position> {
        if p==(self.dest,0) {
            match self.source {Some(src)=>Some((src,0)), None=>None}
        } else { Some((p.0,p.1-self.offset(p.0))) }
    }
    pub open spec fn updated(self,w:Chains,e:usize) -> Chains {
        |r:int| if r==self.dest {seq![e]+w(r)}
            else if self.source==Some(r) {w(r).drop_first()} else {w(r)}
    }
    pub open spec fn index<T>(self,es:Seq<(T,usize)>,w:Chains) -> usize {
        match self.source {Some(src)=>head(w(src)),None=>(es.len()+1) as usize}
    }
    pub open spec fn entries<T>(self,es:Seq<(T,usize)>,w:Chains,v:T) -> Seq<(T,usize)> {
        let entry=(v,head(w(self.dest)));
        if self.source.is_none() {es.push(entry)} else {es.update(self.index(es,w)-1,entry)}
    }
    pub open spec fn roots(self, hs:Heads, next_link:usize, e:usize) -> Heads {
        |r:int| if r==self.dest {e} else if self.source==Some(r) {next_link} else {hs(r)}
    }
}
proof fn positions_forward<T>(op:Transfer, es:Seq<(T,usize)>,hs:Heads,w:Chains,p:Position)
    requires valid(es,hs,w),op.ok(w),live(w,p),
    ensures ({
        let e=op.index(es,w); let w2=op.updated(w,e); let q=op.forward(p);
        &&& live(w2,q)
        &&& id(w2,q)==id(w,p)
        &&& op.origin(q)==Some(p)
    }),
{}
proof fn positions_backward<T>(op:Transfer, es:Seq<(T,usize)>,hs:Heads,w:Chains,q:Position)
    requires valid(es,hs,w),op.ok(w),live(op.updated(w,op.index(es,w)),q),
    ensures ({
        let e=op.index(es,w); let w2=op.updated(w,e);
        match op.origin(q) {
            Some(p) => live(w,p) && id(w2,q)==id(w,p) && op.forward(p)==q,
            None => q==(op.dest,0) && op.source.is_none() && id(w2,q)==e,
        }
    }),
{}

pub proof fn preserves_partition<T>(op:Transfer,es:Seq<(T,usize)>,hs:Heads,w:Chains,v:T)
    requires valid(es,hs,w),op.ok(w),op.source.is_none() ==> es.len()<usize::MAX,
    ensures ({
        let e=op.index(es,w);
        let successor=if op.source.is_none(){0usize}else{es[e-1].1};
        valid(op.entries(es,w,v),op.roots(hs,successor,e),op.updated(w,e))
    }),
{
    let e=op.index(es,w);
    let w2=op.updated(w,e);
    let es2=op.entries(es,w,v);
    let successor=if op.source.is_none(){0usize}else{es[e-1].1};
    let hs2=op.roots(hs,successor,e);
    if let Some(src)=op.source {
        assert(live(w,(src,0)));
        assert(id(w,(src,0))==e);
        assert(successor==next(w(src),0));
    }
    assert forall|r:int| #[trigger] hs2(r)==head(w2(r)) by {};
    assert forall|q:Position| #[trigger] live(w2,q) implies ({
        let value=id(w2,q);
        &&& 0<value<=es2.len()
        &&& es2[value-1].1==next(w2(q.0),q.1)
    }) by {
        positions_backward(op,es,hs,w,q);
        if q==(op.dest,0) {
            assert(id(w2,q)==e);
            assert(next(w2(q.0),q.1)==head(w(q.0)));
        } else {
            let p=op.origin(q).unwrap();
            assert(live(w,p));
            if let Some(src)=op.source {
                assert(p!=(src,0));
                assert(id(w,p)!=id(w,(src,0)));
            }
            assert(id(w,p)!=e);
            assert(next(w2(q.0),q.1)==next(w(p.0),p.1));
        }
    }
    assert forall|p:Position,q:Position| live(w2,p) && live(w2,q)
        && #[trigger] id(w2,p)==#[trigger] id(w2,q) implies p==q by {
        positions_backward(op,es,hs,w,p);
        positions_backward(op,es,hs,w,q);
        if let Some(i)=op.origin(p) {
            if let Some(j)=op.origin(q) {
                assert(id(w,i)==id(w,j));
            } else { assert(id(w,i)<=es.len()); }
        } else if let Some(j)=op.origin(q) { assert(id(w,j)<=es.len()); }
    }
    assert forall|n:usize| 0<n<=es2.len() implies #[trigger] owns(w2,n) by {
        if n<=es.len() {
            assert(owns(w,n));
            let p=choose|p:Position| live(w,p) && #[trigger] id(w,p)==n;
            positions_forward(op,es,hs,w,p);
        } else { assert(id(w2,(op.dest,0))==n); }
    }
}


use kernel::WorkQueue;
pub open spec fn rank<T>(q:&WorkQueue<T>,r:int)->usize {at_rank(q.heads@,q.first_level,r)}
pub open spec fn roots<T>(q:&WorkQueue<T>)->Heads {
    |r:int| if r == -1 {q.free} else {rank(q,r)}
}
pub open spec fn physical<T>(q:&WorkQueue<T>) -> bool {
    &&& q.first_level as int + q.heads.len() <= BucketCount()
    &&& q.cursor <= q.heads.len()
    &&& if q.started { q.cursor < q.heads.len() } else { q.cursor == 0 }
    &&& q.free <= q.entries.len()
    &&& forall|i:int| 0<=i<q.heads.len() ==> #[trigger] q.heads[i] <= q.entries.len()
    &&& forall|r:int| r < q.first_level as int + q.cursor ==> #[trigger] rank(q,r)==0
}
pub open spec fn did_push<T>(a:&WorkQueue<T>,b:&WorkQueue<T>,r:u16,v:T)->bool {
    let old=rank(a,r as int);
    let e=if a.free==0 {a.entries.len() as int+1} else {a.free as int};
    &&& b.entries@ == (if a.free==0 {a.entries@.push((v,old))} else {a.entries@.update(a.free-1,(v,old))})
    &&& b.free == (if a.free==0 {0usize} else {a.entries[a.free-1].1})
    &&& forall|pos:int| #[trigger] rank(b,pos) == (if pos==r as int {e} else {rank(a,pos) as int})
    &&& b.first_level as int + b.heads.len() <= BucketCount()
    &&& b.cursor <= b.heads.len()
    &&& b.cursor == a.cursor && b.started == a.started
    &&& b.started ==> b.cursor < b.heads.len() && b.first_level == a.first_level
    &&& forall|pos:int| pos < b.first_level as int + b.cursor ==> #[trigger] rank(b,pos)==0
}
pub open spec fn did_pop<T>(a:&WorkQueue<T>,b:&WorkQueue<T>,v:Option<T>)->bool {
    if let Some(value)=v {
        let r=b.first_level as int + b.cursor;
        let e=rank(a,r);
        &&& 0<e<=a.entries.len()
        &&& r>=0
        &&& forall|p:int| p<r ==> #[trigger] rank(a,p)==0
        &&& value==a.entries[e-1].0
        &&& b.free==e
        &&& b.entries@==a.entries@.update(e-1,(value,a.free))
        &&& forall|p:int| #[trigger] rank(b,p) == (if p==r {a.entries[e-1].1} else {rank(a,p)})
        &&& b.first_level==a.first_level && b.heads.len()==a.heads.len() && b.cursor<b.heads.len()
        &&& b.started && a.cursor <= b.cursor
    } else {
        &&& forall|r:int| #[trigger] rank(a,r)==0
        &&& b.heads.len()==0 && b.entries.len()==0 && b.free==0 && b.cursor==0 && !b.started
    }
}


pub open spec fn represented<T>(q:&WorkQueue<T>,w:Chains)->bool {
    physical(q) && valid(q.entries@,roots(q),w)
}
pub open spec fn well_formed<T>(q:&WorkQueue<T>)->bool {
    exists |w: Chains| #[trigger] represented(q,w)
}
pub open spec fn payloads<T>(q:&WorkQueue<T>,w:Chains,r:int)->Seq<T> {
    Seq::new(w(r).len(),|i:int| q.entries[w(r)[i]-1].0)
}

proof fn chain_head_is_valid<T>(q:&WorkQueue<T>,w:Chains,r:int)
    requires valid(q.entries@,roots(q),w),
    ensures (roots(q))(r) <= q.entries.len(), ((roots(q))(r)==0) == (w(r).len()==0),
{
    if w(r).len()>0 { assert(live(w,(r,0))); assert(id(w,(r,0))==w(r)[0]); }
}
proof fn valid_roots_in_bounds<T>(q:&WorkQueue<T>,w:Chains)
    requires valid(q.entries@,roots(q),w),
    ensures q.free<=q.entries.len(), forall|i:int| 0<=i<q.heads.len() ==> #[trigger] q.heads[i]<=q.entries.len(),
{
    chain_head_is_valid(q,w,-1);
    assert forall|i:int| 0<=i<q.heads.len() implies #[trigger] q.heads[i]<=q.entries.len() by {
        chain_head_is_valid(q,w,q.first_level as int+i);
    }
}

pub open spec fn no_entries()->Chains { |_:int| Seq::<usize>::empty() }
pub proof fn empty_queue_is_represented<T>(q:&WorkQueue<T>)
    requires q.entries.len()==0 && q.heads.len()==0 && q.free==0 && q.cursor==0 && !q.started,
    ensures represented(q,no_entries()),
{}

pub open spec fn push_op<T>(q:&WorkQueue<T>,r:u16)->Transfer {
    Transfer {source:if q.free==0 {None} else {Some(-1)},dest:r as int}
}
pub proof fn push_preserves_membership<T>(a:&WorkQueue<T>,b:&WorkQueue<T>,r:u16,v:T,w:Chains)
    requires represented(a,w), did_push(a,b,r,v),
    ensures ({
        let op=push_op(a,r);
        let w2=op.updated(w,op.index(a.entries@,w));
        &&& represented(b,w2)
        &&& forall|p:int| p>=0 ==> #[trigger] payloads(b,w2,p)
            == if p==r as int {seq![v]+payloads(a,w,p)} else {payloads(a,w,p)}
    }),
{
    let op=push_op(a,r);
    let e=op.index(a.entries@,w);
    let w2=op.updated(w,e);
    let succ=if a.free==0 {0usize} else {a.entries[e-1].1};
    chain_head_is_valid(a,w,-1);
    assert(op.ok(w));
    assert(op.entries(a.entries@,w,v)==b.entries@) by { assert((roots(a))(r as int)==rank(a,r as int)); }
    assert(roots(b) =~= op.roots(roots(a),succ,e)) by {
        assert forall|p:int| #[trigger] (roots(b))(p) == (op.roots(roots(a),succ,e))(p) by {
            if p != -1 { assert((roots(b))(p)==rank(b,p)); }
        }
    }
    preserves_partition(op,a.entries@,roots(a),w,v);
    valid_roots_in_bounds(b,w2);
    assert forall|p:int| p>=0 implies #[trigger] payloads(b,w2,p)
        == if p==r as int {seq![v]+payloads(a,w,p)} else {payloads(a,w,p)} by {
        let expected=if p==r as int {seq![v]+payloads(a,w,p)} else {payloads(a,w,p)};
        assert(payloads(b,w2,p) =~= expected) by {
            assert forall|i:int| 0<=i<w2(p).len() implies (#[trigger] payloads(b,w2,p)[i])==expected[i] by {
                let pos=(p,i);
                positions_backward(op,a.entries@,roots(a),w,pos);
                if pos!=(r as int,0int) {
                    let old=op.origin(pos).unwrap();
                    if a.free!=0 {
                        assert(id(w,(-1int,0int))==e);
                        assert(id(w,old)!=id(w,(-1int,0int)));
                    }
                    assert(id(w,old)!=e);
                }
            }
        }
    }
}

pub proof fn pop_removes_lowest<T>(a:&WorkQueue<T>,b:&WorkQueue<T>,v:Option<T>,w:Chains)
    requires represented(a,w), did_pop(a,b,v),
    ensures if let Some(value)=v {
        let r=b.first_level as int + b.cursor;
        let op=Transfer {source:Some(r),dest:-1};
        let w2=op.updated(w,op.index(a.entries@,w));
        &&& represented(b,w2)
        &&& payloads(a,w,r).len()>0 && value==payloads(a,w,r)[0]
        &&& forall|p:int| 0<=p<r ==> #[trigger] payloads(a,w,p).len()==0
        &&& forall|p:int| 0<=p ==> #[trigger] payloads(b,w2,p)
            == if p==r {payloads(a,w,r).drop_first()} else {payloads(a,w,p)}
    } else {
        represented(b,no_entries()) && forall|p:int| 0<=p ==> #[trigger] payloads(a,w,p).len()==0
    }
{
    if let Some(value)=v {
        let r=b.first_level as int+b.cursor;
        let op=Transfer {source:Some(r),dest:-1};
        let e=op.index(a.entries@,w);
        let w2=op.updated(w,e);
        let succ=a.entries[e-1].1;
        chain_head_is_valid(a,w,r);
        assert((roots(a))(-1)==a.free);
        assert(op.ok(w));
        assert(op.entries(a.entries@,w,value)==b.entries@);
        assert(roots(b) =~= op.roots(roots(a),succ,e)) by {
            assert forall|p:int| #[trigger] (roots(b))(p) == (op.roots(roots(a),succ,e))(p) by {
                if p != -1 { assert((roots(b))(p)==rank(b,p)); }
            }
        }
        preserves_partition(op,a.entries@,roots(a),w,value);
        valid_roots_in_bounds(b,w2);
        assert forall|p:int| p<r implies #[trigger] rank(b,p)==0 by {};
        assert forall|p:int| 0<=p<r implies #[trigger] payloads(a,w,p).len()==0 by {
            chain_head_is_valid(a,w,p);
        }
        assert forall|p:int| 0<=p implies #[trigger] payloads(b,w2,p)
            == if p==r {payloads(a,w,r).drop_first()} else {payloads(a,w,p)} by {
            let expected=if p==r {payloads(a,w,r).drop_first()} else {payloads(a,w,p)};
            assert(payloads(b,w2,p) =~= expected) by {
                assert forall|i:int| 0<=i<w2(p).len() implies (#[trigger] payloads(b,w2,p)[i])==expected[i] by {
                    positions_backward(op,a.entries@,roots(a),w,(p,i));
                }
            }
        }
    } else {
        empty_queue_is_represented(b);
        assert forall|p:int| 0<=p implies #[trigger] payloads(a,w,p).len()==0 by {
            chain_head_is_valid(a,w,p);
        }
    }
}

/// In a ranked non-flow frame, an unread dependency has a queued entry.
/// Once the production queue pops the lowest available rank, all declared
/// lower-rank reads of that slot can use their already resolved values.
pub proof fn popped_slot_inputs_are_resolved<T>(
    before: &WorkQueue<T>, after: &WorkQueue<T>, selected: T, w: Chains,
    ranks: spec_fn(T) -> u16, inputs: Seq<T>, resolved: spec_fn(T) -> bool,
)
    requires
        represented(before, w), did_pop(before, after, Some(selected)),
        ranks(selected) == after.first_level as int + after.cursor,
        forall |i: int| 0 <= i < inputs.len() ==> ranks(#[trigger] inputs[i]) < ranks(selected),
        forall |i: int| 0 <= i < inputs.len() && !resolved(#[trigger] inputs[i]) ==>
            payloads(before, w, ranks(inputs[i]) as int).contains(inputs[i]),
    ensures forall |i: int| 0 <= i < inputs.len() ==> resolved(#[trigger] inputs[i]),
{
    pop_removes_lowest(before, after, Some(selected), w);
    assert forall |i: int| 0 <= i < inputs.len() implies resolved(#[trigger] inputs[i]) by {
        if !resolved(inputs[i]) {
            let rank = ranks(inputs[i]) as int;
            assert(payloads(before, w, rank).len() == 0);
            assert(payloads(before, w, rank).contains(inputs[i]));
        }
    }
}

}
