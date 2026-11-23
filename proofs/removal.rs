//! Allocation-free removal of an owned detached subtree.
use vstd::prelude::*;
#[path = "../src/layout_tree/removal.rs"]
mod kernel;

verus! {

// Siblings are listed in the order the remover follows them, rightmost first.
pub enum Forest<I> {
    Empty,
    Node { id:I, children:Box<Forest<I>>, siblings:Box<Forest<I>> },
}

pub struct Record<I,V> {
    pub prev:Option<I>,
    pub first:Option<I>,
    pub last:Option<I>,
    // Includes the parent, next sibling and all other data preserved by a splice.
    pub payload:V,
}

pub type Store<I,V> = Map<I,Record<I,V>>;

pub open spec fn ids<I>(f:Forest<I>) -> Set<I>
    decreases f,
{
    match f {
        Forest::Empty => Set::empty(),
        Forest::Node{id,children,siblings} => ids(*children).union(ids(*siblings)).insert(id),
    }
}

pub open spec fn proper<I>(f:Forest<I>) -> bool
    decreases f,
{
    match f {
        Forest::Empty => true,
        Forest::Node{id,children,siblings} =>
            !ids(*children).contains(id) && !ids(*siblings).contains(id) && ids(*children).disjoint(ids(*siblings))
            && proper(*children) && proper(*siblings),
    }
}

pub open spec fn order<I>(f:Forest<I>) -> Seq<I>
    decreases f,
{
    match f {
        Forest::Empty => Seq::empty(),
        Forest::Node{id,children,siblings} => seq![id] + order(*children) + order(*siblings),
    }
}

pub open spec fn head<I>(f:Forest<I>, end:Option<I>) -> Option<I> {
    match f { Forest::Empty => end, Forest::Node{id,..} => Some(id) }
}

pub open spec fn oldest<I>(f:Forest<I>) -> Option<I>
    decreases f,
{
    match f {
        Forest::Empty => None,
        Forest::Node{id,siblings,..} => if *siblings is Empty {Some(id)} else {oldest(*siblings)},
    }
}

pub open spec fn stores<I,V>(s:Store<I,V>, f:Forest<I>, end:Option<I>) -> bool
    decreases f,
{
    match f {
        Forest::Empty => true,
        Forest::Node{id,children,siblings} => {
            &&& s.contains_key(id)
            &&& s[id].prev == head(*siblings,end)
            &&& s[id].first == oldest(*children)
            &&& s[id].last == head(*children,None)
            &&& stores(s,*children,None)
            &&& stores(s,*siblings,end)
        },
    }
}

pub open spec fn erase<I,V>(s:Store<I,V>, gone:Set<I>) -> Store<I,V> {
    Map::new(s.dom().difference(gone), |id:I| s[id])
}

proof fn local<I,V>(s:Store<I,V>, t:Store<I,V>, f:Forest<I>, end:Option<I>)
    requires stores(s,f,end),
        forall |id:I| #[trigger] ids(f).contains(id) ==> s.contains_key(id) && t.contains_key(id) && t[id] == s[id],
    ensures stores(t,f,end),
    decreases f,
{
    if let Forest::Node{id,children,siblings} = f {
        assert(ids(f).contains(id));
        assert(t.contains_key(id) && t[id] == s[id]);
        assert forall |j:I| #[trigger] ids(*children).contains(j) implies s.contains_key(j) && t.contains_key(j) && t[j]==s[j] by {
            assert(ids(f).contains(j));
        }
        assert forall |j:I| #[trigger] ids(*siblings).contains(j) implies s.contains_key(j) && t.contains_key(j) && t[j]==s[j] by {
            assert(ids(f).contains(j));
        }
        local(s,t,*children,None);
        local(s,t,*siblings,end);
        assert(stores(t,f,end));
    }
}

proof fn contains_records<I,V>(s:Store<I,V>, f:Forest<I>, end:Option<I>)
    requires stores(s,f,end),
    ensures forall |j:I| #[trigger] ids(f).contains(j) ==> s.contains_key(j),
    decreases f,
{
    if let Forest::Node{id,children,siblings} = f {
        contains_records(s,*children,None);
        contains_records(s,*siblings,end);
        assert forall |j:I| #[trigger] ids(f).contains(j) implies s.contains_key(j) by {
            if j == id {
                assert(s.contains_key(id));
            } else if ids(*children).contains(j) {
                assert(s.contains_key(j));
            } else {
                assert(ids(*siblings).contains(j));
            }
        }
    }
}

proof fn oldest_in_forest<I>(f:Forest<I>)
    ensures oldest(f).is_some() == !(f is Empty),
        oldest(f).is_some() ==> ids(f).contains(oldest(f).unwrap()),
    decreases f,
{
    if let Forest::Node{siblings,..} = f {oldest_in_forest(*siblings);}
}

pub open spec fn redirect<I,V>(s:Store<I,V>, id:I, end:Option<I>) -> Store<I,V> {
    s.insert(id,Record{prev:end,..s[id]})
}

// Only the leftmost sibling in this forest used to point to old. Replacing its
// prev link gives the entire forest a new successor at the end of its root list.
proof fn splice<I,V>(s:Store<I,V>, f:Forest<I>, old:Option<I>, end:Option<I>)
    requires stores(s,f,old), proper(f), !(f is Empty),
    ensures stores(redirect(s,oldest(f).unwrap(),end),f,end),
    decreases f,
{
    if let Forest::Node{id,children,siblings} = f {
        oldest_in_forest(*siblings);
        let at = oldest(f).unwrap();
        let updated = redirect(s,at,end);
        contains_records(s,*children,None);
        assert forall |j:I| #[trigger] ids(*children).contains(j) implies s.contains_key(j) && updated.contains_key(j) && updated[j] == s[j] by {
            assert(j != at);
        }
        local(s,updated,*children,None);
        if *siblings is Empty {
            assert(at == id);
            assert(updated[id].prev == end);
            assert(updated[id].first == s[id].first && updated[id].last == s[id].last);
        } else {
            assert(at == oldest(*siblings).unwrap());
            assert(ids(*siblings).contains(at));
            assert(at != id);
            splice(s,*siblings,old,end);
            assert(stores(updated,*siblings,end));
            assert(updated.contains_key(id) && updated[id] == s[id]);
        }
        assert(updated.contains_key(id));
        assert(updated[id].prev == head(*siblings,end)) by {
            assert(s[id].prev == head(*siblings,old));
            if let Forest::Node{id:next,..} = *siblings {
                assert(head(*siblings,old) == Some(next));
                assert(head(*siblings,end) == Some(next));
            }
        }
        assert(updated[id].first == oldest(*children));
        assert(updated[id].last == head(*children,None));
        assert(stores(updated,*children,None));
        assert(stores(updated,*siblings,end));
        assert(stores(updated,f,end));
    }
}

pub struct State<I,V> { pub cursor:Option<I>, pub nodes:Store<I,V> }

pub open spec fn pop<I,V>(s:State<I,V>, id:I) -> State<I,V> {
    let r = s.nodes[id];
    let rest = s.nodes.remove(id);
    match r.first {
        None => State {cursor:r.prev,nodes:rest},
        Some(first) => State {cursor:r.last,nodes:redirect(rest,first,r.prev)},
    }
}

pub open spec fn safe_pop<I,V>(s:State<I,V>, id:I) -> bool {
    &&& s.cursor == Some(id)
    &&& s.nodes.contains_key(id)
    &&& match s.nodes[id].first {
        Some(first) => first != id && s.nodes.contains_key(first),
        None => true,
    }
}

// A successful replay certifies the cursor at every step and the validity of
// both arena accesses (removal and the optional continuation splice).
pub open spec fn replay<I,V>(s:State<I,V>, plan:Seq<I>) -> Option<State<I,V>>
    decreases plan.len(),
{
    if plan.len() == 0 { Some(s) }
    else if safe_pop(s,plan.first()) { replay(pop(s,plan.first()),plan.drop_first()) }
    else { None }
}

proof fn replay_append<I,V>(s:State<I,V>, a:Seq<I>, b:Seq<I>, mid:State<I,V>)
    requires replay(s,a) == Some(mid),
    ensures replay(s,a+b) == replay(mid,b),
    decreases a.len(),
{
    if a.len() > 0 {
        assert((a+b).first() == a.first());
        assert((a+b).drop_first() =~= a.drop_first() + b);
        replay_append(pop(s,a.first()),a.drop_first(),b,mid);
    }
}

pub proof fn forest_replays<I,V>(s:Store<I,V>, f:Forest<I>, end:Option<I>)
    requires proper(f), stores(s,f,end),
    ensures replay(State{nodes:s,cursor:head(f,end)}, order(f))
        == Some(State{nodes:erase(s,ids(f)),cursor:end}),
    decreases f,
{
    if let Forest::Node{id,children,siblings} = f {
        let after = head(*siblings,end);
        let initial = State{nodes:s,cursor:Some(id)};
        let rest = s.remove(id);
        contains_records(s,*children,None);
        contains_records(s,*siblings,end);
        oldest_in_forest(*children);
        local(s,rest,*children,None);
        local(s,rest,*siblings,end);
        let next = pop(initial,id);
        if !(*children is Empty) {
            splice(rest,*children,None,after);
        }
        assert(safe_pop(initial,id));
        assert(stores(next.nodes,*children,after));
        assert(next.cursor == head(*children,after));
        forest_replays(next.nodes,*children,after);
        let after_children = erase(next.nodes,ids(*children));
        assert forall |j:I| #[trigger] ids(*siblings).contains(j) implies
            s.contains_key(j) && after_children.contains_key(j) && after_children[j] == s[j] by {
            assert(j != id && !ids(*children).contains(j));
        }
        local(s,after_children,*siblings,end);
        let mid = State{nodes:after_children,cursor:after};
        forest_replays(after_children,*siblings,end);
        replay_append(next,order(*children),order(*siblings),mid);
        assert(order(f).first() == id);
        assert(order(f).drop_first() =~= order(*children) + order(*siblings));
        assert(erase(after_children,ids(*siblings)) =~= erase(s,ids(f)));
    } else {
        assert(erase(s,ids(f)) =~= s);
    }
}

pub open spec fn detached<I>(id:I, children:Forest<I>) -> Forest<I> {
    Forest::Node{id,children:Box::new(children),siblings:Box::new(Forest::Empty)}
}
}
