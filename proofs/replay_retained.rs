//! Show that a structural replay also preserves the cached complement of its
//! measured region. Prior results outside the region come from the old full
//! execution. Equality at those slots is a conclusion, not a supplied witness.
use vstd::prelude::*;
use super::cycles::{Event, Storage, replay, arguments, kernel::SOLVED};
use super::cycles::dfs::*;
use super::cycles::boundary::{ready_nodes_are_not_rewritten, ready_value_is_retained};
use super::replay_view::{self, Replay, PlaceNode, Draw};
use super::production_schedule as roots;

verus! {

pub struct Edit {
    pub old: Replay,
    pub new: Replay,
}

impl Edit {
    pub open spec fn live(self, k:int) -> bool { 0 <= k < self.new.n }
    pub open spec fn outside(self, k:int) -> bool { self.live(k) && !self.new.inside(k) }

    // Ready constants have no events. Exclude them from the projected task
    // list so that an internal read of a ready boundary cannot perturb it.
    pub open spec fn shell(self, k:int) -> bool {
        self.outside(k) && (self.new.initial_state)(k) != SOLVED
    }

    pub open spec fn same_shell(self) -> bool {
        let a = self.old;
        let b = self.new;
        let shell = |k:int| self.shell(k);
        &&& a.scheduled() && b.scheduled() && a.n == b.n
        &&& forall |k:int| !self.live(k) ==> (#[trigger] (a.edges)(k)).len() == 0
        &&& forall |k:int| !self.live(k) ==> (#[trigger] (b.edges)(k)).len() == 0
        &&& project(a.document().todo,shell) == project(b.document().todo,shell)
        &&& forall |k:int| #[trigger] self.outside(k) ==> ({
            &&& !a.inside(k)
            &&& (a.initial_state)(k) == (b.initial_state)(k)
            &&& a.initial.contains_key(k) && b.initial.contains_key(k)
            &&& a.initial[k] == b.initial[k]
        })
        &&& forall |k:int| (#[trigger] a.inside(k)) == b.inside(k)
        &&& forall |k:int| #[trigger] self.shell(k) ==> ({
            &&& (a.edges)(k) == (b.edges)(k)
            &&& (a.provisional)(k) == (b.provisional)(k)
            &&& forall |args:Seq<Seq<u32>>| #[trigger] (a.eval)(k,args) == (b.eval)(k,args)
        })
    }

    // The runtime cache is the previous result outside the region and freshly
    // prepared inside. Model keys for removed slots may still be present. The
    // view lists the live slots, and never asks for removed output geometry.
    pub open spec fn usable_cache(self) -> bool {
        forall |k:int| #[trigger] self.outside(k)
            ==> self.new.cached.contains_key(k) && self.new.cached[k] == self.old.full_sizing()[k]
    }
}

proof fn same_restricted_program(a:Search, b:Search, edit:Edit, gas:nat)
    requires edit.same_shell(), a.todo == b.todo,
        forall |k:int| #[trigger] edit.shell(k) ==> (a.state)(k) == (b.state)(k),
        forall |i:int| 0 <= i < a.todo.len() ==> edit.shell((#[trigger] a.todo[i]).key()),
    ensures ({
        let shell = |k:int| edit.shell(k);
        &&& drive(a,edit.old.edges,edit.old.provisional,Some(shell),shell,gas)
            == drive(b,edit.new.edges,edit.new.provisional,Some(shell),shell,gas)
    }),
    decreases gas,
{
    if a.todo.len() > 0 && gas > 0 {
        let shell = |k:int| edit.shell(k);
        let task = a.todo.first();
        assert(task == a.todo[0]);
        let old = step(a,edit.old.edges,edit.old.provisional,Some(shell));
        let new = step(b,edit.new.edges,edit.new.provisional,Some(shell));
        assert(old.event == new.event);
        assert(old.next.todo == new.next.todo);
        if task is Visit && fresh(a,task.key()) {
            let deps = requests((edit.old.edges)(task.key()));
            let retained = project(deps,shell);
            forall_projected_in_scope(deps,shell);
            assert forall |i:int| 0 <= i < old.next.todo.len() implies edit.shell((#[trigger] old.next.todo[i]).key()) by {
                if i < retained.len() { assert(old.next.todo[i] == retained[i]); }
                else if i == retained.len() { assert(old.next.todo[i].key() == task.key()); }
                else { assert(old.next.todo[i] == a.todo[i - retained.len()]); }
            }
        } else {
            assert forall |i:int| 0 <= i < old.next.todo.len() implies edit.shell((#[trigger] old.next.todo[i]).key()) by {
                assert(old.next.todo[i] == a.todo[i+1]);
            }
        }
        assert forall |k:int| #[trigger] edit.shell(k) implies (old.next.state)(k) == (new.next.state)(k) by {};
        same_restricted_program(old.next,new.next,edit,(gas-1) as nat);
    }
}

proof fn forall_projected_in_scope(todo:Seq<Task>, scope:Region)
    ensures forall |i:int| 0 <= i < project(todo,scope).len() ==> scope((#[trigger] project(todo,scope)[i]).key()),
    decreases todo.len(),
{
    if todo.len() > 0 {
        let t = todo.first();
        let tail = project(todo.drop_first(),scope);
        forall_projected_in_scope(todo.drop_first(),scope);
        assert forall |i:int| 0 <= i < project(todo,scope).len()
            implies scope((#[trigger] project(todo,scope)[i]).key()) by {
            if scope(t.key()) {
                if i > 0 { assert(project(todo,scope)[i] == tail[i-1]); }
                else { assert(project(todo,scope)[i] == t); }
            } else { assert(project(todo,scope)[i] == tail[i]); }
        }
    }
}

proof fn shell_is_isolated(r:Replay, edit:Edit)
    requires edit.same_shell(), r == edit.old || r == edit.new,
    ensures isolated(r.document(),r.edges,|k:int| edit.shell(k)),
{
    assert forall |k:int,j:int| !edit.shell(k)
        && !(super::cycles::kernel::enter((r.initial_state)(k)) is Reuse)
        && !(super::cycles::kernel::enter((r.initial_state)(k)) is BackEdge)
        && 0 <= j < (r.edges)(k).len() implies !edit.shell(#[trigger] (r.edges)(k)[j]) by {
        assert(!edit.live(k) ==> (r.edges)(k).len() == 0);
        assert(edit.live(k));
        assert(!edit.outside(k));
        let dep = (r.edges)(k)[j];
        if edit.shell(dep) {
            assert(!r.inside(dep));
            assert(r.pinned(dep));
        }
    }
}

proof fn shell_events(r:Replay, edit:Edit, gas:nat)
    requires edit.same_shell(), r == edit.old || r == edit.new, r.gas() <= gas,
    ensures ({
        let shell = |k:int| edit.shell(k);
        let restricted = Search { todo: project(r.document().todo,shell), state:r.initial_state };
        drive(restricted,r.edges,r.provisional,Some(shell),shell,gas).0 == visible(r.full_events(),shell)
    }),
{
    let shell = |k:int| edit.shell(k);
    let partial = Search { todo: project(r.document().todo,shell), state:r.initial_state };
    shell_is_isolated(r,edit);
    finite_full_dfs_finishes(r.document(),r.edges,r.provisional,shell,r.n,r.gas());
    visibility_is_event_filter(r.document(),r.edges,r.provisional,shell,r.gas());
    restricted_dfs_generates_canonical_events(r.document(),partial,r.edges,r.provisional,shell,r.gas(),gas);
}

proof fn shell_reads_pinned(r:Replay, edit:Edit, events:Seq<Event>)
    requires edit.same_shell(), r == edit.old || r == edit.new,
        forall |i:int| 0 <= i < events.len() ==> ({
            let e = #[trigger] events[i];
            &&& (r.initial_state)(e.target()) != SOLVED
            &&& e is Finish ==> e.inputs() == (r.edges)(e.target())
        }),
    ensures boundary_cache(events,r.initial,r.initial,|k:int| edit.shell(k),r.eval),
    decreases events.len(),
{
    if events.len() > 0 {
        let before = events.drop_last();
        let e = events.last();
        assert(e == events[events.len()-1]);
        assert forall |j:int| 0 <= j < before.len() implies ({
            let a = #[trigger] before[j];
            &&& (r.initial_state)(a.target()) != SOLVED
            &&& a is Finish ==> a.inputs() == (r.edges)(a.target())
        }) by { assert(before[j] == events[j]); }
        shell_reads_pinned(r,edit,before);
        let deps = e.inputs();
        if edit.shell(e.target()) {
            assert forall |i:int| 0 <= i < deps.len() && !edit.shell(#[trigger] deps[i]) implies ({
                let k = deps[i];
                let prior = replay(before,r.initial,r.eval);
                &&& prior.contains_key(k) && r.initial.contains_key(k)
                &&& prior[k] == r.initial[k]
            }) by {
                assert(e is Finish);
                assert(deps == (r.edges)(e.target()));
                let k = deps[i];
                assert(edit.outside(k));
                assert((r.initial_state)(k) == SOLVED);
                assert forall |j:int| 0 <= j < before.len() implies (#[trigger] before[j]).target() != k by {};
                ready_value_is_retained(before,r.initial,r.eval,k);
            }
        }
    }
}

proof fn same_shell_values(events:Seq<Event>, edit:Edit, k:int)
    requires edit.same_shell(), edit.outside(k),
        forall |i:int| 0 <= i < events.len() ==> ({
            let e = #[trigger] events[i];
            &&& edit.shell(e.target())
            &&& e is Finish ==> e.inputs() == (edit.new.edges)(e.target())
        }),
    ensures
        replay(events,edit.old.initial,edit.old.eval).contains_key(k),
        replay(events,edit.new.initial,edit.new.eval).contains_key(k),
        replay(events,edit.old.initial,edit.old.eval)[k] == replay(events,edit.new.initial,edit.new.eval)[k],
    decreases events.len(),
{
    if events.len() > 0 {
        let before = events.drop_last();
        let e = events.last();
        assert(e == events[events.len()-1]);
        assert forall |j:int| 0 <= j < before.len() implies ({
            let a = #[trigger] before[j];
            &&& edit.shell(a.target())
            &&& a is Finish ==> a.inputs() == (edit.new.edges)(a.target())
        }) by { assert(before[j] == events[j]); }
        if e.target() != k { same_shell_values(before,edit,k); }
        else if e is Finish {
            let deps = e.inputs();
            let a = replay(before,edit.old.initial,edit.old.eval);
            let b = replay(before,edit.new.initial,edit.new.eval);
            assert(arguments(deps,a) =~= arguments(deps,b)) by {
                assert forall |j:int| 0 <= j < deps.len() implies a[#[trigger] deps[j]] == b[deps[j]] by {
                    assert(deps == (edit.new.edges)(k));
                    assert(edit.outside(deps[j]));
                    same_shell_values(before,edit,deps[j]);
                }
            }
        }
    }
}

pub proof fn cached_complement_matches_the_new_document(edit:Edit, k:int)
    requires edit.same_shell(), edit.outside(k),
    ensures edit.old.full_sizing().contains_key(k), edit.new.full_sizing().contains_key(k),
        edit.old.full_sizing()[k] == edit.new.full_sizing()[k],
{
    let shell = |k:int| edit.shell(k);
    let a = edit.old;
    let b = edit.new;
    let common_gas = if a.gas() > b.gas() { a.gas() } else { b.gas() };
    let pruned = project(a.document().todo,shell);
    let sa = Search { todo:pruned, state:a.initial_state };
    let sb = Search { todo:pruned, state:b.initial_state };
    let ready_a = |i:int| (a.initial_state)(i) == SOLVED;
    let ready_b = |i:int| (b.initial_state)(i) == SOLVED;
    ready_nodes_are_not_rewritten(a.document(),a.edges,a.provisional,ready_a,a.gas());
    ready_nodes_are_not_rewritten(b.document(),b.edges,b.provisional,ready_b,b.gas());
    // Unchanged pre-seeded words can be used directly.
    if !edit.shell(k) {
        ready_value_is_retained(a.full_events(),a.initial,a.eval,k);
        ready_value_is_retained(b.full_events(),b.initial,b.eval,k);
    } else {
        shell_events(a,edit,common_gas);
        shell_events(b,edit,common_gas);
        forall_projected_in_scope(a.document().todo,shell);
        same_restricted_program(sa,sb,edit,common_gas);
        shell_reads_pinned(a,edit,a.full_events());
        shell_reads_pinned(b,edit,b.full_events());
        replay_projection(a.full_events(),a.initial,a.initial,shell,a.eval,k);
        replay_projection(b.full_events(),b.initial,b.initial,shell,b.eval,k);
        let events = visible(b.full_events(),shell);
        projection_keeps_event_facts(b.full_events(),edit);
        same_shell_values(events,edit,k);
    }
}

proof fn projection_keeps_event_facts(events:Seq<Event>, edit:Edit)
    requires forall |i:int| 0 <= i < events.len() ==> ({
        let e = #[trigger] events[i];
        e is Finish ==> e.inputs() == (edit.new.edges)(e.target())
    }),
    ensures ({
        let kept = visible(events,|k:int| edit.shell(k));
        forall |i:int| 0 <= i < kept.len() ==> ({
            let e = #[trigger] kept[i];
            &&& edit.shell(e.target())
            &&& e is Finish ==> e.inputs() == (edit.new.edges)(e.target())
        })
    }),
    decreases events.len(),
{
    if events.len() > 0 {
        let tail = events.drop_first();
        let head = events.first();
        let kept = visible(events,|k:int| edit.shell(k));
        assert(head == events[0]);
        assert forall |i:int| 0 <= i < tail.len() implies ({
            let e = #[trigger] tail[i];
            e is Finish ==> e.inputs() == (edit.new.edges)(e.target())
        }) by { assert(tail[i] == events[i+1]); }
        projection_keeps_event_facts(tail,edit);
        assert forall |i:int| 0 <= i < kept.len() implies ({
            let e = #[trigger] kept[i];
            &&& edit.shell(e.target())
            &&& e is Finish ==> e.inputs() == (edit.new.edges)(e.target())
        }) by {
            if edit.shell(head.target()) && i == 0 { assert(kept[i] == head); }
        }
    }
}

pub proof fn edited_document_producer_is_exact(edit:Edit, k:int)
    requires edit.same_shell(), edit.new.closed(), edit.usable_cache(), edit.live(k),
    ensures edit.new.rebuilt_sizing().contains_key(k), edit.new.full_sizing().contains_key(k),
        edit.new.rebuilt_sizing()[k] == edit.new.full_sizing()[k],
{
    let b = edit.new;
    if b.inside(k) {
        replay_view::rebuilt_producers_match_the_document(b,k);
    } else {
        assert(edit.outside(k));
        assert(b.cached.contains_key(k));
        assert(b.cached[k] == edit.old.full_sizing()[k]);
        cached_complement_matches_the_new_document(edit,k);
        let region = |i:int| b.inside(i);
        ready_nodes_are_not_rewritten(b.document(),b.edges,b.provisional,|i:int| b.pinned(i),b.gas());
        replay_view::reads_pinned_values(b,b.full_events());
        replay_view::match_region_events(b);
        replay_projection(b.full_events(),b.initial,b.cached,region,b.eval,k);
        assert(b.rebuilt_events() == visible(b.full_events(),region));
        assert(b.rebuilt_sizing().contains_key(k));
        assert(b.rebuilt_sizing()[k] == b.cached[k]);
    }
}

/// Compare the whole visible document after a localized replay, including
/// rectangles that read retained producer words outside the rebuilt region.
pub proof fn mixed_mode_edit_rebuilds_the_view(edit:Edit, nodes:Seq<PlaceNode>, draw:Draw)
    requires edit.same_shell(), edit.new.closed(), edit.usable_cache(),
        forall |i:int,j:int| 0 <= i < nodes.len() && 0 <= j < nodes[i].inputs.len()
            ==> edit.live((#[trigger] nodes[i].inputs[j]).producer),
    ensures replay_view::place_frame(nodes,edit.new.rebuilt_sizing(),draw)
        == replay_view::place_frame(nodes,edit.new.full_sizing(),draw),
    decreases nodes.len(),
{
    if nodes.len() > 0 {
        let prior = nodes.drop_last();
        assert forall |i:int,j:int| 0 <= i < prior.len() && 0 <= j < prior[i].inputs.len() implies
            edit.live((#[trigger] prior[i].inputs[j]).producer) by { assert(prior[i] == nodes[i]); }
        mixed_mode_edit_rebuilds_the_view(edit,prior,draw);
        let last = nodes.last();
        assert(last == nodes[nodes.len()-1]);
        let a = edit.new.rebuilt_sizing();
        let b = edit.new.full_sizing();
        assert(replay_view::words(a,last) =~= replay_view::words(b,last)) by {
            assert forall |i:int| 0 <= i < last.inputs.len() implies
                replay_view::words(a,last)[i] == replay_view::words(b,last)[i] by {
                edited_document_producer_is_exact(edit,last.inputs[i].producer);
            }
        }
    }
}

}
