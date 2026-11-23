//! Slot dependencies of the acyclic, non-flow measurement queue.
//! The two traversals enumerate the same neighborhood in opposite directions.
use vstd::prelude::*;
#[path = "../src/dependency_rules.rs"]
pub(crate) mod rules;
use rules::{Form, Input};
#[path = "../src/sizing_stack.rs"]
pub(crate) mod sizing_stack;
#[path = "../src/registration_rules.rs"]
mod registration;
use registration::{AxisEdits, Context, Seeds};

verus! {

pub enum ParentRequest { Final(bool), LineExtent }

/// `false` denotes the requested axis and `true` its opposite. This uses
/// the same request expansion as `request_available_from_parent`.
pub fn parent_requests(in_flow:bool, wrap_cross:bool, width_grid_other:bool) -> (requests:Vec<ParentRequest>)
    ensures requests@ == if in_flow && wrap_cross { seq![ParentRequest::LineExtent] }
        else if in_flow && width_grid_other { seq![ParentRequest::Final(false),ParentRequest::Final(true)] }
        else { seq![ParentRequest::Final(false)] },
{
    use rules::request_parent_inputs;
    let mut out = Vec::new();
    request_parent_inputs!(
        in_flow && wrap_cross;
        rules::reads_parent_axis(false,in_flow,width_grid_other);
        other => { out.push(ParentRequest::Final(other)); };
        { out.push(ParentRequest::LineExtent); }
    );
    out
}

pub enum Part { Declared(Form), Final, Share }

/// Relationship of the input node to the reader node.
pub enum Source { SameNode, Parent, Child, Elsewhere }

pub struct Edge {
    pub source: Source,
    pub same_axis: bool,
    /// The child at either end is placed in flow.
    pub in_flow: bool,
    /// Stack main axis of the share owner or the parent allocating the child's size.
    pub stack_axis: bool,
    pub child_has_fill: bool,
    /// The producing axis is the main axis of a width grid.
    pub grid_main: bool,
    pub intrinsic_other: bool,
}

impl Edge {
    pub open spec fn stack_item(self) -> bool {
        self.in_flow && self.stack_axis
    }
}

/// The dependency request issued by the full solver, dispatched on the reader.
/// Only present declarations and main-axis stack share slots can be requested.
pub open spec fn full_read(reader: Part, input: Part, e: Edge) -> bool {
    match reader {
        Part::Final => e.source is SameNode && e.same_axis && input is Declared,
        Part::Share => e.stack_axis && e.same_axis && match e.source {
            Source::SameNode => input is Final,
            Source::Child => e.in_flow && (if e.child_has_fill {
                match input { Part::Declared(form) => form.contributes_to_share(), _ => false }
            } else { input is Final }),
            _ => false,
        },
        Part::Declared(form) => match form.input(e.stack_item()) {
            Input::None => false,
            Input::OppositeFinal => e.source is SameNode && !e.same_axis && input is Final,
            Input::ParentFinal => e.source is Parent && input is Final
                && (e.same_axis || rules::reads_parent_axis(false, e.in_flow, e.grid_main)),
            Input::ParentShare => e.source is Parent && e.same_axis && input is Share,
            Input::IntrinsicChildren => match e.source {
                Source::SameNode => !e.same_axis && input is Final
                    && rules::reads_intrinsic_constraint(e.intrinsic_other, e.grid_main),
                Source::Child => e.in_flow && e.same_axis && match input {
                    Part::Declared(child) => child.contributes_to_intrinsic(),
                    _ => false,
                },
                _ => false,
            }
        }
    }
}

/// Queue notification dispatched on the changed input as in queue_dependents.
pub open spec fn notifies(input: Part, reader: Part, e: Edge) -> bool {
    match input {
        Part::Share => e.source is Parent && e.same_axis && e.stack_item()
            && match reader { Part::Declared(form) => form.input(true) is ParentShare, _ => false },
        Part::Final => match e.source {
            Source::SameNode => match reader {
                Part::Declared(form) => !e.same_axis && form.reads_opposite_final(
                    rules::reads_intrinsic_constraint(e.intrinsic_other, e.grid_main)),
                Part::Share => e.same_axis && e.stack_axis,
                _ => false,
            },
            Source::Parent => rules::reads_parent_axis(e.same_axis, e.in_flow, e.grid_main)
                && match reader { Part::Declared(form) => form.input(e.stack_item()) is ParentFinal, _ => false },
            Source::Child => e.same_axis && e.stack_item() && !e.child_has_fill && reader is Share,
            _ => false,
        },
        Part::Declared(form) => e.same_axis && match e.source {
            Source::SameNode => reader is Final,
            Source::Child => e.in_flow && match reader {
                Part::Share => e.stack_axis && e.child_has_fill && form.contributes_to_share(),
                Part::Declared(target) => target is Intrinsic && form.contributes_to_intrinsic(),
                _ => false,
            },
            _ => false,
        },
    }
}

pub proof fn every_read_and_only_reads_are_notified(reader: Part, input: Part, e: Edge)
    ensures full_read(reader, input, e) == notifies(input, reader, e),
{
    match reader {
        Part::Declared(form) => match form {
            Form::Constant | Form::Ratio | Form::Fraction | Form::Fill | Form::Intrinsic => {},
        },
        _ => {},
    }
}

/// Contract of the actual classifier against each size category. In particular a
/// weighted fill goes through the share only when it participates in its stack.
pub proof fn declaration_sources(form: Form, stack_item: bool)
    ensures
        (form.input(stack_item) is None) == (form is Constant),
        (form.input(stack_item) is OppositeFinal) == (form is Ratio),
        (form.input(stack_item) is ParentFinal) == (form is Fraction || form is Fill && !stack_item),
        (form.input(stack_item) is ParentShare) == (form is Fill && stack_item),
        (form.input(stack_item) is IntrinsicChildren) == (form is Intrinsic),
        form.contributes_to_intrinsic() == (form is Constant || form is Ratio || form is Intrinsic),
        form.contributes_to_share() == !(form is Fill),
{}

pub proof fn ranked_notification(input: u16, reader: u16)
    requires reader >= rules::next_level(input),
    ensures
        rules::queueable(reader) ==> input < reader,
        !rules::queueable(input) ==> !rules::queueable(reader),
        rules::next_level(input) as int == if input < u16::MAX { input as int + 1 } else { u16::MAX as int },
{}

/// Local (non-slot) inputs that can change without changing the dependency graph.
/// Inner dimensions combine padding and spacing on this axis; changing width-grid
/// metrics also changes track allocation on the opposite axis.
pub enum LocalInput {
    Inner, OtherInner, Content, Margin, Weight, Fraction,
    Declaration, Window,
}

pub enum Consumer {
    Own(Part), Parent(Part), Child(Form), Other,
}

pub struct Role {
    pub target: Consumer,
    pub child_stack_item: bool,
    pub matching_declaration: bool,
    pub root: bool,
}

pub open spec fn changed(field: LocalInput, e: AxisEdits, declaration: bool, viewport: bool) -> bool {
    match field {
        LocalInput::Inner => e.inner,
        LocalInput::OtherInner => e.other_inner,
        LocalInput::Content => e.content,
        LocalInput::Margin => e.margin,
        LocalInput::Weight => e.weight,
        LocalInput::Fraction => e.regular_fraction,
        LocalInput::Declaration => declaration,
        LocalInput::Window => viewport,
    }
}

/// Direct numeric reads of the evaluators, described by the *reader*, independent
/// of the edit-to-seed dispatch. Some readers are deliberately conservative.
pub open spec fn reads_local(field: LocalInput, role: Role, c: Context) -> bool {
    match role.target {
        Consumer::Own(Part::Declared(f)) => {
            ||| field is Declaration && role.matching_declaration
            ||| field is Window && role.root && (f is Fill || f is Fraction)
            ||| f is Intrinsic && (field is Content || field is Inner
                || field is OtherInner && (c.width_grid || c.wraps_text))
            ||| f is Fill && c.in_flow && (field is Margin && c.placed_parent
                || field is Weight && c.parent_stack_axis)
        }
        Consumer::Own(Part::Final) => c.grid_main && (field is Inner || field is OtherInner),
        Consumer::Own(Part::Share) => c.stack_axis && field is Inner,
        Consumer::Parent(Part::Declared(f)) => f is Intrinsic && c.in_flow
            && (field is Margin && c.placed_parent || field is Fraction),
        Consumer::Parent(Part::Share) => c.parent_stack_axis && c.in_flow
            && (field is Weight || field is Margin && c.placed_parent),
        Consumer::Child(f) => (f is Fraction || (f is Fill && !role.child_stack_item))
            && (field is Inner || c.width_grid && field is OtherInner),
        _ => false,
    }
}

pub open spec fn is_seeded(role: Role, work: Seeds, declaration: bool, viewport: bool) -> bool {
    match role.target {
        Consumer::Own(Part::Declared(f)) => role.matching_declaration && declaration
            || viewport && role.root && (f is Fill || f is Fraction)
            || f is Fill && work.own_fill || f is Intrinsic && work.own_intrinsic,
        Consumer::Own(Part::Final) => work.own_final,
        Consumer::Own(Part::Share) => work.own_share,
        Consumer::Parent(Part::Declared(f)) => work.parent_intrinsic && f is Intrinsic,
        Consumer::Parent(Part::Share) => work.parent_share,
        Consumer::Child(f) => work.child_available && f.input(role.child_stack_item) is ParentFinal,
        _ => false,
    }
}

/// Every edited direct input is sufficient to seed its reader, even if unrelated
/// edits are batched into the same axis flags and multiple slots have the same form.
pub proof fn registered_local_read_is_seeded(field: LocalInput, role: Role, c: Context,
    e: AxisEdits, declaration: bool, viewport: bool)
    requires changed(field,e,declaration,viewport), reads_local(field,role,c),
    ensures is_seeded(role,e.seeds(c),declaration,viewport),
{}

pub proof fn host_inputs_register_content(image: bool, custom: bool, padding: bool, maximum: bool)
    ensures
        image ==> registration::content_input_changed(image,custom,padding,maximum),
        custom && (padding || maximum) ==> registration::content_input_changed(image,custom,padding,maximum),
{}

/// Reports from distinct edits, nodes, axes and input classes contribute by
/// union. Multiple changed inputs may legitimately notify the same slot.
pub struct Edit {
    pub axis:AxisEdits,
    pub c:Context,
    pub declaration:bool,
    pub viewport:bool,
    pub role:spec_fn(int)->Role,
}
pub open spec fn edit_read(e:Edit, field:LocalInput, r:int) -> bool {
    changed(field,e.axis,e.declaration,e.viewport) && reads_local(field,(e.role)(r),e.c)
}
pub open spec fn reader_changed(edits:Seq<Edit>, r:int) -> bool {
    exists|i:int, field:LocalInput| 0 <= i < edits.len() && #[trigger] edit_read(edits[i],field,r)
}
pub open spec fn batch_seeds(edits:Seq<Edit>, n:nat) -> Set<int>
    decreases n,
{
    if n == 0 { Set::empty() }
    else {
        let r = n-1;
        let prior = batch_seeds(edits,r as nat);
        if exists|i:int| 0 <= i < edits.len() && ({
            let e = #[trigger] edits[i];
            is_seeded((e.role)(r),e.axis.seeds(e.c),e.declaration,e.viewport)
        }) { prior.insert(r) } else { prior }
    }
}
pub proof fn batch_registers_every_reader(edits:Seq<Edit>, n:nat, r:int)
    requires 0 <= r < n, reader_changed(edits,r),
    ensures batch_seeds(edits,n).contains(r),
    decreases n,
{
    if r < n-1 { batch_registers_every_reader(edits,(n-1) as nat,r); }
    else {
        let (i,field) = choose|i:int,field:LocalInput| 0 <= i < edits.len() && #[trigger] edit_read(edits[i],field,r);
        let e=edits[i];
        registered_local_read_is_seeded(field,(e.role)(r),e.c,e.axis,e.declaration,e.viewport);
    }
}

pub proof fn sizing_edit_has_a_consumer(pending:bool, cyclic:bool, structural:bool, flow:bool, at_limit:bool)
    ensures ({
        let action=registration::intake(pending,cyclic,structural,flow,at_limit);
        &&& (action is Queue) == (!pending && !cyclic && !structural && !flow && !at_limit)
        &&& (action is Pending) ==> pending
        &&& (action is Cycle) ==> cyclic
        &&& (action is Region) ==> structural
        &&& (action is Flow) ==> flow
        &&& (action is Budget) ==> at_limit
    }),
{}

// Ordered dependencies are stable during a successful numeric queue pass. A
// value includes every observable result of finishing a slot (e.g. grid shape).
pub type Datum = Seq<u32>;
pub type Locals = Seq<Seq<int>>;

pub struct Graph {
    pub parts: Seq<Part>,
    pub reads: Seq<Seq<int>>,
    pub neighborhood: spec_fn(int, int) -> Edge,
    pub eval: spec_fn(int, Seq<int>, Seq<Datum>) -> Datum,
}

impl Graph {
    pub open spec fn valid(self) -> bool {
        &&& self.parts.len() == self.reads.len()
        &&& forall|r: int, k: int| 0 <= r < self.parts.len() && 0 <= k < self.reads[r].len()
            ==> ({
                let s = #[trigger] self.reads[r][k];
                &&& 0 <= s < r
                &&& full_read(self.parts[r], self.parts[s], (self.neighborhood)(r, s))
            })
    }

    pub open spec fn inputs(self, r: int, values: Seq<Datum>) -> Seq<Datum> {
        Seq::new(self.reads[r].len(), |k: int| values[self.reads[r][k]])
    }

    pub open spec fn notified(self, r: int, s: int) -> bool {
        notifies(self.parts[s], self.parts[r], (self.neighborhood)(r, s))
    }
}

pub open spec fn full_prefix(g: Graph, locals: Locals, n: nat) -> Seq<Datum>
    decreases n,
{
    if n == 0 { Seq::empty() }
    else {
        let r = n - 1;
        let earlier = full_prefix(g, locals, r as nat);
        earlier.push((g.eval)(r, locals[r], g.inputs(r, earlier)))
    }
}

pub struct QueueState {
    pub values: Seq<Datum>,
    pub pending: spec_fn(int) -> bool,
}

pub open spec fn queue_prefix(g: Graph, locals: Locals, old: Seq<Datum>, seeds: Set<int>, n: nat)
    -> QueueState
    decreases n,
{
    if n == 0 {
        QueueState { values: Seq::empty(), pending: |r: int| seeds.contains(r) }
    } else {
        let r = n - 1;
        let earlier = queue_prefix(g, locals, old, seeds, r as nat);
        let v = if (earlier.pending)(r) { (g.eval)(r, locals[r], g.inputs(r, earlier.values)) }
            else { old[r] };
        QueueState {
            values: earlier.values.push(v),
            pending: |next: int| next != r && ((earlier.pending)(next)
                || v != old[r] && r < next < g.parts.len() && g.notified(next, r)),
        }
    }
}

/// Equality of output bits short-circuits propagation. A clean reader may be
/// reused because all of its previously visited inputs retained their old bits.
pub proof fn queue_matches_full_prefix(g: Graph, old_local: Locals, local: Locals, old: Seq<Datum>,
    seeds: Set<int>, n: nat)
    requires
        g.valid(), n <= g.parts.len(), local.len() == g.parts.len(),
        old_local.len() == g.parts.len(), old.len() == g.parts.len(),
        forall|r: int| 0 <= r < old.len()
            ==> #[trigger] old[r] == (g.eval)(r, old_local[r], g.inputs(r, old)),
        forall|r: int| 0 <= r < g.parts.len() && old_local[r] != local[r]
            ==> #[trigger] seeds.contains(r),
    ensures ({
        let state = queue_prefix(g, local, old, seeds, n);
        &&& state.values.len() == n
        &&& state.values == full_prefix(g, local, n)
        &&& forall|r: int| n <= r < g.parts.len() && old_local[r] != local[r]
            ==> #[trigger] (state.pending)(r)
        &&& forall|r: int, k: int| n <= r < g.parts.len() && 0 <= k < g.reads[r].len()
            && (#[trigger] g.reads[r][k]) < n && state.values[g.reads[r][k]] != old[g.reads[r][k]]
            ==> (state.pending)(r)
    }),
    decreases n,
{
    if n > 0 {
        let r = n - 1;
        queue_matches_full_prefix(g, old_local, local, old, seeds, r as nat);
        let prior = queue_prefix(g, local, old, seeds, r as nat);
        let state = queue_prefix(g, local, old, seeds, n);
        if !(prior.pending)(r) {
            assert(g.inputs(r, prior.values) =~= g.inputs(r, old)) by {
                assert forall|k: int| 0 <= k < g.reads[r].len() implies
                    prior.values[#[trigger] g.reads[r][k]] == old[g.reads[r][k]] by {};
            }
        }
        assert(state.values =~= full_prefix(g, local, n));
        assert forall|next: int, k: int| n <= next < g.parts.len() && 0 <= k < g.reads[next].len()
            && (#[trigger] g.reads[next][k]) < n && state.values[g.reads[next][k]] != old[g.reads[next][k]]
            implies (state.pending)(next) by {
            let s = g.reads[next][k];
            if s == r {
                every_read_and_only_reads_are_notified(g.parts[next], g.parts[r], (g.neighborhood)(next, r));
                assert(g.notified(next, r));
            } else {
                assert(prior.values[s] == state.values[s]);
            }
        }
    }
}

}
