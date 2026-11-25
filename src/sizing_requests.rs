//! Ordered sizing requests shared by native recursion and the spill worklist.
#![allow(unexpected_cfgs)]
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(not(verus_keep_ghost))]
use super::{block_schedule, cycle_rules, dependency_rules, wrap_schedule};
#[cfg(verus_keep_ghost)]
use crate::cycles::kernel as cycle_rules;
#[cfg(verus_keep_ghost)]
use crate::{block_schedule::kernel as block_schedule, wrap_schedule::kernel as wrap_schedule};
#[cfg(verus_keep_ghost)]
use crate::{block_schedule as block_spec, wrap_schedule as wrap_spec};
#[cfg(verus_keep_ghost)]
use super::rules as dependency_rules;
use block_schedule::{BlockSchedule, Request as BlockRequest, ScheduleModel as BlockModel};
use crate::declarations::{Axis, LayoutParams, Size, X, Y};
use cycle_rules::Kind;
use wrap_schedule::{FlowRequestSchedule, Model as WrapModel, Producer, Request as WrapRequest};
use dependency_rules::{Form, Input};

#[cfg(verus_keep_ghost)]
#[path = "../proofs/sizing_live.rs"]
pub(crate) mod live;

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
#[derive(Clone, Copy)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub(crate) struct Request<I> {
    pub(crate) node: I,
    pub(crate) vertical: bool,
    pub(crate) kind: Kind,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns target(node, vertical, kind), no_unwind))]
pub(crate) fn target<I: Copy>(node: I, vertical: bool, kind: Kind) -> Request<I> {
    Request { node, vertical, kind }
}

impl<I> Request<I> {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.axis(), no_unwind))]
    pub(crate) fn axis(&self) -> Axis { if self.vertical { Y } else { X } }
}

impl Size {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.dependency_form(), no_unwind))]
    pub(crate) fn dependency_form(self) -> Form {
        match self {
            Size::Pixels(_) => Form::Constant,
            Size::AspectRatio(_) => Form::Ratio,
            Size::Frac(_) => Form::Fraction,
            Size::Fill => Form::Fill,
            Size::FitContent | Size::Auto => Form::Intrinsic,
        }
    }

    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.is_fill(), no_unwind))]
    pub(crate) fn is_fill(&self) -> bool {
        matches!(self, Size::Fill)
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait DeclarationModel {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) trait DeclarationModel {
    type Id: Copy;
    spec fn layout(&self, node: Self::Id) -> LayoutParams;
    spec fn block_item(&self, node: Self::Id) -> bool;
    spec fn auto_block_parent(&self, node: Self::Id) -> bool;
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Declarations: DeclarationModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(params =>
        ensures *params == self.layout(node),
        no_unwind
    ))]
    fn params(&self, node: Self::Id) -> &LayoutParams;

    #[cfg_attr(verus_keep_ghost, verus_spec(block =>
        ensures block == self.block_item(node),
        no_unwind
    ))]
    fn is_block_item(&self, node: Self::Id) -> bool;

    #[cfg_attr(verus_keep_ghost, verus_spec(auto =>
        ensures auto == self.auto_block_parent(node),
        no_unwind
    ))]
    fn block_parent_auto_height(&self, node: Self::Id) -> bool;
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn raw_size(params: LayoutParams, vertical: bool, kind: Kind) -> Option<Size> {
    match kind {
        Kind::Min => if vertical { params.min_size.y } else { params.min_size.x },
        Kind::Max => if vertical { params.max_size.y } else { params.max_size.x },
        Kind::Regular => Some(if vertical { params.size.y } else { params.size.x }),
        _ => None,
    }
}

pub(crate) open spec fn resolved_size(
    params: LayoutParams, vertical: bool, kind: Kind, block_item: bool, auto_block_parent: bool,
) -> Option<Size> {
    match raw_size(params, vertical, kind) {
        Some(Size::Auto) => Some(if block_schedule::inline_auto(!vertical, kind is Regular, block_item) {
            Size::Fill
        } else { Size::FitContent }),
        Some(size) if block_schedule::flex_uses_content_height(vertical, size.is_flex(), auto_block_parent) =>
            if kind is Regular { Some(Size::FitContent) } else { None },
        size => size,
    }
}

pub(crate) proof fn regular_is_present(
    params: LayoutParams, vertical: bool, block_item: bool, auto_block_parent: bool,
)
    ensures resolved_size(params, vertical, Kind::Regular, block_item, auto_block_parent).is_some(),
{
}

} // verus!

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(size =>
    ensures size == resolved_size(
        host.layout(slot.node), slot.vertical, slot.kind,
        host.block_item(slot.node), host.auto_block_parent(slot.node),
    ),
    no_unwind
))]
pub(crate) fn read_declaration<A: Declarations + ?Sized>(host: &A, slot: Request<A::Id>) -> Option<Size> {
    let params = host.params(slot.node);
    let axis = slot.axis();
    let size = match slot.kind {
        Kind::Min => *params.min_size.component(axis),
        Kind::Max => *params.max_size.component(axis),
        Kind::Regular => Some(*params.size.component(axis)),
        Kind::Final | Kind::EvenShare | Kind::Flow => return None,
    };
    match size {
        Some(Size::Auto) => {
            let regular = matches!(slot.kind, Kind::Regular);
            let inline = !slot.vertical && regular;
            let block_item = inline && host.is_block_item(slot.node);
            Some(if block_schedule::inline_auto(!slot.vertical, regular, block_item) {
                Size::Fill
            } else {
                Size::FitContent
            })
        }
        Some(size) if slot.vertical && size.is_flex()
            && block_schedule::flex_uses_content_height(
                true, true, host.block_parent_auto_height(slot.node),
            ) => if matches!(slot.kind, Kind::Regular) { Some(Size::FitContent) } else { None },
        size => size,
    }
}

// Resolve the presence of both bounds from one parameter and Block-context read.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(present =>
    ensures present == (
        resolved_size(host.layout(slot.node), slot.vertical, Kind::Regular, host.block_item(slot.node), host.auto_block_parent(slot.node)).is_some(),
        resolved_size(host.layout(slot.node), slot.vertical, Kind::Min, host.block_item(slot.node), host.auto_block_parent(slot.node)).is_some(),
        resolved_size(host.layout(slot.node), slot.vertical, Kind::Max, host.block_item(slot.node), host.auto_block_parent(slot.node)).is_some(),
    ),
    no_unwind
))]
pub(crate) fn final_presence<A: Declarations + ?Sized>(host: &A, slot: Request<A::Id>) -> (bool, bool, bool) {
    let params = host.params(slot.node);
    let axis = slot.axis();
    let minimum = *params.min_size.component(axis);
    let maximum = *params.max_size.component(axis);
    let min_flex = bound_flexible(minimum);
    let max_flex = bound_flexible(maximum);
    let collapse = slot.vertical && (min_flex || max_flex) && host.block_parent_auto_height(slot.node);
    (true, minimum.is_some() && !(min_flex && collapse), maximum.is_some() && !(max_flex && collapse))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns bound_flexible(size), no_unwind))]
pub(crate) fn bound_flexible(size: Option<Size>) -> bool {
    match size {
        Some(size) => size.is_flex(),
        None => false,
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait RequestView {
    type Id: Copy + Eq;
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait RequestModel {
    type Id: Copy + Eq;
    type Source: RequestSource<Id = Self::Id> + ?Sized;
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) struct Child<I> {
    pub node: I,
    pub in_flow: bool,
}

#[verifier::reject_recursive_types(I)]
pub(crate) struct Topology<I> {
    pub form: spec_fn(Request<I>) -> Option<Form>,
    pub stack_parent: spec_fn(Request<I>) -> Option<I>,
    pub parent: spec_fn(I) -> Option<I>,
    pub parent_flow: spec_fn(Request<I>, I) -> bool,
    pub parent_other: spec_fn(Request<I>, I) -> bool,
    pub intrinsic_flow: spec_fn(Request<I>) -> bool,
    pub intrinsic_other: spec_fn(Request<I>) -> bool,
    pub children: spec_fn(I) -> Seq<Child<I>>,
    pub flow_mode: spec_fn(I) -> FlowMode,
    pub block_children: spec_fn(I) -> Seq<block_spec::Child<I>>,
}

pub(crate) trait RequestView {
    type Id: Copy + Eq;
    spec fn topology(&self) -> Topology<Self::Id>;
}

pub(crate) trait RequestModel {
    type Id: Copy + Eq;
    type Source: RequestSource<Id = Self::Id> + ?Sized;
    type Event;
    type Context;
    #[verifier::prophetic]
    spec fn context(&self) -> Self::Context;
    spec fn topology(&self) -> Topology<Self::Id>;
    spec fn projection(&self) -> spec_fn(Request<Self::Id>) -> Self::Event;
    spec fn requests(&self) -> Seq<Self::Event>;
}

fn snapshot<A: RequestModel>(access: &A) -> (initial: Ghost<Seq<A::Event>>)
    ensures initial@ == access.requests(),
    no_unwind
{
    Ghost(access.requests())
}

fn begin_scan() -> (cursor: Ghost<nat>)
    ensures cursor@ == 0,
    no_unwind
{
    Ghost(0nat)
}

fn step_scan(cursor: Ghost<nat>) -> (next: Ghost<nat>)
    ensures next@ == cursor@ + 1,
    no_unwind
{
    Ghost(cursor@ + 1)
}

pub(crate) open spec fn child_at<I>(children: Seq<Child<I>>, index: nat) -> Option<I> {
    if index < children.len() { Some(children[index as int].node) } else { None }
}

pub(crate) open spec fn presence<I: Copy>(topology: Topology<I>, slot: Request<I>) -> (bool, bool, bool) {
    ((topology.form)(target(slot.node, slot.vertical, Kind::Regular)).is_some(),
     (topology.form)(target(slot.node, slot.vertical, Kind::Min)).is_some(),
     (topology.form)(target(slot.node, slot.vertical, Kind::Max)).is_some())
}

pub(crate) open spec fn selected(form: Option<Form>, intrinsic: bool) -> bool {
    form.is_some() && (!intrinsic || form.unwrap().contributes_to_intrinsic())
}

pub(crate) open spec fn declaration_prefix<I: Copy>(
    topology: Topology<I>, slot: Request<I>, intrinsic: bool, count: nat,
) -> Seq<Request<I>>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let kind = cycle_rules::declaration_order(Kind::Regular, Kind::Min, Kind::Max)@[count - 1];
        let declaration = target(slot.node, slot.vertical, kind);
        let prefix = declaration_prefix(topology, slot, intrinsic, (count - 1) as nat);
        if selected((topology.form)(declaration), intrinsic) { prefix.push(declaration) } else { prefix }
    }
}

pub(crate) open spec fn child_prefix<I: Copy>(topology: Topology<I>, slot: Request<I>, count: nat)
    -> Seq<Request<I>>
    decreases count,
{
    if count == 0 {
        Seq::empty()
    } else {
        let child = (topology.children)(slot.node)[count - 1];
        let prefix = child_prefix(topology, slot, (count - 1) as nat);
        prefix + if child.in_flow {
            declaration_prefix(topology, target(child.node, slot.vertical, slot.kind), true, 3)
        } else { Seq::empty() }
    }
}

pub(crate) open spec fn intrinsic_inputs<I: Copy>(topology: Topology<I>, slot: Request<I>)
    -> Seq<Request<I>>
{
    let inputs = if (topology.intrinsic_flow)(slot) {
        seq![target(slot.node, slot.vertical, Kind::Flow)]
    } else {
        child_prefix(topology, slot, (topology.children)(slot.node).len())
    };
    if (topology.intrinsic_other)(slot) {
        inputs.push(target(slot.node, !slot.vertical, Kind::Final))
    } else { inputs }
}

pub(crate) open spec fn parent_inputs<I: Copy>(topology: Topology<I>, slot: Request<I>)
    -> Seq<Request<I>>
{
    match (topology.parent)(slot.node) {
        None => Seq::empty(),
        Some(parent) => if (topology.parent_flow)(slot, parent) {
            seq![target(parent, slot.vertical, Kind::Flow)]
        } else {
            let same = target(parent, slot.vertical, Kind::Final);
            if (topology.parent_other)(slot, parent) {
                seq![same, target(parent, !slot.vertical, Kind::Final)]
            } else { seq![same] }
        },
    }
}

pub(crate) open spec fn wrap_forms<I: Copy>(
    topology: Topology<I>, child: I, main: bool, producer: Producer,
) -> [bool; 3] {
    [
        wrap_declaration(topology, target(child, main, Kind::Regular), producer),
        wrap_declaration(topology, target(child, main, Kind::Min), producer),
        wrap_declaration(topology, target(child, main, Kind::Max), producer),
    ]
}

pub(crate) open spec fn wrap_declaration<I: Copy>(
    topology: Topology<I>, slot: Request<I>, producer: Producer,
) -> bool {
    let vertical = if producer is Share { slot.vertical } else { !slot.vertical };
    let form = (topology.form)(target(slot.node, vertical, slot.kind));
    form.is_some() && if producer is Share {
        form.unwrap().contributes_to_share()
    } else { form.unwrap().contributes_to_intrinsic() }
}

pub(crate) open spec fn wrap_has_fill<I: Copy>(topology: Topology<I>, child: I, main: bool) -> bool {
    ||| (topology.form)(target(child, main, Kind::Regular)) is Some && (topology.form)(target(child, main, Kind::Regular)).unwrap() is Fill
    ||| (topology.form)(target(child, main, Kind::Min)) is Some && (topology.form)(target(child, main, Kind::Min)).unwrap() is Fill
    ||| (topology.form)(target(child, main, Kind::Max)) is Some && (topology.form)(target(child, main, Kind::Max)).unwrap() is Fill
}

pub(crate) open spec fn wrap_rows<I: Copy>(topology: Topology<I>, node: I, main: bool) -> Seq<wrap_spec::Child<I>> {
    (topology.children)(node).map_values(|child: Child<I>| wrap_spec::Child {
        id: child.node,
        in_flow: child.in_flow,
        has_fill: wrap_has_fill(topology, child.node, main),
        share: wrap_forms(topology, child.node, main, Producer::Share),
        cross: wrap_forms(topology, child.node, main, Producer::Cross),
    })
}

pub(crate) open spec fn wrap_inputs<I: Copy>(
    topology: Topology<I>, node: I, main: bool, producer: Producer,
) -> Seq<Request<I>> {
    let rows = wrap_rows(topology, node, main);
    seq![wrap_slot(node, main, wrap_spec::own(producer))]
        + wrap_spec::child_requests(rows, producer, rows.len()).map_values(
            |request: WrapRequest<I>| wrap_slot(node, main, request),
        )
}

pub(crate) open spec fn block_inputs<I: Copy>(topology: Topology<I>, node: I) -> Seq<Request<I>> {
    let rows = (topology.block_children)(node);
    block_spec::block_inputs(rows, rows.len()).map_values(|request: BlockRequest<I>| block_slot(request))
}

pub(crate) open spec fn ordered_children<I: Copy>(topology: Topology<I>, slot: Request<I>) -> bool {
    match slot.kind {
        Kind::EvenShare => wrap_spec::distinct(wrap_rows(topology, slot.node, slot.vertical)),
        Kind::Flow => match (topology.flow_mode)(slot.node) {
            FlowMode::Block => block_spec::unique((topology.block_children)(slot.node)),
            FlowMode::Wrap(main) => wrap_spec::distinct(wrap_rows(topology, slot.node, main)),
            FlowMode::Other => true,
        },
        _ => true,
    }
}

pub(crate) open spec fn inputs<I: Copy>(topology: Topology<I>, slot: Request<I>) -> Seq<Request<I>> {
    match slot.kind {
        Kind::Final => declaration_prefix(topology, slot, false, 3),
        Kind::EvenShare => wrap_inputs(topology, slot.node, slot.vertical, Producer::Share),
        Kind::Flow => match (topology.flow_mode)(slot.node) {
            FlowMode::Block => block_inputs(topology, slot.node),
            FlowMode::Wrap(main) => wrap_inputs(topology, slot.node, main, Producer::Cross),
            FlowMode::Other => Seq::empty(),
        },
        _ => match (topology.form)(slot) {
            None => Seq::empty(),
            Some(form) => match form.input_for(if form is Fill { (topology.stack_parent)(slot) } else { None }) {
                Input::None => Seq::empty(),
                Input::OppositeFinal => seq![target(slot.node, !slot.vertical, Kind::Final)],
                Input::ParentFinal => parent_inputs(topology, slot),
                Input::ParentShare(parent) => seq![target(parent, slot.vertical, Kind::EvenShare)],
                Input::IntrinsicChildren => intrinsic_inputs(topology, slot),
            },
        },
    }
}

} // verus!

// Inputs and sibling links stay stable while emission may solve the next slot
// immediately or submit it to the spill worklist.
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait RequestSource: RequestView {
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (self.topology().form)(slot), no_unwind))]
    fn form(&self, slot: Request<Self::Id>) -> Option<Form>;
    #[cfg_attr(verus_keep_ghost, verus_spec(found => ensures found == presence(self.topology(), slot), no_unwind))]
    fn final_declarations(&self, slot: Request<Self::Id>) -> (bool, bool, bool);
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (self.topology().stack_parent)(slot), no_unwind))]
    fn stack_parent(&self, slot: Request<Self::Id>) -> Option<Self::Id>;
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (self.topology().parent)(node), no_unwind))]
    fn parent(&self, node: Self::Id) -> Option<Self::Id>;
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (self.topology().parent_flow)(slot, parent), no_unwind))]
    fn parent_uses_flow(&self, slot: Request<Self::Id>, parent: Self::Id) -> bool;
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (self.topology().parent_other)(slot, parent), no_unwind))]
    fn parent_uses_other_axis(&self, slot: Request<Self::Id>, parent: Self::Id) -> bool;
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (self.topology().intrinsic_flow)(slot), no_unwind))]
    fn intrinsic_uses_flow(&self, slot: Request<Self::Id>) -> bool;
    #[cfg_attr(verus_keep_ghost, verus_spec(result => ensures result == (self.topology().intrinsic_other)(slot), no_unwind))]
    fn intrinsic_uses_other_axis(&self, slot: Request<Self::Id>) -> bool;
    #[cfg_attr(verus_keep_ghost, verus_spec(first =>
        ensures first == child_at((self.topology().children)(parent), 0),
            first == block_spec::child_at((self.topology().block_children)(parent), 0),
        no_unwind
    ))]
    fn first_child(&self, parent: Self::Id) -> Option<Self::Id>;
    #[cfg_attr(verus_keep_ghost, verus_spec(result =>
        ensures forall |index: nat| #[trigger] child_at((self.topology().children)(parent), index) == Some(child)
            ==> result == (child_at((self.topology().children)(parent), index + 1),
                           (self.topology().children)(parent)[index as int].in_flow),
        no_unwind
    ))]
    fn child(&self, parent: Self::Id, child: Self::Id) -> (Option<Self::Id>, bool);
    #[cfg_attr(verus_keep_ghost, verus_spec(mode => ensures mode == (self.topology().flow_mode)(parent), no_unwind))]
    fn flow_mode(&self, parent: Self::Id) -> FlowMode;
    #[cfg_attr(verus_keep_ghost, verus_spec(row =>
        requires block_spec::unique((self.topology().block_children)(parent)),
            block_spec::id_index((self.topology().block_children)(parent), child)
                < (self.topology().block_children)(parent).len(),
            block_spec::child_at((self.topology().block_children)(parent),
                block_spec::id_index((self.topology().block_children)(parent), child)) == Some(child),
        ensures ({
            let rows = (self.topology().block_children)(parent);
            let at = block_spec::id_index(rows, child);
            row == (block_spec::child_at(rows, at + 1), rows[at as int].in_flow, rows[at as int].block)
        }),
        no_unwind
    ))]
    fn block_child(&self, parent: Self::Id, child: Self::Id) -> (Option<Self::Id>, bool, bool);
    #[cfg_attr(verus_keep_ghost, verus_spec(row =>
        requires wrap_spec::member(wrap_rows(self.topology(), parent, main), child),
        ensures ({
            let rows = wrap_rows(self.topology(), parent, main);
            row == (wrap_spec::child_at(rows, wrap_spec::index(rows, child) + 1), wrap_spec::current(rows, child).in_flow)
        }),
        no_unwind
    ))]
    fn wrap_child(&self, parent: Self::Id, main: bool, child: Self::Id) -> (Option<Self::Id>, bool);

}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait RequestAccess: RequestModel {
    #[cfg_attr(verus_keep_ghost, verus_spec(source =>
        ensures source.topology() == self.topology(),
        no_unwind
    ))]
    fn source(&self) -> &Self::Source;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        ensures final(self).topology() == old(self).topology(),
            final(self).projection() == old(self).projection(),
            final(self).context() == old(self).context(),
            final(self).requests() == old(self).requests().push((old(self).projection())(slot)),
        no_unwind
    ))]
    fn emit(&mut self, slot: Request<Self::Id>);
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(access).topology() == old(access).topology(),
        final(access).projection() == old(access).projection(),
        final(access).context() == old(access).context(),
        final(access).requests() == old(access).requests()
            + declaration_prefix(old(access).topology(), slot, false, 3).map_values(old(access).projection()),
    no_unwind
))]
fn final_declarations<A: RequestAccess>(access: &mut A, slot: Request<A::Id>) {
    let (regular, minimum, maximum) = access.source().final_declarations(slot);
    if regular { access.emit(target(slot.node, slot.vertical, Kind::Regular)); }
    if minimum { access.emit(target(slot.node, slot.vertical, Kind::Min)); }
    if maximum { access.emit(target(slot.node, slot.vertical, Kind::Max)); }
    #[cfg(verus_keep_ghost)]
    proof! {
        reveal_with_fuel(declaration_prefix, 4);
        assert(access.requests() =~= old(access).requests()
            + declaration_prefix(access.topology(), slot, false, 3).map_values(access.projection()));
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(access).topology() == old(access).topology(),
        final(access).projection() == old(access).projection(),
        final(access).context() == old(access).context(),
        final(access).requests() == old(access).requests()
            + declaration_prefix(old(access).topology(), slot, intrinsic, 3).map_values(old(access).projection()),
    no_unwind
))]
fn declarations<A: RequestAccess>(access: &mut A, slot: Request<A::Id>, intrinsic: bool) {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant access.topology() == old(access).topology(), index <= 3,
            access.projection() == old(access).projection(),
            access.context() == old(access).context(),
            access.requests() == old(access).requests()
                + declaration_prefix(access.topology(), slot, intrinsic, index as nat).map_values(access.projection()),
        decreases 3 - index,
    ))]
    while index < 3 {
        let Some(kind) = cycle_rules::declared_kind(index) else { return; };
        let declaration = target(slot.node, slot.vertical, kind);
        let use_decl = match access.source().form(declaration) {
            Some(form) => !intrinsic || form.contributes_to_intrinsic(),
            None => false,
        };
        if use_decl {
            access.emit(declaration);
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let prefix = declaration_prefix(access.topology(), slot, intrinsic, index as nat);
            let after = declaration_prefix(access.topology(), slot, intrinsic, index as nat + 1);
            assert(after == if use_decl { prefix.push(declaration) } else { prefix });
            assert(access.requests() =~= old(access).requests() + after.map_values(access.projection()));
        }
        index += 1;
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(access).topology() == old(access).topology(),
        final(access).projection() == old(access).projection(),
        final(access).context() == old(access).context(),
        final(access).requests() == old(access).requests()
            + intrinsic_inputs(old(access).topology(), slot).map_values(old(access).projection()),
    no_unwind
))]
fn intrinsic<A: RequestAccess>(access: &mut A, slot: Request<A::Id>) {
    if access.source().intrinsic_uses_flow(slot) {
        access.emit(target(slot.node, slot.vertical, Kind::Flow));
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(access.requests() =~= old(access).requests()
                + seq![target(slot.node, slot.vertical, Kind::Flow)].map_values(access.projection()));
        }
    } else {
        let mut next = access.source().first_child(slot.node);
        #[cfg(verus_keep_ghost)]
        let mut seen = begin_scan();
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant access.topology() == old(access).topology(),
                access.projection() == old(access).projection(),
                access.context() == old(access).context(),
                seen@ <= (access.topology().children)(slot.node).len(),
                next == child_at((access.topology().children)(slot.node), seen@),
                access.requests() == old(access).requests()
                    + child_prefix(access.topology(), slot, seen@).map_values(access.projection()),
            ensures seen@ == (access.topology().children)(slot.node).len(),
            decreases (access.topology().children)(slot.node).len() - seen@,
        ))]
        while let Some(child) = next {
            let (following, in_flow) = access.source().child(slot.node, child);
            next = following;
            if in_flow {
                declarations(access, target(child, slot.vertical, slot.kind), true);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(access.requests() =~= old(access).requests()
                    + child_prefix(access.topology(), slot, seen@ + 1).map_values(access.projection()));
            }
            #[cfg(verus_keep_ghost)]
            {
                seen = step_scan(seen);
            }
        }
    }
    if access.source().intrinsic_uses_other_axis(slot) {
        access.emit(target(slot.node, !slot.vertical, Kind::Final));
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(access.requests() =~= old(access).requests()
            + intrinsic_inputs(access.topology(), slot).map_values(access.projection()));
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    ensures final(access).topology() == old(access).topology(),
        final(access).projection() == old(access).projection(),
        final(access).context() == old(access).context(),
        final(access).requests() == old(access).requests()
            + parent_inputs(old(access).topology(), slot).map_values(old(access).projection()),
    no_unwind
))]
fn parent<A: RequestAccess>(access: &mut A, slot: Request<A::Id>) {
    if let Some(parent) = access.source().parent(slot.node) {
        if access.source().parent_uses_flow(slot, parent) {
            access.emit(target(parent, slot.vertical, Kind::Flow));
        } else {
            access.emit(target(parent, slot.vertical, Kind::Final));
            if access.source().parent_uses_other_axis(slot, parent) {
                access.emit(target(parent, !slot.vertical, Kind::Final));
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(access.requests() =~= old(access).requests()
            + parent_inputs(access.topology(), slot).map_values(access.projection()));
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum FlowMode {
    Block,
    Wrap(bool),
    Other,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns block_slot(request), no_unwind))]
pub(crate) fn block_slot<I: Copy>(request: BlockRequest<I>) -> Request<I> {
    match request {
        BlockRequest::Height(child) => target(child, true, Kind::Final),
        BlockRequest::Margins(child) => target(child, true, Kind::Flow),
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns wrap_slot(parent, main, request), no_unwind))]
pub(crate) fn wrap_slot<I: Copy>(parent: I, main: bool, request: WrapRequest<I>) -> Request<I> {
    match request {
        WrapRequest::ParentMainFinal => target(parent, main, Kind::Final),
        WrapRequest::ParentShare => target(parent, main, Kind::EvenShare),
        WrapRequest::MainFinal(child) => target(child, main, Kind::Final),
        WrapRequest::MainDeclaration(child, index) => {
            let kind = match cycle_rules::declared_kind(index) { Some(kind) => kind, None => Kind::Regular };
            target(child, main, kind)
        }
        WrapRequest::CrossDeclaration(child, index) => {
            let kind = match cycle_rules::declared_kind(index) { Some(kind) => kind, None => Kind::Regular };
            target(child, !main, kind)
        }
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct BlockBinding<A: RequestAccess> {
    access: A,
    parent: A::Id,
}

#[cfg(not(verus_keep_ghost))]
impl<A: RequestAccess> BlockModel for BlockBinding<A> {
    type Id = A::Id;
}

#[cfg(verus_keep_ghost)]
verus! {
impl<A: RequestAccess> BlockModel for BlockBinding<A> {
    type Id = A::Id;

    type Event = A::Event;
    type Scope = (Topology<A::Id>, A::Context, A::Id, spec_fn(Request<A::Id>) -> A::Event);

    closed spec fn children(&self) -> Seq<block_spec::Child<A::Id>> { (self.access.topology().block_children)(self.parent) }
    #[verifier::prophetic]
    closed spec fn scope(&self) -> Self::Scope { (self.access.topology(), self.access.context(), self.parent, self.access.projection()) }
    closed spec fn project(&self) -> spec_fn(BlockRequest<A::Id>) -> Self::Event {
        let project = self.access.projection();
        |request: BlockRequest<A::Id>| project(block_slot(request))
    }
    closed spec fn requests(&self) -> Seq<Self::Event> { self.access.requests() }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<A: RequestAccess> BlockSchedule for BlockBinding<A> {
    #[inline(always)]
    fn first_child(&self) -> Option<Self::Id> { self.access.source().first_child(self.parent) }

    #[inline(always)]
    fn read_child(&self, id: Self::Id) -> (Option<Self::Id>, bool, bool) {
        self.access.source().block_child(self.parent, id)
    }

    #[inline(always)]
    fn request(&mut self, request: BlockRequest<Self::Id>) {
        self.access.emit(block_slot(request));
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
struct WrapBinding<A: RequestAccess> {
    access: A,
    parent: A::Id,
    main: bool,
}

#[cfg(not(verus_keep_ghost))]
impl<A: RequestAccess> WrapModel for WrapBinding<A> {
    type Id = A::Id;
}

#[cfg(verus_keep_ghost)]
verus! {
impl<A: RequestAccess> WrapModel for WrapBinding<A> {
    type Id = A::Id;

    type Event = A::Event;
    type Scope = (Topology<A::Id>, A::Context, A::Id, bool, spec_fn(Request<A::Id>) -> A::Event);

    closed spec fn children(&self) -> Seq<wrap_spec::Child<A::Id>> { wrap_rows(self.access.topology(), self.parent, self.main) }
    #[verifier::prophetic]
    closed spec fn scope(&self) -> Self::Scope {
        (self.access.topology(), self.access.context(), self.parent, self.main, self.access.projection())
    }
    closed spec fn project(&self) -> spec_fn(WrapRequest<A::Id>) -> Self::Event {
        let node = self.parent;
        let main = self.main;
        let project = self.access.projection();
        |request: WrapRequest<A::Id>| project(wrap_slot(node, main, request))
    }
    closed spec fn requests(&self) -> Seq<Self::Event> { self.access.requests() }
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
impl<A: RequestAccess> FlowRequestSchedule for WrapBinding<A> {
    #[inline(always)]
    fn first(&self) -> Option<Self::Id> {
        let first = self.access.source().first_child(self.parent);
        #[cfg(verus_keep_ghost)]
        proof! {
            let rows = (self.access.topology().children)(self.parent);
            assert(self.children().len() == rows.len());
            if rows.len() > 0 { assert(self.children()[0].id == rows[0].node); }
        }
        first
    }

    #[inline(always)]
    fn row(&self, child: Self::Id) -> (Option<Self::Id>, bool) {
        self.access.source().wrap_child(self.parent, self.main, child)
    }

    #[inline(always)]
    fn fills(&self, child: Self::Id) -> bool {
        matches!(self.access.source().form(target(child, self.main, Kind::Regular)), Some(Form::Fill))
            || matches!(self.access.source().form(target(child, self.main, Kind::Min)), Some(Form::Fill))
            || matches!(self.access.source().form(target(child, self.main, Kind::Max)), Some(Form::Fill))
    }

    #[inline(always)]
    fn declaration(&self, child: Self::Id, producer: Producer, index: usize) -> bool {
        let kind = match cycle_rules::declared_kind(index) { Some(kind) => kind, None => return false };
        let vertical = match producer { Producer::Share => self.main, Producer::Cross => !self.main };
        let needed = match self.access.source().form(target(child, vertical, kind)) {
            Some(form) => match producer {
                Producer::Share => form.contributes_to_share(),
                Producer::Cross => form.contributes_to_intrinsic(),
            },
            None => false,
        };
        #[cfg(verus_keep_ghost)]
        proof! {
            assert(kind == if index == 0 { Kind::Regular } else if index == 1 { Kind::Min } else { Kind::Max });
            assert(needed == wrap_declaration(self.access.topology(), target(child, self.main, kind), producer));
        }
        needed
    }

    #[inline(always)]
    fn request(&mut self, request: WrapRequest<Self::Id>) {
        self.access.emit(wrap_slot(self.parent, self.main, request));
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires wrap_spec::distinct(wrap_rows(access.topology(), node, main)),
    ensures result.topology() == access.topology(), result.projection() == access.projection(),
        result.context() == access.context(),
        result.requests() == access.requests()
            + wrap_inputs(access.topology(), node, main, producer).map_values(access.projection()),
    no_unwind
))]
fn wrap<A: RequestAccess>(access: A, node: A::Id, main: bool, producer: Producer) -> A {
    let mut binding = WrapBinding { access, parent: node, main };
    wrap_schedule::request_flow_inputs(&mut binding, producer);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(binding.access.requests() =~= access.requests()
            + wrap_inputs(access.topology(), node, main, producer).map_values(access.projection()));
    }
    binding.access
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires block_spec::unique((access.topology().block_children)(node)),
    ensures result.topology() == access.topology(), result.projection() == access.projection(),
        result.context() == access.context(),
        result.requests() == access.requests()
            + block_inputs(access.topology(), node).map_values(access.projection()),
    no_unwind
))]
fn block<A: RequestAccess>(access: A, node: A::Id) -> A {
    let mut binding = BlockBinding { access, parent: node };
    block_schedule::request_block_inputs(&mut binding);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(binding.access.requests() =~= access.requests()
            + block_inputs(access.topology(), node).map_values(access.projection()));
    }
    binding.access
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(result =>
    requires ordered_children(access.topology(), slot),
    ensures result.topology() == access.topology(), result.projection() == access.projection(),
        result.context() == access.context(),
        result.requests() == access.requests() + inputs(access.topology(), slot).map_values(access.projection()),
    no_unwind
))]
pub(crate) fn request_inputs<A: RequestAccess>(mut access: A, slot: Request<A::Id>) -> A {
    #[cfg(verus_keep_ghost)]
    let initial = snapshot(&access);
    match slot.kind {
        Kind::Final => final_declarations(&mut access, slot),
        Kind::EvenShare => access = wrap(access, slot.node, slot.vertical, Producer::Share),
        Kind::Flow => match access.source().flow_mode(slot.node) {
            FlowMode::Block => access = block(access, slot.node),
            FlowMode::Wrap(main) => access = wrap(access, slot.node, main, Producer::Cross),
            FlowMode::Other => {}
        },
        _ => {
            if let Some(form) = access.source().form(slot) {
                let stack = if matches!(form, Form::Fill) { access.source().stack_parent(slot) } else { None };
                match form.input_for(stack) {
                    Input::None => {}
                    Input::OppositeFinal => access.emit(target(slot.node, !slot.vertical, Kind::Final)),
                    Input::ParentFinal => parent(&mut access, slot),
                    Input::ParentShare(parent) => access.emit(target(parent, slot.vertical, Kind::EvenShare)),
                    Input::IntrinsicChildren => intrinsic(&mut access, slot),
                }
            }
        }
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(access.requests() =~= initial@ + inputs(access.topology(), slot).map_values(access.projection())); }
    access
}
