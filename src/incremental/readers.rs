//! Emit the native numeric queue's reverse sizing requests.
#![allow(unexpected_cfgs)]

use crate::declarations::{Axis, ChildrenLayout, LayoutParams, MainAxisCellSize, Size, X, Xy, Y};
#[cfg(verus_keep_ghost)]
use crate::{cycles::kernel as cycle_rules, dependencies::rules as dependency_rules};
#[cfg(verus_keep_ghost)]
use crate::dependencies::registration as registration_rules;
#[cfg(not(verus_keep_ghost))]
use crate::solve::{cycle_rules, dependency_rules};
#[cfg(not(verus_keep_ghost))]
use super::registration_rules;
use cycle_rules::Kind;
use dependency_rules::{Form, Input};
use registration_rules::{AxisEdits, Context, Seeds, declaration_changed};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

/// The sizing inputs that changed. Placement reads the current parameters.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
pub(crate) struct NodeChange {
    pub declared: u8,
    pub inner: Xy<bool>,
    pub margin: Xy<bool>,
    pub fill_weight: bool,
    pub content: bool,
}

#[derive(Clone, Copy)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) enum Filter {
    Flexible,
    FitContent,
    Own { intrinsic: bool, fill: bool },
    ParentFinal { in_stack: bool },
    ParentShare,
    OppositeFinal { constrained: bool },
    Intrinsic,
}

impl Filter {
    #[inline(always)]
    #[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
    #[cfg_attr(verus_keep_ghost, verus_spec(returns self.accepts(size), no_unwind))]
    pub(crate) fn accepts(self, size: Size) -> bool {
        match self {
            Self::Flexible => size.is_flex(),
            Self::FitContent => matches!(size, Size::FitContent),
            Self::Own { intrinsic, fill } => intrinsic && matches!(size, Size::FitContent) || fill && size.is_fill(),
            Self::ParentFinal { in_stack } => matches!(size.dependency_form().input(in_stack), Input::ParentFinal),
            Self::ParentShare => matches!(size.dependency_form().input(true), Input::ParentShare(())),
            Self::OppositeFinal { constrained } => size.dependency_form().reads_opposite_final(constrained),
            Self::Intrinsic => matches!(size.dependency_form(), Form::Intrinsic),
        }
    }
}

#[cfg(not(verus_keep_ghost))]
pub(crate) trait Model {
    type Id: Copy;
}

#[cfg(verus_keep_ghost)]
verus! {
pub(crate) struct Links<I> {
    pub live: Set<I>,
    pub children: Map<I, Seq<I>>,
    pub parents: Map<I, Option<I>>,
}

impl<I> Links<I> {
    pub(crate) open spec fn valid(self) -> bool {
        forall |parent: I, i: int| self.live.contains(parent) && 0 <= i < self.children[parent].len()
            ==> self.live.contains(#[trigger] self.children[parent][i])
    }

    pub(crate) open spec fn child(self, parent: I, index: int) -> Option<I> {
        if 0 <= index < self.children[parent].len() { Some(self.children[parent][index]) } else { None }
    }
}

#[verifier::reject_recursive_types(I)]
pub(crate) struct ReaderInputs<I> {
    pub links: Links<I>,
    pub parameters: spec_fn(I) -> LayoutParams,
    pub declaration: spec_fn(I, Axis, Kind) -> Option<Size>,
}

pub(crate) trait Model {
    type Id: Copy;
    spec fn inputs(&self) -> ReaderInputs<Self::Id>;
    spec fn seeded(&self) -> Seq<(Self::Id, Axis, Kind)>;
}

pub(crate) open spec fn filtered_kinds<I>(
    inputs: ReaderInputs<I>, node: I, axis: Axis, filter: Filter, count: nat,
) -> Seq<(I, Axis, Kind)>
    decreases count
{
    if count == 0 { Seq::empty() }
    else {
        let index = count - 1;
        let earlier = filtered_kinds(inputs, node, axis, filter, index as nat);
        let kind = cycle_rules::declared_kind(index as usize);
        if let Some(kind) = kind {
            if let Some(size) = (inputs.declaration)(node, axis, kind) {
                if filter.accepts(size) { earlier.push((node, axis, kind)) } else { earlier }
            } else { earlier }
        } else { earlier }
    }
}

pub(crate) open spec fn stack_parent_of<I>(inputs: ReaderInputs<I>, node: I, axis: Axis) -> Option<I> {
    match inputs.links.parents[node] {
        Some(parent) if same_axis(stack_axis((inputs.parameters)(parent).children_layout), axis)
            && !(inputs.parameters)(node).free_placement => Some(parent),
        _ => None,
    }
}

/// A share wakes only enabled in-flow children whose effective declarations
/// read this Stack or Wrap axis. The sequence uses sibling and declaration order.
pub(crate) open spec fn share_readers<I>(inputs: ReaderInputs<I>, node: I, axis: Axis, count: nat) -> Seq<(I, Axis, Kind)>
    decreases count,
{
    if count == 0 { Seq::empty() } else {
        let child = inputs.links.children[node][count - 1];
        let prefix = share_readers(inputs, node, axis, (count - 1) as nat);
        if !(inputs.parameters)(child).disabled && stack_parent_of(inputs, child, axis).is_some() {
            prefix + filtered_kinds(inputs, child, axis, Filter::ParentShare, 3)
        } else { prefix }
    }
}

pub(crate) open spec fn final_child_axis_readers<I>(
    inputs: ReaderInputs<I>, child: I, child_axis: Axis, changed_axis: Axis, grid_main: bool,
) -> Seq<(I, Axis, Kind)> {
    if dependency_rules::reads_parent_axis(child_axis.index() == changed_axis.index(),
        !(inputs.parameters)(child).free_placement, grid_main)
    {
        let in_stack = stack_parent_of(inputs, child, child_axis).is_some();
        filtered_kinds(inputs, child, child_axis, Filter::ParentFinal { in_stack }, 3)
    } else { Seq::empty() }
}

pub(crate) open spec fn final_child_readers<I>(
    inputs: ReaderInputs<I>, parent: I, axis: Axis, grid_main: bool, count: nat,
) -> Seq<(I, Axis, Kind)>
    decreases count
{
    if count == 0 { Seq::empty() } else {
        let child = inputs.links.children[parent][count - 1];
        let prefix = final_child_readers(inputs, parent, axis, grid_main, (count - 1) as nat);
        if (inputs.parameters)(child).disabled { prefix } else {
            prefix + final_child_axis_readers(inputs, child, X, axis, grid_main)
                + final_child_axis_readers(inputs, child, Y, axis, grid_main)
        }
    }
}

pub(crate) open spec fn has_fill<I>(inputs: ReaderInputs<I>, node: I, axis: Axis) -> bool {
    (inputs.declaration)(node, axis, Kind::Regular) == Some(Size::Fill)
        || (inputs.declaration)(node, axis, Kind::Min) == Some(Size::Fill)
        || (inputs.declaration)(node, axis, Kind::Max) == Some(Size::Fill)
}

pub(crate) open spec fn width_grid_axis<I>(inputs: ReaderInputs<I>, node: I, axis: Axis) -> bool {
    match (inputs.parameters)(node).children_layout {
        ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } =>
            main_axis.index() == axis.index(),
        _ => false,
    }
}

pub(crate) open spec fn final_readers<I>(inputs: ReaderInputs<I>, node: I, axis: Axis) -> Seq<(I, Axis, Kind)> {
    let other = axis.other();
    let grid_main = width_grid_axis(inputs, node, axis);
    let constrained = dependency_rules::reads_intrinsic_constraint(
        (inputs.parameters)(node).intrinsic_reads_other_axis(other), grid_main,
    );
    let opposite = filtered_kinds(inputs, node, other, Filter::OppositeFinal { constrained }, 3);
    let own_share = if same_axis(stack_axis((inputs.parameters)(node).children_layout), axis) {
        seq![(node, axis, Kind::EvenShare)]
    } else { Seq::empty() };
    let children = final_child_readers(inputs, node, axis, grid_main, inputs.links.children[node].len());
    let parent_share = if let Some(parent) = stack_parent_of(inputs, node, axis) {
        if !has_fill(inputs, node, axis) { seq![(parent, axis, Kind::EvenShare)] } else { Seq::empty() }
    } else { Seq::empty() };
    opposite + own_share + children + parent_share
}

pub(crate) open spec fn content_requests<I>(inputs: ReaderInputs<I>, node: I) -> Seq<(I, Axis, Kind)> {
    if (inputs.parameters)(node).disabled {
        Seq::empty()
    } else {
        filtered_kinds(inputs, node, X, Filter::FitContent, 3)
            + filtered_kinds(inputs, node, Y, Filter::FitContent, 3)
    }
}

pub(crate) open spec fn width_grid_main(layout: ChildrenLayout) -> Option<Axis> {
    match layout {
        ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } => Some(main_axis),
        _ => None,
    }
}

pub(crate) open spec fn masked_declarations<I>(node: I, axis: Axis, mask: u8) -> Seq<(I, Axis, Kind)> {
    let regular = if declaration_changed(mask, cycle_rules::slot_index(axis.index(), Kind::Regular)) {
        seq![(node, axis, Kind::Regular)]
    } else { Seq::empty() };
    let lower = if declaration_changed(mask, cycle_rules::slot_index(axis.index(), Kind::Min)) {
        regular.push((node, axis, Kind::Min))
    } else { regular };
    if declaration_changed(mask, cycle_rules::slot_index(axis.index(), Kind::Max)) {
        lower.push((node, axis, Kind::Max))
    } else { lower }
}

pub(crate) open spec fn changed_fraction<I>(inputs: ReaderInputs<I>, node: I, axis: Axis, mask: u8) -> bool {
    declaration_changed(mask, cycle_rules::slot_index(axis.index(), Kind::Regular))
        && (if axis is X { (inputs.parameters)(node).size.x } else { (inputs.parameters)(node).size.y }) is Frac
}

#[verifier::opaque]
pub(crate) open spec fn axis_edit_seeds<I>(
    inputs: ReaderInputs<I>, node: I, axis: Axis, change: NodeChange, fraction: bool,
    parent: Option<SeedParent<I>>, stack: Option<Axis>, grid: Option<Axis>,
) -> Seeds {
    let axis_inputs = AxisEdits {
        inner: if axis is X { change.inner.x } else { change.inner.y },
        other_inner: if axis is X { change.inner.y } else { change.inner.x },
        content: change.content,
        margin: if axis is X { change.margin.x } else { change.margin.y },
        weight: change.fill_weight,
        regular_fraction: fraction,
    };
    let (placed_parent, parent_stack) = match parent {
        Some(parent) => (!(parent.layout is Free), stack_axis(parent.layout)),
        None => (false, None),
    };
    axis_inputs.seeds(Context {
        in_flow: !(inputs.parameters)(node).free_placement,
        placed_parent, parent_stack_axis: same_axis(parent_stack, axis),
        stack_axis: same_axis(stack, axis), width_grid: grid.is_some(), grid_main: same_axis(grid, axis),
        wraps_text: (inputs.parameters)(node).text_wraps_on(axis),
    })
}

#[verifier::opaque]
pub(crate) open spec fn edit_axis_requests<I>(
    inputs: ReaderInputs<I>, node: I, axis: Axis, work: Seeds, parent: Option<SeedParent<I>>,
) -> Seq<(I, Axis, Kind)> {
    let own = if work.own_intrinsic || work.own_fill {
        filtered_kinds(inputs, node, axis, Filter::Own { intrinsic: work.own_intrinsic, fill: work.own_fill }, 3)
    } else { Seq::empty() };
    let with_final = if work.own_final { own.push((node, axis, Kind::Final)) } else { own };
    let with_share = if work.own_share { with_final.push((node, axis, Kind::EvenShare)) } else { with_final };
    if let Some(parent) = parent {
        let with_intrinsic = if work.parent_intrinsic {
            with_share + filtered_kinds(inputs, parent.id, axis, Filter::FitContent, 3)
        } else { with_share };
        if work.parent_share { with_intrinsic.push((parent.id, axis, Kind::EvenShare)) } else { with_intrinsic }
    } else { with_share }
}

pub(crate) open spec fn available_child_requests<I>(
    inputs: ReaderInputs<I>, child: I, stack: Option<Axis>, horizontal: bool, vertical: bool,
) -> Seq<(I, Axis, Kind)> {
    let in_flow = !(inputs.parameters)(child).free_placement;
    let x = if horizontal {
        filtered_kinds(inputs, child, X, Filter::ParentFinal { in_stack: same_axis(stack, X) && in_flow }, 3)
    } else { Seq::empty() };
    let y = if vertical {
        filtered_kinds(inputs, child, Y, Filter::ParentFinal { in_stack: same_axis(stack, Y) && in_flow }, 3)
    } else { Seq::empty() };
    if (inputs.parameters)(child).disabled { Seq::empty() } else { x + y }
}

pub(crate) open spec fn available_requests<I>(
    inputs: ReaderInputs<I>, parent: I, stack: Option<Axis>, horizontal: bool, vertical: bool, count: nat,
) -> Seq<(I, Axis, Kind)>
    decreases count
{
    if count == 0 { Seq::empty() }
    else {
        available_requests(inputs, parent, stack, horizontal, vertical, (count - 1) as nat)
            + available_child_requests(inputs, inputs.links.children[parent][count - 1], stack, horizontal, vertical)
    }
}

pub(crate) open spec fn edited_parent<I>(inputs: ReaderInputs<I>, node: I) -> Option<SeedParent<I>> {
    match inputs.links.parents[node] {
        Some(id) => Some(SeedParent { id, layout: (inputs.parameters)(id).children_layout }),
        None => None,
    }
}

#[verifier::opaque]
pub(crate) open spec fn extra_edit_requests<I>(
    inputs: ReaderInputs<I>, node: I, change: NodeChange, horizontal: bool, vertical: bool,
) -> Seq<(I, Axis, Kind)> {
    let parent = edited_parent(inputs, node);
    let layout = (inputs.parameters)(node).children_layout;
    let stack = stack_axis(layout);
    let grid = width_grid_main(layout);
    let x = axis_edit_seeds(inputs, node, X, change, horizontal, parent, stack, grid);
    let y = axis_edit_seeds(inputs, node, Y, change, vertical, parent, stack, grid);
    let local = edit_axis_requests(inputs, node, X, x, parent) + edit_axis_requests(inputs, node, Y, y, parent);
    if x.child_available || y.child_available {
        local + available_requests(inputs, node, stack, x.child_available, y.child_available,
            inputs.links.children[node].len())
    } else { local }
}

pub(crate) open spec fn has_extra_edits(change: NodeChange, horizontal: bool, vertical: bool) -> bool {
    change.inner.x || change.inner.y || change.margin.x || change.margin.y
        || change.content || change.fill_weight || horizontal || vertical
}

pub(crate) open spec fn declaration_requests<I>(inputs: ReaderInputs<I>, node: I, change: NodeChange)
    -> Seq<(I, Axis, Kind)>
{
    if (inputs.parameters)(node).disabled { Seq::empty() }
    else {
        let direct = edited_declarations(node, change);
        let x = changed_fraction(inputs, node, X, change.declared);
        let y = changed_fraction(inputs, node, Y, change.declared);
        if has_extra_edits(change, x, y) {
            direct + extra_edit_requests(inputs, node, change, x, y)
        } else { direct }
    }
}

pub(crate) open spec fn edited_declarations<I>(node: I, change: NodeChange) -> Seq<(I, Axis, Kind)> {
    masked_declarations(node, X, change.declared) + masked_declarations(node, Y, change.declared)
}

pub(crate) open spec fn declaration_readers<I>(inputs: ReaderInputs<I>, node: I, axis: Axis, kind: Kind)
    -> Seq<(I, Axis, Kind)>
{
    let own = seq![(node, axis, Kind::Final)];
    if (inputs.parameters)(node).free_placement { own }
    else {
        match (inputs.links.parents[node], (inputs.declaration)(node, axis, kind)) {
            (Some(parent), Some(size)) => {
                let form = size.dependency_form();
                let with_share = if same_axis(stack_axis((inputs.parameters)(parent).children_layout), axis)
                    && has_fill(inputs, node, axis) && form.contributes_to_share()
                { own.push((parent, axis, Kind::EvenShare)) } else { own };
                with_share + if form.contributes_to_intrinsic() {
                    filtered_kinds(inputs, parent, axis, Filter::Intrinsic, 3)
                } else { Seq::empty() }
            }
            _ => own,
        }
    }
}

/// An enabled child declaration reading this parent's share appears in the
/// transition's request log. The full dispatcher and the notification use the
/// same effective declaration and stack-parent relation.
pub(crate) proof fn requests_native_share_reader<I: Copy>(
    inputs: ReaderInputs<I>, topology: crate::dependencies::sizing_requests::Topology<I>,
    parent: I, at: int, axis: Axis, kind: Kind,
)
    requires
        inputs.links.children.contains_key(parent),
        0 <= at < inputs.links.children[parent].len(),
        !(inputs.parameters)(inputs.links.children[parent][at]).disabled,
        stack_parent_of(inputs, inputs.links.children[parent][at], axis) == Some(parent),
        kind is Regular || kind is Min || kind is Max,
        (inputs.declaration)(inputs.links.children[parent][at], axis, kind) == Some(Size::Fill),
        ({
            let slot = crate::dependencies::sizing_requests::target(inputs.links.children[parent][at], axis is Y, kind);
            &&& (topology.form)(slot) == Some(Form::Fill)
            &&& (topology.stack_parent)(slot) == stack_parent_of(inputs, slot.node, axis)
        }),
    ensures ({
        let child = inputs.links.children[parent][at];
        let slot = crate::dependencies::sizing_requests::target(child, axis is Y, kind);
        let producer = crate::dependencies::sizing_requests::target(parent, axis is Y, Kind::EvenShare);
        &&& crate::dependencies::sizing_requests::inputs(topology, slot) == seq![producer]
        &&& share_readers(inputs, parent, axis, inputs.links.children[parent].len()).contains((child, axis, kind))
    }),
{
    let child = inputs.links.children[parent][at];
    let declaration = match kind { Kind::Regular => 0usize, Kind::Min => 1usize, _ => 2usize };
    fill_request_in_prefix(inputs, child, axis, kind, declaration, 3);
    share_reader_in_prefix(inputs, parent, at, axis, kind, inputs.links.children[parent].len());
}

proof fn fill_request_in_prefix<I>(inputs: ReaderInputs<I>, child: I, axis: Axis, kind: Kind, at: usize, count: nat)
    requires at < count <= 3, cycle_rules::declared_kind(at) == Some(kind),
        (inputs.declaration)(child, axis, kind) == Some(Size::Fill),
    ensures filtered_kinds(inputs, child, axis, Filter::ParentShare, count).contains((child, axis, kind)),
    decreases count,
{
    let item = (child, axis, kind);
    let prior = filtered_kinds(inputs, child, axis, Filter::ParentShare, (count - 1) as nat);
    let all = filtered_kinds(inputs, child, axis, Filter::ParentShare, count);
    if at == count - 1 {
        assert(Filter::ParentShare.accepts(Size::Fill));
        assert(all == prior.push(item));
        assert(all[prior.len() as int] == item);
    } else {
        fill_request_in_prefix(inputs, child, axis, kind, at, (count - 1) as nat);
        let i = choose |i: int| 0 <= i < prior.len() && prior[i] == item;
        assert(all[i] == item);
    }
}

proof fn share_reader_in_prefix<I>(inputs: ReaderInputs<I>, parent: I, at: int, axis: Axis, kind: Kind, count: nat)
    requires
        inputs.links.children.contains_key(parent),
        0 <= at < count <= inputs.links.children[parent].len(),
        !(inputs.parameters)(inputs.links.children[parent][at]).disabled,
        stack_parent_of(inputs, inputs.links.children[parent][at], axis).is_some(),
        filtered_kinds(inputs, inputs.links.children[parent][at], axis, Filter::ParentShare, 3)
            .contains((inputs.links.children[parent][at], axis, kind)),
    ensures share_readers(inputs, parent, axis, count).contains((inputs.links.children[parent][at], axis, kind)),
    decreases count,
{
    let item = (inputs.links.children[parent][at], axis, kind);
    let prior = share_readers(inputs, parent, axis, (count - 1) as nat);
    let all = share_readers(inputs, parent, axis, count);
    if at < count - 1 {
        share_reader_in_prefix(inputs, parent, at, axis, kind, (count - 1) as nat);
        let i = choose |i: int| 0 <= i < prior.len() && prior[i] == item;
        assert(all[i] == item);
    } else {
        let suffix = filtered_kinds(inputs, item.0, axis, Filter::ParentShare, 3);
        assert(all == prior + suffix);
        let i = choose |i: int| 0 <= i < suffix.len() && suffix[i] == item;
        assert(all[prior.len() + i] == item);
    }
}

fn remember_seeds<S: Model + ?Sized>(source: &S) -> (prior: Ghost<Seq<(S::Id, Axis, Kind)>>)
    ensures prior@ == source.seeded(),
    no_unwind
{
    Ghost(source.seeded())
}

fn first_index() -> (index: Ghost<int>)
    ensures index@ == 0,
    no_unwind
{
    Ghost(0int)
}

fn next_index(index: Ghost<int>) -> (next: Ghost<int>)
    ensures next@ == index@ + 1,
    no_unwind
{
    Ghost(index@ + 1)
}
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
pub(crate) trait Access: Model {
    #[cfg_attr(verus_keep_ghost, verus_spec(params =>
        requires self.inputs().links.live.contains(node),
        ensures *params == (self.inputs().parameters)(node),
        no_unwind
    ))]
    fn parameters(&self, node: Self::Id) -> &LayoutParams;

    #[cfg_attr(verus_keep_ghost, verus_spec(size =>
        requires self.inputs().links.live.contains(node),
        ensures size == (self.inputs().declaration)(node, axis, kind),
        no_unwind
    ))]
    fn read_declaration(&self, node: Self::Id, axis: Axis, kind: Kind) -> Option<Size>;

    #[cfg_attr(verus_keep_ghost, verus_spec(parent =>
        requires self.inputs().links.live.contains(node),
        ensures parent == self.inputs().links.parents[node],
            parent.is_some() ==> self.inputs().links.live.contains(parent.unwrap()),
        no_unwind
    ))]
    fn parent_id(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(child =>
        requires self.inputs().links.live.contains(node),
        ensures child == self.inputs().links.child(node, 0),
        no_unwind
    ))]
    fn first_id(&self, node: Self::Id) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(sibling =>
        requires self.inputs().links.live.contains(node), self.inputs().links.child(parent, index@) == Some(node),
        ensures sibling == self.inputs().links.child(parent, index@ + 1),
        no_unwind
    ))]
    fn following_id(
        &self, node: Self::Id,
        #[cfg(verus_keep_ghost)] parent: Self::Id,
        #[cfg(verus_keep_ghost)] index: Ghost<int>,
    ) -> Option<Self::Id>;

    #[cfg_attr(verus_keep_ghost, verus_spec(
        requires old(self).inputs().links.live.contains(node),
        ensures final(self).inputs() == old(self).inputs(), final(self).seeded() == old(self).seeded().push((node, axis, kind)),
        no_unwind
    ))]
    fn enqueue(&mut self, node: Self::Id, axis: Axis, kind: Kind);
}

/// Read exactly Regular, Min and Max, in their original scheduling order.
#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded() + filtered_kinds(old(source).inputs(), node, axis, filter, 3),
    no_unwind
))]
pub(crate) fn declarations<S: Access + ?Sized>(source: &mut S, node: S::Id, axis: Axis, filter: Filter) {
    #[cfg(verus_keep_ghost)]
    let prior = remember_seeds(source);
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= 3, source.inputs() == old(source).inputs(), source.inputs().links.live.contains(node),
            prior@ == old(source).seeded(),
            source.seeded() == prior@ + filtered_kinds(old(source).inputs(), node, axis, filter, index as nat),
        decreases 3 - index,
    ))]
    while index < 3 {
        let Some(kind) = cycle_rules::declared_kind(index) else { return; };
        let size = source.read_declaration(node, axis, kind);
        if let Some(size) = size {
            if filter.accepts(size) {
                source.enqueue(node, axis, kind);
            }
        }
        #[cfg(verus_keep_ghost)]
        proof! {
            let result = filtered_kinds(old(source).inputs(), node, axis, filter, (index + 1) as nat);
            assert(source.seeded() =~= prior@ + result);
        }
        index += 1;
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns same_axis(found, axis), no_unwind))]
pub(crate) fn same_axis(found: Option<Axis>, axis: Axis) -> bool {
    match found {
        Some(found) => found.index() == axis.index(),
        None => false,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify(dual_spec, open))]
#[cfg_attr(verus_keep_ghost, verus_spec(returns stack_axis(layout), no_unwind))]
pub(crate) fn stack_axis(layout: ChildrenLayout) -> Option<Axis> {
    match layout {
        ChildrenLayout::Stack { axis, .. } | ChildrenLayout::Wrap { axis, .. } => Some(axis),
        _ => None,
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(parent =>
    requires source.inputs().links.live.contains(node),
    ensures parent == stack_parent_of(source.inputs(), node, axis),
        parent.is_some() ==> source.inputs().links.live.contains(parent.unwrap()),
    no_unwind
))]
fn stack_parent<S: Access + ?Sized>(source: &S, node: S::Id, axis: Axis) -> Option<S::Id> {
    let parent = source.parent_id(node)?;
    let layout = source.parameters(parent).children_layout;
    if same_axis(stack_axis(layout), axis) && !source.parameters(node).free_placement {
        Some(parent)
    } else {
        None
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(found =>
    requires source.inputs().links.live.contains(node),
    ensures found == has_fill(source.inputs(), node, axis),
    no_unwind
))]
fn any_fill<S: Access + ?Sized>(source: &S, node: S::Id, axis: Axis) -> bool {
    matches!(source.read_declaration(node, axis, Kind::Regular), Some(Size::Fill))
        || matches!(source.read_declaration(node, axis, Kind::Min), Some(Size::Fill))
        || matches!(source.read_declaration(node, axis, Kind::Max), Some(Size::Fill))
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.live.contains(child),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded()
            + final_child_axis_readers(old(source).inputs(), child, child_axis, axis, grid_main),
    no_unwind
))]
fn child_final<S: Access + ?Sized>(source: &mut S, child: S::Id, child_axis: Axis, axis: Axis, grid_main: bool) {
    if dependency_rules::reads_parent_axis(child_axis.index() == axis.index(),
        !source.parameters(child).free_placement, grid_main)
    {
        let in_stack = stack_parent(source, child, child_axis).is_some();
        declarations(source, child, child_axis, Filter::ParentFinal { in_stack });
    }
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[derive(Clone, Copy)]
enum ChildReaders {
    Share(Axis),
    Final { axis: Axis, grid_main: bool },
    Available { stack: Option<Axis>, horizontal: bool, vertical: bool },
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.valid(), old(source).inputs().links.live.contains(parent),
    ensures final(source).inputs() == old(source).inputs(),
        if let ChildReaders::Share(axis) = readers {
            final(source).seeded() == old(source).seeded() + share_readers(old(source).inputs(), parent, axis,
                old(source).inputs().links.children[parent].len())
        } else { true },
        if let ChildReaders::Final { axis, grid_main } = readers {
            final(source).seeded() == old(source).seeded() + final_child_readers(
                old(source).inputs(), parent, axis, grid_main, old(source).inputs().links.children[parent].len())
        } else { true },
        if let ChildReaders::Available { stack, horizontal, vertical } = readers {
            final(source).seeded() == old(source).seeded() + available_requests(
                old(source).inputs(), parent, stack, horizontal, vertical, old(source).inputs().links.children[parent].len())
        } else { true },
    no_unwind
))]
fn request_children<S: Access + ?Sized>(source: &mut S, parent: S::Id, readers: ChildReaders) {
    let mut next = source.first_id(parent);
    #[cfg(verus_keep_ghost)]
    let mut index = first_index();
    #[cfg(verus_keep_ghost)]
    let prior = remember_seeds(source);
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant source.inputs() == old(source).inputs(), source.inputs().links.valid(),
            source.inputs().links.live.contains(parent), next == source.inputs().links.child(parent, index@),
            0 <= index@ <= source.inputs().links.children[parent].len(),
            prior@ == old(source).seeded(),
            if let ChildReaders::Share(axis) = readers {
                source.seeded() == prior@ + share_readers(source.inputs(), parent, axis, index@ as nat)
            } else { true },
            if let ChildReaders::Final { axis, grid_main } = readers {
                source.seeded() == prior@ + final_child_readers(source.inputs(), parent, axis, grid_main, index@ as nat)
            } else { true },
            if let ChildReaders::Available { stack, horizontal, vertical } = readers {
                source.seeded() == prior@ + available_requests(source.inputs(), parent, stack, horizontal, vertical, index@ as nat)
            } else { true },
        decreases source.inputs().links.children[parent].len() - index@,
    ))]
    loop {
        let Some(child) = next else { return; };
        #[cfg(verus_keep_ghost)]
        proof! { assert(child == source.inputs().links.children[parent][index@]); }
        next = source.following_id(
            child,
            #[cfg(verus_keep_ghost)] parent,
            #[cfg(verus_keep_ghost)] index,
        );
        if !source.parameters(child).disabled {
            match readers {
                ChildReaders::Share(axis) => {
                    if stack_parent(source, child, axis).is_some() {
                        declarations(source, child, axis, Filter::ParentShare);
                    }
                }
                ChildReaders::Final { axis, grid_main } => {
                    child_final(source, child, X, axis, grid_main);
                    child_final(source, child, Y, axis, grid_main);
                }
                ChildReaders::Available { stack, horizontal, vertical } => {
                    let in_flow = !source.parameters(child).free_placement;
                    if horizontal {
                        let in_stack = same_axis(stack, X) && in_flow;
                        declarations(source, child, X, Filter::ParentFinal { in_stack });
                    }
                    if vertical {
                        let in_stack = same_axis(stack, Y) && in_flow;
                        declarations(source, child, Y, Filter::ParentFinal { in_stack });
                    }
                }
            }
        }
        #[cfg(verus_keep_ghost)]
        {
            proof! {
                if let ChildReaders::Share(axis) = readers {
                    let result = share_readers(source.inputs(), parent, axis, (index@ + 1) as nat);
                    assert(source.seeded() =~= prior@ + result);
                }
                if let ChildReaders::Final { axis, grid_main } = readers {
                    let result = final_child_readers(source.inputs(), parent, axis, grid_main, (index@ + 1) as nat);
                    assert(source.seeded() =~= prior@ + result);
                }
                if let ChildReaders::Available { stack, horizontal, vertical } = readers {
                    let result = available_requests(source.inputs(), parent, stack, horizontal, vertical, (index@ + 1) as nat);
                    assert(source.seeded() =~= prior@ + result);
                }
            }
            index = next_index(index);
        }
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.valid(), old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded() + final_readers(old(source).inputs(), node, axis),
        same_axis(stack_axis((old(source).inputs().parameters)(node).children_layout), axis)
            ==> final(source).seeded().skip(old(source).seeded().len() as int).contains((node, axis, Kind::EvenShare)),
    no_unwind
))]
fn notify_final<S: Access + ?Sized>(source: &mut S, node: S::Id, axis: Axis) {
    let other = axis.other();
    let grid_main = match source.parameters(node).children_layout {
        ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } =>
            main_axis.index() == axis.index(),
        _ => false,
    };
    let constrained = dependency_rules::reads_intrinsic_constraint(
        source.parameters(node).intrinsic_reads_other_axis(other), grid_main,
    );
    declarations(source, node, other, Filter::OppositeFinal { constrained });
    #[cfg(verus_keep_ghost)]
    let before_share = remember_seeds(source);
    if same_axis(stack_axis(source.parameters(node).children_layout), axis) {
        source.enqueue(node, axis, Kind::EvenShare);
    }
    request_children(source, node, ChildReaders::Final { axis, grid_main });
    #[cfg(verus_keep_ghost)]
    let before_parent = remember_seeds(source);
    if let Some(parent) = stack_parent(source, node, axis) {
        if !any_fill(source, node, axis) { source.enqueue(parent, axis, Kind::EvenShare); }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let input = old(source).inputs();
        let parent = stack_parent_of(input, node, axis);
        let suffix = if parent.is_some() && !has_fill(input, node, axis) {
            seq![(parent.unwrap(), axis, Kind::EvenShare)]
        } else { Seq::empty() };
        assert(source.seeded() =~= before_parent@ + suffix);
        assert(source.seeded() =~= old(source).seeded() + final_readers(input, node, axis));
        if same_axis(stack_axis((source.inputs().parameters)(node).children_layout), axis) {
            let at = before_share@.len() as int;
            let start = old(source).seeded().len() as int;
            let appended = source.seeded().skip(start);
            assert(start <= at < source.seeded().len());
            assert(source.seeded()[at] == (node, axis, Kind::EvenShare));
            assert(appended[at - start] == (node, axis, Kind::EvenShare));
        }
    }
}

/// A changed slot wakes the corresponding parent, child and same-node readers.
/// Each requested ID comes from the live source or one of its stable links.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.valid(), old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        kind is EvenShare ==> final(source).seeded() == old(source).seeded()
            + share_readers(old(source).inputs(), node, axis, old(source).inputs().links.children[node].len()),
        kind is Flow ==> final(source).seeded() == old(source).seeded(),
        kind is Final ==> final(source).seeded() == old(source).seeded() + final_readers(old(source).inputs(), node, axis),
        kind is Final && same_axis(stack_axis((old(source).inputs().parameters)(node).children_layout), axis)
            ==> final(source).seeded().skip(old(source).seeded().len() as int).contains((node, axis, Kind::EvenShare)),
        (kind is Regular || kind is Min || kind is Max) ==> final(source).seeded() == old(source).seeded()
            + declaration_readers(old(source).inputs(), node, axis, kind),
    no_unwind
))]
pub(crate) fn notify<S: Access + ?Sized>(source: &mut S, node: S::Id, axis: Axis, kind: Kind) {
    match kind {
        Kind::EvenShare => request_children(source, node, ChildReaders::Share(axis)),
        Kind::Final => notify_final(source, node, axis),
        Kind::Flow => {}
        declared => {
            source.enqueue(node, axis, Kind::Final);
            #[cfg(verus_keep_ghost)]
            proof! { assert(source.seeded() =~= old(source).seeded() + seq![(node, axis, Kind::Final)]); }
            if source.parameters(node).free_placement { return; }
            let Some(parent) = source.parent_id(node) else { return; };
            let Some(size) = source.read_declaration(node, axis, declared) else { return; };
            let form = size.dependency_form();
            if same_axis(stack_axis(source.parameters(parent).children_layout), axis)
                && any_fill(source, node, axis) && form.contributes_to_share()
            {
                source.enqueue(parent, axis, Kind::EvenShare);
            }
            if form.contributes_to_intrinsic() {
                declarations(source, parent, axis, Filter::Intrinsic);
            }
            #[cfg(verus_keep_ghost)]
            proof! {
                assert(source.seeded() =~= old(source).seeded() + declaration_readers(old(source).inputs(), node, axis, kind));
            }
        }
    }
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(fraction =>
    requires old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        fraction == changed_fraction(old(source).inputs(), node, axis, mask),
        final(source).seeded() == old(source).seeded() + masked_declarations(node, axis, mask),
    no_unwind
))]
fn changed_declarations<S: Access + ?Sized>(source: &mut S, node: S::Id, axis: Axis, mask: u8) -> bool {
    let mut fraction = false;
    if declaration_changed(mask, cycle_rules::slot_index(axis.index(), Kind::Regular)) {
        source.enqueue(node, axis, Kind::Regular);
        fraction = matches!(source.parameters(node).size.component(axis), Size::Frac(_));
    }
    if declaration_changed(mask, cycle_rules::slot_index(axis.index(), Kind::Min)) {
        source.enqueue(node, axis, Kind::Min);
    }
    if declaration_changed(mask, cycle_rules::slot_index(axis.index(), Kind::Max)) {
        source.enqueue(node, axis, Kind::Max);
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(source.seeded() =~= old(source).seeded() + masked_declarations(node, axis, mask)); }
    fraction
}

#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verifier::allow(autoderive_clone_without_spec))]
#[derive(Clone, Copy)]
pub(crate) struct SeedParent<I> {
    pub(crate) id: I,
    pub(crate) layout: ChildrenLayout,
}

#[inline(always)]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(work =>
    requires old(source).inputs().links.live.contains(node),
        parent.is_some() ==> old(source).inputs().links.live.contains(parent.unwrap().id),
    ensures final(source).inputs() == old(source).inputs(),
        work == axis_edit_seeds(old(source).inputs(), node, axis, change, fraction, parent, stack, grid),
        final(source).seeded() == old(source).seeded() + edit_axis_requests(old(source).inputs(), node, axis, work, parent),
    no_unwind
))]
fn seed_axis<S: Access + ?Sized>(
    source: &mut S, node: S::Id, axis: Axis, change: NodeChange, fraction: bool,
    parent: Option<SeedParent<S::Id>>, stack: Option<Axis>, grid: Option<Axis>,
) -> Seeds {
    let (placed_parent, parent_stack) = match parent {
        Some(parent) => (!matches!(parent.layout, ChildrenLayout::Free), stack_axis(parent.layout)),
        None => (false, None),
    };
    let params = source.parameters(node);
    let inputs = AxisEdits {
        inner: *change.inner.component(axis), other_inner: *change.inner.component(axis.other()),
        content: change.content, margin: *change.margin.component(axis), weight: change.fill_weight,
        regular_fraction: fraction,
    };
    let work = inputs.seeds(Context {
        in_flow: !params.free_placement, placed_parent, parent_stack_axis: same_axis(parent_stack, axis),
        stack_axis: same_axis(stack, axis), width_grid: grid.is_some(), grid_main: same_axis(grid, axis),
        wraps_text: params.text_wraps_on(axis),
    });
    if work.own_intrinsic || work.own_fill {
        declarations(source, node, axis, Filter::Own { intrinsic: work.own_intrinsic, fill: work.own_fill });
    }
    if work.own_final { source.enqueue(node, axis, Kind::Final); }
    if work.own_share { source.enqueue(node, axis, Kind::EvenShare); }
    if let Some(parent) = parent {
        if work.parent_intrinsic { declarations(source, parent.id, axis, Filter::FitContent); }
        if work.parent_share { source.enqueue(parent.id, axis, Kind::EvenShare); }
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(work == axis_edit_seeds(old(source).inputs(), node, axis, change, fraction, parent, stack, grid)) by {
            reveal(axis_edit_seeds);
        };
        assert(source.seeded() =~= old(source).seeded() + edit_axis_requests(old(source).inputs(), node, axis, work, parent)) by {
            reveal(edit_axis_requests);
        };
    }
    work
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.valid(), old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded()
            + extra_edit_requests(old(source).inputs(), node, change, horizontal, vertical),
    no_unwind
))]
fn seed_additional_edits<S: Access + ?Sized>(
    source: &mut S, node: S::Id, change: NodeChange, horizontal: bool, vertical: bool,
) {
    let parent = match source.parent_id(node) {
        Some(id) => Some(SeedParent { id, layout: source.parameters(id).children_layout }),
        None => None,
    };
    let layout = source.parameters(node).children_layout;
    let stack = stack_axis(layout);
    let grid = match layout {
        ChildrenLayout::Grid { columns: MainAxisCellSize::Width(_), main_axis, .. } => Some(main_axis),
        _ => None,
    };
    let x = seed_axis(source, node, X, change, horizontal, parent, stack, grid);
    let y = seed_axis(source, node, Y, change, vertical, parent, stack, grid);
    if x.child_available || y.child_available {
        request_children(source, node, ChildReaders::Available {
            stack, horizontal: x.child_available, vertical: y.child_available,
        });
    }
    #[cfg(verus_keep_ghost)]
    proof! {
        let input = old(source).inputs();
        assert(parent == edited_parent(input, node));
        assert(grid == width_grid_main((input.parameters)(node).children_layout));
        assert(stack == stack_axis((input.parameters)(node).children_layout));
        assert(x == axis_edit_seeds(input, node, X, change, horizontal, parent, stack, grid));
        assert(y == axis_edit_seeds(input, node, Y, change, vertical, parent, stack, grid));
        let local = edit_axis_requests(input, node, X, x, parent) + edit_axis_requests(input, node, Y, y, parent);
        let additional = if x.child_available || y.child_available {
            local + available_requests(input, node, stack, x.child_available, y.child_available,
                input.links.children[node].len())
        } else { local };
        assert(additional == extra_edit_requests(input, node, change, horizontal, vertical)) by {
            reveal(extra_edit_requests);
        };
        assert(source.seeded() =~= old(source).seeded() + additional);
    }
}

/// Seed concrete declarations, then notify affected siblings and children.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.valid(), old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded() + declaration_requests(old(source).inputs(), node, change),
        (old(source).inputs().parameters)(node).disabled ==> final(source).seeded() == old(source).seeded(),
        !(old(source).inputs().parameters)(node).disabled ==>
            final(source).seeded().take((old(source).seeded().len() + edited_declarations(node, change).len()) as int)
                == old(source).seeded() + edited_declarations(node, change),
    no_unwind
))]
pub(crate) fn edited<S: Access + ?Sized>(source: &mut S, node: S::Id, change: NodeChange) {
    if source.parameters(node).disabled {
        return;
    }
    let horizontal = changed_declarations(source, node, X, change.declared);
    let vertical = changed_declarations(source, node, Y, change.declared);
    #[cfg(verus_keep_ghost)]
    proof! { assert(source.seeded() =~= old(source).seeded() + edited_declarations(node, change)); }
    if !change.inner.x && !change.inner.y && !change.margin.x && !change.margin.y
        && !change.content && !change.fill_weight && !horizontal && !vertical
    {
        return;
    }
    seed_additional_edits(source, node, change, horizontal, vertical);
    #[cfg(verus_keep_ghost)]
    proof! {
        assert(source.seeded() =~= old(source).seeded() + declaration_requests(old(source).inputs(), node, change));
    }
}

#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded() + content_requests(old(source).inputs(), node),
    no_unwind
))]
pub(crate) fn content_edited<S: Access + ?Sized>(source: &mut S, node: S::Id) {
    if !source.parameters(node).disabled {
        declarations(source, node, X, Filter::FitContent);
        declarations(source, node, Y, Filter::FitContent);
    }
    #[cfg(verus_keep_ghost)]
    proof! { assert(source.seeded() =~= old(source).seeded() + content_requests(old(source).inputs(), node)); }
}

#[cfg(verus_keep_ghost)]
verus! {

pub(crate) open spec fn wrap_cross_axis(axis: Axis) -> Axis {
    if axis is X { Y } else { X }
}

/// The Wrap-specific suffix of the ordinary ranked notification.
pub(crate) open spec fn wrap_readers<I>(inputs: ReaderInputs<I>, node: I, axis: Axis, kind: Kind)
    -> Seq<(I, Axis, Kind)>
{
    let style = (inputs.parameters)(node);
    let own = match style.children_layout {
        ChildrenLayout::Wrap { axis: main, .. } => {
            if kind is EvenShare && main.index() == axis.index() {
                seq![(node, wrap_cross_axis(axis), Kind::Flow)]
            } else if kind is Flow && main.index() != axis.index() {
                filtered_kinds(inputs, node, axis, Filter::Intrinsic, 3)
            } else { Seq::empty() }
        }
        _ => Seq::empty(),
    };
    let parent_requests =
        if !(kind is Regular || kind is Min || kind is Max) || style.free_placement || style.disabled {
            Seq::empty()
        } else {
            match (inputs.links.parents[node], (inputs.declaration)(node, axis, kind)) {
                (Some(parent), Some(size)) => match (inputs.parameters)(parent).children_layout {
                    ChildrenLayout::Wrap { axis: main, .. } => {
                        if main.index() != axis.index() && size.dependency_form().contributes_to_intrinsic() {
                            seq![(parent, axis, Kind::Flow)]
                        } else { Seq::empty() }
                    }
                    _ => Seq::empty(),
                },
                _ => Seq::empty(),
            }
        };
    own + parent_requests
}

/// The cross-flow producer explicitly reads the main EvenShare request.
/// Rebuilding share side words therefore wakes that producer even if its
/// ordinary scalar word is unchanged.
pub(crate) proof fn native_wrap_share_requests_flow<I: Copy>(
    inputs: ReaderInputs<I>, topology: crate::dependencies::sizing_requests::Topology<I>,
    node: I, main: Axis,
)
    requires
        match (inputs.parameters)(node).children_layout {
            ChildrenLayout::Wrap { axis, .. } => axis == main,
            _ => false,
        },
        (topology.flow_mode)(node) == crate::dependencies::sizing_requests::FlowMode::Wrap(main is Y),
    ensures ({
        let cross = wrap_cross_axis(main);
        let flow = crate::dependencies::sizing_requests::target(node, cross is Y, Kind::Flow);
        let share = crate::dependencies::sizing_requests::target(node, main is Y, Kind::EvenShare);
        let reads = crate::dependencies::sizing_requests::inputs(topology, flow);
        &&& reads.len() > 0 && reads[0] == share
        &&& wrap_readers(inputs, node, main, Kind::EvenShare) == seq![(node, cross, Kind::Flow)]
    }),
{
    use crate::dependencies::sizing_requests as requests;
    let rows = requests::wrap_rows(topology, node, main is Y);
    let own = crate::wrap_schedule::own::<I>(crate::wrap_schedule::kernel::Producer::Cross);
    let prefix = seq![requests::wrap_slot(node, main is Y, own)];
    let trailing = crate::wrap_schedule::child_requests(rows, crate::wrap_schedule::kernel::Producer::Cross, rows.len());
    let prefix_and_rows = prefix + trailing.map_values(|req| requests::wrap_slot(node, main is Y, req));
    assert(prefix_and_rows[0] == prefix[0]);
}

pub(crate) open spec fn changed_on_axis(changes: Xy<bool>, axis: Axis) -> bool {
    if axis is X { changes.x } else { changes.y }
}

/// Direct line-geometry edits can wake a Flow slot without a changed size word.
pub(crate) open spec fn wrap_edit_requests<I>(inputs: ReaderInputs<I>, node: I, change: NodeChange)
    -> Seq<(I, Axis, Kind)>
{
    let style = (inputs.parameters)(node);
    if style.disabled {
        Seq::empty()
    } else {
        let own = match style.children_layout {
            ChildrenLayout::Wrap { axis, .. } => {
                let cross = wrap_cross_axis(axis);
                if changed_on_axis(change.inner, cross) { seq![(node, cross, Kind::Flow)] }
                else { Seq::empty() }
            }
            _ => Seq::empty(),
        };
        let parent = if style.free_placement {
            Seq::empty()
        } else {
            match inputs.links.parents[node] {
                Some(parent) => match (inputs.parameters)(parent).children_layout {
                    ChildrenLayout::Wrap { axis, .. } => {
                        let cross = wrap_cross_axis(axis);
                        if changed_on_axis(change.margin, cross) { seq![(parent, cross, Kind::Flow)] }
                        else { Seq::empty() }
                    }
                    _ => Seq::empty(),
                }
                None => Seq::empty(),
            }
        };
        own + parent
    }
}

}

/// Flow notification for a wrapping parent whose in-flow children never read
/// its line share or cross extent. The rest of the ranked notifications remain
/// the ordinary numeric path.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded() + wrap_readers(old(source).inputs(), node, axis, kind),
    no_unwind
))]
pub(crate) fn wrap_notify<S: Access + ?Sized>(source: &mut S, node: S::Id, axis: Axis, kind: Kind) {
    if let ChildrenLayout::Wrap { axis: main, .. } = source.parameters(node).children_layout {
        if matches!(kind, Kind::EvenShare) && main.index() == axis.index() {
            source.enqueue(node, axis.other(), Kind::Flow);
        }
        if matches!(kind, Kind::Flow) && main.index() != axis.index() {
            declarations(source, node, axis, Filter::Intrinsic);
        }
    }
    if !matches!(kind, Kind::Regular | Kind::Min | Kind::Max)
        || source.parameters(node).free_placement
        || source.parameters(node).disabled
    { return; }
    let Some(parent) = source.parent_id(node) else { return; };
    if matches!(source.parameters(parent).children_layout, ChildrenLayout::Wrap { axis: main, .. }
        if main.index() != axis.index())
    {
        if let Some(size) = source.read_declaration(node, axis, kind) {
            if size.dependency_form().contributes_to_intrinsic() { source.enqueue(parent, axis, Kind::Flow); }
        }
    }
}

/// Line spacing and a child's cross margin are direct inputs to the line
/// producer, even when every declared size word compares equal.
#[inline]
#[cfg_attr(verus_keep_ghost, verus_verify)]
#[cfg_attr(verus_keep_ghost, verus_spec(
    requires old(source).inputs().links.live.contains(node),
    ensures final(source).inputs() == old(source).inputs(),
        final(source).seeded() == old(source).seeded() + wrap_edit_requests(old(source).inputs(), node, change),
    no_unwind
))]
pub(crate) fn wrap_edit<S: Access + ?Sized>(source: &mut S, node: S::Id, change: NodeChange) {
    let p = source.parameters(node);
    if p.disabled { return; }
    let placed = !p.free_placement;
    if let ChildrenLayout::Wrap { axis, .. } = p.children_layout {
        let cross = axis.other();
        if *change.inner.component(cross) { source.enqueue(node, cross, Kind::Flow); }
    }
    if placed {
        if let Some(parent) = source.parent_id(node) {
            if let ChildrenLayout::Wrap { axis, .. } = source.parameters(parent).children_layout {
                let cross = axis.other();
                if *change.margin.component(cross) { source.enqueue(parent, cross, Kind::Flow); }
            }
        }
    }
}

#[cfg(all(test, not(verus_keep_ghost)))]
mod tests {
    use super::*;
    use crate::Arrange;

    struct Recording {
        params: [LayoutParams; 6],
        requests: Vec<(usize, Axis, Kind)>,
    }

    impl Model for Recording { type Id = usize; }

    impl Access for Recording {
        fn parameters(&self, node: usize) -> &LayoutParams { &self.params[node] }

        fn read_declaration(&self, node: usize, axis: Axis, kind: Kind) -> Option<Size> {
            let params = &self.params[node];
            match kind {
                Kind::Regular => Some(*params.size.component(axis)),
                Kind::Min => *params.min_size.component(axis),
                Kind::Max => *params.max_size.component(axis),
                _ => None,
            }
        }

        fn parent_id(&self, node: usize) -> Option<usize> { (node > 0).then_some(0) }

        fn first_id(&self, node: usize) -> Option<usize> { (node == 0).then_some(1) }

        fn following_id(&self, node: usize) -> Option<usize> {
            (node + 1 < self.params.len()).then_some(node + 1)
        }

        fn enqueue(&mut self, node: usize, axis: Axis, kind: Kind) {
            self.requests.push((node, axis, kind));
        }
    }

    #[test]
    fn changed_share_notifies_only_its_enabled_flow_readers_in_order() {
        let mut recording = Recording {
            params: [LayoutParams::DEFAULT; 6],
            requests: vec![(0, Y, Kind::Regular)],
        };
        recording.params[0].children_layout = ChildrenLayout::Stack { axis: X, arrange: Arrange::Start, spacing: 2.0 };
        recording.params[1].min_size.x = Some(Size::Fill);
        recording.params[1].max_size.x = Some(Size::Pixels(64.0));
        recording.params[2].disabled = true;
        recording.params[3].free_placement = true;
        recording.params[4].size.x = Size::Frac(0.5);
        recording.params[4].max_size.x = Some(Size::Fill);
        recording.params[5].size.x = Size::FitContent;

        notify(&mut recording, 0, X, Kind::EvenShare);
        notify(&mut recording, 0, Y, Kind::EvenShare);
        notify(&mut recording, 0, X, Kind::Flow);
        assert_eq!(recording.requests, [
            (0, Y, Kind::Regular), (1, X, Kind::Regular), (1, X, Kind::Min), (4, X, Kind::Max),
        ]);
    }

    #[test]
    fn changed_declaration_notifies_own_final_before_parent_readers() {
        let mut recording = Recording { params: [LayoutParams::DEFAULT; 6], requests: Vec::new() };
        recording.params[0].children_layout = ChildrenLayout::Stack { axis: X, arrange: Arrange::Start, spacing: 2.0 };
        recording.params[0].size.x = Size::FitContent;
        recording.params[0].min_size.x = Some(Size::FitContent);
        recording.params[1].max_size.x = Some(Size::Pixels(64.0));
        recording.params[3].free_placement = true;

        notify(&mut recording, 1, X, Kind::Max);
        notify(&mut recording, 3, X, Kind::Regular);
        notify(&mut recording, 4, X, Kind::Min);
        assert_eq!(recording.requests, [
            (1, X, Kind::Final), (0, X, Kind::EvenShare), (0, X, Kind::Regular),
            (0, X, Kind::Min), (3, X, Kind::Final), (4, X, Kind::Final),
        ]);
    }
}
