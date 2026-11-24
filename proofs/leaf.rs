//! An accepted leaf slot keeps its bits and dependency rank when its parent changes.
use super::dependencies::{self, Part, Edge, Source, rules as dependency_rules};
use dependency_rules::Form;
use vstd::prelude::*;
#[path = "../src/leaf_retention.rs"]
pub(crate) mod kernel;
use kernel::LeafInput;

verus! {

// An ordinary leaf has no child reads, width-dependent grid or flow computation.
// Match the retention classifier against the full solver's available slot reads.
pub proof fn classifier_covers_full_reads(form: Form, constrained: bool, source: Part, edge: Edge)
    requires !edge.grid_main, !(edge.source is Child), edge.intrinsic_other == constrained,
    ensures
        dependencies::full_read(Part::Declared(form), source, edge) ==> match kernel::input(form, constrained) {
            LeafInput::Local => false,
            LeafInput::OppositeFinal => edge.source is SameNode && !edge.same_axis && source is Final,
            LeafInput::External => edge.source is Parent,
        },
{}

/// A free parent (or a stack with no live share slot) can keep its solved
/// dimensions across child-list edits when its declarations do not read children.
/// A stack child with a main-axis fraction or Fill is excluded by the sibling
/// scan: those are the declarations whose available space can change with gaps.
pub proof fn independent_parent_boundary(parent: Part, child: Part, edge: Edge)
    requires edge.source is Child,
        match parent { Part::Declared(f) => !f.reads_children(), Part::Final => true, Part::Share => false },
    ensures !dependencies::full_read(parent,child,edge),
{}

pub proof fn independent_stack_item(form: Form, same_axis: bool, grid_main: bool)
    requires !(form is Fraction), !(form is Fill), !grid_main,
    ensures !dependencies::full_read(Part::Declared(form), Part::Share,
                Edge { source: Source::Parent, same_axis, in_flow:true, stack_axis:true,
                       child_has_fill:false, grid_main, intrinsic_other:false }),
            !dependencies::full_read(Part::Declared(form), Part::Final,
                Edge { source: Source::Parent, same_axis, in_flow:true, stack_axis:true,
                       child_has_fill:false, grid_main, intrinsic_other:false }),
{}

pub struct Decl {
    pub form: Form,
    pub constrained: bool,
    // Local style bits, intrinsic content version and the declaration's identity.
    pub local: Seq<int>,
}

pub type Slot = (u32, u16);
pub type Recompute = spec_fn(Decl, Option<Slot>) -> Slot;
pub type Finish = spec_fn(Seq<Slot>) -> Slot;

pub open spec fn slots(ds: Seq<Decl>, opposite: Slot, external: Seq<Slot>, eval: Recompute) -> Seq<Slot> {
    Seq::new(ds.len(), |i:int| {
        let d = ds[i];
        eval(d, match kernel::input(d.form, d.constrained) {
            LeafInput::Local => None, LeafInput::OppositeFinal => Some(opposite),
            LeafInput::External => Some(external[i]),
        })
    })
}

pub open spec fn stable(ds: Seq<Decl>, opposite_known: bool) -> bool {
    forall |i:int| 0 <= i < ds.len() ==> {
        let d = #[trigger] ds[i]; kernel::input(d.form, d.constrained).stable(opposite_known)
    }
}

pub proof fn stable_axis(ds: Seq<Decl>, known: bool, old_other: Slot, new_other: Slot,
    old_parent: Seq<Slot>, new_parent: Seq<Slot>, eval: Recompute)
    requires stable(ds, known), known ==> old_other == new_other,
        ds.len() == old_parent.len(), ds.len() == new_parent.len(),
    ensures slots(ds, old_other, old_parent, eval) == slots(ds, new_other, new_parent, eval),
{
    assert(slots(ds, old_other, old_parent, eval) =~= slots(ds, new_other, new_parent, eval)) by {
        assert forall |i:int| 0 <= i < ds.len() implies
            slots(ds, old_other, old_parent, eval)[i] == slots(ds, new_other, new_parent, eval)[i] by {
            let d = ds[i]; assert(kernel::input(d.form,d.constrained).stable(known));
        }
    }
}

/// First establish independence of all opposite-axis declarations. Then reuse
/// ratios and constrained content on this axis using the resulting final value.
/// The caller may have completely different available space on both axes.
pub proof fn two_axis_leaf(ds: Seq<Decl>, other: Seq<Decl>, old_input: Slot, new_input: Slot,
    parents: (Seq<Slot>, Seq<Slot>), other_parents: (Seq<Slot>, Seq<Slot>),
    eval: Recompute, finish: Finish, i: int)
    requires 0 <= i < ds.len(), ds.len() == parents.0.len(), ds.len() == parents.1.len(),
        other.len() == other_parents.0.len(), other.len() == other_parents.1.len(),
    ensures ({
        let known = stable(other, false);
        let old_final = finish(slots(other, old_input, other_parents.0, eval));
        let new_final = finish(slots(other, new_input, other_parents.1, eval));
        let old_slots = slots(ds, old_final, parents.0, eval);
        let new_slots = slots(ds, new_final, parents.1, eval);
        &&& kernel::input(ds[i].form, ds[i].constrained).stable(known) ==> old_slots[i] == new_slots[i]
        &&& stable(ds, known) ==> finish(old_slots) == finish(new_slots)
    }),
{
    let known = stable(other, false);
    if known { stable_axis(other, false, old_input, new_input, other_parents.0, other_parents.1, eval); }
    if stable(ds, known) {
        stable_axis(ds, known, finish(slots(other,old_input,other_parents.0,eval)),
            finish(slots(other,new_input,other_parents.1,eval)), parents.0, parents.1, eval);
    }
}
}
