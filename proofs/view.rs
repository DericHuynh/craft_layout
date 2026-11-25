//! Incremental and full evaluation of an ordered layout dependency trace.
#![feature(proc_macro_hygiene)]
use vstd::prelude::*;

pub mod fill;
pub mod dependencies;
pub mod queue_view;
pub mod sizing_tape;
pub mod ranked_full;
pub mod frame_equivalence;
pub mod queue_storage;
pub mod history;
pub mod numeric_frame;
pub mod regional_frame;
pub mod regions;
pub mod structural_plan;
pub mod mode_boundary;
pub mod retained_branch;
pub mod removal;
pub mod margin_storage;
#[path = "../src/input_words.rs"]
mod input_words;
pub mod block_flow;
pub mod block_schedule;
pub mod block_frame;
pub mod stack_share;
pub mod leaf;
#[path = "../src/measurement.rs"]
pub mod measurement_contract;
pub mod traversal;
pub mod tree_walk;
#[path = "../src/vec_memory.rs"]
mod vec_memory;
#[path = "../src/work_stack.rs"]
mod work_stack;
#[path = "../src/placement_walk.rs"]
mod placement_walk;
#[path = "../src/placement_adapter.rs"]
mod placement_adapter;
#[path = "../src/prepare_walk.rs"]
mod prepare_walk;
#[path = "../src/layout_tree/text_measure_cache.rs"]
mod text_measure_cache;
#[path = "../src/layout_tree/text_windows.rs"]
pub mod text_windows;
#[path = "../src/layout_tree/svg_control.rs"]
mod svg_control;
#[path = "../src/layout_tree/structural_guard.rs"]
mod owned_guard;
#[path = "../src/layout_tree/output.rs"]
mod owned_output;
#[path = "../src/layout_tree/records.rs"]
mod owned_records;
pub mod fixed_leaf_cache;
pub mod topology_state;
pub mod stack_line;
pub mod placement_batch;
pub mod wrap_lines;
pub mod wrap_metrics;
pub mod wrap_schedule;
pub mod wrap_replay;
pub mod cycles;
pub mod production_schedule;
pub mod replay_view;
pub mod replay_prefix;
pub mod prefix_cache;
pub mod planner_boundary;
pub mod cut_widening;
pub mod replay_retained;
pub mod replay_history;
pub mod mixed_regions;
pub mod replay_publication;
pub mod checked_view;
#[path = "../src/incremental/publication.rs"]
mod publication;
pub mod grid;
pub mod structural;
#[path = "../src/layout_tree/stack_tail.rs"]
mod stack_tail;
pub(crate) use cycles::kernel as cycle_rules;
pub(crate) use fill::budget as fill_budget;
pub(crate) use structural::kernel as structural_changes;
pub mod placement;
use placement::geometry::{Anchor, Arrange, Pos, WindowOverflow};
#[path = "../src/declarations.rs"]
mod declarations;
#[path = "../src/node_flags.rs"]
mod node_flags;
#[path = "../src/node_data.rs"]
mod node_data;
#[path = "../src/prepare_frame.rs"]
mod prepare_frame;
#[path = "../src/prepare_leaf.rs"]
mod prepare_leaf;
#[path = "../src/layout_tree/batch/warm/ratio.rs"]
mod batch_ratio;
#[path = "../src/prepare_nodes.rs"]
mod prepare_nodes;
#[path = "../src/sizing_pass.rs"]
mod sizing_pass;
#[path = "../src/sizing_fill.rs"]
mod sizing_fill;
#[path = "../src/packed_stack_leaf.rs"]
mod packed_stack_leaf;
#[path = "../src/full_layout.rs"]
mod full_layout;
#[path = "../src/layout_tree/solve_frame.rs"]
mod owned_solve_frame;
pub mod placement_complete;
pub mod pixel_dispatch;
pub mod invalidation;
pub mod retained_view;
use placement::PlacementWork;

verus! {

// An incarnation distinguishes a new node reusing a host ID. Each measurement
// slot, flow result and final placement of that incarnation has its own phase.
pub enum Phase {
    Measurement(nat),
    Placement,
}

pub struct Key {
    pub incarnation: nat,
    pub phase: Phase,
}

pub type RectBits = (u32, u32, u32, u32);
pub struct Geometry {
    pub absolute: RectBits,
    pub local: RectBits,
}

pub enum Value {
    Words(Seq<u32>),
    Rects(Geometry),
}

// Local inputs include the rule, its declared numeric bits, viewport/scale
// when read, and the registered version of any host measurement input.
// The ordered reads include sibling, parent-frame and snapped-origin inputs.
pub struct Rule {
    pub local: Seq<int>,
    pub reads: Seq<Key>,
}

pub enum Work {
    Size { recompute: bool },
    Place { path: Seq<placement::PathEdge>, root_force: bool, mark: PlacementWork },
}

pub struct Step {
    pub key: Key,
    pub rule: Rule,
    pub work: Work,
}

pub struct Entry {
    pub rule: Rule,
    pub args: Seq<Value>,
    pub value: Value,
}

pub type Cache = Map<Key, Entry>;
pub struct Eval {
    pub measure: spec_fn(Key, Rule, Seq<Value>) -> Seq<u32>,
    pub place: spec_fn(Key, Rule, Seq<Value>) -> Geometry,
}

impl Eval {
    pub open spec fn apply(self, key: Key, rule: Rule, inputs: Seq<Value>) -> Value {
        match key.phase {
            Phase::Measurement(_) => Value::Words((self.measure)(key, rule, inputs)),
            Phase::Placement => Value::Rects((self.place)(key, rule, inputs)),
        }
    }
}

pub open spec fn writes(work: Work) -> bool {
    match work {
        Work::Size { recompute } => recompute,
        Work::Place { path, root_force, mark } => {
            let route = placement::placement_route(path, root_force);
            route.visited && mark.writes(route.force)
        },
    }
}

pub open spec fn valid_route(work: Work) -> bool {
    match work {
        Work::Size { .. } => true,
        Work::Place { path, mark, .. } => placement::routes_to(path, mark),
    }
}

// A planner may request an entire ancestor subtree. A descendant does not
// need an individual mark for that request to cover its output.
pub open spec fn requested(work: Work) -> bool {
    match work {
        Work::Size { recompute } => recompute,
        Work::Place { path, root_force, mark } =>
            root_force || mark == PlacementWork::Subtree || placement::ancestor_writes(path),
    }
}

pub proof fn requested_work_is_executed(work: Work)
    requires valid_route(work),
    ensures writes(work) == requested(work),
{
    if let Work::Place { path, root_force, mark } = work {
        placement::lemma_path_reached(path, mark, root_force);
    }
}

pub open spec fn args(rule: Rule, earlier: Cache) -> Seq<Value> {
    Seq::new(rule.reads.len(), |i: int| earlier[rule.reads[i]].value)
}

pub open spec fn sound(cache: Cache, eval: Eval) -> bool {
    forall |key: Key| #[trigger] cache.contains_key(key) ==> {
        let entry = cache[key];
        entry.value == eval.apply(key, entry.rule, entry.args)
    }
}

pub open spec fn coherent(cache: Cache) -> bool {
    forall |key: Key| #[trigger] cache.contains_key(key) ==> {
        let entry = cache[key];
        &&& entry.args == args(entry.rule, cache)
        &&& forall |i: int| 0 <= i < entry.rule.reads.len() ==>
            #[trigger] cache.contains_key(entry.rule.reads[i])
    }
}

// Both builds start with an empty current map. Skips fetch from the previous
// frame by identity. The stored rule and arguments are ghost observations,
// independent of the representation or size of the production cache.
pub open spec fn build(steps: Seq<Step>, old: Cache, eval: Eval, full: bool) -> Cache
    decreases steps.len(),
{
    if steps.len() == 0 {
        Map::empty()
    } else {
        let step = steps.last();
        let earlier = build(steps.drop_last(), old, eval, full);
        let inputs = args(step.rule, earlier);
        let value = if full || writes(step.work) {
            eval.apply(step.key, step.rule, inputs)
        } else {
            old[step.key].value
        };
        earlier.insert(step.key, Entry { rule: step.rule, args: inputs, value })
    }
}

// Local proof obligations for a real trace. Validate dependencies against the
// incremental prefix only. No premise mentions the new full-build result.
pub open spec fn covered(steps: Seq<Step>, old: Cache, eval: Eval) -> bool
    decreases steps.len(),
{
    if steps.len() == 0 {
        true
    } else {
        let step = steps.last();
        let earlier = build(steps.drop_last(), old, eval, false);
        covered(steps.drop_last(), old, eval)
        && !earlier.contains_key(step.key)
        && (forall |i: int| 0 <= i < step.rule.reads.len()
            ==> #[trigger] earlier.contains_key(step.rule.reads[i]))
        && (!writes(step.work) ==> (
            old.contains_key(step.key)
            && old[step.key].rule == step.rule
            && old[step.key].args == args(step.rule, earlier)
        ))
    }
}

// The new cache equals a build that recomputes every step from empty storage.
// Soundness is preserved so the resulting cache can seed the next edit.
pub proof fn incremental_matches_full(steps: Seq<Step>, old: Cache, eval: Eval)
    requires sound(old, eval), covered(steps, old, eval),
    ensures
        build(steps, old, eval, false) == build(steps, Map::empty(), eval, true),
        sound(build(steps, old, eval, false), eval),
        coherent(build(steps, old, eval, false)),
    decreases steps.len(),
{
    if steps.len() > 0 {
        let prefix = steps.drop_last();
        incremental_matches_full(prefix, old, eval);
        let step = steps.last();
        let earlier = build(prefix, old, eval, false);
        let inputs = args(step.rule, earlier);
        if !writes(step.work) {
            assert(old.contains_key(step.key));
            assert(old[step.key].value == eval.apply(step.key, old[step.key].rule, old[step.key].args));
        }
        let result = build(steps, old, eval, false);
        assert forall |k: Key| #[trigger] result.contains_key(k) implies
            result[k].value == eval.apply(k, result[k].rule, result[k].args) by {
            if k != step.key {
                assert(earlier.contains_key(k));
            }
        }
        assert forall |k: Key| #[trigger] result.contains_key(k) implies {
            let entry = result[k];
            &&& entry.args == args(entry.rule, result)
            &&& forall |i: int| 0 <= i < entry.rule.reads.len() ==>
                #[trigger] result.contains_key(entry.rule.reads[i])
        } by {
            let rule = result[k].rule;
            if k != step.key {
                assert(earlier.contains_key(k));
            }
            assert forall |i: int| 0 <= i < rule.reads.len() implies
                #[trigger] result.contains_key(rule.reads[i])
                && earlier.contains_key(rule.reads[i])
                && earlier[rule.reads[i]] == result[rule.reads[i]] by {
                if k != step.key {
                    assert(earlier[k].rule == rule);
                }
            }
            assert(args(rule, earlier) =~= args(rule, result));
        }
    }
}

pub open spec fn has_rects(order: Seq<Key>, cache: Cache) -> bool {
    forall |i: int| 0 <= i < order.len() ==> {
        &&& #[trigger] cache.contains_key(order[i])
        &&& cache[order[i]].value is Rects
    }
}

}
