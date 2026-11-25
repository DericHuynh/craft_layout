//! Source-linked checks for the owned stack-tail shortcut.
#![feature(proc_macro_hygiene)]

#[path = "../src/cycle_rules.rs"]
mod cycle_rules;
mod cycles {
    pub(crate) use crate::cycle_rules as kernel;
}
#[path = "../src/declarations.rs"]
mod declarations;
#[path = "../src/fill_budget.rs"]
mod fill_budget;
mod stack_line;
mod wrap_lines;
mod wrap_schedule;
mod wrap_metrics;
#[path = "../src/placement_geometry.rs"]
mod placement_geometry;
mod placement {
    pub(crate) use crate::placement_geometry as geometry;
}
#[path = "../src/dependency_rules.rs"]
mod dependency_rules;
mod dependencies {
    pub(crate) use crate::dependency_rules as rules;
}
#[path = "../src/node_flags.rs"]
mod node_flags;
#[path = "../src/prepare_frame.rs"]
mod prepare_frame;
use placement_geometry::{Anchor, Arrange, Pos, WindowOverflow};
mod structural;
pub(crate) use structural::kernel as structural_changes;
#[path = "../src/layout_tree/stack_tail.rs"]
mod stack_tail;
