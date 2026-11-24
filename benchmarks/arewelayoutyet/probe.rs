mod adapter;
mod pangui_template;

use adapter::KeruLayoutTree;
use pangui_template::{BenchmarkSize, SizeMode, parse_test_case};
use std::alloc::{GlobalAlloc, Layout, System};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::time::Instant;

struct CountingAllocator;
static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);
static REQUESTED_BYTES: AtomicUsize = AtomicUsize::new(0);

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

fn count_allocation(bytes: usize) {
    ALLOCATIONS.fetch_add(1, Relaxed);
    REQUESTED_BYTES.fetch_add(bytes, Relaxed);
}

unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        count_allocation(layout.size());
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        count_allocation(layout.size());
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, old: Layout, bytes: usize) -> *mut u8 {
        count_allocation(bytes);
        unsafe { System.realloc(ptr, old, bytes) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

fn window_extent(size: Option<BenchmarkSize>) -> f32 {
    match size {
        Some(BenchmarkSize { mode: SizeMode::Pixels, value }) => value,
        _ => 1000.0,
    }
}

fn measure(run: impl FnOnce()) -> (u128, usize, usize) {
    ALLOCATIONS.store(0, Relaxed);
    REQUESTED_BYTES.store(0, Relaxed);
    let start = Instant::now();
    run();
    (start.elapsed().as_nanos(), ALLOCATIONS.load(Relaxed), REQUESTED_BYTES.load(Relaxed))
}

fn main() {
    let directory = std::env::args_os().nth(1).expect("missing PanGUI template directory");
    let mut templates: Vec<PathBuf> = std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "txt"))
        .collect();
    templates.sort();

    for path in templates {
        let name = path.file_stem().unwrap().to_str().unwrap();
        let content = std::fs::read_to_string(&path).unwrap();
        let template = parse_test_case(name, &content).unwrap().root_node.unwrap();
        let mut tree = KeruLayoutTree::new(
            &template, window_extent(template.width), window_extent(template.height),
        ).unwrap_or_else(|| panic!("unsupported workload {name}"));
        let nodes = tree.node_count();
        let (_, cold_allocs, cold_bytes) = measure(|| tree.compute_layout());
        let digest = tree.geometry_hash();
        let iterations = (1_000_000 / nodes).clamp(6, 5000);
        let (elapsed, warm_allocs, warm_bytes) = measure(|| {
            for _ in 0..iterations {
                tree.mark_all_dirty();
                tree.compute_layout();
            }
        });
        assert_eq!(digest, tree.geometry_hash(), "different geometry on repeated full solve for {name}");
        println!(
            "{name}\t{nodes}\t{digest:016x}\t{}\t{cold_allocs}\t{cold_bytes}\t{warm_allocs}\t{warm_bytes}",
            elapsed as f64 / iterations as f64,
        );
    }
}
