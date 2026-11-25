use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static CALLS: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(0);

struct CountingAllocator;

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

fn record(bytes: usize) {
    CALLS.fetch_add(1, Relaxed);
    BYTES.fetch_add(bytes, Relaxed);
}

// SAFETY: all allocation operations forward their original arguments and
// results to the same system allocator.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        record(layout.size());
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        record(layout.size());
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, old: Layout, bytes: usize) -> *mut u8 {
        record(bytes);
        unsafe { System.realloc(ptr, old, bytes) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[derive(Clone, Copy, Default)]
pub(super) struct Sample {
    calls: usize,
    bytes: usize,
}

pub(super) const COLUMNS: &str =
    "cold_allocations\tcold_requested_bytes\twarm_allocations\twarm_requested_bytes";

pub(super) fn solve(run: impl FnOnce() -> bool) -> (Sample, bool) {
    CALLS.store(0, Relaxed);
    BYTES.store(0, Relaxed);
    let rebuilt = black_box(run());
    (
        Sample {
            calls: CALLS.load(Relaxed),
            bytes: BYTES.load(Relaxed),
        },
        rebuilt,
    )
}

pub(super) fn print(cold: Sample, samples: &mut [Sample]) {
    let calls: u128 = samples.iter().map(|sample| sample.calls as u128).sum();
    let bytes: u128 = samples.iter().map(|sample| sample.bytes as u128).sum();
    print!("{}\t{}\t{calls}\t{bytes}", cold.calls, cold.bytes);
}
