//! Count heap requests inside track sizing, with inputs allocated before the counter starts.
#[path = "../benchmarks/real_workloads/compare_upstream/src/allocations.rs"]
mod allocations;
use keru_layout::tracks::{Track, TrackAxis, TrackContribution, TrackGrid};
use keru_layout::{Axis, Xy};
use std::hint::black_box;

fn main() {
    const COLS: usize = 64;
    const ROWS: usize = 64;
    let grid = TrackGrid {
        tracks: Xy::new(
            TrackAxis::repeat(COLS as u16, Track::Content),
            TrackAxis::default(),
        ),
        gap: Xy::new(3., 0.),
        ..Default::default()
    };
    println!("scene\titems\tchecksum\t{}", allocations::COLUMNS);
    for (name, spans) in [("single", false), ("mixed", true)] {
        let mut items = Vec::with_capacity(COLS * ROWS);
        for row in 0..ROWS {
            for col in 0..COLS {
                let span = if spans && (row + col) % 8 == 0 {
                    3.min(COLS - col)
                } else {
                    1
                };
                let minimum = (18 + (col + 3 * row) % 29) as f32;
                let preferred = minimum + (8 + (col * 7 + row) % 53) as f32;
                items.push(TrackContribution {
                    tracks: col..col + span,
                    minimum: minimum * span as f32,
                    preferred: preferred * span as f32,
                });
            }
        }
        let resolve = || grid.resolve_axis(Axis::X, Some(8_192.), COLS, black_box(&items));
        let mut reference = None;
        let (cold, _) = allocations::solve(|| {
            reference = Some(resolve());
            true
        });
        let reference = reference.unwrap();
        assert_eq!(reference.0.len(), COLS);
        assert!(
            reference
                .0
                .windows(2)
                .all(|w| (w[1][0] - w[0][1] - 3.).abs() < 0.002)
        );
        let check = || resolve() == reference;
        let (warm, matched) = allocations::solve(check);
        assert!(matched);
        let checksum = reference
            .0
            .iter()
            .flatten()
            .fold(0xcbf29ce484222325u64, |hash, edge| {
                (hash ^ u64::from(edge.to_bits())).wrapping_mul(0x100000001b3)
            });
        print!("{name}\t{}\t{checksum:016x}\t", items.len());
        allocations::print(cold, &mut [warm]);
        println!();
    }
}
