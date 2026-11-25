use harness_common::{Solver, pangui_template::parse_test_case};
use std::{ffi, hint::black_box, path::Path, time::Instant};

#[repr(C)]
struct Timespec {
    seconds: ffi::c_long,
    nanoseconds: ffi::c_long,
}

unsafe extern "C" {
    fn clock_gettime(clock: ffi::c_int, result: *mut Timespec) -> ffi::c_int;
}

fn cpu_ns() -> u128 {
    const THREAD_CPU_TIME: ffi::c_int = 3;
    let mut stamp = Timespec {
        seconds: 0,
        nanoseconds: 0,
    };
    // SAFETY: The Linux clock writes into a valid, initialized timespec.
    assert_eq!(unsafe { clock_gettime(THREAD_CPU_TIME, &mut stamp) }, 0);
    stamp.seconds as u128 * 1_000_000_000 + stamp.nanoseconds as u128
}

fn shuffle<T>(items: &mut [T], seed: &mut u64) {
    for right in (1..items.len()).rev() {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        items.swap(right, (*seed as usize) % (right + 1));
    }
}

fn run(
    fixture: &str,
    groups: usize,
    mut seed: u64,
    names: &[&str],
    build: impl Fn(usize) -> Box<dyn Solver>,
) {
    let requested = std::env::var("COLD_LAYOUT_MODES").unwrap_or_default();
    let mode_indices: Vec<_> = names
        .iter()
        .enumerate()
        .filter(|(_, name)| requested.is_empty() || requested.split(',').any(|s| s == **name))
        .map(|(index, _)| index)
        .collect();
    let n = mode_indices.len();
    if n < 2 {
        return;
    }
    let mut perm_build: Vec<usize> = (0..n).collect();
    let mut perm_solve: Vec<usize> = (0..n).collect();
    // Across each block of n² samples, every mode occupies every build
    // and solve position combination exactly once.
    let mut recipes: Vec<_> = (0..n).flat_map(|a| (0..n).map(move |b| (a, b))).collect();
    for block in 0..groups {
        shuffle(&mut perm_build, &mut seed);
        shuffle(&mut perm_solve, &mut seed);
        shuffle(&mut recipes, &mut seed);
        for (sample, &(build_shift, solve_shift)) in recipes.iter().enumerate() {
            let mut solvers: Vec<Option<Box<dyn Solver>>> = (0..n).map(|_| None).collect();
            let mut build_locations = vec![0; n];
            let mut elapsed = vec![(0, 0, 0); n];
            for position in 0..n {
                let mode = perm_build[(position + build_shift) % n];
                solvers[mode] = Some(build(mode_indices[mode]));
                build_locations[mode] = position;
            }
            for solve_pos in 0..n {
                let mode = perm_solve[(solve_pos + solve_shift) % n];
                let solver = solvers[mode].as_mut().unwrap();
                let cpu_start = cpu_ns();
                let wall_start = Instant::now();
                black_box(solver).solve();
                let wall = wall_start.elapsed().as_nanos();
                elapsed[mode] = (wall, cpu_ns() - cpu_start, solve_pos);
            }
            let expected = solvers[0].as_ref().unwrap().output();
            for mode in 0..n {
                let actual = solvers[mode].as_ref().unwrap().output();
                if actual != expected {
                    let first = actual.iter().zip(&expected).position(|(a, b)| a != b);
                    panic!(
                        "{fixture} {} block {block} sample {sample}: first mismatch at {first:?}; {} vs {} nodes",
                        names[mode_indices[mode]],
                        actual.len(),
                        expected.len()
                    );
                }
                let (wall, cpu, solve_pos) = elapsed[mode];
                println!(
                    "{fixture}\t{block}\t{sample}\t{}\t{}\t{}\t{solve_pos}\t{wall}\t{cpu}",
                    names[mode_indices[mode]],
                    actual.len(),
                    build_locations[mode]
                );
            }
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let templates = args.next().expect("template folder, or '-' for real only");
    let groups: usize = args.next().map_or(2, |arg| arg.parse().unwrap());
    let filter = args.next().unwrap_or_default();
    let seed: u64 = args
        .next()
        .map_or(0x39c6_d28f_febe_8213, |arg| arg.parse().unwrap());
    let suite = args.next().unwrap_or_else(|| "all".to_string());
    assert!(groups > 0 && seed != 0);
    assert!(["all", "pangui", "real"].contains(&suite.as_str()));
    println!("fixture\tblock\tsample\tmode\tnodes\tbuild_pos\tsolve_pos\twall_ns\tcpu_ns");
    if suite != "real" {
        let mut paths = std::fs::read_dir(Path::new(&templates))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "txt"))
            .collect::<Vec<_>>();
        paths.sort_unstable();
        for (fixture, path) in paths.iter().enumerate() {
            let name = path.file_stem().unwrap().to_str().unwrap();
            if !name.contains(&filter) {
                continue;
            }
            let input = std::fs::read_to_string(path).unwrap();
            let root = parse_test_case(name, &input).unwrap().root_node.unwrap();
            run(
                name,
                groups,
                (seed ^ fixture as u64).max(1),
                &[
                    "frozen_owned",
                    "candidate_batch",
                    "prior_batch",
                    "frozen_batch",
                    "frozen_dense",
                    "candidate_owned",
                ],
                |mode| match mode {
                    0 => frozen::owned(&root, false),
                    1 => candidate::owned(&root, true),
                    2 => previous::owned(&root, true),
                    3 => frozen::owned(&root, true),
                    4 => frozen::dense(&root),
                    5 => candidate::owned(&root, false),
                    _ => unreachable!(),
                },
            );
        }
    }
    if suite != "pangui" {
        for (fixture, name) in frozen::names().into_iter().enumerate() {
            if !name.contains(&filter) {
                continue;
            }
            run(
                name,
                groups,
                (seed ^ fixture as u64).max(1),
                &[
                    "frozen_owned",
                    "candidate_batch",
                    "prior_batch",
                    "frozen_batch",
                    "candidate_owned",
                ],
                |mode| match mode {
                    0 => frozen::real(name, false),
                    1 => candidate::real(name, true),
                    2 => previous::real(name, true),
                    3 => frozen::real(name, true),
                    4 => candidate::real(name, false),
                    _ => unreachable!(),
                },
            );
        }
    }
}
