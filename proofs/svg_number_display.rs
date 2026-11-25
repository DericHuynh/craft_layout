//! Exhaust the binary32 domain through the production SVG display call.
//! Run with `python3 proofs/text_intrinsics.py --svg-display`.

#[path = "../src/layout_tree/svg_number_format.rs"]
mod number_format;

use arrayvec::ArrayString;

fn main() {
    const INPUTS: u64 = 1 << 32;
    let workers = std::thread::available_parallelism().map_or(1, |count| count.get().min(32)) as u64;
    let longest = std::thread::scope(|scope| {
        let checks = (0..workers).map(|index| {
            scope.spawn(move || {
                let mut longest = 0;
                let mut output = ArrayString::<{number_format::SVG_NUMBER_CAPACITY}>::new();
                for bits in (INPUTS * index / workers)..(INPUTS * (index + 1) / workers) {
                    output.clear();
                    number_format::write_svg_number(&mut output, f32::from_bits(bits as u32))
                        .unwrap_or_else(|_| panic!("binary32 {bits:#010x} exceeded the SVG cache"));
                    longest = longest.max(output.len());
                }
                longest
            })
        }).collect::<Vec<_>>();
        checks.into_iter().map(|check| check.join().unwrap()).max().unwrap()
    });
    println!("SVG Display returned successfully for all {INPUTS} binary32 encodings, maximum {longest} bytes");
}
