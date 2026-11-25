"""Model-check the installed Rust x86 feature detector with symbolic hardware reports."""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


HARNESS = r'''
#![allow(unexpected_cfgs)]

mod detect {
    pub(crate) mod bit;
    pub(crate) mod cache;
    pub(crate) mod os;
    #[allow(non_camel_case_types)]
    pub(crate) enum Feature { FEATURES }
}

mod hardware {
    pub(crate) use std::arch::x86_64::CpuidResult;

    const ZERO: CpuidResult = CpuidResult { eax: 0, ebx: 0, ecx: 0, edx: 0 };
    static mut CPUID: [CpuidResult; 10] = [ZERO; 10];
    static mut XCR0: u64 = 0;

    pub(crate) fn install(reports: [CpuidResult; 10], xcr0: u64) {
        // This symbolic harness is single-threaded and installs reports before detection.
        unsafe { CPUID = reports; XCR0 = xcr0; }
    }

    pub(crate) fn __cpuid(leaf: u32) -> CpuidResult { __cpuid_count(leaf, 0) }

    pub(crate) fn __cpuid_count(leaf: u32, subleaf: u32) -> CpuidResult {
        let index = match (leaf, subleaf) {
            (0, 0) => 0, (1, 0) => 1, (7, 0) => 2, (7, 1) => 3,
            (0x8000_0000, 0) => 4, (0x8000_0001, 0) => 5,
            (0x19, 0) => 6, (0x1e, 1) => 7, (0xd, 1) => 8, (0x24, 0) => 9,
            _ => panic!("new CPUID leaf needs a symbolic hardware input"),
        };
        unsafe { CPUID[index] }
    }

    pub(crate) unsafe fn _xgetbv(index: u32) -> u64 {
        assert_eq!(index, 0);
        let ecx = __cpuid(1).ecx;
        assert_eq!(ecx & (3 << 26), 3 << 26);
        unsafe { XCR0 }
    }
}

fn arbitrary_report() -> hardware::CpuidResult {
    hardware::CpuidResult { eax: kani::any(), ebx: kani::any(), ecx: kani::any(), edx: kani::any() }
}

#[kani::proof]
fn engine_cpu_reports() {
    use detect::Feature;
    let leaf0 = arbitrary_report();
    let leaf1 = arbitrary_report();
    let leaf7 = arbitrary_report();
    let xcr0: u64 = kani::any();
    hardware::install([leaf0, leaf1, leaf7, arbitrary_report(), arbitrary_report(),
        arbitrary_report(), arbitrary_report(), arbitrary_report(), arbitrary_report(),
        arbitrary_report()], xcr0);

    let flags = detect::os::detect_features();
    let base = leaf0.eax >= 1;
    let extended = leaf0.eax >= 7;
    let vector_state = base && leaf1.ecx & (3 << 26) == (3 << 26) && xcr0 & 6 == 6;
    let sse2 = base && leaf1.edx & (1 << 26) != 0;
    let avx = vector_state && leaf1.ecx & (1 << 28) != 0;
    let avx2 = vector_state && extended && leaf7.ebx & (1 << 5) != 0;
    let fma = vector_state && leaf1.ecx & (1 << 12) != 0;
    let f16c = base && leaf1.ecx & (1 << 29) != 0;
    // Rust's AVX512F target feature also enables FMA and F16C.
    let avx512f = extended && leaf7.ebx & (1 << 16) != 0
        && xcr0 & 0xe0 == 0xe0 && fma && f16c;
    let popcnt = base && leaf1.ecx & (1 << 23) != 0;
    let intel = leaf0.ebx == u32::from_le_bytes(*b"Genu")
        && leaf0.edx == u32::from_le_bytes(*b"ineI")
        && leaf0.ecx == u32::from_le_bytes(*b"ntel");
    let bmi2 = extended && leaf7.ebx & (1 << 8) != 0 && (!intel || avx);
    macro_rules! check {
        ($feature:ident) => {
            assert_eq!(flags.test(Feature::$feature as u32), $feature);
            assert_eq!(detect::cache::test(Feature::$feature as u32), $feature);
        };
    }
    check!(sse2);
    check!(avx);
    check!(avx2);
    check!(fma);
    check!(f16c);
    check!(avx512f);
    check!(popcnt);
    check!(bmi2);
}
'''


def prepare(directory, std_detect):
    feature_source = (std_detect / 'arch/x86.rs').read_text()
    features = re.findall(r'@FEATURE:\s*(?:#\[[^\]]+\]\s*)*([a-zA-Z0-9_]+):', feature_source)
    detect = directory / 'detect'
    detect.mkdir()
    shutil.copyfile(std_detect / 'bit.rs', detect / 'bit.rs')
    shutil.copyfile(std_detect / 'cache.rs', detect / 'cache.rs')
    detector = (std_detect / 'os/x86.rs').read_text()
    hardware = ('#[cfg(target_arch = "x86")]\nuse core::arch::x86::*;\n'
                '#[cfg(target_arch = "x86_64")]\nuse core::arch::x86_64::*;')
    assert detector.count(hardware) == 1, 'unrecognized std_detect hardware imports'
    (detect / 'os.rs').write_text(detector.replace(hardware, 'use crate::hardware::*;'))
    (directory / 'cpu.rs').write_text(HARNESS.replace('FEATURES', ', '.join(features)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kani', default='kani', help='standalone Kani executable')
    args = parser.parse_args()
    kani = shutil.which(args.kani)
    if kani is None:
        parser.error(f'executable not found: {args.kani}')
    sysroot = Path(subprocess.check_output(['rustc', '+1.99.1', '--print', 'sysroot'], text=True).strip())
    std_detect = sysroot / 'lib/rustlib/src/rust/library/std_detect/src/detect'
    env = {**os.environ, 'PATH': os.pathsep.join((str(Path(kani).parent), os.environ['PATH']))}
    env['RUSTFLAGS'] = f"{env.get('RUSTFLAGS', '')} --edition=2024".strip()
    with tempfile.TemporaryDirectory(prefix='keru-cpu-proof-') as temp:
        directory = Path(temp)
        prepare(directory, std_detect)
        subprocess.run([kani, '--harness', 'engine_cpu_reports', '--output-format', 'terse', 'cpu.rs'],
                       cwd=directory, env=env, check=True)


if __name__ == '__main__':
    main()
