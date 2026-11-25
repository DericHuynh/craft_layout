"""Check the no-allocation LLVM lowering of the shared Copy storage primitives."""

from pathlib import Path
import re
import subprocess
import tempfile

SOURCE = Path(__file__).resolve().parents[1] / 'src/vec_memory.rs'
WRAPPERS = '''
use vec_memory::{CapacityMemory, RustVec, VecMemory};

#[unsafe(no_mangle)]
pub fn vec_write_spare(items: &mut Vec<u64>, value: u64) -> bool {
    if items.len() == items.capacity() { return false; }
    RustVec::push_reserved(items, value);
    true
}

#[unsafe(no_mangle)]
pub fn vec_write_spare_zst(items: &mut Vec<()>) -> bool {
    if items.len() == items.capacity() { return false; }
    RustVec::push_reserved(items, ());
    true
}

#[unsafe(no_mangle)]
pub fn vec_clear_copy(items: &mut Vec<u64>) { RustVec::clear(items); }

#[unsafe(no_mangle)]
pub fn vec_empty_copy() -> Vec<u64> { RustVec::empty() }

#[unsafe(no_mangle)]
pub fn vec_take_copy(items: &mut Vec<u64>) -> Vec<u64> { RustVec::take(items) }

#[unsafe(no_mangle)]
pub fn vec_inline_copy() -> [Option<u64>; 8] { RustVec::empty_slots() }
'''

NAMES = ('vec_write_spare', 'vec_write_spare_zst', 'vec_clear_copy', 'vec_empty_copy', 'vec_take_copy', 'vec_inline_copy')


def main():
    with tempfile.TemporaryDirectory() as temporary:
        work = Path(temporary)
        (work / 'kernel.rs').write_text(f'#[path = r"{SOURCE}"] mod vec_memory;\n' + WRAPPERS)
        subprocess.run(['rustc', '--edition=2024', '--crate-type=lib', '-Adead_code',
                        '--emit=llvm-ir', '-Copt-level=3', '-Coverflow-checks=yes',
                        'kernel.rs', '-o', 'memory.ll'], cwd=work, check=True)
        ir = (work / 'memory.ll').read_text()

    for name in NAMES:
        match = re.search(rf'^define [^\n]* @{name}\([^\n]*\{{\n(.*?)^\}}', ir, re.M | re.S)
        if not match:
            raise RuntimeError(f'missing definition for {name}')
        for line in match[1].splitlines():
            instruction = line.split(';', 1)[0]
            if re.search(r'\b(invoke|callbr|unreachable|resume)\b', instruction):
                raise RuntimeError(f'{name} has an unexpected control transfer: {instruction}')
            if re.search(r'\bcall\b', instruction) and not re.search(
                    r'@llvm\.(?:assume|experimental\.noalias\.scope\.decl|mem(?:cpy|set)\.[\w.]+)\(', instruction):
                raise RuntimeError(f'{name} has an unexpected call: {instruction}')
        print(f'{name} verified')


if __name__ == '__main__':
    main()
