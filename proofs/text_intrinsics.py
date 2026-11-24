"""Check native text loads, scalar counts, feature gates, and SVG formatting."""

import argparse
from itertools import product
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
WINDOWS = ROOT / 'src/layout_tree/text_windows.rs'
GATES = {
    'ascii': ('AsciiOrSvg', ('avx2', 'avx')),
    'ascii_wrap': ('AsciiWrap', ('avx2', 'avx', 'popcnt')),
    'unicode_wrap': ('UnicodeWrap', ('avx2', 'avx', 'popcnt', 'bmi2')),
}
SSA = r'%[\w.$-]+'


def compile_primitives(directory):
    wrappers = [f'#[path = r"{WINDOWS}"] mod windows;',
                'use windows::{TextAvx2, text_avx2_supported};',
                'use windows::boundaries::{BitLanes, NativeBitLanes};',
                'use std::arch::x86_64::{__m128i, __m256i};',
                '#[unsafe(no_mangle)] #[target_feature(enable="bmi2")] '
                'pub fn pack(mask: u32, positions: u32) -> u32 { windows::native::pack_lanes(mask, positions) }']
    for name in ('first', 'last', 'count'):
        wrappers.append(f'#[unsafe(no_mangle)] pub fn {name}(mask: u32) -> u32 '
                        f'{{ NativeBitLanes::{name}(mask) }}')
    for lanes, vector, load in [(16, '__m128i', 'load_sse2'), (32, '__m256i', 'load_avx')]:
        feature = '#[target_feature(enable = "avx2")]' if lanes == 32 else ''
        wrappers.append(f'#[unsafe(no_mangle)] {feature} pub fn load{lanes}(bytes: &[u8; {lanes}]) '
                        f'-> {vector} {{ windows::native::{load}(bytes) }}')
    for name, (variant, _) in GATES.items():
        wrappers.append(f'#[unsafe(no_mangle)] pub fn gate_{name}() -> bool '
                        f'{{ text_avx2_supported(TextAvx2::{variant}) }}')
    for width in (4, 8, 16, 32, 34):
        for position in ('first', 'last'):
            wrappers.append(f'#[unsafe(no_mangle)] pub fn {position}{width}(bytes: &[u8]) '
                            f'-> Option<&[u8; {width}]> {{ bytes.{position}_chunk() }}')
    for width in (16, 32, 64):
        wrappers.append(f'#[unsafe(no_mangle)] pub fn chunks{width}(bytes: &[u8]) '
                        f'-> (&[[u8; {width}]], &[u8]) {{ bytes.as_chunks() }}')
    (directory / 'text.rs').write_text('\n'.join(wrappers))
    subprocess.run(['rustc', '--edition=2024', '--crate-type=lib', '--emit=llvm-ir',
                    '-Copt-level=3', '-Coverflow-checks=on', '-Cpanic=unwind', '-Adead_code',
                    'text.rs', '-o', 'text.ll'], cwd=directory, check=True)
    return (directory / 'text.ll').read_text()


def function(ir, name, nounwind=True):
    match = re.search(rf'^define ([^\n]*@{name}\([^\n]*\) [^\n]*#(\d+)[^\n]*)\{{\n(.*?)^\}}', ir, re.M | re.S)
    if match is None:
        raise ValueError(f'missing native definition {name}')
    attrs = re.search(rf'^attributes #{match[2]} = \{{(.+)\}}$', ir, re.M)[1]
    if nounwind and 'nounwind' not in attrs.split():
        raise ValueError(f'{name} lacks nounwind')
    return match[1], match[3], attrs


def check_counts(ir):
    for name, intrinsic in [('first', 'cttz'), ('last', 'ctlz'), ('count', 'ctpop')]:
        _, body, _ = function(ir, name)
        defined_zero = ', i1 false' if intrinsic != 'ctpop' else ''
        operation = (rf'start:\s+({SSA}) = (?:tail )?call (?:range\(i32 0, 33\) )?'
                     rf'i32 @llvm\.{intrinsic}\.i32\(i32 %mask{defined_zero}\)')
        if name == 'last':
            operation += rf'\s+({SSA}) = xor i32 \1, 31\s+ret i32 \2'
        else:
            operation += r'\s+ret i32 \1'
        assert re.fullmatch(operation, body.strip()), (name, body)
    _, body, attrs = function(ir, 'pack')
    pack = (rf'start:\s+({SSA}) = (?:tail )?call i32 @llvm\.pext\.i32\(i32 %mask, i32 %positions\)'
            r'\s+ret i32 \1')
    assert re.fullmatch(pack, body.strip()) and '+bmi2' in attrs, body


def check_loads(ir):
    for width, words in [(16, 2), (32, 4)]:
        signature, body, attrs = function(ir, f'load{width}')
        assert re.search(rf'dereferenceable\({width}\) %bytes', signature), signature
        assert f'sret([{width} x i8]) align {width}' in signature, signature
        vector = rf'<{words} x i64>'
        operation = (r'start:\s+(?:(?:tail )?call void @llvm\.experimental\.noalias\.scope\.decl\(metadata !\d+\)\s+)+'
                     rf'({SSA}) = load {vector}, ptr %bytes, align 1(?:, [^\n]+)?\s+'
                     rf'store {vector} \1, ptr %_0, align {width}(?:, [^\n]+)?\s+ret void')
        assert re.fullmatch(operation, body.strip()), body
        assert ('+avx2' in attrs) == (width == 32), attrs


def check_chunks(ir):
    # The short-input arm returns null. The candidate end pointer is only
    # returned when L >= N, so [L-N,L) lies inside the live input allocation.
    for width in (4, 8, 16, 32, 34):
        for position in ('first', 'last'):
            _, body, _ = function(ir, f'{position}{width}')
            pattern = rf'start:\s+({SSA}) = icmp (?:samesign )?ult i64 %bytes\.1, {width}\s+'
            if position == 'first':
                pattern += rf'({SSA}) = select i1 \1, ptr null, ptr %bytes\.0\s+ret ptr \2'
            else:
                pattern += (rf'({SSA}) = getelementptr i8, ptr %bytes\.0, i64 %bytes\.1\s+'
                            rf'({SSA}) = getelementptr i8, ptr \2, i64 -{width}\s+'
                            rf'({SSA}) = select i1 \1, ptr null, ptr \3\s+ret ptr \4')
            assert re.fullmatch(pattern, body.strip()), (position, width, body)
    for width in (16, 32, 64):
        _, body, _ = function(ir, f'chunks{width}')
        # Borrowed u8 slices have L < 2^63. Masking the low log2(N) bits
        # yields the prefix byte length. The remainder and block count are
        # L mod N and floor(L/N), respectively.
        prefix_mask = (1 << 63) - width
        shift = width.bit_length() - 1
        operations = (rf'start:\s+({SSA}) = and i64 %bytes\.1, {prefix_mask}\s+'
                      rf'({SSA}) = getelementptr inbounds nuw i8, ptr %bytes\.0, i64 \1\s+'
                      rf'({SSA}) = and i64 %bytes\.1, {width - 1}\s+'
                      rf'({SSA}) = lshr i64 %bytes\.1, {shift}\s+'
                      rf'store ptr %bytes\.0, ptr %_0, align 8(?:, [^\n]+)?\s+'
                      rf'({SSA}) = getelementptr inbounds nuw i8, ptr %_0, i64 8\s+'
                      rf'store i64 \4, ptr \5, align 8(?:, [^\n]+)?\s+'
                      rf'({SSA}) = getelementptr inbounds nuw i8, ptr %_0, i64 16\s+'
                      rf'store ptr \2, ptr \6, align 8(?:, [^\n]+)?\s+'
                      rf'({SSA}) = getelementptr inbounds nuw i8, ptr %_0, i64 24\s+'
                      rf'store i64 \3, ptr \7, align 8(?:, [^\n]+)?\s+ret void')
        assert re.fullmatch(operations, body.strip()), (width, body)


def feature_indices():
    sysroot = Path(subprocess.check_output(['rustc', '--print', 'sysroot'], text=True).strip())
    x86 = sysroot / 'lib/rustlib/src/rust/library/std_detect/src/detect/arch/x86.rs'
    names = re.findall(r'@FEATURE:\s*(?:#\[[^\]]+\]\s*)*([a-zA-Z0-9_]+):', x86.read_text())
    wanted = GATES['unicode_wrap'][1]
    indices = {name: names.index(name) for name in wanted}
    assert max(indices.values()) < 63, indices
    return indices


def run_gate(body, mask, misses):
    """Interpret all instructions of the small, acyclic LLVM gate."""
    blocks = {}
    for raw in body.splitlines():
        instruction = raw.split(';', 1)[0].strip()
        if instruction.endswith(':'):
            block = blocks[instruction[:-1]] = []
        elif instruction:
            block.append(instruction)
    previous, active = None, 'start'
    values = {'true': True, 'false': False}
    visited = set()
    while active not in visited:
        visited.add(active)
        for instruction in blocks[active]:
            if match := re.fullmatch(rf'({SSA}) = load atomic i64, ptr @\S+5CACHE monotonic, align 8', instruction):
                values[match[1]] = 0 if next(misses) else mask | (1 << 63)
            elif match := re.fullmatch(rf'({SSA}) = (?:tail )?call noundef i128 @\S+21detect_and_initialize\(\)', instruction):
                values[match[1]] = mask
            elif match := re.fullmatch(rf'({SSA}) = and i(?:64|128) ({SSA}), (\d+)', instruction):
                values[match[1]] = values[match[2]] & int(match[3])
            elif match := re.fullmatch(rf'({SSA}) = icmp (eq|ne) i(?:64|128) ({SSA}), 0', instruction):
                values[match[1]] = (values[match[3]] == 0) == (match[2] == 'eq')
            elif match := re.fullmatch(rf'({SSA}) = phi i1 (.+)', instruction):
                pairs = re.findall(r'\[ ([^, ]+), %([\w.$-]+) \]', match[2])
                values[match[1]] = values[{label: value for value, label in pairs}[previous]]
            elif match := re.fullmatch(rf'br i1 ({SSA}), label %([\w.$-]+), label %([\w.$-]+)(?:, !prof !\d+)?', instruction):
                previous, active = active, match[2 if values[match[1]] else 3]
                break
            elif match := re.fullmatch(r'br label %([\w.$-]+)', instruction):
                previous, active = active, match[1]
                break
            elif match := re.fullmatch(rf'ret i1 ({SSA}|true|false)', instruction):
                return values[match[1]]
            else:
                raise ValueError(f'unsupported gate instruction {instruction}')
        else:
            raise ValueError(f'{active} lacks a terminator')
    raise ValueError(f'cyclic native gate at {active}')


def check_gates(ir):
    indices = feature_indices()
    for name, (_, required) in GATES.items():
        _, body, _ = function(ir, f'gate_{name}', nounwind=False)
        masks = {int(value) for value in re.findall(r'and i(?:64|128) %\S+, (\d+)', body)}
        assert masks == {1 << indices[feature] for feature in required}, (name, masks)
        for flags in product((False, True), repeat=len(indices)):
            available = dict(zip(indices, flags))
            mask = sum(1 << indices[feature] for feature in available if available[feature])
            expected = all(available[feature] for feature in required)
            for misses in product((False, True), repeat=len(required)):
                assert run_gate(body, mask, iter(misses)) == expected, (name, flags, misses)


def check_svg_display(directory):
    metadata = subprocess.check_output(['cargo', 'metadata', '--locked', '--format-version=1'], cwd=ROOT, text=True)
    package, = (entry for entry in json.loads(metadata)['packages'] if entry['name'] == 'arrayvec')
    target, = (entry for entry in package['targets'] if entry['kind'] == ['lib'])
    compiler = ['rustc', '-Copt-level=3', '-Coverflow-checks=on', '-Cpanic=unwind']
    subprocess.run([*compiler, '--edition', target['edition'], '--crate-type=lib', '--crate-name=arrayvec',
                    target['src_path'], '-o', 'libarrayvec.rlib'], cwd=directory, check=True)
    subprocess.run([*compiler, '--edition=2024', '--extern', 'arrayvec=libarrayvec.rlib',
                    str(ROOT / 'proofs/svg_number_display.rs'), '-o', 'svg-number-display'], cwd=directory, check=True)
    subprocess.run(['./svg-number-display'], cwd=directory, check=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--svg-display', action='store_true', help='also test all binary32 encodings')
    args = parser.parse_args()
    if not __debug__:
        parser.error('run without Python optimizations so the checks remain enabled')
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        ir = compile_primitives(directory)
        check_counts(ir)
        check_loads(ir)
        check_chunks(ir)
        check_gates(ir)
        print('Text counts, exact typed loads and chunks, and all native feature gates verified', flush=True)
        if args.svg_display:
            check_svg_display(directory)


if __name__ == '__main__':
    main()
