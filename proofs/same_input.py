"""Prove bit-exact LayoutParams cache comparison and numeric edit registration.

Rustdoc supplies the actual field and variant inventory. A temporary copy of the
crate gains Arbitrary derives and a structural equality oracle generated from
that inventory. Kani runs the unmodified SameInput methods on native Rust types.
Unwinding assertions remain enabled for arrays and the standard library memcmp.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
HARNESSES = (
    'agrees_on_every_field',
    'owned_placement_gate_keeps_sizing_inputs',
    'reports_all_numeric_inputs',
    'structural_inputs_request_rebuild',
)
PRELUDE = """
use crate::*;
pub(crate) trait Bits { fn matches_bits(&self, other: &Self) -> bool; }
impl Bits for f32 {
    fn matches_bits(&self, other: &Self) -> bool { self.to_bits() == other.to_bits() }
}
macro_rules! scalar {
    ($($t:ty),*) => { $(impl Bits for $t {
        fn matches_bits(&self, other: &Self) -> bool { self == other }
    })* };
}
scalar!(bool, u16, u32);
impl<T: Bits> Bits for Option<T> {
    fn matches_bits(&self, other: &Self) -> bool {
        match (self,other) { (None,None) => true, (Some(a),Some(b)) => a.matches_bits(b), _ => false }
    }
}
impl<T: Bits, const N:usize> Bits for [T;N] {
    fn matches_bits(&self, other: &Self) -> bool { (0..N).all(|i| self[i].matches_bits(&other[i])) }
}
"""
HARNESS = """
#[kani::proof]
#[kani::unwind(16)]
fn agrees_on_every_field() {
    let left: LayoutParams = kani::any();
    let right: LayoutParams = kani::any();
    assert!(left.same_input(&right) == left.matches_bits(&right));
}
"""


def payload(kind, index):
    """Read a struct's fields or an enum variant's payload, including every lane."""
    if kind == 'plain':
        return '', []
    if 'tuple' in kind:
        fields = kind['tuple']
        if None in fields:
            raise ValueError('rustdoc stripped a tuple field')
        return 'tuple', list(map(str, range(len(fields))))
    record = kind.get('plain', kind.get('struct'))
    if not record or record['has_stripped_fields']:
        raise ValueError(f'unsupported or stripped Rust payload: {kind}')
    return 'record', [index[str(i)]['name'] for i in record['fields']]


def oracle(item, index):
    name = item['name']
    tag, definition = next(iter(item['inner'].items()))
    params = [p['name'] for p in definition['generics']['params']]
    generic = ('<' + ','.join(p + ':Bits' for p in params) + '>') if params else ''
    arguments = ('<' + ','.join(params) + '>') if params else ''
    if tag == 'struct':
        _, fields = payload(definition['kind'], index)
        body = ' && '.join(f'self.{f}.matches_bits(&other.{f})' for f in fields) or 'true'
    elif tag == 'enum' and not definition['has_stripped_variants']:
        arms = []
        for i in definition['variants']:
            variant = index[str(i)]
            shape, fields = payload(variant['inner']['variant']['kind'], index)

            def pat(prefix):
                names = [prefix + str(k) for k in range(len(fields))]
                tail = ''
                if shape == 'tuple':
                    tail = '(' + ','.join(names) + ')'
                if shape == 'record':
                    tail = '{' + ','.join(f'{f}:{n}' for f, n in zip(fields, names)) + '}'
                return 'Self::' + variant['name'] + tail

            equal = ' && '.join(f'a{k}.matches_bits(b{k})' for k in range(len(fields))) or 'true'
            arms.append(f'({pat("a")},{pat("b")}) => {equal},')
        body = 'match (self,other) {' + '\n'.join(arms) + '_ => false}'
    else:
        raise ValueError(f'unsupported type {name}')
    return f'impl{generic} Bits for {name}{arguments} {{fn matches_bits(&self,other:&Self)->bool{{{body}}}}}'


def generate(index, crate):
    types = {}

    def walk(node):
        if isinstance(node, list):
            for entry in node:
                walk(entry)
        if not isinstance(node, dict):
            return
        if 'resolved_path' in node:
            item = index.get(str(node['resolved_path']['id']))
            if item and item['crate_id'] == 0:
                collect(item)
        for child in node.values():
            walk(child)

    def collect(item):
        name = item['name']
        if name in types:
            return
        types[name] = item
        tag, definition = next(iter(item['inner'].items()))
        kinds = ([definition['kind']] if tag == 'struct' else
                 [index[str(v)]['inner']['variant']['kind'] for v in definition['variants']])
        for kind in kinds:
            if kind == 'plain':
                continue
            ids = kind['tuple'] if 'tuple' in kind else next(iter(kind.values()))['fields']
            for field in ids:
                walk(index[str(field)]['inner']['struct_field'])

    layout = next(item for item in index.values() if item['name'] == 'LayoutParams' and item['crate_id'] == 0)
    collect(layout)
    sources = {}
    oracles = {}
    for item in types.values():
        span = item['span']
        path = (crate / span['filename']).resolve()
        if not path.is_relative_to(crate / 'src') or span['begin'][1] != 1:
            raise ValueError(f"unsupported source location for {item['name']}: {span}")
        if path not in sources:
            sources[path] = path.read_text().splitlines(keepends=True)
            oracles[path] = []
        line = span['begin'][0] - 1
        lines = sources[path]
        lines[line] = '#[cfg_attr(kani, derive(kani::Arbitrary))]\n' + lines[line]
        oracles[path].append(oracle(item, index))
    source = crate / 'src/lib.rs'
    if source not in sources:
        sources[source] = source.read_text().splitlines(keepends=True)
    sources[source].append('\n#[cfg(kani)] mod same_input_proof;\n')
    for path, definitions in oracles.items():
        sources[path].append(
            '\n#[cfg(kani)] mod same_input_oracle {\n'
            'use super::*;\nuse crate::same_input_proof::Bits;\n'
            + '\n'.join(definitions) + '\n}\n'
        )
    for path, lines in sources.items():
        path.write_text(''.join(lines))
    source.with_name('same_input_proof.rs').write_text(PRELUDE + HARNESS)

    _, fields = payload(layout['inner']['struct']['kind'], index)
    ignored = {'position', 'anchor', 'children_origin_flipped', 'window_overflow'}
    if not ignored.issubset(fields):
        raise ValueError('the owned placement-field inventory has changed')
    sizing_bits = '\n        && '.join(f'old.{field}.matches_bits(&new.{field})'
                                        for field in fields if field not in ignored)
    (crate/'src/layout_tree/owned_edit_proof.rs').write_text(f'''
use super::*;
use crate::same_input_proof::Bits;

#[kani::proof]
#[kani::unwind(16)]
fn owned_placement_gate_keeps_sizing_inputs() {{
    let old: LayoutParams = kani::any();
    let new: LayoutParams = kani::any();
    let unchanged = {sizing_bits};
    assert_eq!(solve_frame::same_sizing_inputs(old, new), unchanged);
}}
''')
    with (crate/'src/layout_tree.rs').open('a') as module:
        module.write('\n#[cfg(kani)] mod owned_edit_proof;\n')
    return len(types)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--kani', default='cargo', help='Cargo executable or standalone kani-driver')
    parser.add_argument('--harness', choices=HARNESSES, action='append', help='run only the named harness')
    args = parser.parse_args()
    kani = shutil.which(args.kani)
    if kani is None:
        parser.error(f'executable not found: {args.kani}')
    with tempfile.TemporaryDirectory(prefix='keru-input-proof-') as temp:
        crate = Path(temp).resolve()
        for filename in ('Cargo.toml', 'Cargo.lock', 'README.md', 'build.rs'):
            shutil.copyfile(ROOT/filename, crate/filename)
        shutil.copytree(ROOT/'src', crate/'src')
        for folder in ('examples', 'tests', 'benches'):
            (crate/folder).symlink_to(ROOT/folder, target_is_directory=True)
        env = {**os.environ, 'CARGO_TARGET_DIR': str(crate/'target')}
        if Path(kani).name == 'kani-driver':
            # The standalone driver locates its bundled CBMC tools on PATH.
            env['PATH'] = os.pathsep.join((str(Path(kani).resolve().parent), env.get('PATH', '')))
        subprocess.run(['cargo', 'rustdoc', '--locked', '--lib', '--', '-Zunstable-options',
                        '--output-format', 'json', '--document-private-items'], cwd=crate, env=env, check=True)
        index = json.loads((crate/'target/doc/keru_layout.json').read_text())['index']
        count = generate(index, crate)
        shutil.copyfile(ROOT/'proofs/node_change.rs', crate/'src/incremental/node_change_proof.rs')
        with (crate/'src/incremental.rs').open('a') as module:
            module.write('\n#[cfg(kani)] mod node_change_proof;\n')
        print(f'Checking SameInput against the declared structure of {count} Rust types', flush=True)
        command = [kani, 'kani', '--lib', '--output-format', 'terse']
        for harness in args.harness or HARNESSES:
            command.extend(('--harness', harness))
        subprocess.run(command, cwd=crate, env=env, check=True)


if __name__ == '__main__':
    main()
