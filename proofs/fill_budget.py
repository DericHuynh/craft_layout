"""Check the IEEE binary32 budget laws used by structural::exhausted_tail_share.

Compile the same budget operations called by full and tail layout. Translate their
straight-line LLVM IR to floating-point SMT and reject any unrecognized operation.
"""
import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

SOURCE = Path(__file__).resolve().parents[1] / 'src/fill_budget.rs'
SIGNATURES = {
    'charge': ('x c', 'f32'),
    'nonnegative': ('x', 'f32'),
    'after_gaps': ('inner gaps', 'f32'),
    'share': ('b f w', 'f32'),
    'exhausted': ('inner gaps without_gaps', 'bool'),
}
PRELUDE = """
(set-logic QF_FP)
(define-sort F () (_ FloatingPoint 8 24))
(define-fun zero () F (_ +zero 8 24))
(define-fun valid ((x F)) Bool (not (fp.isNaN x)))
(define-fun fee ((x F)) Bool (and (fp.geq x zero) (not (fp.isInfinite x))))
(declare-const x F)
(declare-const y F)
(declare-const c F)
(declare-const gaps F)
(declare-const weight F)
"""


def compile_definitions(directory):
    wrappers = [f'#[path=r"{SOURCE}"] mod budget;']
    for name, (args, result) in SIGNATURES.items():
        params = args.split()
        typed = ', '.join(f'{p}:f32' for p in params)
        wrappers.append(f'#[unsafe(no_mangle)] pub fn {name}({typed})->{result}'
                        f'{{budget::{name}({",".join(params)})}}')
    (directory / 'kernel.rs').write_text('\n'.join(wrappers))
    subprocess.run(['rustc', '--edition=2024', '--crate-type=lib', '--emit=llvm-ir', '-Copt-level=3',
                    '--cfg', 'feature="incremental"', 'kernel.rs', '-o', 'kernel.ll'], cwd=directory, check=True)
    ir = (directory / 'kernel.ll').read_text()
    definitions = []
    operations = {'fsub float': 'fp.sub RNE', 'fadd float': 'fp.add RNE', 'fdiv float': 'fp.div RNE',
                  'fcmp ogt float': 'fp.gt', 'fcmp oge float': 'fp.geq', 'fcmp ole float': 'fp.leq',
                  'or i1': 'or', 'and i1': 'and'}
    for name, (args, result) in SIGNATURES.items():
        header, body = re.search(rf'^define [^\n]* @{name}\(([^)]*)\)[^\n]*\{{\n(.*?)^\}}', ir, re.M | re.S).groups()
        if re.findall(r'%([\w.]+)', header) != args.split():
            raise ValueError(f'unexpected argument order in {name}')
        values = {f'%{p}': p for p in args.split()}
        values['0.000000e+00'] = 'zero'
        for line in map(str.strip, body.splitlines()):
            if not line or line == 'start:':
                continue
            if match := re.fullmatch(r'ret (float|i1) (\S+)', line):
                sort = 'F' if result == 'f32' else 'Bool'
                params = ' '.join(f'({p} F)' for p in args.split())
                definitions.append(f'(define-fun {name} ({params}) {sort} {values[match[2]]})')
                continue
            lhs, rhs = line.split(' = ')
            if match := re.fullmatch(r'select i1 (\S+), float (\S+), float (\S+)', rhs):
                values[lhs] = '(ite ' + ' '.join(values[v] for v in match.groups()) + ')'
            else:
                op, left, right = re.fullmatch(r'(.*?) (\S+), (\S+)', rhs).groups()
                values[lhs] = f'({operations[op]} {values[left]} {values[right]})'
    return '\n'.join(definitions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--z3', default=os.environ.get('Z3', 'z3'))
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        definitions = compile_definitions(Path(tmp))
    laws = {
        'initial upper bound': '(=> (and (fp.geq x zero) (fp.geq gaps zero)) '
                               '(and (valid (after_gaps x gaps)) (fp.leq (after_gaps x gaps) x)))',
        'exhaustion guard': '(=> (and (fp.geq x zero) (fp.geq gaps zero) (exhausted x gaps y)) '
                            '(or (fp.leq (after_gaps x gaps) zero) (fp.leq y zero)))',
        'cost cannot increase space': '(=> (and (valid x) (fee c)) '
                                      '(and (valid (charge x c)) (fp.leq (charge x c) x)))',
        'zero-cost tail edit': '(=> (and (valid x) (fp.isZero c)) (fp.eq (charge x c) x))',
        'positive-zero share': '(=> (fp.leq x zero) (= (share (nonnegative x) zero weight) zero))',
        'cost preserves the upper bound': '(=> (and (fp.leq x y) (fee c)) '
                                         '(fp.leq (charge x c) (charge y c)))',
    }
    for name, law in laws.items():
        query = PRELUDE + definitions + f'\n(assert (not {law}))\n(check-sat)\n'
        r = subprocess.run([args.z3, '-in'], input=query, capture_output=True, text=True, check=True)
        if r.stdout.strip() != 'unsat':
            raise RuntimeError(f'{name}: {r.stdout.strip()} {r.stderr.strip()}')
        print(f'{name} verified', flush=True)


if __name__ == '__main__':
    main()
