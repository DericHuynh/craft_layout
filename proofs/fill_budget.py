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

# For finite operands IEEE RNE chooses the nearest point to the exact real
# difference. Identify signed zeros and use ±2^128 for the two infinities.
# These are the next points beyond ±FLT_MAX in the format with an unbounded
# exponent, so rounding into those points uses precisely the IEEE overflow
# thresholds. Beyond them the nearest point stays at the corresponding end.
# On ties the specification's even choice is deterministic in this order.
# Reversed rounded results would place a at or above their midpoint and b
# at or below it. With a <= b, both would be the same midpoint.
NEAREST_ORDER = """
(set-logic QF_UFLRA)
(declare-const x Real)
(declare-const y Real)
(declare-const c Real)
(declare-fun rounded (Real) Real)
(define-fun distance ((a Real) (b Real)) Real (ite (<= a b) (- b a) (- a b)))
(define-fun a () Real (- x c))
(define-fun b () Real (- y c))
(assert (<= x y))
; Each chosen point is at least as close as the other chosen point.
(assert (<= (distance a (rounded a)) (distance a (rounded b))))
(assert (<= (distance b (rounded b)) (distance b (rounded a))))
(assert (> (rounded a) (rounded b)))
(check-sat)
"""

INFINITE_ORDER = """
(declare-const left F)
(declare-const right F)
(assert (fp.leq x y))
(assert (or (fp.isInfinite x) (fp.isInfinite y)))
(assert (valid left))
(assert (valid right))
(assert (=> (fp.isInfinite x) (= left x)))
(assert (=> (fp.isInfinite y) (= right y)))
(assert (not (fp.leq left right)))
(check-sat)
"""

UNIT_WEIGHT_FOLD = """
(set-logic QF_FPBV)
(define-sort F () (_ FloatingPoint 8 24))
(declare-const n (_ BitVec 32))
(assert (bvult n #x01000000))
(define-fun before () F ((_ to_fp_unsigned 8 24) RNE n))
(define-fun after () F ((_ to_fp_unsigned 8 24) RNE (bvadd n #x00000001)))
(assert (not (= after (fp.add RNE before ((_ to_fp 8 24) #x3f800000)))))
(check-sat)
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


def verify(z3, name, query):
    result = subprocess.run([z3, '-in'], input=query, capture_output=True, text=True, check=True)
    if result.stdout.strip() != 'unsat':
        raise RuntimeError(f'{name}: {result.stdout.strip()} {result.stderr.strip()}')


def verify_charge_order(z3, program):
    def refute(name, prop):
        verify(z3, name, program + f'\n(assert (not {prop}))\n(check-sat)\n')

    # The analytic finite-operand argument applies only to IEEE RNE subtraction.
    refute('production charge', '(= (charge x c) (fp.sub RNE x c))')
    refute('infinite input to charge', '(=> (and (fp.isInfinite x) (fee c)) (= (charge x c) x))')
    verify(z3, 'exact subtraction followed by nearest rounding', NEAREST_ORDER)
    # The earlier cost law establishes that both outputs are ordered numbers.
    verify(z3, 'charge order with infinite inputs', PRELUDE + INFINITE_ORDER)
    print('cost preserves the upper bound verified', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--z3', default=os.environ.get('Z3', 'z3'))
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        definitions = compile_definitions(Path(tmp))
    program = PRELUDE + definitions
    laws = {
        'initial upper bound': '(=> (and (fp.geq x zero) (fp.geq gaps zero)) '
                               '(and (valid (after_gaps x gaps)) (fp.leq (after_gaps x gaps) x)))',
        'exhaustion guard': '(=> (and (fp.geq x zero) (fp.geq gaps zero) (exhausted x gaps y)) '
                            '(or (fp.leq (after_gaps x gaps) zero) (fp.leq y zero)))',
        'cost cannot increase space': '(=> (and (valid x) (fee c)) '
                                      '(and (valid (charge x c)) (fp.leq (charge x c) x)))',
        'zero-cost tail edit': '(=> (and (valid x) (fp.isZero c)) (fp.eq (charge x c) x))',
        'positive-zero share': '(=> (fp.leq x zero) (= (share (nonnegative x) zero weight) zero))',
        'inactive finite pixel bounds give zero violation':
            '(=> (and (valid x) (valid y) (not (fp.isInfinite x)) (not (fp.isInfinite y))) '
            '(and (=> (fp.leq y x) (= (charge (ite (fp.lt x y) y x) x) zero)) '
            '     (=> (fp.leq x y) (= (charge (ite (fp.lt y x) y x) x) zero)) '
            '     (= (fp.add RNE zero zero) zero)))',
        'one violation has the same freeze decision':
            '(=> (fp.lt zero c) '
            '(let ((total (fp.add RNE zero x))) '
            '(= (fp.lt c (fp.abs x)) '
            '   (and (not (fp.lt (fp.abs total) c)) '
            '        (ite (fp.gt total zero) (fp.gt x c) (fp.lt x (fp.sub RNE zero c)))))))',
    }
    for name, law in laws.items():
        verify(args.z3, name, program + f'\n(assert (not {law}))\n(check-sat)\n')
        print(f'{name} verified', flush=True)
    verify_charge_order(args.z3, program)
    verify(args.z3, 'ordered unit weights equal the exact count', UNIT_WEIGHT_FOLD)
    print('ordered unit weights equal the exact count verified', flush=True)


if __name__ == '__main__':
    main()
