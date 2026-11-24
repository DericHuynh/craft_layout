"""Check the optimized Rust pixel snap against IEEE round-to-nearest, ties away.

Compile the production scalar and packed x86 kernels. Translate the optimized LLVM
instructions to SMT-LIB. Unsupported IR is a verification error. Use cuts at the
scaled input and rounded result to keep the floating-point queries small.
"""
import argparse
import os
from pathlib import Path
import re
import struct
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PRELUDE = """
(set-logic QF_FPBV)
(define-sort F32 () (_ FloatingPoint 8 24))
(define-sort F64 () (_ FloatingPoint 11 53))
(declare-const edge F32)
(declare-const scale F32)
(declare-const scaled32 F32)
(declare-const scaled F64)
(declare-const rounded F64)
(declare-const snapped32 F32)
(declare-const inverse F64)
(define-fun wide ((x F32)) F64 ((_ to_fp 11 53) RNE x))
(define-fun narrow ((x F64)) F32 ((_ to_fp 8 24) RNE x))
(define-fun possible-product ((x F64)) Bool
    (or (fp.isNaN x) (fp.isInfinite x)
        (= ((_ extract 4 0) (fp.to_ieee_bv x)) #b00000)))
(define-fun copysign ((x F64) (y F64)) F64
    (ite (fp.isNaN x) x
        ((_ to_fp 11 53) (concat ((_ extract 63 63) (fp.to_ieee_bv y))
                                 ((_ extract 62 0) (fp.to_ieee_bv x))))))
(define-fun bits64 ((x F64) (nan-bits (_ BitVec 64))) (_ BitVec 64)
    (ite (fp.isNaN x) nan-bits (fp.to_ieee_bv x)))
(define-fun bits32 ((x F32) (nan-bits (_ BitVec 32))) (_ BitVec 32)
    (ite (fp.isNaN x) nan-bits (fp.to_ieee_bv x)))
(define-fun trunc32 ((x F32)) (_ BitVec 32)
    (ite (and (fp.geq x ((_ to_fp 8 24) #xcf000000))
              (fp.lt x ((_ to_fp 8 24) #x4f000000)))
        ((_ fp.to_sbv 32) RTZ x) #x80000000))
"""


def check(z3, name, definitions, claim):
    problem = PRELUDE + '\n'.join(definitions) + f'\n(assert (not {claim}))\n(check-sat)\n'
    result = subprocess.run([z3, '-in'], input=problem, text=True, capture_output=True)
    if result.returncode or result.stdout.strip() != 'unsat':
        raise RuntimeError(f'{name}: {result.stdout.strip()} {result.stderr.strip()}')
    print(f'{name} verified', flush=True)


def operand(token):
    if token.startswith('%'):
        return '|' + token[1:] + '|'
    if re.fullmatch(r'f?0x[0-9A-Fa-f]{16}', token):
        return '((_ to_fp 11 53) #x' + token[-16:].lower() + ')'
    if re.fullmatch(r'-?\d+\.\d+e[+-]\d+', token):
        return '((_ to_fp 11 53) #x' + struct.pack('>d', float(token)).hex() + ')'
    raise ValueError(f'unsupported LLVM operand {token}')


def translate(rhs):
    if match := re.fullmatch(r'fpext float (\S+) to double', rhs):
        return 'F64', f'(wide {operand(match[1])})'
    if match := re.fullmatch(r'fptrunc double (\S+) to float', rhs):
        return 'F32', f'(narrow {operand(match[1])})'
    if match := re.fullmatch(r'(fadd|fsub|fmul|fdiv|fcmp olt) double (\S+), (\S+)', rhs):
        op = match[1]
        args = f'{operand(match[2])} {operand(match[3])}'
        if op == 'fcmp olt':
            return 'Bool', f'(fp.lt {args})'
        return 'F64', f'(fp.{op[1:]} RNE {args})'
    if match := re.fullmatch(r'select i1 (\S+), double (\S+), double (\S+)', rhs):
        return 'F64', '(ite ' + ' '.join(map(operand, match.groups())) + ')'
    if match := re.fullmatch(
        r'(?:tail )?call (?:noundef )?double @llvm\.(fabs|copysign|round)\.f64'
        r'\(double (?:noundef )?(\S+?)(?:, double (?:noundef )?(\S+))?\)', rhs
    ):
        op = {'fabs': 'fp.abs', 'copysign': 'copysign', 'round': 'fp.roundToIntegral RNA'}[match[1]]
        args = ' '.join(operand(arg) for arg in match.groups()[1:] if arg is not None)
        return 'F64', f'({op} {args})'
    raise ValueError(f'unsupported LLVM instruction {rhs}')


def verify(ir, backend, z3):
    header, body = re.search(r'^define ([^\n]*@kernel\([^\n]+)\{\n(.*?)^\}', ir, re.M | re.S).groups()
    if not re.search(r'float [^%(),]*%edge, float [^%(),]*%scale\)', header):
        raise ValueError('unknown kernel signature')
    definitions = []
    # The scaled input and rounded result are local proof cuts. At each cut we
    # prove its contract before replacing it with an arbitrary satisfying value.
    stage = 0
    wide_scale = None
    saw_inverse = False
    for line in map(str.strip, body.splitlines()):
        if not line or line == 'start:':
            continue
        if line.startswith('ret float ') and stage == 2:
            result = operand(line.removeprefix('ret float '))
            check(z3, backend + ' published edge', definitions,
                  f'(or (= {result} (narrow (fp.mul RNE rounded inverse))) '
                  f'    (= {result} (narrow (fp.mul RNE inverse rounded))))')
            stage = 3
            continue
        name, rhs = line.split(' = ')
        ty, expr = translate(rhs)
        if rhs == 'fpext float %scale to double':
            wide_scale = operand(name)
        if rhs.startswith('fdiv '):
            if saw_inverse or expr != f'(fp.div RNE {render(ONE64)} {wide_scale})':
                raise ValueError('expected the binary64 reciprocal of the widened scale')
            saw_inverse = True
            expr = 'inverse'
        if stage == 0 and rhs.startswith('fmul '):
            ref = '(fp.mul RNE (wide edge) (wide scale))'
            check(z3, backend + ' scaled input', definitions,
                  f'(and (= {expr} {ref}) (possible-product {expr}))')
            stage, expr = 1, 'scaled'
        elif stage == 1 and ('@llvm.copysign.' in rhs or '@llvm.round.' in rhs):
            check(z3, backend + ' ties away', definitions,
                  f'(=> (possible-product scaled) (= {expr} (fp.roundToIntegral RNA scaled)))')
            stage, expr = 2, 'rounded'
        definitions.append(f'(define-fun {operand(name)} () {ty} {expr})')
    if stage != 3 or not saw_inverse:
        raise ValueError('kernel did not produce all proof cuts')


VECTOR = r'<(\d+) x (double|float|i1|i32|i64)>'
WIDTH = {'double': 64, 'float': 32, 'i32': 32, 'i64': 64}
FP32 = '(_ to_fp 8 24)'
FP64 = '(_ to_fp 11 53)'
ONE64 = (FP64, '#x3ff0000000000000')
SCALE = ('wide', 'scale')
INVERSE = ('fp.div', 'RNE', ONE64, SCALE)
NARROW_INVERSE = ('narrow', INVERSE)


def render(term):
    if isinstance(term, tuple):
        return '(' + ' '.join(map(render, term)) + ')'
    return term


def lane_constant(kind, literal):
    if literal in ('poison', 'undef'):
        return None
    if kind in ('double', 'float'):
        if literal.startswith('f0x'):
            digits = literal[3:].lower()
            if len(digits) != WIDTH[kind] // 4:
                raise ValueError(f'invalid LLVM hex literal {literal} for {kind}')
            return (FP64 if kind == 'double' else FP32, '#x' + digits)
        if literal.startswith('0x'):
            # LLVM hexadecimal float literals use the corresponding double bits.
            bits = '#x' + literal[-16:]
            fp = (FP64, bits)
            return fp if kind == 'double' else ('narrow', fp)
        if kind == 'double':
            return (FP64, '#x' + struct.pack('>d', float(literal)).hex())
        return (FP32, '#x' + struct.pack('>f', float(literal)).hex())
    if kind == 'i1':
        if literal not in ('true', 'false'):
            raise ValueError(f'unsupported i1 literal {literal}')
        return literal
    width = WIDTH[kind]
    return f'#x{int(literal) % (1 << width):0{width // 4}x}'


def split_arguments(line):
    """Split LLVM operands without splitting vector literals or splats."""
    parts, start, depth = [], 0, 0
    for i, char in enumerate(line):
        if char in '<(':
            depth += 1
        elif char in '>)':
            depth -= 1
        elif char == ',' and depth == 0:
            parts.append(line[start:i].strip())
            start = i + 1
    return parts + [line[start:].strip()]


def half_word(word, lo):
    if isinstance(word, str) and word.startswith('#x'):
        return '#x' + (word[-8:] if lo == 0 else word[2:10])
    if isinstance(word, tuple):
        op, *args = word
        if op == 'concat':
            return args[1] if lo == 0 else args[0]
        if op in ('bvand', 'bvor', 'bvxor'):
            return (op, *(half_word(arg, lo) for arg in args))
    return (f'(_ extract {lo + 31} {lo})', word)


def bit_lanes(values, source, dest):
    """Interpret data as x86 little-endian lane bits, including i32 splits."""
    def raw(value):
        if value is None or source not in ('double', 'float'):
            return value
        fp = FP64 if source == 'double' else FP32
        if isinstance(value, tuple) and len(value) == 2 and value[0] == fp:
            return value[1]
        return (f'bits{WIDTH[source]}', value)

    def cast(value):
        if value is None or dest not in ('double', 'float'):
            return value
        return (FP64 if dest == 'double' else FP32, value)

    words = tuple(map(raw, values))
    if WIDTH[source] == WIDTH[dest]:
        return tuple(map(cast, words))
    if WIDTH[source] == 64:
        return tuple(cast(None if word is None else half_word(word, lo))
                     for word in words for lo in (0, 32))
    return tuple(cast(None if lo is None or hi is None else ('concat', hi, lo))
                 for lo, hi in zip(words[::2], words[1::2], strict=True))


def vector_operand(values, kind, count, literal):
    if literal.startswith('%'):
        lanes = values[literal]
    elif literal in ('poison', 'undef', 'zeroinitializer'):
        zero = 'false' if kind == 'i1' else '0'
        lanes = (lane_constant(kind, zero) if literal == 'zeroinitializer' else None,) * count
    elif literal.startswith('splat (') and literal.endswith(')'):
        lanes = (lane_constant(kind, literal[7:-1].removeprefix(kind + ' ')),) * count
    elif literal.startswith('<') and literal.endswith('>'):
        lanes = tuple(lane_constant(kind, item.strip().removeprefix(kind + ' '))
                      for item in literal[1:-1].split(','))
    else:
        raise ValueError(f'unsupported LLVM vector operand {literal}')
    if len(lanes) != count:
        raise ValueError(f'expected {count} LLVM lanes for {literal}, found {len(lanes)}')
    return lanes


def packed_operand(values, typed):
    match = re.fullmatch(rf'({VECTOR}) (.+)', typed)
    if not match:
        raise ValueError(f'unsupported typed vector operand {typed}')
    _, count, kind, literal = match.groups()
    return vector_operand(values, kind, int(count), literal)


def lanes_using(op, *vectors):
    return tuple(None if None in operands else op(*operands)
                 for operands in zip(*vectors, strict=True))


def scaled_product(a, b):
    if b == 'scale':
        a, b = b, a
    if a == 'scale' and b in EDGES:
        return ('scaled32-lane', b)
    if b == SCALE:
        a, b = b, a
    if a == SCALE and isinstance(b, tuple) and b[0] == 'wide' and b[1] in EDGES:
        return ('scaled-lane', b[1])
    return ('fp.mul', 'RNE', a, b)


EDGES = tuple(f'edge{i}' for i in range(8))


def vector_rhs(values, rhs, lane_count):
    if match := re.fullmatch(rf'load {VECTOR}, ptr %input, align \d+', rhs):
        n, kind = match.groups()
        if int(n) * WIDTH[kind] != lane_count * 32:
            raise ValueError(f'invalid rectangle load {rhs}')
        edges = EDGES[:lane_count]
        return bit_lanes(edges, 'float', kind) if kind != 'float' else edges
    if rhs == 'fpext float %scale to double':
        return (SCALE,)
    if match := re.fullmatch(r'fptrunc double (%\S+) to float', rhs):
        value, = values[match[1]]
        return (('narrow', value),)
    if rhs == 'fdiv float 1.000000e+00, %scale':
        # Both division widths produce the exact reciprocal for the admitted
        # normal binary32 powers of two. LLVM can narrow this division.
        return (NARROW_INVERSE,)
    if match := re.fullmatch(r'fdiv double (\S+), (%\S+)', rhs):
        value, = values[match[2]]
        return (('fp.div', 'RNE', lane_constant('double', match[1]), value),)
    if match := re.fullmatch(rf'insertelement ({VECTOR} (?:poison|undef)), (double|float) (%\S+), i64 (\d+)', rhs):
        old, _, kind, scalar_kind, name, i = match.groups()
        if kind != scalar_kind:
            raise ValueError(f'mismatched LLVM scalar and vector lane: {rhs}')
        lanes = list(packed_operand(values, old))
        lanes[int(i)], = ('scale',) if name == '%scale' and kind == 'float' else values[name]
        return tuple(lanes)
    if rhs.startswith('shufflevector '):
        a, b, mask = split_arguments(rhs.removeprefix('shufflevector '))
        lanes = packed_operand(values, a) + packed_operand(values, b)
        mask_size, indices = re.fullmatch(r'<(\d+) x i32> (.+)', mask).groups()
        if indices == 'zeroinitializer':
            return (lanes[0],) * int(mask_size)
        return tuple(None if i == 'poison' else lanes[int(i)]
                     for i in re.findall(r'i32 (\d+|poison)', indices))
    if match := re.fullmatch(rf'(fpext|fptrunc) ({VECTOR} %\S+) to {VECTOR}', rhs):
        op, src, *_ = match.groups()
        return lanes_using(lambda x: ('wide' if op == 'fpext' else 'narrow', x), packed_operand(values, src))
    if match := re.fullmatch(rf'bitcast ({VECTOR} %\S+) to {VECTOR}', rhs):
        src, _, src_kind, dest_n, dest_kind = match.groups()
        lanes = bit_lanes(packed_operand(values, src), src_kind, dest_kind)
        if len(lanes) != int(dest_n):
            raise ValueError(f'unsupported LLVM bitcast {rhs}')
        return lanes
    if match := re.fullmatch(r'sitofp (<4 x i32> %\S+) to <4 x float>', rhs):
        return lanes_using(lambda x: (FP32, 'RNE', x), packed_operand(values, match[1]))
    if match := re.fullmatch(rf'(fmul|fadd|fsub|fdiv|and|or(?: disjoint)?|xor) {VECTOR} (.+)', rhs):
        op, count, kind, operands = match.groups()
        a, b = (vector_operand(values, kind, int(count), token) for token in split_arguments(operands))
        if op == 'fmul':
            return lanes_using(scaled_product, a, b)
        if op.startswith('f'):
            return lanes_using(lambda x, y: ('fp.' + op[1:], 'RNE', x, y), a, b)
        return lanes_using(lambda x, y: ('bv' + op.split()[0], x, y), a, b)
    if match := re.fullmatch(rf'(?:tail )?call {VECTOR} @([\w.]+)\((.*)\)', rhs):
        n, kind, function, inputs = match.groups()
        args = split_arguments(inputs)
        if function in (f'llvm.fabs.v{n}f64', f'llvm.floor.v{n}f64') and kind == 'double' and len(args) == 1:
            def fp_unary(x):
                return ('fp.abs', x) if 'fabs' in function else ('fp.roundToIntegral', 'RTN', x)
            return lanes_using(fp_unary, packed_operand(values, args[0]))
        if function == f'llvm.copysign.v{n}f64' and kind == 'double' and len(args) == 2:
            return lanes_using(lambda x, y: ('copysign', x, y),
                               packed_operand(values, args[0]), packed_operand(values, args[1]))
        if function == f'llvm.fma.v{n}f64' and kind == 'double' and len(args) == 3:
            def add_to_exact_product(a, b, c):
                product = scaled_product(a, b)
                if product[0] != 'scaled-lane':
                    raise ValueError(f'expected FMA on widened binary32 edge and scale: {a}, {b}')
                # The binary32 product has at most 48 significant bits and
                # lies within the normal binary64 range when nonzero and finite.
                # The widening and multiplication are exact, so only the add rounds.
                return ('fp.add', 'RNE', product, c)
            return lanes_using(add_to_exact_product, *(packed_operand(values, arg) for arg in args))
        if function == 'llvm.x86.avx.round.pd.256' and n == '4' and kind == 'double' and args[-1] == 'i32 3':
            return lanes_using(lambda x: ('fp.roundToIntegral', 'RTZ', x), packed_operand(values, args[0]))
        if function == 'llvm.x86.sse41.round.ps' and n == '4' and kind == 'float' and args[-1] == 'i32 3':
            return lanes_using(lambda x: ('fp.roundToIntegral', 'RTZ', x), packed_operand(values, args[0]))
        if function == 'llvm.x86.sse2.cmp.pd' and n == '2' and kind == 'double' and args[-1] == 'i8 1':
            return lanes_using(lambda x, y: (FP64, ('ite', ('fp.lt', x, y), '#xffffffffffffffff', '#x0000000000000000')),
                               packed_operand(values, args[0]), packed_operand(values, args[1]))
        if function == 'llvm.x86.sse.cmp.ps' and n == '4' and kind == 'float' and args[-1] == 'i8 1':
            return lanes_using(lambda x, y: (FP32, ('ite', ('fp.lt', x, y), '#xffffffff', '#x00000000')),
                               packed_operand(values, args[0]), packed_operand(values, args[1]))
        if function == 'llvm.x86.sse2.cvttps2dq' and n == '4' and kind == 'i32' and len(args) == 1:
            return lanes_using(lambda x: ('trunc32', x), packed_operand(values, args[0]))
        if n == '8' and args[-2:] == ['i8 -1', 'i32 4']:
            x = packed_operand(values, args[0])
            if function == 'llvm.x86.avx512.mask.cvtps2pd.512' and kind == 'double':
                return lanes_using(lambda lane: ('wide', lane), x)
            if function == 'llvm.x86.avx512.mask.cvtpd2ps.512' and kind == 'float':
                return lanes_using(lambda lane: ('narrow', lane), x)
            if function == 'llvm.x86.avx512.mask.rndscale.pd.512' and kind == 'double' and args[1] in ('i32 1', 'i32 3'):
                mode = 'RTN' if args[1] == 'i32 1' else 'RTZ'
                return lanes_using(lambda lane: ('fp.roundToIntegral', mode, lane), x)
    raise ValueError(f'unsupported LLVM vector instruction {rhs}')


def lane_expression(term, edge, unit=False, reads_edge=False, power_of_two=False):
    if isinstance(term, tuple):
        if term[0] in ('scaled-lane', 'scaled32-lane'):
            if unit or term[1] != edge or (term[0] == 'scaled32-lane') != power_of_two:
                raise ValueError(f'crossed vector lanes: {term[1]} read while publishing {edge}')
            return 'scaled32' if power_of_two else 'scaled'
        if power_of_two and term == NARROW_INVERSE:
            return 'inverse32'
        return tuple(lane_expression(child, edge, unit, reads_edge, power_of_two) for child in term)
    if term in EDGES:
        if (unit or reads_edge or power_of_two) and term == edge:
            return 'edge'
        raise ValueError(f'crossed or unscaled lane: {term} read while publishing {edge}')
    if term is None:
        raise ValueError(f'unscaled or uninitialized lane {term}')
    return term


def ieee_words(term, payloads):
    if not isinstance(term, tuple):
        return term
    *prefix, last = tuple(ieee_words(child, payloads) for child in term)
    if prefix in (['bits64'], ['bits32']):
        # SMT floats represent all NaNs as one value. Give each bitcast
        # source its own arbitrary NaN word before verifying the bit masks.
        kind, = prefix
        name = payloads.setdefault((kind, last), f'nan{len(payloads)}')
        return (kind, last, name)
    return (*prefix, last)


def vector_output(ir, backend, unit, lane_count=4):
    header, body = re.search(rf'^define void ([^\n]*@{backend}_kernel\([^\n]+)\{{\n(.*?)^\}}', ir, re.M | re.S).groups()
    scale_arg = '' if unit else r'float [^%]*%scale, '
    if not re.search(rf'ptr [^%]*%input, {scale_arg}ptr [^%]*%output\)', header):
        raise ValueError('unknown vector kernel signature')
    values, stored = {}, None
    for line in map(str.strip, body.splitlines()):
        if not line or (not values and re.fullmatch(r'[\w.]+:', line)):
            continue
        if line == 'ret void':
            if stored is None:
                raise ValueError('vector kernel did not publish the result')
            continue
        if match := re.fullmatch(rf'store ({VECTOR} %\S+), ptr %output, align \d+', line):
            if stored is not None:
                raise ValueError('vector kernel published several results')
            src, n, kind = match.groups()
            if int(n) * WIDTH[kind] != lane_count * 32:
                raise ValueError(f'invalid rectangle store {line}')
            stored = packed_operand(values, src)
            if kind != 'float':
                stored = bit_lanes(stored, kind, 'float')
            continue
        if ' = ' not in line:
            raise ValueError(f'unsupported LLVM vector line {line}')
        name, rhs = line.split(' = ')
        values[name] = vector_rhs(values, rhs, lane_count)
    return stored


def check_lanes(z3, backend, proofs, claim):
    for expression in sorted(proofs, key=render):
        payloads = {}
        expr = render(ieee_words(expression, payloads))
        definitions = []
        for (kind, _), name in payloads.items():
            fp = FP64 if kind == 'bits64' else FP32
            definitions.extend((f'(declare-const {name} (_ BitVec {kind[4:]}))', f'(assert (fp.isNaN ({fp} {name})))'))
        check(z3, backend + ' packed lanes', definitions, claim(expr))


def verify_vector(ir, backend, z3, lane_count=4):
    stored = vector_output(ir, backend, unit=False, lane_count=lane_count)
    reads_edge = backend == 'avx2_fma'

    # Scaled markers can only come from the exact product checked by the
    # scalar proof. Check every lane route, then reuse identical SMT terms.
    proofs = set()
    for edge, lane in zip(EDGES[:lane_count], stored, strict=True):
        if (not isinstance(lane, tuple) or lane[0] != 'narrow'
                or lane[1][:2] != ('fp.mul', 'RNE') or INVERSE not in lane[1][2:]):
            raise ValueError(f'expected multiply by the binary64 inverse and narrow in {backend}: {lane}')
        a, b = lane[1][2:]
        proofs.add(lane_expression(b if a == INVERSE else a, edge, reads_edge=reads_edge))
    input_contract = '(possible-product scaled)'
    if reads_edge:
        # Positive finite scaling preserves the sign (including signed zero and
        # infinities) and NaN classification. The FMA's half can use the edge sign.
        input_contract = (f'(and {input_contract} '
                          '(= (fp.isNegative scaled) (fp.isNegative (wide edge))) '
                          '(= (fp.isNaN scaled) (fp.isNaN (wide edge))))')
    check_lanes(z3, backend.upper(), proofs,
                lambda expr: f'(=> {input_contract} (= {expr} (fp.roundToIntegral RNA scaled)))')


def verify_unit_vector(ir, backend, z3):
    stored = vector_output(ir, 'sse2_unit', unit=True)
    proofs = {lane_expression(lane, edge, unit=True) for edge, lane in zip(EDGES[:4], stored, strict=True)}
    check_lanes(z3, backend + ' unit', proofs, lambda expr: f'(= {expr} (fp.roundToIntegral RNA edge))')


def cut_power_of_two_unscale(term, roundings):
    if not isinstance(term, tuple):
        return term
    if term[:2] == ('fp.mul', 'RNE') and 'inverse32' in term[2:]:
        a, b = term[2:]
        roundings.add(b if a == 'inverse32' else a)
        return 'snapped32'
    return tuple(cut_power_of_two_unscale(child, roundings) for child in term)


def verify_power_of_two(ir, backend, z3):
    stored = vector_output(ir, 'sse2_power_of_two', unit=False)
    # Each cut is available only after the IR matches its lane-local multiply
    # by the original scale or its narrowing of the correctly widened inverse.
    roundings = set()
    proofs = {cut_power_of_two_unscale(lane_expression(lane, edge, power_of_two=True), roundings)
              for edge, lane in zip(EDGES[:4], stored, strict=True)}
    small = '(fp.lt (fp.abs scaled32) ((_ to_fp 8 24) #x4b000000))'
    check_lanes(z3, backend + ' power of two rounding', roundings,
                lambda expr: f'(=> {small} (= {expr} (fp.roundToIntegral RNA scaled32)))')
    check_lanes(z3, backend + ' power of two publication', proofs,
                lambda expr: f'(= {expr} (ite {small} snapped32 edge))')


def scaled_vector_wrapper(backend, entry, feature):
    return (f'#[unsafe(no_mangle)] #[target_feature(enable="{feature}")]\n'
            f'pub unsafe fn {backend}_kernel(input: *const [f32; 4], scale: f32, output: *mut [f32; 4]) {{\n'
            f'    unsafe {{ output.write(vector::{entry}(input.read(), Scale::new(scale))); }}\n'
            '}\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--z3', default=os.environ.get('Z3', 'z3'))
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory)
        # Include the very function called by snap_rect and parent-local placement.
        (tmp / 'kernel.rs').write_text(
            f'#[path=r"{ROOT}/src/pixel_grid.rs"] mod pixel_grid;\n'
            '#[unsafe(no_mangle)] pub fn kernel(edge: f32, scale: f32) -> f32 '
            '{ pixel_grid::snap_edge(edge, pixel_grid::Scale::new(scale)) }\n')
        for backend, feature in [('SSE2', '-sse4.1'), ('SSE4.1', '+sse4.1')]:
            subprocess.run(['rustc', '--edition=2024', '--crate-type=lib', '--emit=llvm-ir',
                            '--target=x86_64-unknown-linux-gnu', '-Copt-level=3', '-Ctarget-cpu=x86-64',
                            '-Adead_code', f'-Ctarget-feature={feature}', 'kernel.rs', '-o', 'kernel.ll'],
                           cwd=tmp, check=True)
            verify((tmp / 'kernel.ll').read_text(), backend, args.z3)

        backends = {'sse2': 'sse2', 'avx2': 'avx2', 'avx512': 'avx512f'}
        production = f'include!(r"{ROOT}/src/pixel_grid.rs");\n'
        wrapper = [production]
        for backend, feature in backends.items():
            entry = 'sse2_scaled' if backend == 'sse2' else backend
            wrapper.append(scaled_vector_wrapper(backend, entry, feature))
        wrapper.append(
            '#[unsafe(no_mangle)] #[target_feature(enable="sse2")]\n'
            'pub unsafe fn sse2_unit_kernel(input: *const [f32; 4], output: *mut [f32; 4]) {\n'
            '    unsafe { output.write(vector::sse2_unit(input.read(), Scale::new(1.0))); }\n'
            '}\n')
        wrapper.append(scaled_vector_wrapper('sse2_power_of_two', 'sse2_power_of_two', 'sse2'))
        wrapper.append(
            '#[unsafe(no_mangle)] #[target_feature(enable="avx512f")]\n'
            'pub unsafe fn avx512_many_kernel(input: *const [[f32; 4]; 2], scale: f32, output: *mut [[f32; 4]; 2]) {\n'
            '    let mut pair = unsafe { input.read() };\n'
            '    unsafe { vector::avx512_many(&mut pair, Scale::new(scale)); output.write(pair); }\n'
            '}\n'
        )
        (tmp / 'vector.rs').write_text(''.join(wrapper))
        compile_vector = ['rustc', '--edition=2024', '--crate-type=lib', '--emit=llvm-ir',
                          '--target=x86_64-unknown-linux-gnu', '-Copt-level=3', '-Ctarget-cpu=x86-64',
                          '-Adead_code', '--cfg', 'keru_avx512']
        for unit_backend, feature in [('SSE2', '-sse4.1'), ('SSE4.1', '+sse4.1')]:
            subprocess.run([*compile_vector, f'-Ctarget-feature={feature}', 'vector.rs', '-o', 'vector.ll'],
                           cwd=tmp, check=True)
            vector = (tmp / 'vector.ll').read_text()
            if unit_backend == 'SSE2':
                for backend in backends:
                    verify_vector(vector, backend, args.z3)
                verify_vector(vector, 'avx512_many', args.z3, lane_count=8)
            verify_unit_vector(vector, unit_backend, args.z3)
            verify_power_of_two(vector, unit_backend, args.z3)
        # The FMA route is compiled into AVX2+FMA builds. Verify the optimized
        # wrapper with those same global features in a separate compilation.
        (tmp / 'vector_fma.rs').write_text(production + scaled_vector_wrapper('avx2_fma', 'avx2_fma', 'avx2,fma'))
        subprocess.run([*compile_vector, '-Ctarget-feature=+avx2,+fma', 'vector_fma.rs', '-o', 'vector_fma.ll'],
                       cwd=tmp, check=True)
        verify_vector((tmp / 'vector_fma.ll').read_text(), 'avx2_fma', args.z3)


if __name__ == '__main__':
    main()
