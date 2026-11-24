"""Check native grid bit counts, track normalization and Start rectangle lanes."""

from pathlib import Path
import re
import subprocess
import tempfile
from textwrap import dedent


SOURCE = Path(__file__).resolve().parents[1] / 'src/grid_words.rs'
STATE = SOURCE.with_name('grid_state.rs')
INTRINSICS = {'leading': 'ctlz', 'trailing': 'cttz'}


def compile_primitives(directory):
    wrappers = [f'#[path = r"{SOURCE}"] mod words;',
                f'#[path = r"{STATE}"] mod state;',
                'use words::{IntrinsicZeroCounts, ZeroCounts};',
                'use state::{RustWidthRounding, width_key};']
    for name in INTRINSICS:
        wrappers.append(f'#[unsafe(no_mangle)] pub fn grid_{name}(word: u64) -> u32 '
                        f'{{ IntrinsicZeroCounts::{name}(word) }}')
    for field, result in [('tracks', 'f32'), ('columns', 'usize')]:
        wrappers.append(f'#[unsafe(no_mangle)] pub fn grid_width_{field}'
                        f'(inner: f32, width: f32, gap: f32) -> {result} '
                        f'{{ width_key::<RustWidthRounding>(inner, width, gap).{field} }}')
    (directory / 'kernel.rs').write_text('\n'.join(wrappers))
    subprocess.run(['rustc', '--edition=2024', '--crate-type=lib', '--emit=llvm-ir',
                    '-Copt-level=3', '-Coverflow-checks=on', '-Cpanic=unwind',
                    '-Adead_code', 'kernel.rs', '-o', 'kernel.ll'], cwd=directory, check=True)
    return (directory / 'kernel.ll').read_text()


def check_lowering(ir, name, intrinsic):
    function = re.search(rf'^define [^\n]*i32 @grid_{name}\(i64 (?:noundef )?%word\)'
                         r'[^\n]*#(\d+)[^\n]*\{\n(.*?)^\}', ir, re.M | re.S)
    if function is None:
        raise ValueError(f'missing definition for {name}')
    attributes = re.search(rf'^attributes #{function[1]} = \{{[^\n]*\bnounwind\b', ir, re.M)
    if attributes is None:
        raise ValueError(f'{name} lacks nounwind')

    # LLVM's i1 false makes the zero-input result the input width. The
    # intrinsic returns a count in 0..=64, so trunc to i32 preserves it.
    operation = (rf'start:\s+(%[\w.]+) = (?:tail )?call (?:range\(i64 0, 65\) )?'
                 rf'i64 @llvm\.{intrinsic}\.i64\(i64 %word, i1 false\)\s+'
                 r'(%[\w.]+) = trunc (?:(?:nuw|nsw) )*i64 \1 to i32\s+'
                 r'ret i32 \2')
    if re.fullmatch(operation, function[2].strip()) is None:
        raise ValueError(f'unexpected lowering for {name}:\n{function[2]}')
    print(f'grid {name} zero count verified')


def check_width(ir, field, result):
    function = re.search(rf'^define [^\n]*{result} @grid_width_{field}'
                         rf'\(float noundef %inner, float noundef %width, float noundef %gap\)'
                         r'[^\n]*#(\d+)[^\n]*\{\n(.*?)^\}', ir, re.M | re.S)
    if function is None:
        raise ValueError(f'missing width definition for {field}')
    if re.search(rf'^attributes #{function[1]} = \{{[^\n]*\bnounwind\b', ir, re.M) is None:
        raise ValueError(f'width {field} lacks nounwind')
    body = '\n'.join(line.partition(';')[0].strip() for line in function[2].splitlines())
    word = r'%[\w.]+'
    # Binary32 operations remain in their original order. Floor on NaN
    # yields NaN, so maximumNumber selects 1. The upper cap is 2**64
    # rounded in binary32. A saturating unsigned cast preserves positivity.
    operation = (
        rf'start:\s+(?P<step>{word}) = fadd float %width, %gap\s+'
        rf'(?P<zero>{word}) = fcmp oeq float (?P=step), 0\.000000e\+00\s+'
        rf'br i1 (?P=zero), label %(?P<join>\w+), label %(?P<divide>\w+)\s+'
        rf'(?P=divide):\s+(?P<sum>{word}) = fadd float %inner, %gap\s+'
        rf'(?P<quotient>{word}) = fdiv float (?P=sum), (?P=step)\s+'
        rf'(?P<floor>{word}) = tail call float @llvm\.floor\.f32\(float (?P=quotient)\)\s+'
        rf'(?P<lower>{word}) = tail call nsz float @llvm\.maximumnum\.f32'
        rf'\(float (?P=floor), float 1\.000000e\+00\)\s+'
        rf'(?P<upper>{word}) = tail call nsz float @llvm\.minimumnum\.f32'
        rf'\(float (?P=lower), float f0x5F800000\)\s+'
    )
    if field == 'columns':
        operation += rf'(?P<count>{word}) = tail call i64 @llvm\.fptoui\.sat\.i64\.f32\(float (?P=upper)\)\s+'
    chosen, one = ('count', '1') if field == 'columns' else ('upper', r'1\.000000e\+00')
    operation += (
        rf'br label %(?P=join)\s+(?P=join):\s+'
        rf'(?P<result>{word}) = phi {result} \[ (?P={chosen}), %(?P=divide) \], \[ {one}, %start \]\s+'
        rf'ret {result} (?P=result)'
    )
    if re.fullmatch(operation, body.strip()) is None:
        raise ValueError(f'unexpected lowering for width {field}:\n{function[2]}')
    print(f'grid width {field} normalization verified')


def compile_start_edges(directory):
    sources = SOURCE.parent
    packed = re.search(r'^fn grid_start_rect\([^\n]+\n.*?^}',
                       (sources / 'place.rs').read_text(), re.M | re.S)[0]
    scalar = re.search(r'^pub\(crate\) fn grid_start_edges\([^\n]+\n.*?^}',
                       (sources / 'placement_geometry.rs').read_text(), re.M | re.S)[0]
    (directory / 'edges.rs').write_text('''
struct Xy<T> { x: T, y: T }
impl<T> Xy<T> { fn new(x: T, y: T) -> Self { Self { x, y } } }
type XyRect = Xy<[f32; 2]>;
''' + packed + '\nmod geometry { ' + scalar + ' }\n' + '''
#[unsafe(no_mangle)]
pub fn grid_start_packed(input: &[f32; 8], output: &mut [f32; 4]) {
    let &[x, y, dx, dy, cx, cy, w, h] = input;
    let rect = grid_start_rect(Xy::new(x, y), Xy::new(dx, dy), Xy::new(cx, cy), Xy::new(w, h));
    *output = [rect.x[0], rect.x[1], rect.y[0], rect.y[1]];
}
#[unsafe(no_mangle)]
pub fn grid_start_scalar(input: &[f32; 8], output: &mut [f32; 4]) {
    let &[x, y, dx, dy, cx, cy, w, h] = input;
    let [left, right] = geometry::grid_start_edges(x, dx, cx, w);
    let [top, bottom] = geometry::grid_start_edges(y, dy, cy, h);
    *output = [left, right, top, bottom];
}
''')
    subprocess.run(['rustc', '--edition=2024', '--crate-type=lib', '--emit=llvm-ir',
                    '--target=x86_64-unknown-linux-gnu', '-Ctarget-cpu=x86-64', '-Copt-level=3',
                    '-Adead_code', 'edges.rs', '-o', 'edges.ll'], cwd=directory, check=True)
    return (directory / 'edges.ll').read_text()


def start_edges(ir, route, inputs=8):
    body = re.search(rf'^define void @grid_start_{route}\([^\n]+\{{\n(.*?)^}}', ir, re.M | re.S)[1]
    address = {'%input': ('input', 0), '%output': ('output', 0)}
    values, output = {}, [None] * 4
    lane_type = r'(?:<\d+ x float>|float)'
    value = r'(?:%[\w.]+|zeroinitializer|0\.000000e\+00|poison|<float [^>]+>)'

    def lanes(operand, count):
        if operand in values:
            result = values[operand]
        elif operand.startswith('<'):
            result = tuple(lanes(item.removeprefix('float '), 1)[0] for item in operand[1:-1].split(', '))
        elif operand in ('0.000000e+00', 'zeroinitializer', 'poison'):
            result = (('poison' if operand == 'poison' else 'zero'),) * count
        else:
            raise ValueError(f'unknown grid edge operand {operand}')
        if len(result) != count:
            raise ValueError(f'mismatched grid lane type for {operand}')
        return result

    def width(kind):
        return 1 if kind == 'float' else int(kind.split()[0][1:])

    lines = tuple(map(str.strip, body.splitlines()))
    if not re.fullmatch(r'[\w.]+:', lines[0]) or lines[-1] != 'ret void':
        raise ValueError('expected a single straight-line Grid Start block')
    for line in lines[1:-1]:
        if m := re.fullmatch(r'(%\S+) = getelementptr inbounds(?: nuw)? i8, ptr (%\S+), i64 (\d+)', line):
            name, base, offset = m.groups()
            origin, index = address[base]
            if int(offset) % 4:
                raise ValueError('grid edge pointer is not aligned to a word')
            address[name] = (origin, index + int(offset) // 4)
        elif m := re.fullmatch(rf'(%\S+) = load ({lane_type}), ptr (%\S+), align 4(?:, !noundef !\d+)?', line):
            name, kind, pointer = m.groups()
            origin, begin = address[pointer]
            end = begin + width(kind)
            if origin != 'input' or end > inputs:
                raise ValueError('grid edge kernel reads beyond its inputs')
            values[name] = tuple(('input', i) for i in range(begin, end))
        elif m := re.fullmatch(rf'(%\S+) = (fadd|fmul) ({lane_type}) ({value}), ({value})', line):
            name, op, kind, left, right = m.groups()
            # Ordinary addition and multiplication commute on IEEE values.
            # The host sink supplies a fixed word for all NaN results.
            values[name] = tuple((op, *sorted([x, y], key=repr)) for x, y in
                                 zip(lanes(left, width(kind)), lanes(right, width(kind)), strict=True))
        elif m := re.fullmatch(rf'(%\S+) = insertelement ({lane_type}) ({value}), float ({value}), i(?:32|64) (\d+)', line):
            name, kind, original, item, index = m.groups()
            output_lanes = list(lanes(original, width(kind)))
            output_lanes[int(index)] = lanes(item, 1)[0]
            values[name] = tuple(output_lanes)
        elif m := re.fullmatch(rf'(%\S+) = extractelement ({lane_type}) ({value}), i(?:32|64) (\d+)', line):
            name, kind, original, index = m.groups()
            values[name] = (lanes(original, width(kind))[int(index)],)
        elif m := re.fullmatch(rf'(%\S+) = shufflevector ({lane_type}) ({value}), ({lane_type}) ({value}), <\d+ x i32> <([^>]+)>', line):
            name, left_type, left, right_type, right, selected = m.groups()
            choices = lanes(left, width(left_type)) + lanes(right, width(right_type))
            indices = [item.removeprefix('i32 ') for item in selected.split(', ')]
            values[name] = tuple('poison' if index == 'poison' else choices[int(index)] for index in indices)
        elif m := re.fullmatch(rf'store ({lane_type}) (%\S+), ptr (%\S+), align 4', line):
            kind, name, pointer = m.groups()
            origin, begin = address[pointer]
            end = begin + width(kind)
            if origin != 'output' or end > len(output) or any(output[begin:end]):
                raise ValueError('invalid grid edge publication')
            output[begin:end] = lanes(name, width(kind))
        else:
            raise ValueError(f'unknown grid edge instruction {line}')
    if any(edge is None or 'poison' in repr(edge) for edge in output):
        raise ValueError('grid edge kernel publishes an uninitialized lane')
    return output


def item_source(text, declaration, indent=''):
    match = re.search(rf'^{indent}{declaration}[^{{]*\{{\n.*?^{indent}\}}', text, re.M | re.S)
    if match is None:
        raise ValueError(f'missing Grid Start source item: {declaration}')
    return dedent(match[0])


def compile_grid_start_recipe(directory):
    sources = SOURCE.parent
    placement = (sources / 'placement_modes.rs').read_text()
    native = (sources / 'place.rs').read_text()
    adapter = (sources / 'placement_adapter.rs').read_text()
    declarations = (sources / 'declarations.rs').read_text()
    float_bridge = (sources / 'prepare_frame.rs').read_text()
    grid = item_source(placement, r'pub\(crate\) fn grid<')
    context = re.search(
        r'^    let \[left, _\] = [^\n]+\n'
        r'    let \[top, _\] = [^\n]+\n'
        r'    let step = [^\n]+\n'
        r'    let forward = !frame\.flipped\[0\] && !frame\.flipped\[1\];',
        grid, re.M,
    )
    # Match the fast and ordinary sibling branches together. The fixture fixes
    # only properties required by the guards around the actual fast call.
    routes = re.search(
        r'if tree\.disabled\(id\) \|\| node::skip_clean::<_, _, PARTIAL>\(tree, id\) \{\s*None\s*\} else \{\s*'
        r'let size = tree\.size\(id\);\s*let GridStyle \{ align: style, span \} = tree\.grid_style\(id\);\s*'
        r'let rect = if style\.free \{[^{}]+\} else \{\s*let child_cell = tree\.grid_cell\(id\);\s*'
        r'if forward && matches!\(style\.pos, \[Pos::Start, Pos::Start\]\) && style\.zero_margins \{\s*'
        r'T::(grid_start\([^\n]+\))\s*\} else \{\n'
        r'(.*?)^                \}\s*\}\s*;\s*emit::<_, _, PARTIAL>\(tree, id, rect, frame\.origin\)',
        grid, re.M | re.S,
    )
    if context is None or routes is None:
        raise ValueError('Grid Start layout recipe changed')

    frame = item_source(placement, r'pub\(crate\) struct Frame\b')
    stack_style = item_source(placement, r'pub\(crate\) struct StackStyle\b')
    grid_style = item_source(placement, r'pub\(crate\) struct GridStyle\b')
    aligned_axis = item_source(placement, r'fn aligned_axis<')
    zero_margins = item_source(placement, r'pub\(crate\) fn zero_margins\b')
    style = item_source(adapter, r'pub\(crate\) fn stack_style<')
    grid_style_read = item_source(adapter, r'pub\(crate\) fn grid_style<')
    native_style = item_source(native, r'fn grid_style\(', indent='    ')
    grid_native = item_source(native, r'fn grid_start\(', indent='    ')
    grid_packed = item_source(native, r'fn grid_start_rect\(')
    margin_type = re.search(r'^pub struct Margin\(u32\);$', declarations, re.M)
    margins = item_source(declarations, r'impl Margin\b')
    if (margin_type is None or 'fn is_zero(self) -> bool { self.0 == 0 }' not in margins
            or 'pub const ZERO: Self = Self(0);' not in margins):
        raise ValueError('Grid Start no longer selects precisely the all-zero margin words')
    if 'crate::placement_adapter::grid_style::<RustFloat>(self.tree.node_layout_params(id))' not in native_style:
        raise ValueError('Grid Start style no longer reads the checked adapter fields')
    float_bindings = ('margin', 'add', 'subtract', 'multiply', 'divide', 'less_or_equal', 'less_than')
    float_impl = re.findall(
        r'^    fn (?:' + '|'.join(float_bindings) + r')\([^\n]+ \{ [^\n]+ \}$', float_bridge, re.M,
    )
    margin_math = re.findall(r'^    fn (?:negate|with_margin)\([^\n]+ \{ [^\n]+ \}$', native, re.M)
    if len(float_impl) != len(float_bindings) or len(margin_math) != 2:
        raise ValueError('Grid Start scalar arithmetic bindings changed')
    float_traits = [binding.strip().partition(' { ')[0] + ';' for binding in float_impl]

    # Retain the source inlining attribute on aligned_axis so the compiler can
    # specialize the ignored far edge and anchor without going through its ABI.
    base = f'''
#[path = "{sources / 'placement_geometry.rs'}"] mod geometry;
#[path = "{sources / 'input_words.rs'}"] mod input_words;
mod place {{
    #[path = "{sources / 'stack_line.rs'}"] pub mod stack_line;
}}
use geometry::{{Anchor, Pos, RustFloat}};
use place::stack_line;
mod placement_node {{ pub type Edges = [[f32;2];2]; }}
use placement_node::Edges;

struct Xy<T> {{ x: T, y: T }}
impl<T> Xy<T> {{ fn new(x: T, y: T) -> Self {{ Self {{ x, y }} }} }}
type XyRect = Xy<[f32; 2]>;

#[derive(Clone, Copy)] {margin_type[0]}
{margins}
struct LayoutParams {{
    disabled: bool,
    free_placement: bool,
    position: Xy<Pos>,
    anchor: Xy<Anchor>,
    margin: Xy<[Margin;2]>,
    grid_span: Xy<u16>,
}}
mod prepare_frame {{
    use super::{{Margin, RustFloat}};
    pub trait FrameFloat {{
{chr(10).join(float_traits)}
    }}
    impl FrameFloat for RustFloat {{
{chr(10).join(float_impl)}
    }}
}}
use prepare_frame::FrameFloat;
trait StackMath: FrameFloat {{
    fn negate(value: f32) -> f32;
    fn with_margin(value: f32, margin: f32) -> f32;
}}
impl StackMath for RustFloat {{
{chr(10).join(margin_math)}
}}
#[derive(Clone, Copy)]
{frame}
{stack_style}
{grid_style}
{zero_margins}
{style}
{grid_style_read}
#[inline(always)]
{aligned_axis}
{grid_native}
{grid_packed}
'''

    # Far edges, trailing padding, line count, anchor and spans are arbitrary.
    # The checker permits only dependencies on input lanes and rejects any
    # surviving span/anchor reads, so specialisation cannot rely on their value.
    operands = '''
    let &[left, right, top, bottom, padx, far_x, pady, far_y,
        trackx, tracky, gapx, gapy, cellx, celly, width, height, nx, ny] = input;
    let frame = &Frame {
        edges: [[left, right], [top, bottom]],
        padding: [[padx, far_x], [pady, far_y]],
        flipped: [false, false],
        origin: [0.0, 0.0],
    };
    let params = LayoutParams {
        disabled: false,
        free_placement: false,
        position: Xy::new(Pos::Start, Pos::Start),
        anchor: Xy::new(anchors[0], anchors[1]),
        margin: Xy::new([Margin::ZERO; 2], [Margin::ZERO; 2]),
        grid_span: Xy::new(spans[0], spans[1]),
    };
    let GridStyle { align: style, span } = grid_style::<RustFloat>(&params);
    let size = [width, height];
    let child_cell = [cellx, celly];
    let lines = [nx, ny];
    let cell = [trackx, tracky];
    let spacing = [gapx, gapy];
'''
    for mode, expression in [
        ('ordinary', dedent(routes[2]).replace('::<M>', '::<RustFloat>')),
        ('fast', f'{dedent(context[0])}\n{routes[1]}'.replace('::<M>', '::<RustFloat>')),
    ]:
        base += f'''
#[unsafe(no_mangle)]
pub fn grid_start_{mode}(input: &[f32;18], spans: &[u16; 2], anchors: &[Anchor; 2], output: &mut [f32;4]) {{
{operands}
    let rect = {{
{expression}
    }};
    *output = [rect[0][0], rect[0][1], rect[1][0], rect[1][1]];
}}
'''
    (directory / 'recipe.rs').write_text(base)
    subprocess.run(['rustc', '--edition=2024', '--crate-type=lib', '--emit=llvm-ir',
                    '--target=x86_64-unknown-linux-gnu', '-Ctarget-cpu=x86-64', '-Copt-level=3',
                    '-Adead_code', '-Aunused_variables', 'recipe.rs', '-o', 'recipe.ll'], cwd=directory, check=True)
    return (directory / 'recipe.ll').read_text()


def main():
    with tempfile.TemporaryDirectory() as tmp:
        ir = compile_primitives(Path(tmp))
        edge_ir = compile_start_edges(Path(tmp))
        recipe_ir = compile_grid_start_recipe(Path(tmp))
    for name, intrinsic in INTRINSICS.items():
        check_lowering(ir, name, intrinsic)
    for field, result in [('tracks', 'float'), ('columns', 'i64')]:
        check_width(ir, field, result)
    if start_edges(edge_ir, 'packed') != start_edges(edge_ir, 'scalar'):
        raise ValueError('packed grid edges do not implement scalar layout order')
    print('grid Start rectangle lanes verified')
    if start_edges(recipe_ir, 'fast', 18) != start_edges(recipe_ir, 'ordinary', 18):
        raise ValueError('ordinary Grid Start placement differs from the fast lane recipe')
    print('ordinary and fast Grid Start layout recipes verified')


if __name__ == '__main__':
    main()
