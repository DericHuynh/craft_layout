"""Check the Rust binary32 word conversions against their native bitcasts."""

from argparse import ArgumentParser
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory


SOURCE = Path(__file__).resolve().parents[1] / "src" / "prepare_frame.rs"
VALUE = r"%[\w.]+"


def extracted_source():
    source = SOURCE.read_text().split("impl FrameFloat for RustFloat {", 1)[1]
    methods = []
    for name in ("bits", "from_word"):
        method = re.search(rf"^    fn {name}\([^\n]*\) -> [^\n]*\{{[^\n]*\}}$", source, re.M)
        if method is None:
            raise ValueError(f"cannot read RustFloat::{name} from {SOURCE}")
        methods.append("#[inline(always)]\n" + method[0])
    return """
struct RustFloat;
trait FrameFloat {
    fn bits(value: f32) -> u32;
    fn from_word(word: u32) -> f32;
}
impl FrameFloat for RustFloat {
""" + "\n".join(methods) + """
}
#[unsafe(no_mangle)]
pub fn layout_float_bits(value: f32) -> u32 { RustFloat::bits(value) }
#[unsafe(no_mangle)]
pub fn layout_float_from_word(word: u32) -> f32 { RustFloat::from_word(word) }
#[unsafe(no_mangle)]
pub fn layout_float_roundtrip(value: f32) -> f32 { RustFloat::from_word(RustFloat::bits(value)) }
#[unsafe(no_mangle)]
pub fn layout_word_roundtrip(word: u32) -> u32 { RustFloat::bits(RustFloat::from_word(word)) }
"""


def compile_ir(directory, target):
    path = directory / "native.rs"
    output = directory / "native.ll"
    path.write_text(extracted_source())
    command = ["rustc", "--edition=2024", "--crate-type=lib", "--emit=llvm-ir",
               "-Copt-level=3", "-Coverflow-checks=on", "-Cpanic=unwind"]
    if target is not None:
        command.extend(["--target", target])
    subprocess.run(command + [str(path), "-o", str(output)], check=True)
    return output.read_text()


def check_lowering(ir, name, input_type, output_type):
    # The i686 Rust ABI may use a four-byte vector for the return register.
    output_pattern = r"(float|<4 x i8>)" if output_type == "float" else r"(i32)"
    function = re.search(
        rf"^define [^\n]*?{output_pattern} @{name}\({input_type} [^\n]*?({VALUE})\)"
        r"[^\n]* #(\d+)[^\n]*\{\n(.*?)^\}", ir, re.M | re.S)
    if function is None:
        raise ValueError(f"missing LLVM definition for {name}")
    returned, argument, attrs, body = function.groups()
    attributes = re.search(rf"^attributes #{attrs} = \{{([^\n]*)\}}", ir, re.M)
    if attributes is None or not all(token in attributes[1] for token in ("nounwind", "memory(none)")):
        raise ValueError(f"{name} can unwind or access memory")
    if input_type == returned:
        expected = rf"start:\s+ret {returned} {re.escape(argument)}"
    else:
        expected = (rf"start:\s+({VALUE}) = bitcast {input_type} {re.escape(argument)} to {returned}"
                    rf"\s+ret {returned} \1")
    if re.fullmatch(expected, body.strip()) is None:
        raise ValueError(f"{name} did not preserve every bit of its input:\n{body}")


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--target")
    args = parser.parse_args()
    with TemporaryDirectory() as directory:
        ir = compile_ir(Path(directory), args.target)
    for name, source, target in [
        ("layout_float_bits", "float", "i32"),
        ("layout_float_from_word", "i32", "float"),
        ("layout_float_roundtrip", "float", "float"),
        ("layout_word_roundtrip", "i32", "i32"),
    ]:
        check_lowering(ir, name, source, target)
    print(f"Native binary32 conversions and both roundtrips verified for {args.target or 'host'}")


if __name__ == "__main__":
    main()
