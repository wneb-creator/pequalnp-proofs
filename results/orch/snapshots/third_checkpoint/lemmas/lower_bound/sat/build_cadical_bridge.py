import argparse
import subprocess
from pathlib import Path


parser = argparse.ArgumentParser()
parser.add_argument('--toolchain', type=Path, default=Path(
    '/tmp/oec/pequalnp-pilot-57/elan/toolchains/leanprover--lean4---v4.36.0'))
parser.add_argument('--output', type=Path,
                    default=Path('/tmp/oec/pequalnp-pilot-57/libcadical.so'))
args = parser.parse_args()
lib = args.toolchain / 'lib'
command = ['c++', '-shared', '-fPIC', str(Path(__file__).with_name('cadical_wrapper.cpp')),
           str(lib / 'lean/libcadical.a'), str(lib / 'libc++.so.1.0'),
           str(lib / 'libc++abi.so.1.0'), str(lib / 'libunwind.so.1.0'),
           '-Wl,-rpath,' + str(lib), '-o', str(args.output)]
with args.output.with_suffix('.build.log').open('w') as log:
    result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
raise SystemExit(result.returncode)
