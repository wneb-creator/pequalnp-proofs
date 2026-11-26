#!/usr/bin/env python3
"""Build the modular research checker using already installed Lean libraries."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--lean', default='lean')
parser.add_argument('--memory', type=int, default=11000)
parser.add_argument('--modules', nargs='+', default=['Checker', 'Half', 'Initial', 'Coordinates', 'PreparedLinks', 'SameSet', 'Replay', 'CheckNode', 'BlockReplay', 'DirectDecode', 'DirectReplay'])
args = parser.parse_args()
source = Path(__file__).resolve().parent
repo = args.repo.resolve() / 'lean'
out = args.output.resolve()
if out == source or source in out.parents:
    parser.error('output must be a separate scratch directory')
if not (repo / '.lake/build/lib/lean/PEqualNP/Outside/L_meta_6581.olean').is_file():
    parser.error('build the existing L_meta_6581 dependency with Lake first')
lean = shutil.which(args.lean)
if lean is None:
    parser.error('Lean executable was not found')
lean = os.path.abspath(lean)
modules = args.modules
for module in modules:
    if not module.isidentifier() or not (source / (module + '.lean')).is_file():
        parser.error('unknown source module: ' + module)
out.mkdir(parents=True, exist_ok=True)
for path in source.glob('*.lean'):
    shutil.copyfile(path, out / path.name)
paths = [out, repo / '.lake/build/lib/lean']
paths.extend(sorted(p / '.lake/build/lib/lean' for p in (repo / '.lake/packages').iterdir() if (p / '.lake/build/lib/lean').is_dir()))
os.environ['LEAN_PATH'] = ':'.join(str(p) for p in paths)
os.environ['ELAN_TOOLCHAIN'] = (repo / 'lean-toolchain').read_text().strip()
for module in modules:
    start = time.monotonic()
    with (out / (module + '.stdout')).open('w') as stdout, (out / (module + '.stderr')).open('w') as stderr:
        result = subprocess.run([lean, '-M', str(args.memory), '-o', str(out / (module + '.olean')), str(out / (module + '.lean'))], cwd=out, stdout=stdout, stderr=stderr)
    print(f'{module}: exit={result.returncode}, seconds={time.monotonic()-start:.2f}', flush=True)
    if result.returncode:
        raise SystemExit(result.returncode)
