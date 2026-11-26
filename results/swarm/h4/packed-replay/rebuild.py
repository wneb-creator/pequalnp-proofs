"""Rebuild the frozen H4 range proofs against an already-built packed checker."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--basis', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--lean', default='lean')
p.add_argument('--memory', type=int, default=6000)
p.add_argument('--modules', nargs='+')
p.add_argument('--check-only', action='store_true')
a = p.parse_args()
root = Path(__file__).resolve().parent
repo = a.repo.resolve()
basis = a.basis.resolve()
out = a.output.resolve()
manifest = json.loads((root / 'manifest.json').read_text())
imports = json.loads((root / 'checker-import-hashes.json').read_text())

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for module, expected in imports['modules'].items():
    if not module.isidentifier():
        p.error('invalid checker module name')
    source = basis / (module + '.lean')
    if not source.is_file() or digest(source) != expected:
        p.error('checker source hash mismatch: ' + module)
    if not (basis / (module + '.olean')).is_file():
        p.error('checker module is not built: ' + module)
for name, expected in imports['repository_files'].items():
    path = (repo / name).resolve()
    if not path.is_relative_to(repo) or not path.is_file() or digest(path) != expected:
        p.error('repository source hash mismatch: ' + name)
for module, expected in manifest['source_sha256'].items():
    if not module.isidentifier():
        p.error('invalid proof module name')
    if digest(root / 'sources' / (module + '.lean')) != expected:
        p.error('proof source hash mismatch: ' + module)
modules = a.modules or manifest['build_order']
if any(m not in manifest['source_sha256'] for m in modules):
    p.error('requested module is outside the frozen manifest')
if out == root or root in out.parents:
    p.error('output must be outside the frozen artifact directory')
lean = shutil.which(a.lean)
if lean is None:
    p.error('Lean executable not found')
if a.check_only:
    print('Frozen checker and proof source hashes verified.')
    raise SystemExit(0)
out.mkdir(parents=True, exist_ok=True)
for module in manifest['build_order']:
    shutil.copyfile(root / 'sources' / (module + '.lean'), out / (module + '.lean'))
project = repo / 'lean'
paths = [out, basis, project / '.lake/build/lib/lean']
paths.extend(sorted(q / '.lake/build/lib/lean' for q in (project / '.lake/packages').iterdir()
    if (q / '.lake/build/lib/lean').is_dir()))
os.environ['LEAN_PATH'] = ':'.join(map(str, paths))
os.environ['ELAN_TOOLCHAIN'] = (project / 'lean-toolchain').read_text().strip()
for module in modules:
    result = subprocess.run([sys.executable, str(root / 'measure.py'), '--label', module,
        '--directory', str(out), '--cwd', str(out), '--', os.path.abspath(lean),
        '-M', str(a.memory), '-o', module + '.olean', module + '.lean'])
    if result.returncode:
        raise SystemExit(result.returncode)
