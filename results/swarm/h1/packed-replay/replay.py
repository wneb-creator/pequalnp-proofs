#!/usr/bin/env python3
"""Rebuild published helper-1 chunks against the separately built pinned checker."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--build', type=Path, required=True)
    parser.add_argument('--lean', required=True)
    parser.add_argument('--memory', type=int, default=7000)
    parser.add_argument('--modules', nargs='+')
    parser.add_argument('--verify-only', action='store_true',
                        help='check toolchain and source pins without writing or building')
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    repo = args.repo.resolve() / 'lean'
    build = args.build.resolve()
    if build == source or source in build.parents or build in source.parents:
        parser.error('build must be a separate scratch directory')
    if not (build / 'PackedDirect.olean').is_file():
        parser.error('build the pinned packed checker in --build first')
    lean = shutil.which(args.lean)
    if lean is None:
        parser.error('Lean executable not found')
    lean = os.path.abspath(lean)
    if not 1000 <= args.memory <= 7000:
        parser.error('memory must be between 1000 and 7000 MB')
    manifest = json.loads((source / 'manifest.json').read_text())
    if manifest['snapshot'] != '36375ce3bb56c227c81ecae98f6641800006b8c2':
        parser.error('unexpected checker snapshot')
    lean_env = {'PATH': str(Path(lean).parent),
                'ELAN_TOOLCHAIN': (repo / 'lean-toolchain').read_text().strip()}
    for key in ('HOME', 'ELAN_HOME'):
        if key in os.environ:
            lean_env[key] = os.environ[key]
    version = subprocess.run([lean, '--version'], env=lean_env, capture_output=True, text=True)
    if version.returncode or not re.search(r'\bversion 4\.36\.0(?:,|\s|\))', version.stdout):
        parser.error('use the pinned Lean 4.36.0 executable')
    pins = manifest['dependency_pins']
    for name, expected in pins['checker_sources'].items():
        if Path(name).name != name or not name.endswith('.lean'):
            parser.error('invalid checker source pin')
        path = build / name
        if not path.is_file() or sha256(path) != expected:
            parser.error('pinned checker source mismatch: ' + name)
    for name, expected in pins['repo_sources'].items():
        relative = Path(name)
        if relative.is_absolute() or '..' in relative.parts:
            parser.error('invalid repository source pin')
        path = args.repo.resolve() / relative
        if not path.is_file() or sha256(path) != expected:
            parser.error('pinned repository source mismatch: ' + name)
    records = {r['module']: r for r in manifest['batches']}
    modules = args.modules or list(records)
    if len(modules) != len(set(modules)) or any(m not in records for m in modules):
        parser.error('select distinct published chunk module names')
    files = ['PackedChunkTools.lean'] + [m + '.lean' for m in modules]
    for name in files:
        expected = (manifest['range_wrapper']['source_sha256'] if name == files[0]
                    else records[name[:-5]]['source_sha256'])
        if sha256(source / name) != expected:
            parser.error('source hash mismatch: ' + name)
    if args.verify_only:
        print(json.dumps({'source_pins_verified': True, 'chunk_modules': len(modules),
                          'lean_version': version.stdout.strip()}))
        return 0
    for name in files:
        shutil.copyfile(source / name, build / name)
    paths = [build, repo / '.lake/build/lib/lean']
    paths.extend(sorted(p / '.lake/build/lib/lean'
                        for p in (repo / '.lake/packages').iterdir()
                        if (p / '.lake/build/lib/lean').is_dir()))
    env = dict(lean_env, LEAN_PATH=':'.join(map(str, paths)))
    namespace = 'PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper1Chunks.'
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    receipts = []
    for module in ['PackedChunkTools'] + modules:
        started = time.monotonic()
        stdout = build / (module + '.replay.stdout')
        stderr = build / (module + '.replay.stderr')
        output = build / (module + '.olean')
        with stdout.open('w') as out, stderr.open('w') as err:
            result = subprocess.run(
                [lean, '-j', '1', '-M', str(args.memory), '-o', str(output),
                 str(build / (module + '.lean'))],
                cwd=build, env=env, stdout=out, stderr=err)
        text = stdout.read_text() + stderr.read_text()
        names = (['range_all_sound'] if module == 'PackedChunkTools' else
                 ['raw_' + module[9:], 'checked_' + module[9:]])
        axioms = {}
        for name in names:
            full = namespace + name
            if "'" + full + "' does not depend on any axioms" in text:
                axioms[full] = []
            else:
                match = re.search(re.escape("'" + full + "'") +
                                  r' depends on axioms:\s*\[([^\]]*)\]', text)
                axioms[full] = ([x.strip() for x in match.group(1).split(',')
                                 if x.strip()] if match else None)
        accepted = (result.returncode == 0 and output.is_file() and
                    all(a is not None and set(a) <= allowed for a in axioms.values()))
        receipt = {'module': module, 'exit_code': result.returncode,
                   'accepted': accepted, 'elapsed_seconds': time.monotonic() - started,
                   'axioms': axioms, 'source_sha256': sha256(build / (module + '.lean')),
                   'stdout_sha256': sha256(stdout), 'stderr_sha256': sha256(stderr),
                   'olean_sha256': sha256(output) if output.is_file() else None}
        receipts.append(receipt)
        (build / 'helper1-replay-receipts.json').write_text(
            json.dumps({'snapshot': manifest['snapshot'], 'lean_version': version.stdout.strip(),
                        'memory_limit_mb': args.memory, 'receipts': receipts}, indent=2) + '\n')
        print(json.dumps({'module': module, 'accepted': accepted,
                          'seconds': receipt['elapsed_seconds']}), flush=True)
        if not accepted:
            return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
