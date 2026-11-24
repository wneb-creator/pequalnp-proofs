"""Regenerate the four archived CNFs exactly; never launch a solver."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def within(base, relative):
    name = Path(relative)
    if name.is_absolute() or '..' in name.parts:
        raise ValueError('Unsafe relative path')
    path = base/name
    if not path.resolve().is_relative_to(base.resolve()) or path.is_symlink():
        raise ValueError('Path escapes its root or is a symlink')
    return path


def reconstruct(output):
    package = Path(__file__).resolve().parent
    recipe = json.loads((package/'reconstruction.json').read_text())
    root = Path(recipe['scratch_root'])
    if root != Path('/tmp/oec/pequalnp-pilot-18'):
        raise ValueError('Unexpected scratch root')
    output = output.resolve()
    if output.exists() or not output.is_relative_to(root.resolve()):
        raise ValueError('Output must be a fresh directory inside the named scratch root')
    staging = []
    for row in recipe['stage_sources']:
        source = within(package,row['package_path'])
        raw = source.read_bytes()
        if digest(raw) != row['sha256']:
            raise ValueError('Archived source hash mismatch')
        destination = within(root,row['scratch_path'])
        if destination.exists():
            if not destination.is_file() or destination.read_bytes() != raw:
                raise ValueError('Existing scratch source differs; refusing to overwrite')
        else:
            staging.append((destination,raw))
    for path,raw in staging:
        path.parent.mkdir(parents=True,exist_ok=True)
        with path.open('xb') as stream:
            stream.write(raw)
    output.mkdir(parents=True,exist_ok=False)
    checks = []
    for family in recipe['families']:
        destination = within(output,family['name'])
        command = [sys.executable,'-B',str(root/'orch/S02/prepare_positive_repairs.py'),
                   str(within(root,family['source_scratch_path'])),str(destination),
                   '--budgets',*map(str,family['budgets']),
                   '--local-counts',*map(str,family['local_counts'])]
        with (output/(family['name']+'.stdout')).open('x') as stdout, (output/(family['name']+'.stderr')).open('x') as stderr:
            result = subprocess.run(command,stdout=stdout,stderr=stderr,timeout=120)
        if result.returncode:
            raise RuntimeError('Generator failed; full logs retained')
        expected = family['expected_files_sha256']
        if {p.name for p in destination.iterdir()} != set(expected):
            raise ValueError('Generated file set differs')
        for name,wanted in expected.items():
            path = within(destination,name)
            actual = digest(path.read_bytes())
            if actual != wanted:
                raise ValueError('Generated artifact hash differs')
            checks.append({'family':family['name'],'file':name,'sha256':actual})
    report = {'status':'PASS_EXACT_RECONSTRUCTION','files':checks,'solver_launched':False}
    (output/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'files':len(checks),'output':str(output)}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output',type=Path)
    reconstruct(parser.parse_args().output)
