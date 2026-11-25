from pathlib import Path
import gzip
import hashlib
import json
import resource
import shutil

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
repo = Path('/workspace/pequalnp-proofs')
destination = repo / 'results/orch/meta3773_sat_six'
destination.mkdir(exist_ok=True)


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


names = [
    'meta3773_six_sat.py', 'meta3773_six_verify_encoding.py',
    'meta3773_six_verify_physical.py', 'meta3773-six-patch-data.json',
    'meta3773-six-known29.json', 'meta3773-six-known29-verification.log',
    'meta3773-six-known29-physical-verification.log',
]
for number in [0, 990]:
    for suffix in ['-metadata.json', '-status.json', '-run.log', '-solver.log',
                   '-source.py', '-candidate.json']:
        name = 'meta3773-six-sat-r' + str(number) + suffix
        if (job / name).is_file():
            names.append(name)
records = []
for name in names:
    source = job / name
    digest = sha(source)
    target = destination / name
    shutil.copyfile(source, target)
    assert sha(source) == sha(target) == digest
    records.append({'path': str(target.relative_to(repo)), 'sha256': digest,
        'bytes': target.stat().st_size})
source = job / 'meta3773-six-sat-r0.cnf'
digest = sha(source)
target = destination / (source.name + '.gz')
with source.open('rb') as stream, target.open('wb') as raw:
    with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0,
                      compresslevel=6) as zipped:
        shutil.copyfileobj(stream, zipped, 1024 * 1024)
assert sha(source) == digest
with gzip.open(target, 'rb') as stream:
    expanded = hashlib.sha256()
    for block in iter(lambda: stream.read(1024 * 1024), b''):
        expanded.update(block)
assert expanded.hexdigest() == digest
records.append({'path': str(target.relative_to(repo)), 'sha256': sha(target),
    'bytes': target.stat().st_size, 'uncompressed_sha256': digest,
    'uncompressed_bytes': source.stat().st_size})
readme = '''# Six-point SAT diagnostics

This is a parameter adaptation of the independently reviewed five-point SAT
encoder. It uses 19 raw inputs, 21 compatible outside OR signals, 28 local
gates and all 83 extremal rows (24 positives and 59 maximal negatives).
Each of seven outside groups has 15 tree variants. The production query fixes
exactly seven AND gates and requires all gates active and positive somewhere,
with an AND that fires on a negative cut. It is a restricted diagnostic query.
No global lower bound or new Lean proof is claimed.

The ordinary six-star positive control has 29 local gates. Its complete
408,893-clause encoding was checked under the explicit assignment, and its
physical function was independently verified on all 524,288 inputs. The
control is not a solution of the requested 28-gate patch.

Any production SAT candidate must pass the independent exhaustive physical
replay and then be assembled and checked on the original 26-input instance,
including the prescribed first gate. A status without a verified 28-gate
candidate is not a witness. Full source, model data, metadata, status and
solver logs are preserved; the exact production CNF is losslessly compressed.
'''
(destination / 'README.md').write_text(readme)
for source in [destination / 'README.md', Path(__file__)]:
    target = destination / source.name
    if source != target:
        shutil.copyfile(source, target)
    records.append({'path': str(target.relative_to(repo)), 'sha256': sha(target),
        'bytes': target.stat().st_size})
manifest = {'classification': 'incomplete six-point circuit search; no new proof',
    'files': sorted(records, key=lambda row: row['path']),
    'total_bytes': sum(row['bytes'] for row in records)}
(job / 'three-plane-meta3773-six-archive-manifest.json').write_text(
    json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'files': len(records), 'bytes': manifest['total_bytes']}))
