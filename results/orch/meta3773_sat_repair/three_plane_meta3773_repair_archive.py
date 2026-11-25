from pathlib import Path
import gzip
import hashlib
import json
import resource
import shutil

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
repo = Path('/workspace/pequalnp-proofs')
destination = repo / 'results/orch/meta3773_sat_repair'
destination.mkdir(exist_ok=True)


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


names = [
    'meta3773_five_repair_sat.py', 'meta3773_five_repair_verify_encoding.py',
    'meta3773_five_repair_verify_padding.py', 'meta3773_phase_run.py',
    'meta3773-five-patch-over-frozen21.json',
    'meta3773-five-patch-data.json', 'meta3773-five-known24.json',
    'meta3773-five-repair-padding-verification.log',
    'meta3773-five-repair-padding-production-verification.log',
    'meta3773-five-repair-known24-verification.log',
]
for prefix, numbers in [
    ('meta3773-five-repair-r', [0, 1, 990, 991]),
    ('meta3773-five-phase-r', [0, 990, 991]),
]:
    for number in numbers:
        for suffix in ['-metadata.json', '-status.json', '-source.py', '-run.log',
                       '-solver.log', '-candidate.json']:
            name = prefix + str(number) + suffix
            if (job / name).is_file():
                names.append(name)
records = []
for name in sorted(set(names)):
    source = job / name
    assert source.is_file(), source
    digest = sha(source)
    target = destination / name
    shutil.copyfile(source, target)
    assert sha(source) == sha(target) == digest
    records.append({'path': str(target.relative_to(repo)), 'sha256': digest,
        'bytes': target.stat().st_size})
for name in ['meta3773-five-repair-r0.cnf', 'meta3773-five-repair-r1.cnf',
             'meta3773-five-repair-r990.cnf', 'meta3773-five-phase-r0.cnf',
             'meta3773-five-phase-r990.cnf']:
    source = job / name
    digest = sha(source)
    target = destination / (name + '.gz')
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

readme = '''# Five-point repair and warm-phase SAT diagnostics

These are incomplete search diagnostics for L-meta-3773. No 63-gate circuit,
global refutation, or new Lean proof is claimed.

The seed has 21 local gates, preserves all 20 positive edges, and is wrong on
15 of 30 maximal negative cuts (309 of the 65,536 physical assignments).
Padding with edge AND(0,12) and a final OR produces 23 gates without changing
its physical truth table. The colex reordering was also checked exhaustively.
The local SAT searches retain all compatible outside OR-tree choices as free
variables, require all gates active and positive somewhere, and require an
AND that fires on a negative cut. Raw leaf and helper-count constraints remain.

Cold repair round 0 reports UNSAT in 25.97 seconds for at most five gate
changes relative to that normalized seed. This is only a restricted finite
neighborhood exclusion, not a global lower bound. Its exact CNF, inputs,
metadata, frozen generator and full solver output are preserved. No checked
SAT proof certificate was generated. Cold round 1 allows eight changes and
is inconclusive after 110 seconds.

The warm-phase wrapper performs only a bijective variable-polarity renaming
of that same eight-change CNF, making the default false phase correspond to
the seed selectors, operations and test values. It checks the renaming is an
involution clause by clause, binds both DIMACS hashes, undoes the polarity
changes before model decoding, checks every original clause, and verifies any
decoded circuit on all 65,536 physical assignments.

The 24-gate positive control passes every original and renamed clause, returns
SAT in 0.066 seconds, and passes full physical verification. This control has
24 local gates and is not a solution of the requested 23-gate patch. Warm
production results are recorded in their status and full solver log; absent
a zero-error 23-gate candidate file they provide no witness.

The source seed uses 0=AND,1=OR. The normalized SAT circuit uses 1=AND,0=OR.
The strict conversion, integer fanin guards, decoded mutation count, original
clause replay and exhaustive physical checks protect this interface.

All source/data/CNF inputs are hash-bound. Child solvers use only an ordinary
environment, disable core dumps and impose CPU, address-space and wall caps.
The exact original and transformed DIMACS files are compressed losslessly;
the manifest binds both compressed and uncompressed hashes and lengths.
'''
(destination / 'README.md').write_text(readme)
for source in [destination / 'README.md', Path(__file__)]:
    target = destination / source.name
    if source != target:
        shutil.copyfile(source, target)
    records.append({'path': str(target.relative_to(repo)), 'sha256': sha(target),
        'bytes': target.stat().st_size})
manifest = {'classification': 'incomplete local circuit repair diagnostics; no new proof',
    'files': sorted(records, key=lambda row: row['path']),
    'total_bytes': sum(row['bytes'] for row in records)}
(job / 'three-plane-meta3773-repair-archive-manifest.json').write_text(
    json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'files': len(records), 'bytes': manifest['total_bytes']}))
