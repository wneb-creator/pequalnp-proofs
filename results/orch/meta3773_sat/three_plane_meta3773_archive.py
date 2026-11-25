from pathlib import Path
import gzip
import hashlib
import json
import resource
import shutil

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
repo = Path('/workspace/pequalnp-proofs')
destination = repo / 'results/orch/meta3773_sat'
destination.mkdir(exist_ok=True)


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


names = [
    'meta3773_whole_sat.py', 'meta3773_core_sat.py',
    'meta3773_core_sat_validation60.py',
    'meta3773_core_verify_encoding.py',
    'meta3773_core_verify_encoding_typed.py',
    'meta3773_verify_encoding.py', 'meta3773_verify_colex.py',
    'meta3773_five_sat.py', 'meta3773_five_verify_encoding.py',
    'meta3773_pack_seed.py', 'meta3773_pencil_overapprox.py',
    'meta3773-synthesis-data.json', 'geometry-meta3773-core-data.json',
    'geometry-core-search7901-best.json',
    'geometry-core-search7902-best.json',
    'meta3773-five-patch-data.json',
    'meta3773-core-validation60-seed.json',
    'meta3773-core-validation60-seed-typed.json',
    'meta3773-known64-circuit.json', 'meta3773-known64-colex.json',
    'meta3773-five-known24.json', 'meta3773-dense63-seed.json',
    'meta3773-bad63-frozen-seed.json',
    'meta3773-bad63-frozen-diagnostics.json',
    'meta3773-bad63-negative-care.json',
    'meta3773-essential63-frozen-raw.json',
    'meta3773-essential63-frozen-seed.json',
    'meta3773-essential63-frozen-diagnostics.json',
    'meta3773-essential63-negative-care.json',
    'meta3773-pencil61-p9-overapprox.json',
    'meta3773-pencil60-union-overapprox.json',
    'meta3773-pencil56-core-overapprox.json',
    'meta3773-pencil56-union-core-overapprox.json',
    'meta3773-pencil-overapprox.log', 'meta3773-pencil-union-overapprox.log',
    'meta3773-whole-encoding-verification.log',
    'meta3773-whole-colex-verification.log',
    'meta3773-core-encoding-verification.log',
    'meta3773-core-encoding-verification-complete.log',
    'meta3773-core-encoding-verification-typed.log',
    'meta3773-five-encoding-verification.log',
    'meta3773-five-encoding-canonical-verification.log',
    'meta3773-five-encoding-folded-verification.log',
    'meta3773-cadical-help.txt',
]

for prefix, rounds in [
    ('meta3773-whole-1-r', list(range(9)) + [990, 992]),
    ('meta3773-core-sat-r', [0, 1, 2, 980, 990, 991]),
    ('meta3773-five-sat-r', list(range(4)) + [990, 991, 992]),
]:
    for number in rounds:
        for suffix in [
            '-metadata.json', '-status.json', '-run.log', '-solver.log',
            '-candidate.json', '-source.py',
        ]:
            candidate = prefix + str(number) + suffix
            if (job / candidate).is_file():
                names.append(candidate)

compressed = [
    'meta3773-core-sat-r1.cnf',
    'meta3773-whole-1-r4.cnf', 'meta3773-whole-1-r6.cnf',
    'meta3773-five-sat-r0.cnf', 'meta3773-five-sat-r1.cnf',
    'meta3773-five-sat-r2.cnf', 'meta3773-five-sat-r3.cnf',
    'meta3773-five-sat-r992.cnf',
]

records = []
missing = []
for name in sorted(set(names)):
    source = job / name
    if not source.is_file():
        missing.append(name)
        continue
    original_sha = sha(source)
    target = destination / name
    shutil.copyfile(source, target)
    assert sha(source) == sha(target) == original_sha
    records.append({'path': str(target.relative_to(repo)),
        'sha256': original_sha, 'bytes': target.stat().st_size})

for name in compressed:
    source = job / name
    assert source.is_file(), source
    original_sha = sha(source)
    target = destination / (name + '.gz')
    with source.open('rb') as stream, target.open('wb') as raw:
        with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0,
                          compresslevel=6) as zipped:
            shutil.copyfileobj(stream, zipped, 1024 * 1024)
    assert sha(source) == original_sha
    with gzip.open(target, 'rb') as stream:
        digest = hashlib.sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    assert digest.hexdigest() == original_sha
    records.append({'path': str(target.relative_to(repo)),
        'sha256': sha(target), 'bytes': target.stat().st_size,
        'uncompressed_sha256': original_sha,
        'uncompressed_bytes': source.stat().st_size})

readme = '''# L-meta-3773 circuit search diagnostics

No 63-gate witness was found by these runs. No global lower bound or refutation
is claimed. There is no new Lean proof in this directory.

The whole-circuit encoding uses two one-hot fanin selectors per binary gate.
The five-point encoding additionally selects compatible outside OR trees.
All successful SAT candidates are independently evaluated against the full
finite test family; a five-point candidate is additionally evaluated on all
65,536 physical assignments. The two whole-circuit curriculum models are
invalid: they fail hundreds of negative tests and are preserved only as
search diagnostics.

The core round 1 solver reports UNSAT for at most two gate changes from the
specified frozen 58-gate seed, with all three output choices free and 109
selected constraints. This excludes only that finite repair neighborhood.
The exact CNF, metadata, seed, data and full solver output are preserved.
No independently checked SAT proof or Lean certificate was produced.
Core rounds 0 and 2 are inconclusive. Core round 980 is a zero-change UNSAT
smoke test, not an additional circuit lower bound. The bounded whole and
five-point searches are inconclusive unless their status file explicitly
records a successful (possibly invalid curriculum) candidate.

Known controls verify every clause of the whole 64-gate, core 60-gate, and
five-point 24-gate encodings. The original core control failed because its
string operation labels were passed to an integer-label interface; that
failed log is retained. The typed control fixes the interface and passes.
Later production code explicitly checks the integer-label schema.

The pencil circuits are all-positive overapproximations with false positives;
they are not witnesses. Both frozen global 63-gate near-candidates miss three
positive edges. Their bad AND gates admit absorption or double-star consensus
rewrites, so neither indicates a genuine saving over the 64-gate star cover.

Operation conventions are explicit in generators/metadata: whole SAT uses
strings; core/five SAT and pencil generators use 1=AND,0=OR; raw stochastic
global seeds use 0=AND,1=OR. Do not mix these conventions.

The scripts expect their data under /tmp/oec/pequalnp-pilot-79 and use the
bundled Lean-toolchain CaDiCaL. Each solver run is bounded by CPU, address-space
and wall limits, with an ordinary child environment and core dumps disabled.
Full stdout/stderr logs are retained. Current scripts may contain later
reviewed improvements; exact selected historical CNFs are therefore frozen
with compressed and uncompressed SHA-256 hashes. Exact source snapshots exist
for five-point rounds 2, 3 and control 992. Older inconclusive whole/core runs
are preserved as diagnostics, not claimed byte-for-byte source reconstructions.
'''
(destination / 'README.md').write_text(readme)
records.append({'path': str((destination / 'README.md').relative_to(repo)),
    'sha256': sha(destination / 'README.md'),
    'bytes': (destination / 'README.md').stat().st_size})
source = Path(__file__)
shutil.copyfile(source, destination / source.name)
records.append({'path': str((destination / source.name).relative_to(repo)),
    'sha256': sha(destination / source.name),
    'bytes': (destination / source.name).stat().st_size})
manifest = {'classification': 'incomplete circuit-search diagnostics; no new proof',
    'files': sorted(records, key=lambda row: row['path']),
    'missing_optional_files': missing,
    'total_bytes': sum(row['bytes'] for row in records)}
(job / 'three-plane-meta3773-archive-manifest.json').write_text(
    json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'files': len(records), 'bytes': manifest['total_bytes'],
    'missing_optional_files': missing}))
