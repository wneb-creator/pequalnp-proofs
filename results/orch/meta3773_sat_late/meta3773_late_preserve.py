from pathlib import Path
import hashlib
import json
import resource
import shutil

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
repo = Path('/workspace/pequalnp-proofs')
destination = repo / 'results/orch/meta3773_sat_late'
destination.mkdir(exist_ok=True)


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            digest.update(block)
    return digest.hexdigest()


raw_path = job / 'meta3773-late63-frozen-raw.json'
seed_path = job / 'meta3773-late63-frozen-seed.json'
data_path = job / 'meta3773-synthesis-data.json'
bound = {str(path): sha(path) for path in [raw_path, seed_path, data_path]}
raw = json.loads(raw_path.read_text())
seed = json.loads(seed_path.read_text())
data = json.loads(data_path.read_text())
assert len(raw['gates']) == len(seed) == 63 and seed[0] == ['or', 0, 1]
assert raw.get('output', 88) == 88
for index, ((operation, a, b), encoded) in enumerate(zip(raw['gates'], seed)):
    assert type(operation) is int and operation in [0, 1]
    assert type(a) is int and type(b) is int and 0 <= a < 26 + index and 0 <= b < 26 + index
    assert a != b
    assert encoded == ['and' if operation == 0 else 'or', *sorted([a, b])]
expected = {(1 << a) | (1 << (13 + b)) for a, b in data['edges']}
expected.update([(1 << 0) | (1 << 15), (1 << 12) | (1 << 22)])
terms = [{1 << i} for i in range(26)]
for operation, a, b in seed:
    combined = terms[a] | terms[b] if operation == 'or' else {x | y for x in terms[a] for y in terms[b]}
    minimal = []
    for term in sorted(combined, key=lambda x: (x.bit_count(), x)):
        if not any(other & term == other for other in minimal):
            minimal.append(term)
    terms.append(set(minimal))
assert terms[-1] == expected and len(expected) == 54
errors = []
rows = data['positive'] + data['negative_full']
assert len(rows) == 808
for index, sample in enumerate(rows):
    wires = [bool(sample >> i & 1) for i in range(26)]
    for operation, a, b in seed:
        wires.append(wires[a] and wires[b] if operation == 'and' else wires[a] or wires[b])
    if wires[-1] != (index < 52):
        errors.append(index)
assert all(index >= 52 for index in errors) and len(errors) == 148
metadata_path = job / 'meta3773-whole-1-r9-metadata.json'
metadata = json.loads(metadata_path.read_text())
assert metadata['data_sha256'] == bound[str(data_path)] and metadata['seed'] == seed
assert metadata['max_deviations'] == 6
assert set(map(tuple, metadata['tests'])) == (
    {(x, True) for x in data['positive']} | {(x, False) for x in data['negative_full']})
cnf_path = job / 'meta3773-whole-1-r9.cnf'
assert sha(cnf_path) == metadata['cnf_sha256']
assert sha(job / 'meta3773_whole_sat.py') == sha(job / 'meta3773-late63-whole-encoder-source.py')
assert all(sha(Path(path)) == digest for path, digest in bound.items())
result = {'frozen_input_bindings': bound, 'verified_posted_rows': 808,
    'false_negatives': 0, 'false_positives': 148, 'exact_quadratic_minterms': 54,
    'extra_edges': [[0, 2], [12, 9]], 'posted_head_verified': True,
    'cnf_sha256': metadata['cnf_sha256'], 'cnf_bytes': cnf_path.stat().st_size,
    'cnf_preservation': 'deterministic source/data regeneration; not duplicated',
    'status': json.loads((job / 'meta3773-whole-1-r9-status.json').read_text())}
(job / 'meta3773-late63-independent-preservation-verification.json').write_text(
    json.dumps(result, indent=2) + '\n')
names = ['meta3773-late63-frozen-raw.json', 'meta3773-late63-frozen-seed.json',
    'meta3773-late63-frozen-verification.json', 'meta3773-late63-freeze-verification.log',
    'meta3773-late63-whole-encoder-source.py', 'meta3773-synthesis-data.json',
    'meta3773-late63-independent-preservation-verification.json',
    'meta3773-whole-1-r9-metadata.json', 'meta3773-whole-1-r9-status.json',
    'meta3773-whole-1-r9-run.log', 'meta3773-whole-1-r9-solver.log']
records = []
for name in names:
    source = job / name
    digest = sha(source)
    target = destination / name
    shutil.copyfile(source, target)
    assert sha(source) == sha(target) == digest
    records.append({'path': str(target.relative_to(repo)), 'sha256': digest,
        'bytes': target.stat().st_size})
readme = '''# Late full-instance repair diagnostic

The frozen 63-gate seed is not a witness. It computes exactly the desired
52 quadratic edges plus two unwanted edges (point0,line2) and(point12,line9).
Independent antichain propagation verifies that there are no higher minterms.
Its prescribed first gate is OR(0,1). It accepts all52 positives and wrongly
accepts148 of the756 listed negative tests.

The reviewed whole-instance SAT encoder searched at most six gate changes,
with all756 distinct constraints (all808 posted rows modulo duplicate negatives)
and the posted first gate. The80-second query returned unknown after80.72s.
No repaired circuit, global lower bound, or new Lean proof is claimed.

The frozen source, exact inputs, metadata, complete stdout/stderr and original
DIMACS hash/length are retained. The183,866,483-byte DIMACS is not duplicated
because it regenerates deterministically from the preserved source/data:

    python /tmp/oec/pequalnp-pilot-79/meta3773-late63-whole-encoder-source.py --first 1 --round 9 --seconds 80 --all-tests --near-seed /tmp/oec/pequalnp-pilot-79/meta3773-late63-frozen-seed.json --changes 6 --false-phase --sat-profile --generate-only

Restore the files under the named job directory before running that command.
The preservation verifier also rechecks the seed, every posted row, exact
quadratic minterms, metadata test completeness, immutable source and CNF hash.
'''
(destination / 'README.md').write_text(readme)
for source in [destination / 'README.md', Path(__file__)]:
    target = destination / source.name
    if source != target:
        shutil.copyfile(source, target)
    records.append({'path': str(target.relative_to(repo)), 'sha256': sha(target),
        'bytes': target.stat().st_size})
manifest = {'classification': 'incomplete late full-instance repair; no witness',
    'files': sorted(records, key=lambda row: row['path']),
    'total_bytes': sum(row['bytes'] for row in records)}
(job / 'three-plane-meta3773-late-archive-manifest.json').write_text(
    json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'files': len(records), 'bytes': manifest['total_bytes'],
    'seed_verified': True, 'full_row_set_verified': True, 'status': result['status']}))
