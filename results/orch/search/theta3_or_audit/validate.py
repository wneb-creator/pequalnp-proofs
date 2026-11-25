from pathlib import Path
import gzip
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root / 'manifest.json').read_text())
for entry in manifest['files']:
    data = (root / entry['file']).read_bytes()
    assert len(data) == entry['bytes']
    assert hashlib.sha256(data).hexdigest() == entry['sha256']
    if entry.get('encoding') == 'gzip':
        original = gzip.decompress(data)
        assert len(original) == entry['original_bytes']
        assert hashlib.sha256(original).hexdigest() == entry['original_sha256']

edges = manifest['edges']


def target(mask):
    return any(mask >> a & 1 and mask >> b & 1 for a, b in edges)


for run in manifest['runs']:
    result = run['summary']
    expected_code = 10 if run['variant'] == 'or8' else 0
    assert result['solver_code'] == expected_code
    output = gzip.decompress((root / ('audit-theta3-' + run['variant'] + '.stdout.gz')).read_bytes())
    if expected_code == 10:
        assert b'\ns SATISFIABLE\n' in output
    else:
        assert b'\ns SATISFIABLE\n' not in output
        assert b'\ns UNSATISFIABLE\n' not in output
    if 'basis_rows' in result:
        positives = [(1 << a) | (1 << b) for a, b in edges]
        negatives = result['negative_rows']
        assert len(positives) + len(negatives) == result['basis_rows'] == 18
        for mask in range(256):
            assert target(mask) == any(mask & positive == positive for positive in positives)
            assert (not target(mask)) == any(mask & negative == mask for negative in negatives)

control = json.loads((root / 'audit-theta3-or8-summary.json').read_text())
gates = control['normalized_or_gates']
assert len(gates) == 9
for assignment in range(256):
    values = [bool(assignment >> i & 1) for i in range(8)]

    def conjunction(mask):
        return all(values[i] for i in range(len(values)) if mask >> i & 1)

    for j, (a, b) in enumerate(gates[:-1]):
        assert 0 < a < (1 << (8 + j)) and 0 < b < (1 << (8 + j))
        values.append(conjunction(a) or conjunction(b))
    assert 0 < gates[-1] < (1 << len(values))
    assert conjunction(gates[-1]) == target(assignment)

print('PASS: hashes, three UNKNOWN verdicts, exact boundary basis, eight-OR control on all 256 assignments')
