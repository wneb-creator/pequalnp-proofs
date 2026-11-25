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

four = json.loads((root / 'audit-cycle6-or4-summary.json').read_text())
five = json.loads((root / 'audit-cycle6-or5-summary.json').read_text())
assert four['solver_code'] == 20 and five['solver_code'] == 10
assert b'\ns UNSATISFIABLE\n' in gzip.decompress((root / 'audit-cycle6-or4.stdout.gz').read_bytes())
assert b'\ns SATISFIABLE\n' in gzip.decompress((root / 'audit-cycle6-or5.stdout.gz').read_bytes())
gates = five['normalized_or_gates']
assert len(gates) == 6
for assignment in range(64):
    values = [bool(assignment >> i & 1) for i in range(6)]

    def conjunction(mask):
        return all(values[i] for i in range(len(values)) if mask >> i & 1)

    for j, (a, b) in enumerate(gates[:-1]):
        assert 0 < a < (1 << (6 + j)) and 0 < b < (1 << (6 + j))
        values.append(conjunction(a) or conjunction(b))
    assert 0 < gates[-1] < (1 << len(values))
    expected = any(assignment >> i & 1 and assignment >> ((i + 1) % 6) & 1
                   for i in range(6))
    assert conjunction(gates[-1]) == expected

print('PASS: artifact hashes, complete solver verdicts, five-OR witness on all 64 assignments')
