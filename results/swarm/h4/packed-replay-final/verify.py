"""Verify the immutable artifact hashes and exact accepted interval metadata."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent
seen = set()
for line in (root / 'SHA256SUMS').read_text().splitlines():
    expected, name = line.split('  ', 1)
    path = root / name
    assert name not in seen and name not in {'SHA256SUMS', 'validation.txt'}
    assert path.resolve().is_relative_to(root) and not path.is_symlink()
    assert path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == expected, name
    seen.add(name)
manifest = json.loads((root / 'manifest.json').read_text())
ranges = json.loads((root / 'receipts/accepted-ranges.json').read_text())['ranges']
assert ranges[0]['first'] == manifest['first']
assert ranges[-1]['last'] == manifest['last']
assert sum(x['count'] for x in ranges) == manifest['accepted_node_count']
for previous, current in zip(ranges, ranges[1:]):
    assert previous['last'] + 1 == current['first']
for item in ranges:
    assert item['count'] == item['last'] - item['first'] + 1
    assert 0 <= item['first'] <= item['last'] < manifest['forest_node_count']
    assert item['compiler_resources']['exit'] == item['audit_resources']['exit'] == 0
    assert item['source_sha256'] == manifest['source_sha256'][item['module']]
    assert set(item['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
for module, expected in manifest['source_sha256'].items():
    source = root / 'sources' / (module + '.lean')
    assert hashlib.sha256(source.read_bytes()).hexdigest() == expected
assert set(manifest['build_order']) == set(manifest['source_sha256'])
print(f"Verified {len(seen)} immutable files; nodes {manifest['first']}..{manifest['last']} inclusive ({manifest['accepted_node_count']} nodes).")
