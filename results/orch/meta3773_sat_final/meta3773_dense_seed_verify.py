from pathlib import Path
import hashlib
import json
import resource

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
paths = [job / 'meta3773-six-dense-patch-data.json',
    job / 'meta3773-six-dense-matched-over-seed.json']
bindings = {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}
data, seed = [json.loads(path.read_text()) for path in paths]
width = 1 << 17
ones = (1 << width) - 1
raw = []
for i in range(17):
    block = 1 << i
    raw.append((ones // ((1 << (2 * block)) - 1)) * ((1 << block) - 1) << block)
words = raw.copy()
for a, b in seed['free_ors']:
    words.append(words[a] | words[b])
for operation, a, b in seed['gates']:
    assert type(operation) is int and operation in [0, 1]
    words.append(words[a] & words[b] if operation == 0 else words[a] | words[b])
actual = words[seed['output']]
target = 0
for a, b in data['edges']:
    target |= raw[a] & raw[b]
assert target & ~actual == 0
true_pairs = [(a, b) for a in range(17) for b in range(a + 1, 17)
    if actual >> ((1 << a) | (1 << b)) & 1]
quadratic = 0
for a, b in true_pairs:
    quadratic |= raw[a] & raw[b]
assert actual == quadratic
extra = [list(pair) for pair in true_pairs if list(pair) not in data['edges']]
assert len(extra) == 6 and len(true_pairs) == 30
assert all(hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest
    for path, digest in bindings.items())
print(json.dumps({'physical_inputs_verified': width, 'raw_seed_gates': len(seed['gates']),
    'false_negative_inputs': 0, 'false_positive_inputs': (actual & ~target).bit_count(),
    'exactly_30_quadratic_minterms': True, 'extra_raw_edges': extra, 'bindings': bindings}))
