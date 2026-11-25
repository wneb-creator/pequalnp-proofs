from pathlib import Path
import hashlib
import json
import resource

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
data_path = job / 'meta3773-six-patch-data.json'
circuit_path = job / 'meta3773-six-known29.json'
bound = {str(path): hashlib.sha256(path.read_bytes()).hexdigest()
    for path in [data_path, circuit_path]}
data = json.loads(data_path.read_text())
circuit = json.loads(circuit_path.read_text())
width = 1 << 19
ones = (1 << width) - 1
raw = []
for index in range(19):
    block = 1 << index
    raw.append((ones // ((1 << (2 * block)) - 1)) * ((1 << block) - 1) << block)
words = raw.copy()
for group in data['outside_groups']:
    for a, b in group['variants'][0]:
        words.append(words[a] | words[b])
assert len(words) == 40
for index, (operation, a, b) in enumerate(circuit):
    assert type(operation) is int and operation in [0, 1]
    assert type(a) is int and type(b) is int and 0 <= a < b < 40 + index
    words.append(words[a] & words[b] if operation else words[a] | words[b])
target = 0
for a, b in data['edges']:
    target |= raw[a] & raw[b]
assert words[-1] == target
assert all(hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest
    for path, digest in bound.items())
print(json.dumps({'known_control_gates': len(circuit),
    'all_524288_physical_inputs_verified': True, 'bindings': bound}))
