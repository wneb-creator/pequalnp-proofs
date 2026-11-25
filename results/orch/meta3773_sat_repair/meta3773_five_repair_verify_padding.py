from pathlib import Path
import hashlib
import json
import resource
import sys

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
number = int(sys.argv[1]) if len(sys.argv) > 1 else 991
source = job / 'meta3773-five-patch-over-frozen21.json'
metadata = json.loads((job / ('meta3773-five-repair-r' + str(number) +
    '-metadata.json')).read_text())
raw = json.loads(source.read_text())
assert hashlib.sha256(source.read_bytes()).hexdigest() == metadata['near_seed_sha256']
width = 1 << 16
ones = (1 << width) - 1
words = []
for index in range(16):
    block = 1 << index
    words.append((ones // ((1 << (2 * block)) - 1)) * ((1 << block) - 1) << block)
for a, b in raw['free_ors']:
    words.append(words[a] | words[b])
old = words.copy()
for operation, a, b in raw['gates']:
    old.append(old[a] & old[b] if operation == 0 else old[a] | old[b])
new = words.copy()
for operation, a, b in metadata['near_seed_normalized']:
    new.append(new[a] & new[b] if operation else new[a] | new[b])
assert len(new) == 55 and old[-1] == new[-1]
if metadata['colex']:
    assert all(metadata['near_seed_normalized'][i][2] <=
        metadata['near_seed_normalized'][i + 1][2] for i in range(22))
for operation, left, right in metadata['near_seed_normalized']:
    assert left < right
assert hashlib.sha256(source.read_bytes()).hexdigest() == metadata['near_seed_sha256']
print(json.dumps({'full_65536_padding_and_colex_preservation': True,
    'normalized_gates': 23, 'seed_sha256': metadata['near_seed_sha256']}))
