from pathlib import Path
import hashlib
import json
import resource
import sys

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path('/tmp/oec/pequalnp-pilot-79')
source, destination = job / sys.argv[1], job / sys.argv[2]
assert source.parent == destination.parent == job
assert source != destination
data_file = job / 'meta3773-synthesis-data.json'
source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
data_sha = hashlib.sha256(data_file.read_bytes()).hexdigest()
data = json.loads(data_file.read_text())
candidate = json.loads(source.read_text())
original = candidate['circuit'] if isinstance(candidate, dict) else candidate
assert len(original) == 63 and original[0] == ['or', 0, 1]
rows = data['positive'] + data['negative_maximal']
assert len(rows) == len(set(rows)) == 756
inputs = [sum(((sample >> i) & 1) << k for k, sample in enumerate(rows)) for i in range(26)]
values = list(inputs)
first_wire = {value: i for i, value in enumerate(inputs)}
mapping = {i: i for i in range(26)}
unique = []
for index, (operation, a, b) in enumerate(original):
    assert operation in ['and', 'or'] and 0 <= a < 26 + index and 0 <= b < 26 + index
    a, b = mapping[a], mapping[b]
    value = values[a] & values[b] if operation == 'and' else values[a] | values[b]
    if index != 0 and value in first_wire:
        mapping[26 + index] = first_wire[value]
        continue
    wire = 26 + len(unique)
    unique.append([operation, *sorted([a, b])])
    mapping[26 + index] = wire
    values.append(value)
    first_wire.setdefault(value, wire)
output = mapping[88]
needed = {26}
pending = [output]
while pending:
    wire = pending.pop()
    if wire < 26 or wire in needed:
        continue
    needed.add(wire)
    pending.extend(unique[wire - 26][1:])
mapping = {i: i for i in range(26)}
compact = []
for index, (operation, a, b) in enumerate(unique):
    if 26 + index in needed:
        mapping[26 + index] = 26 + len(compact)
        compact.append([operation, *sorted([mapping[a], mapping[b]])])
assert mapping[output] == 25 + len(compact)
assert compact[0] == ['or', 0, 1]
assert len(compact) >= 2
if len(compact) <= 61:
    packed = list(compact)
    core_output = 25 + len(compact)
    while len(packed) < 62:
        packed.append(['and', 0, 13])
    packed.append(['or', core_output, 87])
else:
    packed = compact[:-1]
    while len(packed) < 62:
        packed.append(['and', 0, 13])
    packed.append(compact[-1])
assert len(packed) == 63

def evaluate(gates):
    wires = list(inputs)
    for operation, a, b in gates:
        wires.append(wires[a] & wires[b] if operation == 'and' else wires[a] | wires[b])
    return wires[-1]

assert evaluate(original) == evaluate(packed)
assert hashlib.sha256(source.read_bytes()).hexdigest() == source_sha
assert hashlib.sha256(data_file.read_bytes()).hexdigest() == data_sha
destination.write_text(json.dumps(packed) + '\n')
status = {'active_before_padding': len(compact), 'gate_count': len(packed),
    'all_756_distinct_test_rows_preserved': True,
    'source_sha256': source_sha, 'data_sha256': data_sha,
    'destination_sha256': hashlib.sha256(destination.read_bytes()).hexdigest()}
destination.with_suffix('.status.json').write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps(status))
