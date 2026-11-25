from pathlib import Path
import json, hashlib
base = Path('/tmp/oec/pequalnp-pilot-121/plane2056-cegis')
prefix = base / 'warm-nonread-readone64-fixed'
mapping = json.loads(prefix.with_suffix('.mapping.json').read_text())
metadata = json.loads(prefix.with_suffix('.json').read_text())
assert metadata['exit_code'] == 20
assert prefix.with_suffix('.sol').read_text().strip() == 's UNSATISFIABLE'
count = 0
failed = []
with prefix.with_suffix('.cnf').open('rb') as stream:
    header = stream.readline().split()
    assert list(map(int, header[2:])) == [metadata['variables'], metadata['clauses']]
    for line in stream:
        if b'-' not in line:
            failed.append(list(map(int, line.split()[:-1])))
        count += 1
last = mapping['joint_profiles'][-1][2]
assert last in mapping['flipped_variables']
assert failed == [[last]] and count == 9097867
for point, line in mapping['joint_edges']:
    proof = [{(1, 0)} if i == point else {(0, 1)} if i == line else set() for i in range(26)]
    for op, a, b in mapping['warm_gates']:
        proof.append(proof[a] | proof[b] if op else
                     {(x + u, y + v) for x, y in proof[a] for u, v in proof[b]
                      if x + u <= 1 and y + v <= 1})
    assert (1, 1) in proof[-1]
rows = mapping['rows']
values = [sum(((row >> i) & 1) << k for k, row in enumerate(rows)) for i in range(26)]
for op, a, b in mapping['warm_gates']:
    values.append(values[a] | values[b] if op else values[a] & values[b])
target = sum(any(row & (1 << p) and row & (1 << (13 + l))
                 for p in range(13) for l in range(13) if (p + l) % 13 in {0, 1, 3, 9}) << k
             for k, row in enumerate(rows))
assert values[-1] == target
path = Path('/tmp/oec/pequalnp-pilot-121/nonread2056-independent-artifact-review.json')
report = json.loads(path.read_text())
report['scope'] = 'Future full-SAT non-read1 preparation controls only; no63 witness or unrestricted lower-bound claim.'
report['negative64_control'] = {'native_exit': 20, 'clauses': count,
    'variables': metadata['variables'], 'all_false_phase_failures': 1,
    'sole_failed_unit_original_id': last, 'all52_edges_independently_read1': True,
    'actual64_gate_control_full_boundary_errors': 0,
    'cnf_sha256': hashlib.sha256(prefix.with_suffix('.cnf').read_bytes()).hexdigest()}
report['combined_verdict'] = 'APPROVED source, target phase, actual67 positive model and fixed64 negative control'
path.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report['negative64_control'], indent=2))
