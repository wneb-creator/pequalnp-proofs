import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--records', required=True)
parser.add_argument('--output', required=True)
args = parser.parse_args()
base_path = Path('/tmp/oec/pequalnp-pilot-121/andcount2056/andcount2056.py')
spec = importlib.util.spec_from_file_location('base', base_path)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
edges, rows = base.geometry()
positive = (1 << len(edges)) - 1
negative = ((1 << len(rows)) - 1) ^ positive
reports = []
seen = set()
for line_number, line in enumerate(Path(args.records).read_text().splitlines(), 1):
    if not line.strip():
        continue
    circuit = json.loads(line)
    gates = circuit['gates']
    output = circuit['output']
    identity = hashlib.sha256(json.dumps([gates, output]).encode()).hexdigest()
    if identity in seen:
        continue
    seen.add(identity)
    values = [sum(((row >> i) & 1) << k for k, row in enumerate(rows)) for i in range(26)]
    readers = [[] for _ in range(26 + len(gates))]
    for j, (op, a, b) in enumerate(gates):
        assert op in (0, 1) and 0 <= a < 26+j and 0 <= b < 26+j
        values.append((values[a] | values[b]) if op else (values[a] & values[b]))
        for x in set((a, b)):
            readers[x].append(j)
    assert output == 26 + len(gates) - 1
    assert values[output] == positive
    missing = []
    for ei, (a, b) in enumerate(edges):
        profile = [int(i == a) + 2 * int(i == b) for i in range(26)]
        for op, x, y in gates:
            u, v = profile[x], profile[y]
            profile.append((u | v) if op else (4 if ((u & 1 and v & 2) or (u & 2 and v & 1)) else 0))
        if not profile[output] & 4:
            missing.append(ei)
    dirty = [j for j, (op, _, _) in enumerate(gates) if op == 0 and values[26+j] & negative]
    shared_dirty = [j for j in dirty if len(readers[26+j]) > 1]
    reports.append({'line': line_number, 'kind': circuit.get('kind'), 'identity': identity,
                    'gates': len(gates), 'ANDs': sum(op == 0 for op, _, _ in gates),
                    'boundary_errors': 0, 'missing_joint_Read1_edges': missing,
                    'dirty_ANDs': dirty, 'shared_dirty_ANDs_direct_readers': shared_dirty})
assert reports
nonlinear = [r for r in reports if r['missing_joint_Read1_edges']]
result = {'records': args.records, 'distinct_circuits': len(reports),
          'best_gate_count': min(r['gates'] for r in reports),
          'best_nonread1_gate_count': min((r['gates'] for r in nonlinear), default=None),
          'at_most63': [r for r in reports if r['gates'] <= 63], 'circuits': reports}
Path(args.output).write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({key: value for key, value in result.items() if key != 'circuits'}))
