import argparse
import json
from pathlib import Path
from repair_neighborhood import normalize_gates

parser = argparse.ArgumentParser()
parser.add_argument('--cnf', type=Path, required=True)
parser.add_argument('--seed', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--toposort', action='store_true')
args = parser.parse_args()
metadata = json.loads(args.cnf.with_suffix('.map.json').read_text())
gates = normalize_gates(json.loads(args.seed.read_text()))
assert len(gates) == metadata['gates']
if args.toposort:
    ninputs = metadata['ninputs']
    mapping = {i: i for i in range(ninputs)}
    pending = set(range(len(gates)))
    ordered = []
    while pending:
        choices = []
        for i in pending:
            op, a, b = gates[i]
            if a in mapping and b in mapping:
                a, b = sorted((mapping[a], mapping[b]))
                choices.append(((a, b, op == 'or'), i, [op, a, b]))
        _, i, gate = min(choices)
        mapping[ninputs + i] = ninputs + len(ordered)
        ordered.append(gate)
        pending.remove(i)
    assert mapping[ninputs + len(gates) - 1] == ninputs + len(gates) - 1
    gates = ordered
units = []
for (op, a, b), gate in zip(gates, metadata['structure']):
    units.extend((gate['left'][a], gate['right'][b], gate['op'] if op == 'or' else -gate['op']))
lines = args.cnf.read_text().splitlines(keepends=True)
headers = [i for i, line in enumerate(lines) if line.startswith('p cnf ')]
assert len(headers) == 1
header = headers[0]
_, _, variables, clauses = lines[header].split()
assert int(variables) == metadata['nv'] and int(clauses) == metadata['clauses']
assert not args.output.exists() and not args.output.with_suffix('.map.json').exists()
metadata['clauses'] += len(units)
metadata['fixed_smoke_gates'] = gates
lines[header] = f'p cnf {metadata["nv"]} {metadata["clauses"]}\n'
lines.extend(f'{literal} 0\n' for literal in units)
args.output.write_text(''.join(lines))
args.output.with_suffix('.map.json').write_text(json.dumps(metadata) + '\n')
print(json.dumps({'gates': len(gates), 'units': len(units), 'topologically_sorted': args.toposort}))
