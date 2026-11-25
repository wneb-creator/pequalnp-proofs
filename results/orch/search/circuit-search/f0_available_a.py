import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
sub = parser.add_subparsers(dest='action', required=True)
fix = sub.add_parser('fix-prefix')
fix.add_argument('cnf', type=Path)
fix.add_argument('output', type=Path)
allfix = sub.add_parser('fix-network')
allfix.add_argument('cnf', type=Path)
allfix.add_argument('output', type=Path)
allfix.add_argument('gates', type=Path)
extend = sub.add_parser('extend')
extend.add_argument('gates', type=Path)
extend.add_argument('output', type=Path)
args = parser.parse_args()

if args.action in ('fix-prefix', 'fix-network'):
    mapping = json.loads(args.cnf.with_suffix('.map.json').read_text())
    assert mapping['ninputs'] == 13 and mapping['gates'] >= 2
    assert all(13 not in e for e in mapping['edges'])
    expected = [('or', 1, 2), ('or', 4, 13)]
    if args.action == 'fix-network':
        expected = json.loads(args.gates.read_text())
        assert len(expected) == mapping['gates']
    units = []
    for i, ((op, a, b), gate) in enumerate(zip(expected, mapping['structure'])):
        assert op in ('and', 'or') and 0 <= a <= b < 13 + i
        units += [gate['left'][a], gate['right'][b], gate['op'] if op == 'or' else -gate['op']]
    lines = args.cnf.read_text().splitlines(keepends=True)
    headers = [i for i, line in enumerate(lines) if line.startswith('p cnf ')]
    assert len(headers) == 1
    header = headers[0]
    _, _, variables, clauses = lines[header].split()
    assert int(variables) == mapping['nv'] and int(clauses) == mapping['clauses']
    assert not args.output.exists() and not args.output.with_suffix('.map.json').exists()
    lines[header] = f'p cnf {variables} {int(clauses) + len(units)}\n'
    lines.extend(f'{lit} 0\n' for lit in units)
    mapping['clauses'] += len(units)
    mapping['auxiliary_prefix'] = expected[:2]
    mapping['fixed_gate_count'] = len(expected)
    mapping['scope'] = ('fixed baseline regression' if args.action == 'fix-network' else
                        'sufficient F0 construction with A=x1 OR x2 OR x4 available after gate2')
    args.output.write_text(''.join(lines))
    args.output.with_suffix('.map.json').write_text(json.dumps(mapping, separators=(',', ':')) + '\n')
    print(json.dumps({'units': units, 'nv': mapping['nv'], 'clauses': mapping['clauses']}))
else:
    data = json.loads(args.gates.read_text())
    gates = data['gates'] if isinstance(data, dict) else data
    assert gates[:2] == [['or', 1, 2], ['or', 4, 13]]
    assert all(op in ('and', 'or') and 0 <= a < 13 + i and 0 <= b < 13 + i
               for i, (op, a, b) in enumerate(gates))
    edges = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
             (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
             (6,8),(6,9),(6,11)]
    edges0 = [edge for edge in edges if 13 not in edge]
    def evaluate(program, ninputs, mask):
        values = [bool(mask >> i & 1) for i in range(ninputs)]
        for op, a, b in program:
            values.append(values[a] or values[b] if op == 'or' else values[a] and values[b])
        return values[-1]
    for mask in range(1 << 13):
        target = any(mask >> a & 1 and mask >> b & 1 for a, b in edges0)
        assert evaluate(gates, 13, mask) == target
    def rename(wire):
        return wire + (wire >= 13)
    full = [[op, rename(a), rename(b)] for op, a, b in gates]
    f0 = 13 + len(full)
    full.append(['or', 15, f0])
    f1 = 13 + len(full)
    full.append(['or', 13, f0])
    factor = 13 + len(full)
    full.append(['and', f1, factor])
    for mask in range(1 << 14):
        target = any(mask >> a & 1 and mask >> b & 1 for a, b in edges)
        assert evaluate(full, 14, mask) == target
    args.output.write_text(json.dumps(full, indent=2) + '\n')
    print(json.dumps({'input_gates': len(gates), 'extended_gates': len(full),
                      'checked_F0_rows': 1 << 13, 'checked_full_rows': 1 << 14,
                      'output': str(args.output)}))
