import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('cnf', type=Path)
parser.add_argument('mapping', type=Path)
parser.add_argument('output', type=Path)
parser.add_argument('--op', choices=('and', 'or'), required=True)
args = parser.parse_args()
mapping = json.loads(args.mapping.read_text())
assert isinstance(mapping, dict) and isinstance(mapping['structure'], list)
assert mapping['structure'] and len(mapping['structure']) == mapping['gates']
operation = mapping['structure'][-1]['op']
assert type(operation) is int and 1 <= operation <= mapping['nv']
assert args.output.resolve() not in (args.cnf.resolve(), args.mapping.resolve())
outmap = args.output.with_suffix('.map.json')
assert outmap.resolve() not in (args.cnf.resolve(), args.mapping.resolve())
assert not args.output.exists() and not outmap.exists()
content = args.cnf.read_text()
lines = content.splitlines(keepends=True)
headers = [i for i, line in enumerate(lines) if line.startswith('p cnf ')]
assert len(headers) == 1
header = headers[0]
_, _, variables, clauses = lines[header].split()
assert int(variables) == mapping['nv'] and int(clauses) == mapping['clauses']
literal = operation if args.op == 'or' else -operation
lines[header] = f'p cnf {variables} {int(clauses) + 1}\n'
if lines and not lines[-1].endswith('\n'):
    lines[-1] += '\n'
lines.append(f'{literal} 0\n')
mapping['clauses'] += 1
mapping['final_operation'] = args.op
mapping['final_operation_source_sha256'] = hashlib.sha256(args.cnf.read_bytes()).hexdigest()
args.output.write_text(''.join(lines))
outmap.write_text(json.dumps(mapping, separators=(',', ':')) + '\n')
print(json.dumps({'output': str(args.output), 'mapping': str(outmap),
                  'literal': literal, 'clauses': mapping['clauses']}))
