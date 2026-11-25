import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('cnf')
parser.add_argument('mapping')
parser.add_argument('prefix')
args = parser.parse_args()
mapping = json.loads(Path(args.mapping).read_text())
assert isinstance(mapping, dict)
rows = mapping['rows']
structure = mapping['structure']
assert len(rows) == 58 and len(set(rows)) == 58
assert mapping['gates'] == len(structure)
units = [v if i < 21 else -v for i, v in enumerate(structure[-1]['out'])]
lines = Path(args.cnf).read_text().splitlines()
header = lines[0].split()
assert header[:2] == ['p', 'cnf']
variables, count = map(int, header[2:])
assert len(lines) == count + 1
assert lines[-58:] == [f'{v} 0' for v in units]
prefix = Path(args.prefix)
prefix.with_suffix('.cnf').write_text(
    f'p cnf {variables} {count - 58}\n' + '\n'.join(lines[1:-58]) + '\n')
with prefix.with_suffix('.meta').open('w') as f:
    f.write(f'{len(structure)} {len(rows)} {variables}\n')
    for i, (mask, unit) in enumerate(zip(rows, units)):
        initial = i < 21 or mask in [127, 16256]
        f.write(f'{mask} {int(i < 21)} {int(initial)} {abs(unit)}\n')
    for i, gate in enumerate(structure):
        assert len(gate['left']) == len(gate['right']) == 14 + i
        f.write(f'{gate["op"]} {len(gate["left"])}\n')
        f.write(' '.join(map(str, gate['left'])) + '\n')
        f.write(' '.join(map(str, gate['right'])) + '\n')
print(json.dumps({'base_clauses': count - 58, 'variables': variables,
                  'rows': len(rows), 'initial_rows': 23, 'prefix': str(prefix)}))
