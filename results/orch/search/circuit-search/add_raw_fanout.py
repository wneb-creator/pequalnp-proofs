import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('cnf', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
metadata = json.loads(args.cnf.with_suffix('.map.json').read_text())
edges = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),
         (3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),
         (6,8),(6,9),(6,11)]
assert metadata['ninputs'] == 14 and sorted(map(tuple, metadata['edges'])) == sorted(edges)
assert not metadata.get('raw_pair_fanout')
assert not args.output.exists() and not args.output.with_suffix('.map.json').exists()
clauses = []
for i, gate in enumerate(metadata['structure']):
    other_uses = [[variable for j, other in enumerate(metadata['structure']) if j != i
                   for variable in (other['left'][raw], other['right'][raw])]
                  for raw in range(14)]
    for a in range(14):
        for b in range(a + 1, 14):
            prefix = [-gate['left'][a], -gate['right'][b]]
            clauses.append(prefix + other_uses[a])
            clauses.append(prefix + other_uses[b])
lines = args.cnf.read_text().splitlines(keepends=True)
headers = [i for i, line in enumerate(lines) if line.startswith('p cnf ')]
assert len(headers) == 1
header = headers[0]
_, _, variables, count = lines[header].split()
assert int(variables) == metadata['nv'] and int(count) == metadata['clauses']
lines[header] = f'p cnf {metadata["nv"]} {metadata["clauses"] + len(clauses)}\n'
lines.extend(' '.join(map(str, clause)) + ' 0\n' for clause in clauses)
metadata['clauses'] += len(clauses)
metadata['raw_pair_fanout'] = {'added_clauses': len(clauses),
                              'source_sha256': hashlib.sha256(args.cnf.read_bytes()).hexdigest(),
                              'scope': 'Each distinct raw-input pair gate must have another direct consumer of each input.'}
args.output.write_text(''.join(lines))
args.output.with_suffix('.map.json').write_text(json.dumps(metadata, separators=(',', ':')) + '\n')
print(json.dumps({'added_clauses': len(clauses), 'clauses': metadata['clauses'], 'variables': metadata['nv']}))
