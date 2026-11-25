import argparse
import json
from pathlib import Path

from fano_sat import CNF


p = argparse.ArgumentParser()
p.add_argument('--source', required=True)
p.add_argument('--stem', required=True)
p.add_argument('--and-count', type=int, required=True)
a = p.parse_args()
data = json.loads(Path(a.source + '.json').read_text())
lines = Path(a.source + '.cnf').read_text().splitlines()
header = lines[0].split()
assert header[:2] == ['p', 'cnf']
c = CNF()
c.n = int(header[2])
c.clauses = []
c.at_least([-op for op in data['ops']], a.and_count)
c.at_least(data['ops'], data['k'] - a.and_count)
lines[0] = 'p cnf %d %d' % (c.n, int(header[3]) + len(c.clauses))
lines.extend(' '.join(map(str, clause)) + ' 0' for clause in c.clauses)
Path(a.stem + '.cnf').write_text('\n'.join(lines) + '\n')
data['variables'] = c.n
data['clauses'] = int(header[3]) + len(c.clauses)
data['exact_and_count'] = a.and_count
Path(a.stem + '.json').write_text(json.dumps(data))
print(json.dumps({'and_count': a.and_count, 'variables': c.n, 'clauses': data['clauses']}))
