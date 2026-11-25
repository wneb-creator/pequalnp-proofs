import argparse
import json
from pathlib import Path

from fano_sat import CNF


p = argparse.ArgumentParser()
p.add_argument('--source', required=True)
p.add_argument('--stem', required=True)
a = p.parse_args()
data = json.loads(Path(a.source + '.json').read_text())
lines = Path(a.source + '.cnf').read_text().splitlines()
header = lines[0].split()
assert header[:2] == ['p', 'cnf']
c = CNF()
c.n = int(header[2])
c.clauses = []
terms = []
for g, op in enumerate(data['ops']):
    accepts_independent = -1
    for r in range(len(data['independent'])):
        accepts_independent = c.or_(accepts_independent, data['vals'][data['n'] + g][r])
    terms.append(c.and_(-op, accepts_independent))
c.add(*terms)
lines[0] = 'p cnf %d %d' % (c.n, int(header[3]) + len(c.clauses))
lines.extend(' '.join(map(str, clause)) + ' 0' for clause in c.clauses)
Path(a.stem + '.cnf').write_text('\n'.join(lines) + '\n')
data['variables'] = c.n
data['clauses'] = int(header[3]) + len(c.clauses)
data['require_nonbelow_and'] = True
Path(a.stem + '.json').write_text(json.dumps(data))
print(json.dumps({'variables': c.n, 'clauses': data['clauses']}))
