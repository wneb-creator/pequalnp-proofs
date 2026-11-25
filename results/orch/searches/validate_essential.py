import argparse
import json
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('stem')
ap.add_argument('metadata')
args = ap.parse_args()
data = json.loads(Path(args.metadata).read_text())
solution = Path(args.stem+'.solution').read_text()
model = {abs(int(v)): int(v)>0 for line in solution.splitlines()
         if line.startswith('v ') for v in line.split()[1:] if int(v)}
gates = json.loads(Path(args.stem+'.verified.json').read_text())['gates']
assert len(gates) == len(data['O'])
for forced, selectors in enumerate(data['essential_witness']):
    choices = [i for i, v in enumerate(selectors) if model[v]]
    assert len(choices) == 1
    a, b = data['edges'][choices[0]]
    values = [i in [a, b] for i in range(data['n'])]
    for j, (u, v, op) in enumerate(gates):
        values.append(False if j == forced else
                      (values[u] or values[v] if op else values[u] and values[v]))
    assert not values[-1]
print('Independently verified', len(data['essential_witness']),
      'existential edge-essentiality witnesses on', len(gates), 'gates.')
