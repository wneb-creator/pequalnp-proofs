"""Pinned cyclic core control: exact C6 function, then (f OR x0) AND f."""
import argparse
import json
from pathlib import Path

from fano_multi_sat import generate


p = argparse.ArgumentParser()
p.add_argument('--stem', required=True)
a = p.parse_args()
gates = [(1, 7, 8), (1, 7, 13), (1, 8, 13),
         (0, 1, 14), (0, 0, 15), (0, 2, 16),
         (1, 17, 18), (1, 19, 20), (1, 0, 21), (0, 21, 22)]
generate(10, 6, True, [0, 1, 2, 7, 8, 13], a.stem,
         violation=False, ordered=True, projected=True,
         fanout_budget=True, roots=1)
data = json.loads(Path(a.stem + '.json').read_text())
pins = []
for g, (op, u, v) in enumerate(gates):
    pins.extend([data['ops'][g] if op else -data['ops'][g],
                 data['selectors'][g][0][u], data['selectors'][g][1][v]])
path = Path(a.stem + '.cnf')
lines = path.read_text().splitlines()
lines[0] = 'p cnf %d %d' % (data['variables'], data['clauses'] + len(pins))
lines.extend('%d 0' % lit for lit in pins)
path.write_text('\n'.join(lines) + '\n')
print(json.dumps({'pins': len(pins), 'gates': gates}))
