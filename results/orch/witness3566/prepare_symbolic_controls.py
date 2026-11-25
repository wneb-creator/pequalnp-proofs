#!/usr/bin/env python3
"""Prepare known upper-bound controls; no counterexample is asserted."""
import json
from pathlib import Path

from make_symbolic_witness import symbolic_render

here = Path(__file__).resolve().parent
root = here.parent
small = json.loads((root / 'finite_search/c8-amplified-4-27.witness.json').read_text())
small_plan = {'cuts': [{'wire': 30, 'edges': small['edges'][:8]}]}
(here / 'symbolic-small-plan.json').write_text(json.dumps(small_plan, indent=2))
(here / 'SymbolicSmall.lean').write_text(symbolic_render(small, small_plan))

base = json.loads((root / 'certificate_search/subk33.json').read_text())
helpers = json.loads((root / 'certificate_search/subk33-free-program.json').read_text())
n0 = base['n']
n = n0 + 2 * len(helpers['outputs'])
shift = lambda w: w if w < n0 else w + n - n0
gates = [[op, shift(a), shift(b)] for op, a, b in helpers['gates']]


def gate(op, a, b):
    gates.append([op, a, b])
    return n + len(gates) - 1


stars = []
for u in range(6):
    neighbors = [v if a == u else a for a, v in base['edges'] if a == u or v == u]
    assert len(neighbors) == 3
    union = gate('or', neighbors[0], neighbors[1])
    union = gate('or', union, neighbors[2])
    stars.append(gate('and', u, union))
output = stars[0]
for star in stars[1:]:
    output = gate('or', output, star)
base_output = output
edges = [e[:] for e in base['edges']]
for j, (helper, support) in enumerate(zip(helpers['outputs'], helpers['supports'])):
    center, private = n0 + 2*j, n0 + 2*j + 1
    union = gate('or', shift(helper), private)
    star = gate('and', center, union)
    output = gate('or', output, star)
    edges.extend([[center, v] for v in support] + [[center, private]])

large = {'n': n, 'edges': edges, 'size': len(gates), 'gates': gates,
         'output': output, 'control': 'Known star-cover upper bound; not a counterexample'}
large_plan = {'cuts': [{'wire': base_output, 'edges': base['edges']}]}
assert n == 31 and len(gates) == 63
(here / 'symbolic-large-control.json').write_text(json.dumps(large, indent=2))
(here / 'symbolic-large-plan.json').write_text(json.dumps(large_plan, indent=2))
(here / 'SymbolicLarge.lean').write_text(symbolic_render(large, large_plan))
print(json.dumps({'small': {'n': small['n'], 'gates': small['size']},
                  'large': {'n': n, 'gates': len(gates), 'edges': len(edges),
                            'cut_wire': base_output}}, sort_keys=True))
