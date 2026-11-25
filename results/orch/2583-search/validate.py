#!/usr/bin/env python3
"""Independently compare a binary monotone circuit on a complete boundary basis."""
import json
import pathlib
import sys

problem = json.loads(pathlib.Path(sys.argv[1]).read_text())
candidate = json.loads(pathlib.Path(sys.argv[2]).read_text())
n = problem['inputs']
assert candidate['inputs'] == n
gates = candidate['gates']
assert 0 <= candidate['output'] < n + len(gates)
for i, gate in enumerate(gates):
    assert gate['op'] in ('and', 'or')
    assert 0 <= gate['a'] < n+i and 0 <= gate['b'] < n+i


def evaluate(x):
    values = [bool(x >> j & 1) for j in range(n)]
    for g in gates:
        a, b = values[g['a']], values[g['b']]
        values.append(a and b if g['op'] == 'and' else a or b)
    return values[candidate['output']]


miss = [x for x in problem['minimal_true'] if not evaluate(x)]
extra = [x for x in problem['maximal_false'] if evaluate(x)]
print(json.dumps(dict(gates=len(gates), missing_edges=miss,
                     false_positive_maximal_inputs=extra,
                     exact=not miss and not extra), indent=2))
if not miss and not extra:
    print('EXACT: every true input contains a minimal true edge; every false input lies under a tested maximal false input; candidate is monotone.')
