import argparse
import functools
import itertools
import json
import operator
import time
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('candidate', type=Path)
ap.add_argument('--seconds', type=int, default=30)
args = ap.parse_args()
a = json.loads(args.candidate.read_text())
n = a['n']
gates = a['prefix'] + a['tail']
N = 1 << n
all_bits = (1 << N)-1
values = []
anc = [0]*n
for p in range(n):
    block = 1 << p
    values.append((all_bits // ((1 << (2*block))-1))*(((1 << block)-1) << block))
not_wire = None
for i, (op, left, right) in enumerate(gates):
    value = (all_bits ^ values[left]) if op == 'not' else (
        values[left] | values[right] if op == 'or' else values[left] & values[right])
    values.append(value)
    anc.append(anc[left] | (anc[right] if right is not None else 0) | (1 << i))
    if op == 'not':
        not_wire = n+i
assert not_wire is not None
ys = [sum(1 << p for p in comb) for comb in itertools.combinations(range(n), 3)
      if not (values[not_wire] >> sum(1 << p for p in comb)) & 1]
ors = {}
for wire, bits in enumerate(values):
    supp = sum(1 << p for p in range(n) if (bits >> (1 << p)) & 1)
    if supp.bit_count() < 2:
        continue
    expected = functools.reduce(operator.or_, (values[p] for p in range(n) if (supp >> p) & 1), 0)
    if bits == expected and (supp not in ors or anc[wire].bit_count() < anc[ors[supp]].bit_count()):
        ors[supp] = wire
best = {'margin_without_refunds': -999}
deadline = time.monotonic()+args.seconds
complete = True
nodes = 0
for y in ys:
    candidates = [(s, w, (s.bit_count() if not s & y else min(3, s.bit_count()))-1)
                  for s, w in ors.items()]
    candidates.sort(key=lambda row: -row[2])
    mandatory = anc[not_wire]

    def dfs(todo, selected, used, benefit):
        global best, complete, nodes
        nodes += 1
        if time.monotonic() >= deadline:
            complete = False
            return
        margin = benefit - used.bit_count()
        if margin > best['margin_without_refunds']:
            best = {'margin_without_refunds': margin, 'y': y, 'selected': selected,
                    'used_gates': used.bit_count(), 'benefit': benefit}
        if benefit + sum(row[2] for row in todo) - used.bit_count() <= best['margin_without_refunds']:
            return
        if not todo:
            return
        s, w, score = todo[0]
        compatible = [row for row in todo[1:] if (row[0] & s).bit_count() <= 1]
        dfs(compatible, selected+[s], used | anc[w], benefit+score)
        dfs(todo[1:], selected, used, benefit)

    dfs(candidates, [], mandatory, 0)
    if not complete:
        break
best.update({'available_or_outputs': len(ors), 'minimum_y_choices': len(ys),
             'search_complete': complete, 'nodes': nodes,
             'note': 'Gate trimming considered; nonnegative refunds omitted from margin.'})
print(json.dumps(best, indent=2))
