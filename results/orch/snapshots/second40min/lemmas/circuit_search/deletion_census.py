import itertools
import json
from pathlib import Path
from prune import signatures, prune_once

root = Path(__file__).resolve().parent
case = json.loads((root / 'subsets/k6_p3.json').read_text())
seeds = json.loads((root.parent / 'algebra_strategy/k6_p3_internal_and_seeds.json').read_text())
seeds.append(case['seed'])
target = sum(bool(y) << i for i, (_, y) in enumerate(case['tests']))
inputs = signatures(17, [], case['tests'])
pool = {}
tried = 0
best = 1000

def delete(gs, index, side):
    replacement = gs[index][1+side]
    def rename(i):
        return replacement if i == 17+index else i-1 if i > 17+index else i
    return [[op, rename(a), rename(b)] for j, (op, a, b) in enumerate(gs) if j != index]

def evaluate(gs):
    values = inputs.copy()
    for op, a, b in gs:
        values.append((values[a] | values[b]) if op else (values[a] & values[b]))
    return values[-1]

for si, seed in enumerate(seeds):
    gs = seed['gates']
    count = len(gs)-28
    for removed in itertools.combinations(range(len(gs)-1), count):
        for sides in itertools.product([0, 1], repeat=count):
            candidate = gs
            for gate, side in reversed(list(zip(removed, sides))):
                candidate = delete(candidate, gate, side)
            tried += 1
            value = evaluate(candidate)
            if value & target != target:
                continue
            wrong = (value & ~target).bit_count()
            if wrong <= 32 and value not in pool:
                pool[value] = dict(miss=0, false=wrong, gates=candidate,
                                   seed_index=si, removed=list(removed), sides=list(sides))
            if wrong < best:
                best = wrong
                print('BEST false', wrong, 'after', tried, 'candidates', flush=True)
    if si % 20 == 0:
        print('seeds', si+1, 'tried', tried, 'pool', len(pool), flush=True)

print('DONE tried', tried, 'best false', best, 'pool', len(pool), flush=True)
(root / 'k6-all-positive-pool.json').write_text(json.dumps(list(pool.values())))
best_pruned = 1000
for ci, item in enumerate(pool.values()):
    gs = item['gates']
    while True:
        new = prune_once(17, gs, case['tests'])
        if gs == new:
            break
        gs = new
    wrong = (evaluate(gs) & ~target).bit_count()
    if wrong < best_pruned:
        best_pruned = wrong
        (root / 'k6-all-positive-best.json').write_text(json.dumps(gs))
        print('PRUNED BEST false', wrong, 'gates', len(gs), 'index', ci, flush=True)
    if wrong == 0:
        (root / 'k6-deletion-solution.json').write_text(json.dumps(gs))
        print('SOLUTION; independently validate before reporting', flush=True)
        break
