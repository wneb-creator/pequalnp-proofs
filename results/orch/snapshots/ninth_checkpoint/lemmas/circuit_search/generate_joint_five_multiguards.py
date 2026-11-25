"""Finite partition-guard constructions; no stochastic search process."""
import itertools
import json
import random
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
Builder = runpy.run_path(str(HERE / 'generate_full_guard_seeds.py'))['Builder']
assembly = runpy.run_path(str(HERE.parent / 'algebra_strategy/assemble_five_owner.py'))
compact, assemble = assembly['compact_core'], assembly['assemble_five']
case = json.loads((HERE.parent / 'algebra_strategy/five-owner-joint-packet.json').read_text())[0]
n, raw = case['inputs'], case['raw_inputs']
neighbors = [{b for a, b in case['edges'] if a == p} for p in range(5)]
rng = random.Random(650687)

def expand(gates, index, child, other):
    ren, made = list(range(n)), []
    for i, (op, a, b) in enumerate(gates):
        if i == index:
            _, u, v = gates[child - n]
            made.append([0, ren[u], ren[other]])
            left = n + len(made) - 1
            made.append([0, ren[v], ren[other]])
            right = n + len(made) - 1
            made.append([1, left, right])
        else:
            made.append([op, ren[a], ren[b]])
        ren.append(n + len(made) - 1)
    return compact(n, made)[0]

def raise_ands(gates):
    for _ in range(5):
        if sum(op == 0 for op, _, _ in gates) >= 6:
            return gates
        pure = [i < 5 for i in range(n)]
        for _, a, b in gates:
            pure.append(pure[a] and pure[b])
        choices = []
        for i, (op, a, b) in enumerate(gates):
            if op:
                continue
            for child, other in [(a, b), (b, a)]:
                if child >= n and gates[child - n][0] and pure[child]:
                    result = expand(gates, i, child, other)
                    if len(result) <= 23:
                        choices.append(result)
        if not choices:
            return None
        gates = rng.choice(choices)
    return None

columns = [int(('1' * (1 << i) + '0' * (1 << i)) * (1 << (raw-i-1)), 2)
           for i in range(raw)]
for feature in case['features']:
    value = 0
    for i in feature['raw_indices']:
        value |= columns[i]
    columns.append(value)
target = 0
for a, b in case['edges']:
    target |= columns[a] & columns[b]

seeds, seen, builds, feasible = [], set(), 0, 0
for size in (3, 4, 5):
    for group_tuple in itertools.combinations(range(5), size):
        group = set(group_tuple)
        subsets = [set(p) for k in range(1, size) for p in itertools.combinations(group_tuple, k)]
        for guard_count in range(2, min(3, len(subsets))+1):
            for guarded in itertools.combinations(subsets, guard_count):
                for order in range(2):
                    builds += 1
                    builder = Builder(n)
                    builder.unions = {1 << i: i for i in range(raw)}
                    features = list(enumerate(case['features']))
                    if order % 2:
                        features.reverse()
                    for i, feature in features:
                        builder.unions[sum(1 << j for j in feature['raw_indices'])] = raw+i
                    selected = list(guarded)
                    if order >= 2:
                        selected.reverse()
                    guards = [builder.gate(1, builder.union(a), builder.union(set().union(*(neighbors[p] for p in group-a))))
                              for a in selected]
                    out = builder.gate(0, builder.union(group), builder.union(set().union(*(neighbors[p] for p in group))))
                    for guard in guards:
                        out = builder.gate(0, out, guard)
                    for p in set(range(5))-group:
                        out = builder.gate(1, out, builder.gate(0, p, builder.union(neighbors[p])))
                    gates = builder.compact(out)
                    if len(gates) > 23:
                        continue
                    gates = raise_ands(gates)
                    if gates is None:
                        continue
                    key = tuple(map(tuple, gates))
                    if key in seen:
                        continue
                    seen.add(key)
                    _, report = assemble(case, gates)
                    if not report['within_budget']:
                        continue
                    feasible += 1
                    values = columns.copy()
                    for op, a, b in gates:
                        values.append(values[a] | values[b] if op else values[a] & values[b])
                    actual = values[-1]
                    assert target & ~actual == 0
                    wrong = [mask for mask, label in case['raw_tests'] if not label and actual >> mask & 1]
                    one_owner = sum((mask & 31).bit_count() == 1 for mask in wrong)
                    quadratic = 0
                    for a, b in itertools.combinations(range(raw), 2):
                        if actual >> ((1 << a) | (1 << b)) & 1:
                            quadratic |= columns[a] & columns[b]
                    higher = (actual & ~quadratic).bit_count()
                    if not higher:
                        continue
                    seeds.append(dict(gates=gates, group=group_tuple, guard_sets=[sorted(a) for a in selected],
                                      ands=sum(op == 0 for op, _, _ in gates), assembly=report,
                                      false_assignments=(actual & ~target).bit_count(), boundary_errors=len(wrong),
                                      one_owner_errors=one_owner, weighted_score=len(wrong)+16*one_owner,
                                      assignments_requiring_higher_terms=higher))
seeds.sort(key=lambda s: (s['weighted_score'], s['false_assignments']))
(HERE / 'joint-five-multiguard-seeds.json').write_text(json.dumps(seeds))
print(dict(builds=builds, feasible_min6=feasible, genuine_higher_degree_seeds=len(seeds),
           best_weighted=min((s['weighted_score'] for s in seeds), default=None)))
