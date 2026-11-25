import json
import time
from semantics_restrict1006 import terms, minimal, graph_data, simplify


def partitions(k):
    labels = [0] * k

    def rec(i, maximum):
        if i == k:
            yield labels
            return
        for j in range(maximum + 2):
            labels[i] = j
            yield from rec(i + 1, max(maximum, j))

    if k:
        yield from rec(1, 0)


start = time.monotonic()
stats = {'quotients': 0, 'quadratic': 0, 'bipartite_squarefree': 0, 'improvements': 0}
best = None
for keep in range(1, 1 << 11):
    vs = [v for v in range(11) if keep >> v & 1]
    states = [2 if keep >> v & 1 else 0 for v in range(11)]
    residual = [t for t in terms if t & keep == t]
    if not residual:
        continue
    supports = [[i for i, v in enumerate(vs) if t >> v & 1] for t in residual]
    for labels in partitions(len(vs)):
        stats['quotients'] += 1
        poly = minimal(sum({1 << labels[i] for i in s}) for s in supports)
        if not poly or any(t.bit_count() != 2 for t in poly):
            continue
        stats['quadratic'] += 1
        data = graph_data(poly)
        if data is None:
            continue
        stats['bipartite_squarefree'] += 1
        mapping = [0] * 11
        for i, v in enumerate(vs):
            mapping[v] = labels[i]
        size, out, new_gates = simplify(states, mapping)
        budget, n, cover = data
        delta = size - budget
        if best is None or (delta, -len(poly), -n) < (best['delta'], -len(best['edges']), -best['n']):
            best = {'delta': delta, 'keep': keep, 'mapping': mapping, 'edges': poly,
                    'n': n, 'cover': cover, 'size': size, 'budget': budget,
                    'output': out, 'gates': new_gates}
        if delta < 0:
            stats['improvements'] += 1
            print('IMPROVEMENT', json.dumps(best), flush=True)
print(json.dumps({'stats': stats, 'best': best, 'seconds': time.monotonic() - start}, indent=2))
