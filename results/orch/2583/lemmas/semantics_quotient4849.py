from itertools import product
import json
import time
import semantics_restrict1006 as model


raw = [('or',3,4),('or',4,6),('and',8,7),('or',10,1),
       ('or',6,7),('and',2,12),('or',0,13),('and',14,9),
       ('or',5,12),('and',11,16),('or',15,17)]
model.gates = [(op, a if a < 8 else a + 3, b if b < 8 else b + 3) for op,a,b in raw]
model.output = 21
polys = [[1 << i] for i in range(11)]
for op,a,b in model.gates:
    poly = polys[a] + polys[b] if op == 'or' else [u|v for u in polys[a] for v in polys[b]]
    polys.append(model.minimal(poly))
terms = polys[model.output]


def partitions(k):
    labels = [0] * k

    def rec(i, maximum):
        if i == k:
            yield labels
            return
        for j in range(maximum + 2):
            labels[i] = j
            yield from rec(i+1, max(maximum,j))

    if k:
        yield from rec(1,0)


start = time.monotonic()
stats = {'quotients': 0, 'quadratic': 0, 'bipartite_squarefree': 0, 'improvements': 0}
best = None
for states0 in product(range(3), repeat=8):
    states = list(states0) + [0,0,0]
    zero = sum(1<<i for i,s in enumerate(states0) if s == 0)
    one = sum(1<<i for i,s in enumerate(states0) if s == 1)
    vs = [i for i,s in enumerate(states0) if s == 2]
    residual = model.minimal(t & ~one for t in terms if not t & zero)
    if not residual or 0 in residual:
        continue
    supports = [[i for i,v in enumerate(vs) if t>>v&1] for t in residual]
    for labels in partitions(len(vs)):
        stats['quotients'] += 1
        poly = model.minimal(sum({1<<labels[i] for i in s}) for s in supports)
        if not poly or any(t.bit_count() != 2 for t in poly):
            continue
        stats['quadratic'] += 1
        data = model.graph_data(poly)
        if data is None:
            continue
        stats['bipartite_squarefree'] += 1
        mapping = [0]*11
        for i,v in enumerate(vs):
            mapping[v] = labels[i]
        size,out,new_gates = model.simplify(states,mapping)
        budget,n,cover = data
        delta = size-budget
        if best is None or (delta,-len(poly),-n) < (best['delta'],-len(best['edges']),-best['n']):
            best = {'delta':delta,'states':states0,'mapping':mapping[:8],
                    'edges':poly,'n':n,'cover':cover,'budget':budget,'size':size,
                    'output':out,'gates':new_gates}
        if delta < 0:
            stats['improvements'] += 1
            print('IMPROVEMENT',json.dumps(best),flush=True)
print(json.dumps({'stats':stats,'best':best,'base_minterms':terms,
                  'seconds':time.monotonic()-start},indent=2))
