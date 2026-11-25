from pathlib import Path
import itertools
import json

HERE = Path(__file__).resolve().parent
NEIGHBORS = {0:[8,10],1:[7,9,13],2:[8,13],3:[7,11,12],4:[10,11,13],5:[9,10,12],6:[8,9,11]}
EDGES = [(a,b) for a in NEIGHBORS for b in NEIGHBORS[a]]

def target(x):
    return any(x >> a & 1 and x >> b & 1 for a,b in EDGES)

def baseline(edges):
    gates,terms = [],[]
    def add(op,a,b):
        gates.append([op,a,b])
        return 13+len(gates)
    for a in range(7):
        neighbors = [b for aa,b in edges if aa == a]
        assert neighbors
        wire = neighbors[0]
        for b in neighbors[1:]:
            wire = add(1,wire,b)
        terms.append(add(0,a,wire))
    out = terms[0]
    for wire in terms[1:]:
        out = add(1,out,wire)
    return gates

def evaluate(gates,x):
    values = [bool(x >> j & 1) for j in range(14)]
    for op,a,b in gates:
        values.append((values[a] or values[b]) if op else (values[a] and values[b]))
    return values[-1]

negative = [x for x in range(1<<14) if not target(x) and
            all(target(x | (1<<j)) for j in range(14) if not (x >> j & 1))]
positive = [(1<<a)|(1<<b) for a,b in EDGES]
assert len(EDGES) == 19 and len(negative) == 36
assert all(len(set(NEIGHBORS[a]) & set(NEIGHBORS[b])) <= 1
           for a,b in itertools.combinations(range(7),2))
known = baseline(EDGES)
assert len(known) == 25 and all(evaluate(known,x) == target(x) for x in range(1<<14))
(HERE/'baseline25.json').write_text(json.dumps(known,indent=2)+'\n')
wrong = [gate[:] for gate in known]
wrong[-1][0] = 0
(HERE/'wrong-baseline25.json').write_text(json.dumps(wrong,indent=2)+'\n')
assert any(evaluate(wrong,x) != target(x) for x in range(1<<14))
seeds = []
for k,edge in enumerate(EDGES):
    gates = baseline(EDGES[:k]+EDGES[k+1:])
    assert len(gates) == 24
    fn = [x for x in range(1<<14) if target(x) and not evaluate(gates,x)]
    fp = [x for x in range(1<<14) if evaluate(gates,x) and not target(x)]
    assert not fp and fn
    (HERE/f'near24-edge-{k}.json').write_text(json.dumps(gates)+'\n')
    seeds.append(dict(edge_index=k,edge=edge,false_negatives=len(fn),false_positives=0))
data = dict(n=14,edges=EDGES,positive_rows=positive,negative_rows=negative,
            baseline_size=25,baseline_checked_rows=16384,c4_free=True,near_seeds=seeds)
(HERE/'data.json').write_text(json.dumps(data,indent=2)+'\n')
print('Verified19 positive/36 negative extrema, exact25-gate baseline, and19 near24-gate seeds.')
