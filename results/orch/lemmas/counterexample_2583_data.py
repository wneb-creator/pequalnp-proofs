from itertools import product
from pathlib import Path
import json

vectors = [v for v in product(range(3), repeat=3) if any(v) and next(a for a in v if a) == 1]
assert len(vectors) == 13
incidence = [[sum(a*b for a,b in zip(p,l)) % 3 == 0 for l in vectors] for p in vectors]
assert all(sum(row) == 4 for row in incidence)
assert all(sum(incidence[p][l] for p in range(13)) == 4 for l in range(13))
assert all(sum(incidence[p][l] and incidence[q][l] for l in range(13)) == 1
           for p in range(13) for q in range(p))
edges = [(p,13+l) for p in range(13) for l in range(13) if incidence[p][l]]
assert len(edges) == 52
all13 = (1<<13)-1
maximal_independent = []
for S in range(1<<13):
    T = sum(1<<l for l in range(13) if all(not ((S>>p)&1) or not incidence[p][l] for p in range(13)))
    closure = sum(1<<p for p in range(13) if all(not ((T>>l)&1) or not incidence[p][l] for l in range(13)))
    if S == closure:
        maximal_independent.append(S | (T<<13))
assert len(maximal_independent) == len(set(maximal_independent))
for x in maximal_independent:
    assert not any((x>>p)&(x>>l)&1 for p,l in edges)
    for i in range(26):
        if not ((x>>i)&1):
            y=x|(1<<i)
            assert any((y>>p)&(y>>l)&1 for p,l in edges)
data = {
    'q': 3, 'N': 13, 'input_count': 26,
    'coordinates': vectors,
    'incidence_rows': incidence,
    'edges': edges,
    'maximal_independent_masks': maximal_independent,
    'boundary_rows': [[(1<<p)|(1<<l),1] for p,l in edges] + [[x,0] for x in maximal_independent],
    'read1_star_gate_count': 64,
}
out=Path('results/orch/lemmas/counterexample_2583_data.json')
out.write_text(json.dumps(data,indent=2)+'\n')
print('Generated PG(2,3):',len(edges),'edges;',len(maximal_independent),'maximal independent sets;',len(data['boundary_rows']),'complete monotone boundary rows')
print(out)
