import json
from pathlib import Path

edges = [(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
def target(mask):
    return any(mask>>a&1 and mask>>b&1 for a,b in edges)

positive = sorted((1<<a)|(1<<b) for a,b in edges)
negative = [m for m in range(1<<14) if not target(m) and all(m>>v&1 or target(m|(1<<v)) for v in range(14))]
for m in range(1<<14):
    if target(m):
        assert any(p&m == p for p in positive)
    else:
        assert any(m&n == m for n in negative)

gates = []
outputs = []
for a in range(7):
    neighbors = [b for u,b in edges if u==a]
    current = neighbors[0]
    for b in neighbors[1:]:
        gates.append([1,current,b])
        current = 13+len(gates)
    gates.append([0,a,current])
    outputs.append(13+len(gates))
current = outputs[0]
for b in outputs[1:]:
    gates.append([1,current,b])
    current = 13+len(gates)
assert len(gates) == 25
for mask in range(1<<14):
    w = [bool(mask>>v&1) for v in range(14)]
    for op,a,b in gates:
        w.append((w[a] and w[b]) if op==0 else (w[a] or w[b]))
    assert w[current] == target(mask)

base = Path('results/orch9775/search-alt')
(base/'data.json').write_text(json.dumps(dict(edges=edges,positive=positive,negative=negative,rows=positive+negative,full_assignments_checked=16384),indent=2)+'\n')
(base/'baseline25.json').write_text(json.dumps(dict(inputs=14,output=current,gates=gates,full_assignments_checked=16384),indent=2)+'\n')
print(json.dumps(dict(edges=len(edges),positive=len(positive),negative=len(negative),rows=len(positive)+len(negative),baseline_gates=len(gates))))
