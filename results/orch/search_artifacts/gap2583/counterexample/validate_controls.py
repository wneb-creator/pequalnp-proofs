import json
from pathlib import Path

P=Path(__file__).resolve().parent
data=json.loads((P/'fano.json').read_text())
edges=[(p,7+l) for l in range(7) for p in range(7) if (p-l)%7 in (0,1,3)]
assert set(map(tuple,data['edges']))==set(edges)
target=lambda r:any(r>>a&1 and r>>b&1 for a,b in edges)
independent=[r for r in range(1<<14) if not target(r)]
maximal=[r for r in independent if all(target(r|(1<<i)) for i in range(14) if not r>>i&1)]
rows=sorted(set(maximal+[sum(1<<i for i in e) for e in edges]))
assert sorted(data['rows'])==rows
print('Independent sets',len(independent),'maximal',len(maximal),'edges',len(edges),'rows',len(rows))

for name in ('upper27.json','fano27-control.circuit.json','fano27-visible-control.circuit.json'):
    circ=json.loads((P/name).read_text());gs=circ['gates'];out=circ['output'];bad=[]
    assert len(gs)==27
    assert all(op in (0,1) and 0<=a<14+j and 0<=b<14+j for j,(op,a,b) in enumerate(gs))
    for row in range(1<<14):
        w=[bool(row>>i&1) for i in range(14)]
        for op,a,b in gs:w.append(w[a] or w[b] if op else w[a] and w[b])
        if w[out]!=target(row):bad.append(row)
    assert not bad
    for a,b in edges:
        w=[{(1,0)} if i==a else {(0,1)} if i==b else set() for i in range(14)]
        for op,x,y in gs:
            w.append(w[x]|w[y] if op else {(min(2,u+s),min(2,v+t)) for u,v in w[x] for s,t in w[y]})
        assert (1,1) in w[out]
    print(name,'AO2 checked; all16384 truth rows correct; joint read1 vectors on all21 prime edges')
