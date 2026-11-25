import json
from pathlib import Path

p=Path(__file__).resolve().parent
edges=[(0,4),(1,5),(0,6),(2,6),(0,7),(1,7),(2,7),(3,7),(5,7)]
positive=sorted((1<<a)|(1<<b) for a,b in edges)
target=lambda mask:any(mask>>a&1 and mask>>b&1 for a,b in edges)
negative=[m for m in range(256) if not target(m) and all(m>>v&1 or target(m|(1<<v)) for v in range(8))]
for m in range(256):
    if target(m): assert any(e&m==e for e in positive)
    else: assert any(m&n==m for n in negative)
gates=[[1,0,2],[1,6,7],[0,8,9],[0,0,4],[1,1,3],[1,12,5],[0,7,13],[0,1,5],[1,10,11],[1,16,14],[1,17,15]]
for m in range(256):
    values=[bool(m>>v&1) for v in range(8)]
    for op,a,b in gates:
        assert a<len(values) and b<len(values)
        values.append((values[a] and values[b]) if op==0 else (values[a] or values[b]))
    assert values[-1]==target(m)
data=dict(inputs=8,edges=edges,positive=positive,negative=negative,rows=positive+negative,full_assignments_checked=256)
(p/'data.json').write_text(json.dumps(data,indent=2)+'\n')
(p/'baseline11.json').write_text(json.dumps(dict(inputs=8,gates=gates,output=18,full_assignments_checked=256,operations={'0':'AND','1':'OR'}),indent=2)+'\n')
print(json.dumps(dict(positive=len(positive),negative=len(negative),rows=len(positive)+len(negative),baseline_gates=11,full_assignments_checked=256)))
