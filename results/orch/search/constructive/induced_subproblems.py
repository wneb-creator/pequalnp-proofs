import json
from pathlib import Path

base = Path('/tmp/oec/pequalnp-pilot-70/constructive')
edges = [(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
cases = {
    'k3_collinear': [0,1,3],
    'k3_noncollinear': [0,1,2],
    'k4_complement_collinear': [2,4,5,6],
    'k4_complement_noncollinear': [3,4,5,6],
    'k5': [0,1,2,3,4],
    'k6': [0,1,2,3,4,5],
}
result = []
for name, left in cases.items():
    selected = [(a,b) for a,b in edges if a in left]
    vertices = sorted(set(v for e in selected for v in e))
    mapping = {v:i for i,v in enumerate(vertices)}
    remapped = [(mapping[a],mapping[b]) for a,b in selected]
    n = len(vertices)
    def target(mask):
        return any((mask>>a&1) and (mask>>b&1) for a,b in remapped)
    positive = [(1<<a)|(1<<b) for a,b in remapped]
    negative = [mask for mask in range(1<<n) if not target(mask) and all((mask>>i&1) or target(mask|(1<<i)) for i in range(n))]
    gates, terms = [], []
    for vertex in left:
        ns = [mapping[b] for a,b in selected if a==vertex]
        gates.append([ns[0],ns[1],'or'])
        gates.append([n+len(gates)-1,ns[2],'or'])
        gates.append([mapping[vertex],n+len(gates)-1,'and'])
        terms.append(n+len(gates)-1)
    while len(terms)>1:
        a,b=terms.pop(),terms.pop()
        gates.append([a,b,'or'])
        terms.append(n+len(gates)-1)
    for mask in range(1<<n):
        wires=[bool(mask>>i&1) for i in range(n)]
        for a,b,op in gates:
            wires.append(wires[a] and wires[b] if op=='and' else wires[a] or wires[b])
        assert wires[-1] == target(mask)
    row={'name':name,'left_vertices':left,'original_vertices':vertices,'n_inputs':n,'edges':remapped,'positive_rows':positive,'negative_rows':negative,'target_gates':len(gates)-1,'baseline_gates':gates}
    (base/(name+'.json')).write_text(json.dumps(row,indent=2)+'\n')
    summary={k:row[k] for k in ('name','n_inputs','target_gates')}
    summary.update(positive=len(positive),negative=len(negative),baseline=len(gates))
    result.append(summary)
print(json.dumps(result,indent=2))
