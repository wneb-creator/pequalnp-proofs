from itertools import combinations
import json
N=4
n=2*N
variables=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
records=[]
for mask in [r['mask'] for r in json.load(open('/tmp/oec/pequalnp-pilot-51/counterexample_sat_classes.json'))]:
    edges=[(p,N+l) for p in range(N) for l in range(N) if mask>>(N*p+l)&1]
    if any(all((p,N+l) in edges for p in [p0,p1] for l in [l0,l1]) for p0,p1 in combinations(range(N),2) for l0,l1 in combinations(range(N),2)): continue
    if not edges:
        records.append({'mask':0,'size':0,'cover':0,'gates':[],'output':n})
        continue
    covers=[t for t in range(1<<n) if all(t>>u&1 or t>>v&1 for u,v in edges)]
    cover=min(covers,key=int.bit_count)
    owners={v:[] for v in range(n) if cover>>v&1}
    for u,v in edges:
        if cover>>u&1: owners[u].append(v)
        else: owners[v].append(u)
    wires=variables[:]
    gates=[]
    def gate(op,a,b):
        gates.append([op,a,b])
        wires.append(wires[a]&wires[b] if op=='and' else wires[a]|wires[b])
        return len(wires)-1
    outs=[]
    for v,ns in owners.items():
        assert ns
        w=ns[0]
        for x in ns[1:]: w=gate('or',w,x)
        outs.append(gate('and',v,w))
    output=outs[0]
    for w in outs[1:]: output=gate('or',output,w)
    truth=0
    for u,v in edges: truth|=variables[u]&variables[v]
    assert wires[output]==truth
    assert len(gates)==len(edges)+cover.bit_count()-1
    for j,(op,a,b) in enumerate(gates):
        if op=='and':
            assert all(not(wires[n+j]>>(1<<i)&1) for i in range(n))
            assert all(not(wires[n+j]>>((1<<p)|(1<<(N+l)))&1) for p in range(N) for l in range(N) if not mask>>(N*p+l)&1)
    records.append({'mask':mask,'size':len(gates),'cover':cover,'gates':gates,'output':output})
print(json.dumps({'graphs':len(records),'max_size':max(r['size'] for r in records),'all_truth_tables_and_clean_ANDs_verified':True}))
with open('/tmp/oec/pequalnp-pilot-51/counterexample_clean_witnesses_n4.json','w') as f: json.dump(records,f)
