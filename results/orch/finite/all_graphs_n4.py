from itertools import combinations, combinations_with_replacement
from collections import Counter
import json
import time

n = 4
all_mask = (1 << (1 << n)) - 1
inputs = tuple(sum(1 << x for x in range(1 << n) if x & (1 << i)) for i in range(n))
pairs = list(combinations(range(n), 2))
targets = {}
for graph_bits in range(1 << len(pairs)):
    edges = [e for i,e in enumerate(pairs) if graph_bits & (1 << i)]
    edge_set = {frozenset(e) for e in edges}
    mask = 0
    for a,b in edges:
        mask |= inputs[a] & inputs[b]
    targets[mask] = {'edges':edges, 'graph_bits':graph_bits}

base = tuple(sorted(set(inputs + (0,))))
states = {(): ()}
found = {0: {'size':0,'gates':[],'all_ands_own':True}}
start = time.time()

def ownership(gates, edges):
    values = list(inputs) + [0]
    cones = [set() for _ in values]
    good = True
    reports = []
    for j,(op,a,b,v) in enumerate(gates):
        # Operand indices refer to input wires plus the permanently available false wire.
        cone = cones[a] | cones[b]
        if a >= n+1 and gates[a-n-1][0] == 'and': cone.add(a-n-1)
        if b >= n+1 and gates[b-n-1][0] == 'and': cone.add(b-n-1)
        owned = []
        if op == 'and':
            for u,w in edges:
                x=(1<<u)|(1<<w)
                if (v>>x)&1 and all(not ((gates[k][3]>>x)&1) for k in cone):
                    owned.append((u,w))
            if not owned: good=False
            reports.append({'gate':j,'owned':owned})
        values.append(v)
        cones.append(cone)
    return good,reports

bad_minimum=[]
for depth in range(1,7):
    new = {}
    for added,gates in states.items():
        vals = list(inputs) + [0] + [g[3] for g in gates]
        valset = set(vals)
        possibilities = [(all_mask,'const',n,n)]
        for a,b in combinations_with_replacement(range(len(vals)),2):
            possibilities.append((vals[a]&vals[b],'and',a,b))
            possibilities.append((vals[a]|vals[b],'or',a,b))
        for value,op,a,b in possibilities:
            if value in valset: continue
            key=tuple(sorted(added+(value,)))
            path=gates+((op,a,b,value),)
            if value in targets and (value not in found or found[value]['size']==depth):
                good,report=ownership(path,targets[value]['edges'])
                if not good and len(bad_minimum)<10:
                    bad_minimum.append({'edges':targets[value]['edges'],'gates':path,'ownership':report,'size':depth})
            if key in new: continue
            new[key]=path
            if value in targets and value not in found:
                good, report=ownership(path, targets[value]['edges'])
                found[value]={'size':depth,'gates':path,'all_ands_own':good,'ownership':report}
    print(json.dumps({'depth':depth,'states':len(new),'found':len(found),'targets':len(targets),'elapsed':time.time()-start}),flush=True)
    states=new
    if len(found)==len(targets): break

if len(found)<len(targets):
    remaining=set(targets)-set(found)
    for added,gates in states.items():
        vals=list(inputs)+[0]+[g[3] for g in gates]
        for a,b in combinations_with_replacement(range(len(vals)),2):
            for op,value in [('and',vals[a]&vals[b]),('or',vals[a]|vals[b])]:
                if value in remaining:
                    path=gates+((op,a,b,value),)
                    good,report=ownership(path,targets[value]['edges'])
                    found[value]={'size':7,'gates':path,'all_ands_own':good,'ownership':report}
                    remaining.remove(value)
        if not remaining: break
    print(json.dumps({'seventh_gate_remaining':len(remaining),'elapsed':time.time()-start}),flush=True)
print(json.dumps({'bad_minimum':bad_minimum},indent=2),flush=True)
results=[]
for mask,target in targets.items():
    results.append(dict(target,**found.get(mask,{'missing':True})))
print(json.dumps({'n':n,'all_found':len(found)==len(targets),'targets':len(targets),'sizes':dict(Counter(r.get('size') for r in results)),'constant_witnesses':sum(any(g[0]=='const' for g in r.get('gates',[])) for r in results),'and_singleton_witnesses':sum(any(g[0]=='and' and g[3]&sum(1<<(1<<i) for i in range(n)) for g in r.get('gates',[])) for r in results),'bad_stored_witnesses':[r for r in results if not r.get('all_ands_own',False)]},indent=2),flush=True)
