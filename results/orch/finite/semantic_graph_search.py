from itertools import combinations, combinations_with_replacement
from collections import Counter
import json
import time
from argparse import ArgumentParser

parser=ArgumentParser()
parser.add_argument("--n",type=int,default=4)
parser.add_argument("--max-gates",type=int,default=5)
parser.add_argument("--check-cycle-six",action="store_true")
args=parser.parse_args()

n = args.n
all_mask = (1 << (1 << n)) - 1
inputs = tuple(sum(1 << x for x in range(1 << n) if x & (1 << i)) for i in range(n))
pairs = list(combinations(range(n), 2))
targets = {}
for graph_bits in range(1 << len(pairs)):
    edges = [e for i,e in enumerate(pairs) if graph_bits & (1 << i)]
    edge_set = {frozenset(e) for e in edges}
    if any(all(frozenset(e) in edge_set for e in combinations(tri, 2)) for tri in combinations(range(n),3)):
        continue
    if any(sum(frozenset((a,w)) in edge_set and frozenset((b,w)) in edge_set for w in range(n)) > 1 for a,b in pairs):
        continue
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
        if a >= n+1 and gates[a-n-1][0] in ('and','const'): cone.add(a-n-1)
        if b >= n+1 and gates[b-n-1][0] in ('and','const'): cone.add(b-n-1)
        owned = []
        if op in ('and','const'):
            for u,w in edges:
                x=(1<<u)|(1<<w)
                if (v>>x)&1 and all(not ((gates[k][3]>>x)&1) for k in cone):
                    owned.append((u,w))
            if not owned: good=False
            reports.append({'gate':j,'owned':owned})
        values.append(v)
        cones.append(cone)
    return good,reports

for depth in range(1,args.max_gates+1):
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
            if key in new: continue
            path=gates+((op,a,b,value),)
            new[key]=path
            if value in targets and value not in found:
                good, report=ownership(path, targets[value]['edges'])
                found[value]={'size':depth,'gates':path,'all_ands_own':good,'ownership':report}
    print(json.dumps({'depth':depth,'states':len(new),'found':len(found),'targets':len(targets),'elapsed':time.time()-start}),flush=True)
    states=new
    if len(found)==len(targets): break


if args.check_cycle_six:
    assert n == 5 and args.max_gates == 5
    cycle_edges=[(0,1),(1,2),(2,3),(3,4),(4,0)]
    cycle_target=0
    for a,b in cycle_edges: cycle_target |= inputs[a] & inputs[b]
    six_witness=None
    for added,gates in states.items():
        vals=list(inputs)+[0]+[g[3] for g in gates]
        for a,b in combinations_with_replacement(range(len(vals)),2):
            for op,value in [('and',vals[a]&vals[b]),('or',vals[a]|vals[b])]:
                if value==cycle_target:
                    six_witness=gates+((op,a,b,value),)
                    break
            if six_witness is not None: break
        if six_witness is not None: break
    print(json.dumps({'cycle5_six_gate_witness':six_witness,'elapsed':time.time()-start}),flush=True)
    
results=[]
for mask,target in targets.items():
    results.append(dict(target,**found.get(mask,{'missing':True})))
present=[r for r in results if not r.get('missing')]
summary={'n':n,'targets':len(targets),'found':len(present),'all_found':len(found)==len(targets),
'all_stored_minimum_witnesses_have_ownership':all(r['all_ands_own'] for r in present),
'size_distribution':dict(Counter(r['size'] for r in present)),
'missing_edge_counts':dict(Counter(len(r['edges']) for r in results if r.get('missing'))),
'constant_gate_witnesses':sum(any(g[0]=='const' for g in r['gates']) for r in present),
'bad_witnesses':[r for r in present if not r['all_ands_own']]}
print(json.dumps(summary,indent=2),flush=True)
