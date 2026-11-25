from itertools import combinations
from datetime import datetime, timezone
import json

N = 3
n = 2*N
variables = tuple(sum(1 << x for x in range(1 << n) if x & (1 << i)) for i in range(n))
graphs = [e for e in range(1 << (N*N)) if not any(all(e & (1 << (p*N+l)) for p in [p0,p1] for l in [l0,l1]) for p0,p1 in combinations(range(N),2) for l0,l1 in combinations(range(N),2))]
def graph_fun(edges):
    return sum(1 << x for x in range(1 << n) if any(edges & (1 << (p*N+l)) and x & (1 << p) and x & (1 << (N+l)) for p in range(N) for l in range(N)))
targets = {graph_fun(e):e for e in graphs if e}
valid_bits = sum(1 << e for e in graphs)
singletons = sum(1 << (1 << i) for i in range(n))
def permitted(f):
    if f & singletons: return 0
    return sum(1 << e for e in graphs if all(e & (1 << (p*N+l)) or not f & (1 << ((1 << p) | (1 << (N+l)))) for p in range(N) for l in range(N)))
cache = {}
def perm(f):
    if f not in cache: cache[f] = permitted(f)
    return cache[f]
first = {0:0}
clean = {0:0}
levels = {():valid_bits}
records = []
for depth in range(1,5):
    next_level = {}
    for state,good in levels.items():
        avail = variables + state
        for a,b in combinations(avail,2):
            for f,g in ((a|b,good),(a&b,good & perm(a&b))):
                if f in avail: continue
                if f in targets:
                    e=targets[f]
                    first.setdefault(e,depth)
                    if g & (1 << e): clean.setdefault(e,depth)
                ns = tuple(sorted(state+(f,)))
                next_level[ns] = next_level.get(ns,0) | g
    levels=next_level
    rec={'depth':depth,'states':len(levels),'unrestricted_found':len(first),'clean_found':len(clean),'at':datetime.now(timezone.utc).isoformat()}
    records.append(rec)
    print(json.dumps(rec),flush=True)
    if len(clean)==len(graphs): break
assert first==clean,(first,clean)
print(json.dumps({'N':N,'graphs':len(graphs),'minimum_by_edge_mask':first,'all_minima_clean':first==clean,'scope':'Exhaustive useful binary AND/OR circuits; repeated operands/copies omitted. Constants do not help nonconstant monotone minimum circuits.'},sort_keys=True),flush=True)
