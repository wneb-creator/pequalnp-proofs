from itertools import combinations
from time import monotonic
N=4
FULL=(1<<(1<<N))-1
inputs=tuple(sum(1<<x for x in range(1<<N) if (x>>i)&1) for i in range(N))
edges=list(combinations(range(N),2))
def girth_ok(es):
    E={frozenset(e) for e in es}
    for a,b,c in combinations(range(N),3):
        if all(frozenset(e) in E for e in [(a,b),(b,c),(c,a)]):return False
    for a,b,c,d in __import__('itertools').permutations(range(N),4):
        if all(frozenset(e) in E for e in [(a,b),(b,c),(c,d),(d,a)]):return False
    return True
def target(es):
    return sum(1<<x for x in range(1<<N) if any((x>>a)&1 and (x>>b)&1 for a,b in es))
targets={target(es):es for mask in range(1<<len(edges)) if girth_ok(es:=[e for i,e in enumerate(edges) if (mask>>i)&1])}
levels={():()}
found={0:(0,(),True,targets[0])}

def profile(gates,es):
    vals=list(inputs)
    cones=[set() for _ in inputs]
    andids=set()
    for i,(op,a,b,v) in enumerate(gates,N):
        if op=='true':con=set()
        else:con=cones[a]|cones[b]|{a,b}
        vals.append(v);cones.append(con)
        if op=='and' or op=='true':andids.add(i)
    for i in andids:
        owned=[]
        for a,b in es:
            point=(1<<a)|(1<<b)
            if (vals[i]>>point)&1 and not any((vals[j]>>point)&1 for j in cones[i]&andids):owned.append({a,b})
        if owned and not set.intersection(*owned):return False
    return True
start=monotonic()
for depth in range(1,7):
    nxt={}
    for state,gates in levels.items():
        vals=list(inputs)+[g[3] for g in gates]
        generated={}
        if FULL not in vals:generated[FULL]=('true',0,0,FULL)
        for a,b in combinations(range(len(vals)),2):
            x,y=vals[a],vals[b]
            for op,v in [('and',x&y),('or',x|y)]:
                if v and v not in vals:generated.setdefault(v,(op,a,b,v))
        for v,gate in generated.items():
            gs=gates+(gate,)
            if v in targets and v not in found:
                found[v]=(depth,gs,profile(gs,targets[v]),targets[v])
                print('FOUND',depth,targets[v],found[v][2],gs,flush=True)
            key=tuple(sorted(state+(v,)))
            nxt.setdefault(key,gs)
    print('LEVEL',depth,'states',len(nxt),'targets',len(found),'of',len(targets),'seconds',monotonic()-start,flush=True)
    levels=nxt
    if len(found)==len(targets):break
print('ALL_FOUND',len(found)==len(targets),'ALL_PROFILE',all(v[2] for v in found.values()),flush=True)
