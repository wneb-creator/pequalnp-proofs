import itertools,json,time
from pathlib import Path
n=4
inputs=tuple(sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n))
# Canonical functional states: each non-input output function once.
states={():()}
seen={f: (0, ()) for f in inputs}
results=[]
def classify(f):
    pairs=[(u,v) for u in range(n) for v in range(u+1,n) if f>>(1<<u|1<<v)&1]
    exp=sum(1<<x for x in range(1<<n) if any(x>>u&1 and x>>v&1 for u,v in pairs))
    if exp != f:return None
    adj=lambda u,v: tuple(sorted((u,v))) in pairs
    for k in [3,4]:
        if any(all(adj(p[i],p[(i+1)%k]) for i in range(k)) for p in itertools.permutations(range(n),k)):return None
    return pairs
for depth in range(1,7):
    newer={}
    start=time.time()
    for state,circuit in states.items():
        fs=inputs+state
        for a,b in itertools.combinations(fs,2):
            for op in ['and','or']:
                f=(a&b) if op=='and' else (a|b)
                if f in fs:continue
                ns=tuple(sorted((*state,f)))
                if ns in newer:continue
                nc=(*circuit,(op,a,b,f))
                newer[ns]=nc
                if f not in seen:
                    seen[f]=(depth,nc)
                    g=classify(f)
                    if g is not None:
                        results.append(dict(depth=depth,edges=g,circuit=nc))
    states=newer
    print(json.dumps(dict(depth=depth,states=len(states),seconds=time.time()-start,functions=len(seen),graph_targets=len(results))),flush=True)
    Path('/tmp/oec/pequalnp-pilot-63/Counterexample_graph_minima.json').write_text(json.dumps(results,indent=2))
    if depth==5:break
