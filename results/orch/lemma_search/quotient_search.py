import gtree_search as g
from time import monotonic

start=monotonic()
edges=set(tuple(sorted(e)) for e in g.EDGES)
best=0
for a in range(7):
    for b in range(7,14):
        if (a,b) in edges:continue
        es=tuple(sorted(set((1<<(a if p==b else p))|(1<<(a if q==b else q)) for p,q in edges)))
        lower=g.lb(0,es)
        best=max(best,lower)
        print(a,b,lower,'states',g.lb.cache_info().currsize,'elapsed',round(monotonic()-start,2),flush=True)
        g.lb.cache_clear()
print('BEST',best,flush=True)
