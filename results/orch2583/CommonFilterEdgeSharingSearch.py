from itertools import product
from random import Random
import json

def test(n,ps,ls,w):
    wp=w&((1<<n)-1);wl=w>>n
    rows=[0]*n
    for P,L in zip(ps,ls):
        for p in range(n):
            if P>>p&1:rows[p]|=L
    erows=[r if wp>>p&1 else r&wl for p,r in enumerate(rows)]
    if any((erows[p]&erows[r]).bit_count()>1 for p in range(n) for r in range(p)):return None
    m=sum(r.bit_count() for r in erows)
    sides=sum(p.bit_count() for p in ps)+sum(l.bit_count() for l in ls)
    sharing=max((ps[0]&ps[1]).bit_count()-1,0)+max((ls[0]&ls[1]).bit_count()-1,0)
    return dict(n=n,ps=ps,ls=ls,wp=wp,wl=wl,E=erows,edges=m,sides=sides,sharing=sharing,slack=sides-sharing-m-2)
for n,mode,total in [(3,'exhaustive',0),(4,'random',1000000),(6,'random',1000000)]:
    rng=Random(2583+n)
    if mode=='exhaustive':samples=product(range(1,1<<n),range(1,1<<n),range(1,1<<n),range(1,1<<n),range(1,1<<(2*n)))
    else:samples=((rng.randrange(1,1<<n),rng.randrange(1,1<<n),rng.randrange(1,1<<n),rng.randrange(1,1<<n),rng.randrange(1,1<<(2*n))) for i in range(total))
    counts=[0,0];best=None
    for p1,l1,p2,l2,w in samples:
        counts[0]+=1;t=test(n,[p1,p2],[l1,l2],w)
        if t is None:continue
        counts[1]+=1
        if best is None or t['slack']<best['slack']:best=t
        if t['slack']<0: print(json.dumps(dict(kind='counterexample',sample=t)),flush=True);break
    else:print(json.dumps(dict(n=n,kind=mode,counts=counts,best=best)),flush=True)
