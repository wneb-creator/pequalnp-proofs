from itertools import product
from random import Random
from time import monotonic
import json

def test(n, ps, ls, wp, wl):
    rows=[0]*n
    for P,L in zip(ps,ls):
        for p in range(n):
            if P>>p&1: rows[p]|=L
    erows=[r if wp>>p&1 else r&wl for p,r in enumerate(rows)]
    for p in range(n):
        for r in range(p):
            if (erows[p]&erows[r]).bit_count()>1: return None
    # Each triple consisting of a rectangle pair and a W leaf needs an E edge.
    for p,row in enumerate(rows):
        outside=row&~wl if not(wp>>p&1) else 0
        if outside:
            if wl&~row: return None
            for w in range(n):
                if wp>>w&1 and outside&~rows[w]: return None
    m=sum(r.bit_count() for r in erows)
    # Bipartite vertex cover by choosing arbitrary point cover and forcing lines.
    tau=2*n
    for P in range(1<<n):
        L=0
        for p,row in enumerate(erows):
            if not(P>>p&1): L|=row
        tau=min(tau,P.bit_count()+L.bit_count())
    cost=sum(P.bit_count() for P in ps)+sum(L.bit_count() for L in ls)+wp.bit_count()+wl.bit_count()
    return dict(n=n,ps=ps,ls=ls,wp=wp,wl=wl,rows=rows,E=erows,edges=m,tau=tau,cost=cost,slack=cost-m-tau)

def main():
    start=monotonic(); counts=dict(total=0,safe_c4free=0,tight=0); best=None
    for p1,l1,p2,l2,w in product(range(1,8),range(1,8),range(1,8),range(1,8),range(1,64)):
        counts['total']+=1
        t=test(3,[p1,p2],[l1,l2],w&7,w>>3)
        if t is None: continue
        counts['safe_c4free']+=1
        if t['slack']==0: counts['tight']+=1
        if best is None or t['slack']<best['slack']: best=t
        if t['slack']<0: print(json.dumps(dict(kind='counterexample',sample=t)),flush=True);return
    print(json.dumps(dict(kind='exhaustive3',counts=counts,best=best,seconds=monotonic()-start)),flush=True)
    rng=Random(2583); counts=dict(total=0,safe_c4free=0,tight=0);best=None
    for _ in range(1000000):
        n=4;ps=[rng.randrange(1,16),rng.randrange(1,16)];ls=[rng.randrange(1,16),rng.randrange(1,16)];w=rng.randrange(1,256)
        counts['total']+=1
        t=test(n,ps,ls,w&15,w>>4)
        if t is None:continue
        counts['safe_c4free']+=1
        if t['slack']==0: counts['tight']+=1
        if best is None or t['slack']<best['slack']:best=t
        if t['slack']<0: print(json.dumps(dict(kind='counterexample',sample=t)),flush=True);return
    print(json.dumps(dict(kind='random4',counts=counts,best=best,seconds=monotonic()-start)),flush=True)

if __name__=='__main__':main()
