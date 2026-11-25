from itertools import product, combinations, permutations
from collections import deque, Counter
import json

def norm(p,q):
    c=next(x for x in p if x)
    return tuple(x*pow(c,-1,q)%q for x in p)

def modules(q,k):
    pts=sorted({norm(p,q) for p in product(range(q),repeat=3) if any(p)})
    lines=pts
    masks = [sum(1<<i for i,p in enumerate(pts) if sum(a*b for a,b in zip(p,l))%q==0) for l in lines]
    def act(ts):
        return tuple(pts.index(norm(ts(p),q)) for p in pts)
    gens=[act(lambda p:(p[1],p[0],p[2])),act(lambda p:(p[0],p[2],p[1])),act(lambda p:((p[0]+p[1])%q,p[1],p[2])),act(lambda p:((-p[0])%q,p[1],p[2]))]
    unseen={sum(1<<i for i in b) for b in combinations(range(len(pts)),k)}
    out=[]
    while unseen:
        s=min(unseen);todo=deque([s]);unseen.remove(s);orbitsize=0
        while todo:
            v=todo.popleft();orbitsize+=1
            for per in gens:
                w=sum(1<<per[i] for i in range(len(pts)) if v>>i&1)
                if w in unseen: unseen.remove(w); todo.append(w)
        inds=[i for i in range(len(pts)) if s>>i&1]
        grp=Counter(tuple(j for j,i in enumerate(inds) if mask>>i&1) for mask in masks)
        grp.pop((),None)
        groups=sorted(grp,key=lambda g:(-len(g),g))
        e=sum(map(len,groups));n=k+len(groups);can=e+k-1
        out.append(dict(q=q,k=k,rows=inds,orbit_size=orbitsize,groups=groups,multiplicities=[grp[g] for g in groups],n=n,canonical=can,excess=can-1-(n-1)))
    out.sort(key=lambda d:(d['excess'],d['rows']))
    for i,r in enumerate(out): r['id']=f'q{q}k{k}o{i}'
    return out

if __name__=='__main__':
    allrows=[]
    for q,ks in [(2,range(2,7)),(3,range(3,7))]:
        for k in ks: allrows.extend(modules(q,k))
    with open('fresh-module-catalog.json','w') as f:json.dump(allrows,f,indent=2)
    for r in allrows:print(r['id'],r['orbit_size'],r['n'],r['canonical'],r['excess'],[len(g) for g in r['groups']])
