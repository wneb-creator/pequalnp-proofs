from functools import lru_cache
from time import monotonic
from pathlib import Path
import json

N = 14
EDGES = [(0,8),(0,10),(1,7),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)]
E0 = tuple(sorted((1 << a) | (1 << b) for a,b in EDGES))
start=monotonic()
BASES={}
def info(E):
    ns={}
    for a,b in E:
        ns.setdefault(a,set()).add(b)
        ns.setdefault(b,set()).add(a)
    key=(len(ns),len(E),tuple(sorted(len(v) for v in ns.values())))
    return key,ns
for row in json.loads(Path('/tmp/oec/pequalnp-pilot-85/lemma_search/base-graphs.json').read_text()):
    key,ns=info(row['edges'])
    BASES.setdefault(key,[]).append((ns,row['lb'],row['file']))
def iso(ns,nt):
    order=sorted(ns,key=lambda p:-len(ns[p]))
    mp={};used=set()
    def rec(i):
        if i==len(order):return True
        p=order[i]
        for q in nt:
            if q in used or len(ns[p])!=len(nt[q]):continue
            if any((v in ns[p])!=(w in nt[q]) for v,w in mp.items()):continue
            mp[p]=q;used.add(q)
            if rec(i+1):return True
            del mp[p];used.remove(q)
        return False
    return rec(0)
@lru_cache(None)
def base_lb(E):
    edges=[]
    for e in E:
        a=e&-e;b=e^a
        edges.append((a.bit_length()-1,b.bit_length()-1))
    key,ns=info(edges)
    return max([0]+[lb for nt,lb,_ in BASES.get(key,[]) if iso(ns,nt)])

@lru_cache(None)
def lb(A,E):
    V=A
    for e in E: V |= e
    if not E: return max(0,A.bit_count()-1)
    best=V.bit_count()-1
    if not A:best=max(best,base_lb(E))
    neighbours={p:0 for p in range(N) if V&(1<<p)}
    for e in E:
        for p in neighbours:
            if e&(1<<p): neighbours[p] |= e&~(1<<p)
    nofunnel=not A and len(set(neighbours.values()))==len(neighbours)
    if nofunnel:
        for e in E:
            a,b=[p for p in neighbours if e&(1<<p)]
            if neighbours[a]==1<<b and neighbours[b]==1<<a:nofunnel=False
    read_bound=10**9
    for p in range(N):
        bit=1<<p
        if not V&bit: continue
        A0=A&~bit
        E0=tuple(e for e in E if not e&bit)
        z=lb(A0,E0) if A0 or E0 else -1
        if z>=0: best=max(best,1+z)
        if A&bit: continue
        A1=A
        for e in E:
            if e&bit: A1 |= e&~bit
        E1=tuple(e for e in E0 if not e&A1)
        o=lb(A1,E1) if A1 or E1 else -1
        if o>=0: best=max(best,1+o)
        if o>=0 and z>=0: best=max(best,2+min(z,o))
        if nofunnel:
            if z<0 or o<0:nofunnel=False
            read_bound=min(read_bound,min(max(z+3,o+3),max(z+4,o+2),max(z+2,o+4)))
    if nofunnel:best=max(best,read_bound)
    return best

if __name__=='__main__':
    print('lower bound',lb(0,E0),flush=True)
    for p in range(N):
        bit=1<<p;es=tuple(e for e in E0 if not e&bit)
        print('delete',p,'bound',lb(0,es),flush=True)
    print(lb.cache_info(),'seconds',monotonic()-start,flush=True)
