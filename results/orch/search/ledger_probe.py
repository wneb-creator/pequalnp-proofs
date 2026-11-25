from itertools import combinations, product
from functools import lru_cache
import json
import time
import sys

edges = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
T = [0,2,8,9]
S = [v for v in range(10) if v not in T]
adj = lambda x,y: (x,y) in edges or (y,x) in edges
extra=[int(x) for x in sys.argv[1:]]
rows=[0]+[1<<v for v in S]+extra
width=len(rows)
ones=(1<<width)-1
profiles = [sum(1 << r for r,bs in enumerate(rows) if any(adj(t,v) and (bs>>v)&1 for v in S)) for t in T]
cells = [(p,1<<r) for p in profiles for r in range(width) if not (p>>r)&1]
key = lambda x:min(x,ones^x)
seeds = tuple(sorted(key(sum(1<<r for r,bs in enumerate(rows) if (bs>>v)&1)) for v in S))
hit = lambda c,z: (c[0]&z)==0 and (c[1]&z)!=0
coverage = {z:sum((1<<i) for i,c in enumerate(cells) if hit(c,z)) for z in range(1,ones+1)}
opts = [[(key(z),coverage[z]) for z in range(1,ones+1) if hit(c,z)] for c in cells]
disj4 = next((cs for cs in combinations(range(len(cells)),4) if all((cells[i][0]&cells[j][1]) or (cells[j][0]&cells[i][1]) for i,j in combinations(cs,2))),None)
print('T',T,'S',S,'rows',rows,'profiles',profiles,'seeds',seeds,'cells',cells,'disj4',disj4,flush=True)
full=(1<<len(cells))-1
seeds_mask=sum(1<<z for z in seeds)

@lru_cache(None)
def products(m):
    vals=[]
    mm=m
    while mm:
        b=mm&-mm;mm-=b;vals.append(b.bit_length()-1)
    out=0
    for i,a in enumerate(vals):
        for b in vals[:i+1]:
            for x,y in product((a,ones^a),(b,ones^b)):
                out |= 1<<key(x&y)
    return out

calls=0
@lru_cache(None)
def build(wanted,k,m):
    global calls
    calls+=1
    need=wanted&~m
    if not need:return ()
    if need.bit_count()>k:return None
    pm=products(m)&~m
    if need.bit_count()==k:pm &= need
    while pm:
        qbit=pm&-pm;pm-=qbit
        r=build(wanted,k-1,m|qbit)
        if r is not None:return (qbit.bit_length()-1,)+r
    return None

def lb(cov):
    if cov==full:return 0
    if disj4:return max(1,sum(1 for i in disj4 if not (cov>>i)&1))
    return 1

@lru_cache(None)
def solve(budget,n,cov,wanted):
    if n+lb(cov)+wanted.bit_count()>budget:return None
    if cov==full:
        r=build(wanted,budget-n,seeds_mask)
        return ((),r) if r is not None else None
    unseen=[i for i in range(len(cells)) if not (cov>>i)&1]
    i=min(unseen,key=lambda i:len(opts[i]))
    for z,cs in opts[i]:
        ws=wanted if (seeds_mask>>z)&1 else wanted|(1<<z)
        r=solve(budget,n+1,cov|cs,ws)
        if r is not None:return ((z,)+r[0],r[1])
    return None

for budget in (11,):
    start=time.monotonic()
    r=solve(budget,0,0,0)
    print('budget',budget,'result',r,'seconds',time.monotonic()-start,'solve',solve.cache_info(),'build',build.cache_info(),flush=True)
