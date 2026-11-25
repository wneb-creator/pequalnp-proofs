"""Read-once feasibility on a fixed complete separating set. Constants and dropping leaves are allowed."""
from functools import lru_cache
from itertools import combinations,permutations
from time import perf_counter
import json
from pathlib import Path
STEM=Path(__file__).resolve().parent
E=[(i,j)for i in range(4)for j in (4,5+i)];P=[(1<<i)|(1<<j)for i,j in E];N=[X|sum(1<<j for j in range(4,9)if not any(X>>i&1 and e==j for i,e in E)) for X in range(16)]
F=tuple(sum(1<<j for j in v)for n in [2,3,4]for v in combinations(range(4),n))
def canon(G):return min(tuple(sorted(sum(1<<pi[i] for i in range(4) if mask>>i&1) for mask in G)) for pi in permutations(range(4)))
reps=sorted({canon(G) for k in range(3) for G in combinations(F,k)},key=lambda G:(-len(G),G))
def solve(free):
 def augment(m):return m|sum(1<<(9+i) for i,f in enumerate(free) if (m>>5)&f)
 pos=list(map(augment,P)); neg=list(map(augment,N)); feats=9+len(free); diff=[[p&~n for n in neg]for p in pos]; row=tuple(tuple((1<<j,d)for j,d in enumerate(ds)) for ds in diff)
 @lru_cache(None)
 def sep(S):return tuple(sum(b for b,d in r if d&S) for r in row)
 @lru_cache(None)
 def rec(S,A,B):
  if not A or not B:return True
  rows=sep(S); active=[i for i in range(len(pos)) if A>>i&1]
  if any((rows[i]&B)!=B for i in active):return False
  if (S & (S-1))==0:return True
  T=(S-1)&S
  while T:
   U=S^T
   if T<U:
    t=sep(T);u=sep(U)
    # AND root needs every positive on both sides; partition negatives across sides.
    ca=cb=B; ta=tb=0
    for i in active:
     ca&=t[i];cb&=u[i]
     if (t[i]&B)==B:ta|=1<<i
     if (u[i]&B)==B:tb|=1<<i
    if ca|cb==B:
     opt=ca&cb; left=B&~cb;right=B&~ca;sel=opt
     while True:
      if rec(T,A,left|sel) and rec(U,A,right|(opt^sel)):return True
      if not sel:break
      sel=(sel-1)&opt
    # OR root dually assigns positives while both sides reject every negative.
    if ta|tb==A:
     opt=ta&tb; left=A&~tb;right=A&~ta;sel=opt
     while True:
      if rec(T,left|sel,B) and rec(U,right|(opt^sel),B):return True
      if not sel:break
      sel=(sel-1)&opt
   T=(T-1)&S
  return False
 start=perf_counter(); answer=rec((1<<feats)-1,(1<<len(pos))-1,(1<<len(neg))-1);return dict(free=free,readonce=answer,seconds=perf_counter()-start,states=rec.cache_info().currsize)
results=[solve(f) for f in reps];print(json.dumps(results,indent=2));(STEM/'fresh-meta3773-claw4-readonce.json').write_text(json.dumps(results,indent=2)+'\n')
