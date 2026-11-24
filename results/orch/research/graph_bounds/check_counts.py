from itertools import combinations
from time import monotonic
import json
from pathlib import Path

def closure(xs):
 s={0}
 for x in xs:s|={z|x for z in s}
 return tuple(sorted(s))

def target(n,edges):
 return sum(1<<s for s in range(1<<n) if any((s>>i)&(s>>j)&1 for i,j in edges))

def can_and2(n,t):
 inp=[sum(1<<s for s in range(1<<n) if s>>i&1) for i in range(n)]
 ors=closure(inp); full=(1<<(1<<n))-1
 cand={a&b for i,a in enumerate(ors) for b in ors[:i+1]}-set(ors)
 out0=0
 for x in inp:
  if not(x&~t):out0|=x
 if out0==t:return True,0
 if any(not(g&~t) and (g|out0)==t for g in cand):return True,1
 for g1 in cand:
  xs=closure(inp+[g1])
  out1=out0|(g1 if not(g1&~t) else 0)
  need=t&~out1
  elig=[a for a in xs if a&need==need]
  for i,a in enumerate(elig):
   for b in elig[:i+1]:
    g2=a&b
    if not(g2&~t) and (g2|out1)==t:return True,2
 return False,2

def can_and3(n,t):
 inp=[sum(1<<s for s in range(1<<n) if s>>i&1) for i in range(n)]
 ors=closure(inp); full=(1<<(1<<n))-1
 cand=sorted({a&b for i,a in enumerate(ors) for b in ors[:i+1]}-set(ors))
 print('initial',len(cand),flush=True)
 start=monotonic();states=0
 for k,g1 in enumerate(cand):
  xs=closure(inp+[g1]);out1=g1 if not(g1&~t) else 0
  second={a&b for i,a in enumerate(xs) for b in xs[:i+1]}-set(xs)
  for g2 in second:
   states+=1
   out12=out1|(g2 if not(g2&~t) else 0)
   if out12==t:return True,[g1,g2]
   need=t&~out12
   zs=closure(inp+[g1,g2]); elig=[a for a in zs if a&need==need]
   for i,a in enumerate(elig):
    for b in elig[:i+1]:
     g3=a&b
     if not(g3&~t) and (g3|out12)==t:return True,[g1,g2,g3]
  if k%20==0:print('first',k,'states',states,'seconds',monotonic()-start,flush=True)
 return False,states

if __name__=='__main__':
 n=5;edges=[(0,1),(1,2),(2,3),(3,4),(4,0)]
 t=target(n,edges);full=(1<<(1<<n))-1
 dual=sum(1<<s for s in range(1<<n) if not (t>>(((1<<n)-1)^s)&1))
 print('C5 AND<=2',can_and2(n,t),flush=True)
 print('C5 OR<=3 dualAND',can_and3(n,dual),flush=True)
