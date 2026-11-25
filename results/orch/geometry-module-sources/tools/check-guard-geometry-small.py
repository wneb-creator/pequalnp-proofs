from itertools import combinations, product
from pathlib import Path
import json,time
started=time.monotonic()
V=range(13)
inc=lambda p,l:(p-l)%13 in (0,1,3,9)
pencils=[frozenset(l for l in V if inc(p,l)) for p in V]
ray=lambda p,q,r:bool(pencils[p]&pencils[q]&pencils[r])
residual=lambda p,A:frozenset(q for q in V if q!=p and not(A&pencils[q]))
counts={'pencil_card':0,'pencil_inter_card':0,'residual_configurations':0,'ray_card_cases':0,'noncollinear_triples':0}
for p in V:
 assert len(pencils[p])==4;counts['pencil_card']+=1
 for q in V:
  if p!=q:
   assert len(pencils[p]&pencils[q])==1;counts['pencil_inter_card']+=1
 outside=set(V)-pencils[p]
 for n in range(3):
  for xs in combinations(sorted(outside),n):
   A=frozenset(xs);R=residual(p,A)
   assert len(R)==(12,8,5)[n];counts['residual_configurations']+=1
   for q in V:
    if q!=p:
     size=sum(ray(p,q,r) for r in R)
     if n==0: assert size==3
     if n==1: assert size==2
     if n==2: assert size<=2
     counts['ray_card_cases']+=1
for p,q,r in product(V,repeat=3):
 if p==q or p==r or ray(p,q,r):continue
 N=frozenset(V)-(pencils[p]|pencils[q]|pencils[r])
 assert len(N)==4
 assert all(len(N&pencils[s])<=2 for s in V)
 assert frozenset(s for s in V if not(N&pencils[s]))==frozenset((p,q,r))
 counts['noncollinear_triples']+=1
report={'status':'Python finite sanity check passed; not a Lean certificate','counts':counts,'wall_seconds':time.monotonic()-started}
print(json.dumps(report,indent=2))
