import sys,time
from itertools import combinations
from formula_cofactors import fam
k=int(sys.argv[1]);limit=int(sys.argv[2]);full=(1<<(1<<k))-1
pins=[sum(((x>>j)&1)<<x for x in range(1<<k)) for j in range(k)]
D={1:{(frozenset([0,full,pins[j]]),tuple(int(i==j) for i in range(k))) for j in range(k)}}
targets={fam(S):S for S in combinations(range(10),k)}
found={}
for r in range(1,limit+1):
 t=time.monotonic()
 if r>1:
  D[r]=set()
  for a in range(1,r//2+1):
   b=r-a
   for A,ca in D[a]:
    for B,cb in D[b]:
     cc=tuple(x+y for x,y in zip(ca,cb))
     if max(cc)>2:continue
     for op in [0,1]:
      C=frozenset([0,full]+[(x&y) if op==0 else (x|y) for x in A for y in B])
      D[r].add((C,cc))
 for target,S in targets.items():
  if target not in found:
   for C,cc in D[r]:
    if target<=C:found[target]=(r,cc);break
 print('r',r,'states',len(D[r]),'covered',len(found),'of',len(targets),'seconds',time.monotonic()-t,flush=True)
print('RESULTS',[(S,found.get(F)) for F,S in targets.items()],flush=True)
