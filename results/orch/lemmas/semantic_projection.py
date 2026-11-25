#!/usr/bin/env python3
import itertools,json
from collections import Counter
from pathlib import Path
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
N=[{b for a,b in E if a==v}|{a for a,b in E if b==v} for v in range(10)]
def independent(A):return not any(a in A and b in A for a,b in E)
def sensitivity(A,v):return independent(A) and bool(A&N[v])
records=[];counts=Counter()
for S0 in itertools.combinations(range(10),3):
 S=set(S0);T=set(range(10))-S;Tl=sorted(T)
 for v in S:
  forcing=[];missing=[];indcount=0
  for bits in range(1<<len(Tl)):
   A={t for i,t in enumerate(Tl) if bits>>i&1}
   formula=independent(A) and (bool(A&N[v]) or any(not(A&N[u]) for u in N[v]&S))
   others=sorted(S-{v})
   brute=any(sensitivity(A|{u for i,u in enumerate(others) if bits2>>i&1},v) for bits2 in range(1<<len(others)))
   assert formula==brute
   if independent(A):
    indcount+=1
    if not formula:missing.append(A)
   if formula:forcing.append(A)
  assert missing
  witness=min(missing,key=lambda A:(len(A),sorted(A)))
  d=len(N[v]&S)
  assert len(witness)==d
  counts[d]+=1
  records.append({'singletons':S0,'vertex':v,'internal_degree':d,'forcing_assignments':len(forcing),'independent_assignments':indcount,'smallest_independent_nonforcing':sorted(witness)})
result={'cases':len(records),'count_by_internal_degree':dict(counts),'all_cases_have_independent_nonforcing_assignment':True,'records':records}
Path('results/orch/semantic-projection.json').write_text(json.dumps(result,indent=2)+'\n')
print('cases',len(records),'counts by induced degree',dict(counts))
print('No projected sensitivity region covers all independent outside assignments.')
print('Minimum missing independent witness size equals induced singleton degree (0,1,2) in every case.')
