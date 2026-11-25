"""Finite semantic probe only; not a Lean proof or an exhaustive circuit search."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
EDGES = {(min(a,b),max(a,b)) for a,b in [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]}
FULL = (1 << 1024)-1
PIN = [sum(1<<x for x in range(1024) if x>>v&1) for v in range(10)]
TARGET = sum(1<<x for x in range(1024) if any(x>>a&1 and x>>b&1 for a,b in EDGES))
PIVOTAL = [(~PIN[v] & ~TARGET & (TARGET >> (1<<v))) & FULL for v in range(10)]
summary=Counter(); survivors=[]; witnesses=[]
for a,b in combinations(range(10),2):
 q=PIN[a]|PIN[b]
 bank=PIN+[q]
 for i,j in combinations(range(11),2):
  for kind, r in [('and',bank[i]&bank[j]),('diff',bank[i]&~bank[j]&FULL),('rdiff',bank[j]&~bank[i]&FULL)]:
   if r in bank or r in (0,FULL):continue
   certificate=None
   for v in range(10):
    vr=r & ~PIN[v]
    if vr !=0 and vr !=(FULL & ~PIN[v]):continue
    witness=PIVOTAL[v] & ~(q ^ (q >> (1<<v))) & ~(r ^ (r >> (1<<v)))
    if witness:
     lowbit=witness & -witness
     certificate={'v':v,'row':lowbit.bit_length()-1,'constant':bool(vr),'q_rebuild':int(v not in (a,b))}
     break
   if certificate:
    summary[(kind,'single_pin')]+=1
    witnesses.append({'q':[a,b],'args':[i,j],'op':kind,**certificate})
   elif kind=='and' and {i,j}=={a,b}:
    # q=a OR b and r=a AND b are fixed by swapping a,b.
    # Petersen is not invariant under this transposition, forcing one raw pin.
    assert any(((TARGET>>x)&1)!=((TARGET>>(x ^ (1<<a) ^ (1<<b)))&1) for x in range(1024) if ((x>>a)&1)!=((x>>b)&1))
    summary[(kind,'swap_pair')]+=1
   else:
    summary[(kind,'uncovered')]+=1
    survivors.append({'q':[a,b],'args':[i,j],'op':kind})
print({str(k):v for k,v in summary.items()})
# Claimed survivor classification: q AND NOT(c), c outside q; or
# v AND NOT(w), q=(v OR a), a adjacent w, all three distinct.
for case in survivors:
 a,b=case['q'];i,j=case['args'];kind=case['op']
 assert kind !='and'
 positive,negative=(i,j) if kind=='diff' else(j,i)
 form1=positive==10 and negative not in (a,b)
 form2=False
 if positive<10 and negative<10 and positive in (a,b):
  other=b if positive==a else a
  form2=negative not in (a,b) and tuple(sorted((other,negative))) in EDGES
 assert form1 or form2,case
report={'scope':'semantic two-prefix witness probe only; not checked in Lean','counts':{str(k):v for k,v in summary.items()},'survivors':survivors,'single_pin_witnesses':witnesses}
Path('results/orch1884/two_prefix_probe.json').write_text(json.dumps(report,indent=2)+'\n')
print('All uncovered cases match the two mixed-operation patterns.')
