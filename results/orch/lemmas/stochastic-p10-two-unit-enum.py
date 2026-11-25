from pathlib import Path
from itertools import product
from collections import Counter
import json,time
start=time.monotonic();base=Path('/tmp/oec/pequalnp-pilot-81');patterns=[p for p in json.loads((base/'algebraic-p10-line-count-patterns.json').read_text())['patterns'] if p['Bplus']==12 and p['Bzero']==2]
N=[{7,8,10},{7,9,13},{8,12,13},{7,11,12},{10,11,13},{9,10,12},{8,9,11}];nb=[sum(1<<(x-7) for x in s) for s in N];Q=set(range(4));E=set(range(4,7));degree=[sum(x+7 in N[i] for i in Q) for x in range(7)];outside=[any(x+7 in N[i] for i in E) for x in range(7)];domains=[[1,2,3] if degree[x]+outside[x]>=3 else list(range(4)) for x in range(7)];vectors=list(product(*domains));results=[]
for pattern in patterns:
 M=set(pattern['missing']);protected=Q-M if pattern['saturated'] else set();full=set(range(7))-M
 for two_slot in [False,True]:
  counts=Counter();survivors7=[];survivors6=[]
  for r in vectors:
   counts['initial']+=1;units=[sum(1<<x for x in range(7) if r[x]>>j&1) for j in range(2)]
   if any(u==nb[i] for u in units for i in M):continue
   counts['missing_mask']+=1
   exact={i for i in protected if any(x+7 in N[i] and ((degree[x]>=2 and r[x].bit_count()<=1) or (two_slot and degree[x]==1 and r[x]==0)) for x in range(7))}
   shared=[1<<x for x in range(7)]
   for mask in units+[nb[i] for i in full]:
    for x in range(7):
     if mask>>x&1:shared[x]|=mask
   A=nb[:4];changed=True
   while changed:
    old=A[:]
    for i in Q:
     for x in range(7):
      if not(nb[i]>>x&1):continue
      for t in range(7):
       if not(r[x]&~r[t]) and shared[x]>>t&1:A[i]|=1<<t
    if any(A[i]&~nb[i] for i in exact):break
    for mask in A:
     for x in range(7):
      if mask>>x&1:shared[x]|=mask
    changed=A!=old
   if any(A[i]&~nb[i] for i in exact):continue
   counts['co_label_exact_closure']+=1
   if any(sum(mask>>t&1 for mask in A)+outside[t]>2+r[t].bit_count() for t in range(7)):continue
   counts['assigned_budget']+=1
   costs=[];Xs=[]
   for c in range(7):
    X=[x for x in range(7) if x!=c and not(r[x]&~r[c]) and shared[x]>>c&1];Xs.append([x+7 for x in X]);costs.append(r[c].bit_count()+len(X))
   row={'r':list(r),'units':[[x+7 for x in range(7) if mask>>x&1] for mask in units],'assigned':[[x+7 for x in range(7) if mask>>x&1] for mask in A],'exact_points':sorted(exact),'cofactor_costs':costs,'X':Xs}
   if max(costs)>7:continue
   counts['cofactor_six']+=1;survivors7.append(row)
   if max(costs)>6:continue
   counts['cofactor_seven_free']+=1;survivors6.append(row)
  results.append({'missing':sorted(M),'saturated':pattern['saturated'],'protected':sorted(protected),'extra_two_slot_full_rule':two_slot,'counts':dict(counts),'survivors_generic_cofactor':survivors7,'survivors_free_eligible_cofactor':survivors6})
report={'scope':'Finite necessary-constraint experiment only. Existing generic lemmas justify residual co-label, three-slot full, assigned budgets and cofactor bounds under explicit hypotheses; two-slot full is an optional unproved extension. Actual-circuit two-unit transfer not formalized here.','Q':sorted(Q),'eligible_points':sorted(E),'forced_nonempty_lines':[x+7 for x in range(7) if domains[x]==[1,2,3]],'vectors_each':len(vectors),'elapsed_seconds':time.monotonic()-start,'results':results};(base/'stochastic-p10-two-unit-enum.json').write_text(json.dumps(report,indent=2)+'\n')
for r in results:print('M',r['missing'],'protected',r['protected'],'two_slot',r['extra_two_slot_full_rule'],r['counts'])
print('elapsed_seconds',report['elapsed_seconds'])
