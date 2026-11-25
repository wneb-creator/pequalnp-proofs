import json,time
from itertools import combinations_with_replacement
from datetime import datetime,timezone
n=4;m=4;edges=[(0,1),(1,2),(2,3)]
F=sum(1<<x for x in range(1<<n) if any(x>>a&1 and x>>b&1 for a,b in edges));mask=(1<<(1<<n))-1
values=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
below=[False]*n;gates=[];counts=[0]*(m+1);target_count=0;dirty_target_count=0
start=time.monotonic()
def visit(depth,dirty):
 global target_count,dirty_target_count
 counts[depth]+=1
 if depth==m:
  if values[-1]!=F:return
  reached=set();todo=[n+m-1]
  while todo:
   w=todo.pop()
   if w<n or w in reached:continue
   reached.add(w);todo.extend(gates[w-n][1:])
  if len(reached)!=m:return
  target_count+=1
  if dirty:
   dirty_target_count+=1
   print('DIRTY_MODEL',json.dumps(gates),flush=True)
  return
 for a,b in combinations_with_replacement(range(n+depth),2):
  for op in ['and','or']:
   if op=='or' and below[a]!=below[b]:continue
   v=values[a]&values[b] if op=='and' else values[a]|values[b]
   bf=v&(mask^F)==0
   values.append(v);below.append(bf);gates.append([op,a,b])
   visit(depth+1,dirty or (op=='and' and not bf))
   gates.pop();below.pop();values.pop()
print(datetime.now(timezone.utc).isoformat(),'P4 all4-gate AO circuits with every OR lift-fixed',flush=True)
visit(0,False)
print(json.dumps(dict(states_by_depth=counts,target_all_used=target_count,dirty_target_all_used=dirty_target_count,seconds=time.monotonic()-start)),flush=True)
assert target_count>0 and dirty_target_count==0
