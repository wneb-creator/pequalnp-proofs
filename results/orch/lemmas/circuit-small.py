from itertools import combinations
from collections import defaultdict
from time import perf_counter
import sys
n=int(sys.argv[1]) if len(sys.argv)>1 else 4
depth=int(sys.argv[2]) if len(sys.argv)>2 else 4
full=(1<<(1<<n))-1
variables=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
pairs=list(combinations(range(n),2))
def good(edges):
 E={frozenset(e) for e in edges}
 for abc in combinations(range(n),3):
  if all(frozenset(e) in E for e in combinations(abc,2)): return False
 for a,b in pairs:
  if sum(frozenset((a,v)) in E and frozenset((b,v)) in E for v in range(n))>1:return False
 return True
targets={}
for mask in range(1,1<<len(pairs)):
 es=[e for j,e in enumerate(pairs) if mask>>j&1]
 if good(es):
  out=0
  for a,b in es: out|=variables[a]&variables[b]
  targets[out]=es
best={x:99 for x in targets};counts=defaultdict(int);junkleast=defaultdict(int)
visited=0
start=perf_counter()
def visit(values,gates):
 global visited
 visited+=1
 if gates and values[-1] in targets:
  out=values[-1];k=len(gates)
  if k<best[out]:best[out]=k;counts[out]=0;junkleast[out]=0
  if k==best[out]:
   counts[out]+=1
   if any(op==0 and (val&(~out&full))!=0 for (op,a,b),val in zip(gates,values[n:])):
    junkleast[out]+=1
 if len(gates)==depth:return
 for a,b in combinations(range(len(values)),2):
  for op in (0,1):
   value=(values[a]&values[b]) if op==0 else (values[a]|values[b])
   if value in values:continue
   visit(values+[value],gates+[(op,a,b)])
visit(variables,[])
print('inputs',n,'girth5_nonempty_targets',len(targets),'circuits_enumerated',visited,'seconds',round(perf_counter()-start,3))
print('all_targets_found',all(k<99 for k in best.values()))
print('targets_missing',[(targets[x],best[x]) for x in targets if best[x]==99])
print('minimum_sizes',dict(sorted(__import__('collections').Counter(best.values()).items())))
print('minimum_circuits_with_dirty_AND',sum(junkleast.values()))
print('All valid least circuits can omit duplicate or previously computed gate functions; repeated operands and unused gates cannot occur in a least circuit.')
