"""Explore equality in the exact20-leaf signed KW rectangle bound.

All rectangle weights are checked using integers. The optional MILP result
is exploratory and is not a kernel-checked formula/circuit lower bound.
"""
from pathlib import Path
from fractions import Fraction
from functools import reduce
from math import lcm
import json
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
r=json.loads(Path('results/orch2590/kw_partition_lp.json').read_text())
autos=json.loads(Path('results/orch2590/search/petersen-orbits.json').read_text())['automorphisms']
assert isinstance(autos,list) and len(autos)==120
edges=[tuple(sorted(e)) for e in r['edges']]; negatives=r['negative_masks']
ei={e:i for i,e in enumerate(edges)}; ni={s:j for j,s in enumerate(negatives)}
w=[[Fraction(x) for x in row] for row in r['weights']]
sym=[[Fraction(0) for _ in negatives] for _ in edges]
for p in autos:
 em=[ei[tuple(sorted((p[a],p[b])))] for a,b in edges]
 nm=[ni[sum(1 << p[v] for v in range(10) if s & (1 << v))] for s in negatives]
 for i in range(15):
  for j in range(15):sym[i][j]+=w[em[i]][nm[j]]/120
assert sum(map(sum,sym))==20
denom=reduce(lcm,(x.denominator for row in sym for x in row),1)
ints=[[int(x*denom) for x in row] for row in sym]
rects={}
for v in range(10):
 rows=[i for i,e in enumerate(edges) if v in e]
 cols=[j for j,s in enumerate(negatives) if not s & (1 << v)]
 for rm in range(1,1<<len(rows)):
  rs=[i for k,i in enumerate(rows) if rm & (1<<k)]
  weights=[sum(ints[i][j] for i in rs) for j in cols]
  sums=[0]*(1<<len(cols))
  for cm in range(1,1<<len(cols)):
   bit=cm & -cm; k=bit.bit_length()-1
   sums[cm]=sums[cm^bit]+weights[k]
   assert sums[cm]<=denom
   if sums[cm]==denom:
    cs=[j for k,j in enumerate(cols) if cm & (1<<k)]
    cells=sum(1<<(15*i+j) for i in rs for j in cs)
    if cells not in rects:rects[cells]={'rows':rs,'cols':cs,'labels':[]}
    rects[cells]['labels'].append(v)
items=list(rects.items()); ar=[];ac=[];av=[]
coverage=[0]*225
for k,(bits,_) in enumerate(items):
 while bits:
  low=bits&-bits; pos=low.bit_length()-1;bits^=low
  ar.append(pos);ac.append(k);av.append(1);coverage[pos]+=1
mat=coo_matrix((av,(ar,ac)),shape=(225,len(items))).tocsr()
report={'scope':'exploratory equality-case rectangle partition; not Lean checked','denominator':denom,'symmetrized_weights':ints,'tight_rectangles':len(items),'minimum_cell_coverage':min(coverage),'row_weight_sums':[str(sum(row)) for row in sym],'column_weight_sums':[str(sum(sym[i][j] for i in range(15))) for j in range(15)]}
sol=linprog(np.ones(len(items)),A_eq=mat,b_eq=np.ones(225),bounds=(0,1),integrality=np.ones(len(items)),method='highs',options={'time_limit':30})
report.update(status=int(sol.status),message=sol.message)
if sol.success:
 selected=[k for k,x in enumerate(sol.x) if x>0.5]
 counts=[0]*225
 for k in selected:
  for i in items[k][1]['rows']:
   for j in items[k][1]['cols']:counts[15*i+j]+=1
 assert counts==[1]*225
 report['partition_size']=len(selected)
 report['partition']=[items[k][1] for k in selected]
Path('results/orch2590/kw_partition_tight.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('symmetrized_weights','partition')},indent=2))
