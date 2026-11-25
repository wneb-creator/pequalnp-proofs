from itertools import combinations
from pathlib import Path
import json
n=6;edges=[(i,(i+1)%6) for i in range(6)];rows=list(range(64));allpos=(1<<6)-1
F=sum(1<<x for x in rows if any(x>>u&1 and x>>v&1 for u,v in edges))
OR=[sum(1<<x for x in rows if x&s) for s in range(64)]
products=[]
for p in range(1,64):
 for q in range(p+1,64):
  if p&q in [p,q]:continue
  v=OR[p]&OR[q]
  if v&~F:products.append((p,q,v))
def emask(v):return sum(1<<j for j,(u,z) in enumerate(edges) if v>>((1<<u)|(1<<z))&1)
results=[]
for B in range(1,64):
 if any(not(B>>u&1 or B>>v&1) for u,v in edges):continue
 cand=[(p,q,v,emask(v)) for p,q,v in products if not (OR[B]&v&~F)]
 best=None;cnt=0
 for j,(p,q,g,ge) in enumerate(cand):
  for r,s,h,he in cand[j+1:]:
   if ge|he!=allpos:continue
   assert OR[B]&(g|h)==F
   targets=set([p,q,r,s,B]); naive=sum(t.bit_count()-1 for t in targets)+4
   cnt+=1
   if best is None or naive<best['naive_gates']:best={'B':B,'g':[p,q],'h':[r,s],'naive_gates':naive,'edges_g':ge,'edges_h':he}
 if cnt:results.append({'B':B,'candidates':len(cand),'pairs':cnt,'best':best})
print(json.dumps(results,indent=2))
Path('/tmp/oec/pequalnp-pilot-176/twojunk-common-filter-results.json').write_text(json.dumps(results,indent=2))
