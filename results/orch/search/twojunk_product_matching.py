from itertools import product,combinations
import json,time
from pathlib import Path
n=6;edges=[(i,(i+1)%6) for i in range(6)];rows=list(range(64))
full=(1<<64)-1
F=sum(1<<x for x in rows if any(x>>u&1 and x>>v&1 for u,v in edges))
OR=[sum(1<<x for x in rows if x&s) for s in range(64)]
prods={}
for p in range(1,64):
 for q in range(p+1,64):
  if p&q in [p,q]:continue
  v=OR[p]&OR[q]
  if v&~F:prods.setdefault(v,(p,q))
print('dirty distinct products',len(prods),flush=True)
match={}
for m in range(64):
 es=[e for i,e in enumerate(edges) if m>>i&1]
 match[m]=max(len(ss) for j in range(len(es)+1) for ss in combinations(es,j) if len(set(u for e in ss for u in e))==2*len(ss))
maxv=-1;witness=None;hist={};pairs=0
a=list(prods)
for i,g in enumerate(a):
 for h in a[i+1:]:
  v=g&h
  if v&~F:continue
  em=sum(1<<j for j,(u,z) in enumerate(edges) if v>>((1<<u)|(1<<z))&1)
  nu=match[em];pairs+=1;hist[nu]=hist.get(nu,0)+1
  if nu>maxv:maxv=nu;witness={'g':prods[g],'h':prods[h],'edges':[e for j,e in enumerate(edges) if em>>j&1]}
print(json.dumps({'safe_pairs':pairs,'matching_histogram':hist,'max_matching':maxv,'witness':witness}),flush=True)
# All 3x3 graphs containing the fixed diagonal perfect matching, no four-cycle.
results=[]
for mask in range(512):
 if any(not(mask>>(3*i+i)&1) for i in range(3)):continue
 es=[(i,j+3) for i in range(3) for j in range(3) if mask>>(3*i+j)&1]
 if any(sum((u,v+3) in es and (z,v+3) in es for v in range(3))>=2 for u in range(3) for z in range(u+1,3)):continue
 inds=[s for s in range(64) if all(not(s>>u&1 and s>>v&1) for u,v in es)]
 maxinds=[s for s in inds if not any(s!=t and s&t==s for t in inds)]
 def conflict(a,b):return any((a|b)>>i&1 and (a|b)>>(i+3)&1 for i in range(3))
 cert=next((ss for ss in combinations(maxinds,5) if all(conflict(a,b) for a,b in combinations(ss,2))),None)
 results.append({'mask':mask,'edges':es,'maximal_independent_sets':maxinds,'five_certificate':cert})
print('3x3 graphs',len(results),'certified',sum(x['five_certificate'] is not None for x in results),flush=True)
Path('/tmp/oec/pequalnp-pilot-176/twojunk-five-independent-certificates.json').write_text(json.dumps(results,indent=2))
for x in results:
 if x['five_certificate'] is None:print('FAIL',json.dumps(x),flush=True)
