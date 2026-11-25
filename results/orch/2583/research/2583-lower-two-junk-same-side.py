from itertools import combinations
from pathlib import Path
import json
var=[sum(1<<s for s in range(64) if s>>i&1) for i in range(6)]
ors=[]
for a in range(64):
 z=0
 for i in range(6):
  if a>>i&1:z|=var[i]
 ors.append(z)
diag=[(1<<i)|(1<<(i+3)) for i in range(3)]
results=[]
for extra in [0,98,140]:
 edges={(i,i) for i in range(3)}|{(i,j) for i in range(3) for j in range(3) if extra>>(3*i+j)&1}
 goal=sum(1<<s for s in range(64) if any(s>>i&1 and s>>(j+3)&1 for i,j in edges))
 found=None
 for b in range(1,64):
  bg=ors[b]
  a=sum(1<<i for i in range(6) if var[i]&bg&~goal==0)
  acov=sum(1<<i for i,s in enumerate(diag) if ors[a]&bg>>s&1)
  acov=sum(1<<i for i,s in enumerate(diag) if (ors[a]&bg)>>s&1)
  cand={}
  for c in range(1,64):
   for d in range(c,64):
    g=ors[c]&ors[d]
    if g&~goal==0 or g&bg&~goal:continue
    cov=sum(1<<i for i,s in enumerate(diag) if (g&bg)>>s&1)
    cand.setdefault(cov,(c,d))
  for u,v in combinations(list(cand),2):
   if acov|u|v==7:
    found={'a':a,'b':b,'g0':cand[u],'g1':cand[v]};break
  if found:break
 result={'extra':extra,'witness':found};print(result);results.append(result)
Path('/tmp/oec/pequalnp-pilot-107/2583-lower-two-junk-same-side.json').write_text(json.dumps(results,indent=2))
