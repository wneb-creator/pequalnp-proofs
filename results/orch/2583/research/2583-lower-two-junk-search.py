from itertools import combinations
from pathlib import Path
import json,time
start=time.monotonic()
full=(1<<64)-1
var=[sum(1<<s for s in range(64) if s>>i&1) for i in range(6)]
ors=[]
for a in range(64):
 z=0
 for i in range(6):
  if a>>i&1:z|=var[i]
 ors.append(z)
diag=[(1<<i)|(1<<(i+3)) for i in range(3)]
dm=sum(1<<s for s in diag)
results=[]
for extra in [0, (1<<1)|(1<<5)|(1<<6), (1<<2)|(1<<3)|(1<<7)]:
 edges={(i,i) for i in range(3)}|{(i,j) for i in range(3) for j in range(3) if extra>>(3*i+j)&1}
 goal=sum(1<<s for s in range(64) if any(s>>i&1 and s>>(j+3)&1 for i,j in edges))
 bad=[s for s in range(64) if not (goal>>s&1)]
 factors={}
 for c in range(1,64):
  for d in range(c,64):
   g=ors[c]&ors[d]
   if g&~goal==0:continue
   for a in range(64):
    h=ors[a]|g
    if h&dm!=dm:continue
    bm=sum(1<<k for k,s in enumerate(bad) if h>>s&1)
    factors.setdefault(bm,(a,c,d,h))
 found=None
 pairs=list(factors)
 for i,a in enumerate(pairs):
  for b in pairs[i:]:
   if not a&b:
    found=(factors[a][:3],factors[b][:3]);break
  if found:break
 result={'extra':extra,'negative_assignments':len(bad),'factor_bad_masks':len(pairs),'witness':found}
 print(result,flush=True);results.append(result)
Path('/tmp/oec/pequalnp-pilot-107/2583-lower-two-junk-search.json').write_text(json.dumps(results,indent=2))
print('elapsed',time.monotonic()-start)
