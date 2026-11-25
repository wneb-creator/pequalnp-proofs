from itertools import combinations,permutations,product
from pathlib import Path
import json,runpy,time
BASE=Path('/tmp/oec/pequalnp-pilot-74')
def canonical(n,es):
 if not es:return ()
 deg=[0]*n
 for a,b in es:deg[a]+=1;deg[b]+=1
 blocks=[[v for v in range(n) if deg[v]==d] for d in sorted(set(deg))]
 best=None
 for ts in product(*(permutations(b) for b in blocks)):
  order=sum((list(t) for t in ts),[]);p={old:new for new,old in enumerate(order)}
  key=tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in es))
  if best is None or key<best:best=key
 return best
classes=[()]
for n in range(2,8):
 new=set()
 for es in classes:
  adj=[set() for _ in range(n)]
  for a,b in es:adj[a].add(b);adj[b].add(a)
  for m in range(1<<(n-1)):
   nb=[v for v in range(n-1) if m>>v&1]
   if any(b in adj[a] or adj[a]&adj[b] for a,b in combinations(nb,2)):continue
   ext=tuple(es)+tuple((v,n-1) for v in nb)
   new.add(canonical(n,ext))
 classes=sorted(new)
 print('classes',n,len(classes),flush=True)
(BASE/'star-seven-graphs.json').write_text(json.dumps(classes))
s=runpy.run_path(str(BASE/'star-sat.py'))
results=[]
for i,es in enumerate(classes):
 if len(es)<2:continue
 tau=min(m.bit_count() for m in range(1<<7) if all(m>>a&1 or m>>b&1 for a,b in es))
 k=len(es)+tau-2
 r=s['synth'](7,es,k,'star-seven-'+str(i),seconds=20)
 r['cover_bound']=k+1
 print(json.dumps(r),flush=True);results.append(r)
 (BASE/'star-seven-results.json').write_text(json.dumps(results,indent=2))
