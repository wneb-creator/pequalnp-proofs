from itertools import combinations, permutations
from check_counts import target, closure, can_and2, can_and3
from time import monotonic
import json
from pathlib import Path
n=5; pairs=list(combinations(range(n),2));seen=set();graphs=[];start=monotonic()
for bits in range(1,1<<len(pairs)):
 E={p for j,p in enumerate(pairs) if bits>>j&1}
 if any(all(e in E for e in combinations(s,2)) for s in combinations(range(n),3)):continue
 if any(sum(tuple(sorted((a,v))) in E and tuple(sorted((b,v))) in E for v in range(n))>1 for a,b in pairs):continue
 canon=min(sum(1<<pairs.index(tuple(sorted((p[a],p[b])))) for a,b in E) for p in permutations(range(n)))
 if canon in seen:continue
 seen.add(canon)
 alpha=max(len(s) for k in range(n+1) for s in combinations(range(n),k) if not any(e in E for e in combinations(s,2)))
 tau=n-alpha;t=target(n,E); dual=sum(1<<s for s in range(1<<n) if not(t>>(((1<<n)-1)^s)&1))
 inp=[sum(1<<s for s in range(1<<n) if s>>i&1) for i in range(n)]
 ors=closure(inp);first={a&b for a in ors for b in ors}
 def can1(f):
  base=0
  for x in inp:
   if not(x&~f):base|=x
  return any(not(g&~f) and base|g==f for g in first)
 and_lower_ok = not (t in ors if tau==1 else can1(t) if tau==2 else can_and2(n,t)[0])
 r=len(E)-1
 if r==0:or_lower_ok=True
 elif r==1:or_lower_ok=dual not in ors
 elif r==2:or_lower_ok=not can1(dual)
 elif r==3:or_lower_ok=not can_and2(n,dual)[0]
 elif r==4:or_lower_ok=not can_and3(n,dual)[0]
 else:raise ValueError(r)
 rec={'edges':sorted(E),'tau':tau,'and_lb':and_lower_ok,'or_lb':or_lower_ok,'or_required':r}
 graphs.append(rec);print(rec,'seconds',monotonic()-start,flush=True)
 assert and_lower_ok and or_lower_ok
Path('/tmp/oec/pequalnp-pilot-32/graph_bounds/small_graphs.json').write_text(json.dumps(graphs,indent=2))
print('ALL PASSED',len(graphs),'unlabelled nonempty girth5graphs on5 vertices',flush=True)
