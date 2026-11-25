import json,sys,itertools,collections,functools,time
from pathlib import Path
x=json.loads(Path(sys.argv[1]).read_text()); n=x['n']; adj=[0]*n
for u,v in x['edges']:adj[u]|=1<<v;adj[v]|=1<<u
U=(1<<n)-1; counts=collections.Counter(); failures=[]; lowerhist=collections.Counter(); start=time.monotonic()
for A in range(1<<n):
 if A.bit_count()<4 or any(A>>v&1 and adj[v]&A for v in range(n)):continue
 S=U^A; verts=[v for v in range(n) if S>>v&1]
 if len(verts)>6:continue
 ext={v:(adj[v]&A).bit_count() for v in verts}; internal={v:bool(adj[v]&S) for v in verts}
 active=[v for v in verts if max(1,ext[v]+internal[v]-1)-1>0]
 d=tuple(max(1,ext[v]+internal[v]-1)-1 for v in active)
 k=len(active); compat=[0]*k
 for i,v in enumerate(active):
  for j,w in enumerate(active):
   if i!=j and internal[v] and internal[w] and adj[v]&adj[w]&A:compat[i]|=1<<j
 cliques=[]
 for mask in range(1,1<<k):
  if all((mask^(1<<i))&~compat[i]==0 for i in range(k) if mask>>i&1):cliques.append(mask)
 byv=[[m for m in cliques if m>>i&1] for i in range(k)]
 @functools.lru_cache(None)
 def cover(ds):
  if not any(ds):return 0
  i=next(i for i,z in enumerate(ds) if z)
  choices=[]
  for m in byv[i]:
   if all(ds[j]>0 for j in range(k) if m>>j&1):choices.append(m)
  choices.sort(key=int.bit_count,reverse=True)
  return 1+min(cover(tuple(z-((m>>j)&1) for j,z in enumerate(ds))) for m in choices)
 extra=cover(d); bound=len(verts)+extra;counts[len(verts)]+=1;lowerhist[bound]+=1
 if bound<7:failures.append({'A':[v for v in range(n) if A>>v&1],'S':verts,'demand':dict(zip(active,d)),'extra':extra,'bound':bound,'compatibility':[(active[i],active[j]) for i in range(k) for j in range(i+1,k) if compat[i]>>j&1]})
out={'scope':'conditional clique-multicover model only; branch-sharing link not established','count_by_cover_size':dict(counts),'bound_histogram':dict(lowerhist),'failures':failures,'elapsed_seconds':time.monotonic()-start}
Path(sys.argv[2]).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
