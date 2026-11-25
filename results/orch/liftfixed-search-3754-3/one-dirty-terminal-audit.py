import time,json,sys
from pathlib import Path
from datetime import datetime,timezone
spec=json.loads(Path(sys.argv[1]).read_text());n=spec['n'];edges=[tuple(e) for e in spec['edges']]
def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
mins=[(1<<a)|(1<<b) for a,b in edges]
maxzeros=[x for x in range(1<<n) if not target(x) and all(x>>i&1 or target(x|(1<<i)) for i in range(n))]
E=[sum(1<<i for i,x in enumerate(mins) if a&x) for a in range(1<<n)]
Z=[sum(1<<i for i,x in enumerate(maxzeros) if a&x) for a in range(1<<n)]
validA=[[a for a in range(1<<n) if Z[a]&Z[b]==0] for b in range(1<<n)]
H={}
for p in range(1,1<<n):
 for q in range(p,1<<n):
  he=E[p]&E[q];hz=Z[p]&Z[q]
  if hz and he:H.setdefault((he,hz),(p,q))
start=time.monotonic();exceptions=[];largest=0;maxexceptional=0
print(datetime.now(timezone.utc).isoformat(),spec['name'],n,'edges',len(edges),'unique_dirty_h',len(H),flush=True)
for i,((he,hz),(p,q)) in enumerate(H.items()):
 exceptional={};localmax=0
 for b in range(1,1<<n):
  if hz&Z[b]:continue
  for a in validA[b]:
   cover=(he|E[a])&E[b];k=cover.bit_count();localmax=max(localmax,k)
   if k>=3:exceptional.setdefault(cover,(a,b))
 largest=max(largest,localmax);maxexceptional=max(maxexceptional,len(exceptional))
 if localmax>3 or len(exceptional)>1:
  row=dict(p=p,q=q,edge_signature=he,false_signature=hz,largest=localmax,exceptional=[dict(edges=[edges[j] for j in range(len(edges)) if cover>>j&1],a=a,b=b) for cover,(a,b) in exceptional.items()])
  exceptions.append(row);print('EXCEPTION',json.dumps(row),flush=True)
  if len(exceptions)==10:break
print('AUDIT',json.dumps(dict(examined=i+1,total=len(H),largest_terminal_edgecount=largest,max_distinct_exceptional_covers=maxexceptional,exceptions=len(exceptions),seconds=time.monotonic()-start)),flush=True)
