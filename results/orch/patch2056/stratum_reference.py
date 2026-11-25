import json
import sys
from pathlib import Path

data=json.loads(Path(sys.argv[1]).read_text())
rows=data['rows'];n=data['ninputs'];m=len(data['positive'])
goal=(1<<m)-1;negative=((1<<len(rows))-1)^goal
inputs=[sum(((row>>i)&1)<<j for j,row in enumerate(rows)) for i in range(n)]
edges=[]
for row in rows[:m]:
 points=[p for p in range(13) if row>>p&1]
 lines=[l for l in range(13,26) if row>>l&1]
 assert len(points)==len(lines)==1
 edges.append((points[0],lines[0]))
edge_set=set(edges)
count=eligible=nested_count=0
for text in Path(sys.argv[2]).read_text().splitlines():
 record=json.loads(text);gs=record['gates'];out=record['output']
 values=inputs[:];pvars=[{i} if i<13 else set() for i in range(n)];lvars=[{i} if i>=13 else set() for i in range(n)];proofs=[set() for _ in range(n)]
 uses=[set() for _ in range(n+len(gs))]
 for j,(op,a,b) in enumerate(gs):
  assert op in (0,1) and 0<=a<n+j and 0<=b<n+j
  values.append(values[a]|values[b] if op else values[a]&values[b])
  if op:
   pvars.append(pvars[a]|pvars[b]);lvars.append(lvars[a]|lvars[b]);proofs.append(proofs[a]|proofs[b])
  else:
   pvars.append(set());lvars.append(set())
   proofs.append({(p,l) for p,l in edges if (p in pvars[a] and l in lvars[b]) or(p in pvars[b] and l in lvars[a])})
  uses[a].add(j);uses[b].add(j)
 live={out}
 for j in range(len(gs)-1,-1,-1):
  if n+j in live:live.update(gs[j][1:])
 assert all(n+j in live for j in range(len(gs)))
 clean=[not(v&negative) for v in values]
 dirty={j for j,(op,a,b) in enumerate(gs) if not op and not clean[n+j] and values[n+j]&goal}
 shared=nested=0
 for j in dirty:
  todo=[n+j];visited=set();frontier=set()
  while todo:
   w=todo.pop()
   if w in visited:continue
   visited.add(w)
   for consumer in uses[w]:
    if gs[consumer][0]:todo.append(n+consumer)
    elif values[n+consumer]&goal:frontier.add(consumer)
  shared+=len(frontier)>=2
  nested+=bool(frontier&dirty)
 expected={'raw':(values[out]^goal).bit_count(),'violations':sum((not op and(clean[a] or clean[b])) or(op and clean[a]!=clean[b]) for op,a,b in gs),'nonread':len(edge_set-proofs[out]),'shared':shared,'nested':nested}
 for key,value in expected.items():assert record[key]==value,(record['record'],key,record[key],value)
 if record['record']<755:
  assert expected['raw']==0
  ok=expected['violations']==0 and expected['nonread']>0 and shared>0
  eligible+=ok;nested_count+=ok and nested>0
 count+=1
assert count==1757 and eligible==572 and nested_count==104
print(json.dumps({'records':count,'eligible_seeds':eligible,'nested_seeds':nested_count,'all_metrics_match':True}),flush=True)
