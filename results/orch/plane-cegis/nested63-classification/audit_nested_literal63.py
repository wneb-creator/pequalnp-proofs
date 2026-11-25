import hashlib,json,datetime
from pathlib import Path
s=Path('/tmp/oec/pequalnp-pilot-121/not-elimination')
literalp=s/'final-budget-nested-literal63.json';literal=json.loads(literalp.read_text());gates=literal['gates']
assert literal['size']==len(gates)==63 and literal['output']==88 and literal['constant_false'] is False
edges={(p,13+l) for p in range(13) for l in range(13) if (p+l)%13 in (0,1,3,9)}
positive={1<<p|1<<l for p,l in edges};negative=set()
neighbors=[sum(1<<l for l in range(13) if (p,13+l) in edges) for p in range(13)]
for points in range(8192):
 lines=8191
 for p in range(13):
  if points>>p&1:lines&=~neighbors[p]
 if points==sum(1<<p for p in range(13) if not neighbors[p]&lines):negative.add(points|(lines<<13))
assert len(positive)==52 and len(negative)==704
rows=sorted(positive)+sorted(negative)+[1<<p for p in range(26)]
values=[sum((bool(r>>p&1))<<k for k,r in enumerate(rows)) for p in range(26)]
for j,(op,a,b) in enumerate(gates):
 assert type(op)is int and type(a)is int and type(b)is int
 assert op in (0,1) and 0<=a<26+j and 0<=b<26+j
 values.append(values[a]|values[b] if op else values[a]&values[b])
misses=[r for k,r in enumerate(rows[:52]) if not values[-1]>>k&1]
falsepos=[r for k,r in enumerate(rows[52:756],52) if values[-1]>>k&1]
negmask=((1<<704)-1)<<52;singlemask=((1<<26)-1)<<756
dirty=[26+j for j,g in enumerate(gates) if g[0]==0 and values[26+j]&negmask]
single=[26+j for j,g in enumerate(gates) if g[0]==0 and values[26+j]&singlemask]
assert len(misses)==6 and falsepos==[] and dirty==[28,31] and single==[]
modelp=s/'andbudget-prefix-nested63-model.json';model=json.loads(modelp.read_text())
compact=values[:26].copy()
for gate in model['ands']:
 pair=[]
 for side in ['left','right']:
  v=0
  for i in gate[side]:assert type(i)is int and 0<=i<len(compact);v|=compact[i]
  pair.append(v)
 compact.append(pair[0]&pair[1])
v=0
for i in model['output']:v|=compact[26+i]
assert v==values[-1]
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Independent finite replay of incomplete nested63 warm circuit; no exact witness','literal_sha256':hashlib.sha256(literalp.read_bytes()).hexdigest(),'model_sha256':hashlib.sha256(modelp.read_bytes()).hexdigest(),'gates':len(gates),'AND_gates':sum(g[0]==0 for g in gates),'complete_boundary_rows':756,'singleton_rows':26,'positive_missed_masks':misses,'false_positive_masks':falsepos,'dirty_AND_wires':dirty,'singleton_accepting_AND_wires':single,'compact_model_matches_literal_on_all782_test_rows':True}
(s/'final-budget-nested-literal63-independent-review.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
