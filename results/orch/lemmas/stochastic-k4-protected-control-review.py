from pathlib import Path
from itertools import combinations
import json,hashlib
D=Path('results/orch/lemmas');source=D/'status-k4-protected-matching-control.json';data=json.loads(source.read_text());gates=data['gates'];n=10
columns=[sum(1<<row for row in range(1<<n) if row>>i&1) for i in range(n)]
values=columns[:];derivatives=[[((1<<(1<<n))-1) if i==j else 0 for j in range(n)] for i in range(n)];readers=[set() for _ in range(n+len(gates))]
for j,(op,a,b) in enumerate(gates):
 assert op in ['and','or'] and a!=b and 0<=a<n+j and 0<=b<n+j
 readers[a].add(n+j);readers[b].add(n+j)
 if op=='and':
  v=values[a]&values[b];d=[(values[a]&derivatives[b][i])|(derivatives[a][i]&values[b]) for i in range(n)]
 else:v=values[a]|values[b];d=[derivatives[a][i]|derivatives[b][i] for i in range(n)]
 values.append(v);derivatives.append(d)
edges=[(v,4+k) for k,pair in enumerate(combinations(range(4),2)) for v in pair];target=0
for a,b in edges:target|=columns[a]&columns[b]
assert values[-1]==target
live={26}
for j in reversed(range(len(gates))):
 if n+j in live:live.update(gates[j][1:])
assert live==set(range(27))
supports=[{i for i in range(n) if v>>(1<<i)&1} for v in values]
elig=set().union(*(supports[w] for w in range(27) if len(readers[w])>=2))
bplus=sum(max(0,len(readers[w])-1) for w in range(26) if supports[w]);bzero=sum(max(0,len(readers[w])-1) for w in range(26) if not supports[w])
assert sorted(elig)==data['eligible']==[0,1,2,3,4,6,7,9];assert(bplus,bzero)==(8,0);assert bplus-len(elig)==0
for i in [5,8]:
 todo=[i];seen=set()
 while todo:
  w=todo.pop()
  if w in seen:continue
  seen.add(w);assert len(readers[w])<=1;todo.extend(readers[w])
for a,b in edges:
 assert derivatives[-1][b]>>(1<<a)&1
 assert derivatives[-1][a]>>(1<<b)&1
r={'verdict':'PASS independent1024-bit truth-table and product-rule derivative evaluation','control_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256((D/'status-k4-protected-matching-control.py').read_bytes()).hexdigest(),'truth_rows':1024,'directed_edge_derivatives':24,'strict_and_fully_live':True,'size':17,'eligible':sorted(elig),'Bplus':bplus,'Bzero':bzero,'residual_units':bplus-len(elig),'protected_inputs':[5,8],'scope':'Ordinary K4 control only. It has both derivatives bright on every incidence, so it is not a quiet witness and establishes no Fano or Lean result.','method':'Independent bit-parallel evaluation from JSON gate list; exact K4 incidence target regenerated from unordered pairs, reader sets and all live ancestors independently computed.'}
(D/'stochastic-k4-protected-control-review.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
