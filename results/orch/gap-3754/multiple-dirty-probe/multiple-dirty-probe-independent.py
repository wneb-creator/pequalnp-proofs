import json
from pathlib import Path
p=Path(__file__).with_name('multiple-dirty-probe-audit.json')
rows=json.loads(p.read_text());assert isinstance(rows,list) and len(rows)==4
for d in rows:
 assert isinstance(d,dict)
 m=d['matching_edges'];n=d['inputs'];gs=d['circuit'];assert n==2*m and 2<=m<=5
 vals=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
 F=sum(1<<x for x in range(1<<n) if any(x>>(2*i)&1 and x>>(2*i+1)&1 for i in range(m)))
 mask=(1<<(1<<n))-1
 for k,(op,a,b) in enumerate(gs):
  assert op in ['and','or'] and 0<=a<n+k and 0<=b<n+k
  vals.append(vals[a]&vals[b] if op=='and' else vals[a]|vals[b])
 out=d['output'];assert out==len(vals)-1 and vals[out]==F and len(vals)==len(set(vals))
 below=[v&(mask^F)==0 for v in vals]
 for op,a,b in gs:
  if op=='or':assert below[a]==below[b]
  else:assert not below[a] and not below[b]
 seen=set();todo=[out]
 while todo:
  w=todo.pop()
  if w<n or w in seen:continue
  seen.add(w);todo.extend(gs[w-n][1:])
 assert len(seen)==len(gs)
 mins=[(1<<(2*i))|(1<<(2*i+1)) for i in range(m)]
 for k,(op,fa,fb) in enumerate(gs):
  for replacement in [None,fa,fb]:
   altered=vals[:n]
   for j,(operation,a,b) in enumerate(gs):
    altered.append((0 if replacement is None else altered[replacement]) if j==k else (altered[a]&altered[b] if operation=='and' else altered[a]|altered[b]))
   assert altered[out]!=F
   if replacement is None:assert any(not(altered[out]>>x&1) for x in mins)
   elif op=='or':assert any(not(altered[out]>>x&1) for x in mins)
   else:assert altered[out]&(mask^F)
 op,a,b=gs[out-n]
 assert [i for i in range(n) if vals[a]>>(1<<i)&1]==[0]
 assert [i for i in range(n) if vals[b]>>(1<<i)&1]==[1]
 assert vals[a]!=vals[0] and vals[b]!=vals[1]
 dirty=sum(op=='and' and not below[n+k] for k,(op,a,b) in enumerate(gs))
 assert dirty==2**m-2 and len(gs)==3*2**m-5
 print('VERIFIED matching',m,'gates',len(gs),'dirty_ANDs',dirty,'assignments',1<<n,'plus every local parent bypass changes F')
print('INDEPENDENT_AUDIT_PASSED')
