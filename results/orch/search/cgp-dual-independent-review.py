import json, hashlib
from pathlib import Path
base=Path('/workspace/pequalnp-proofs/results/orch/search')
meta=json.loads((base/'fano-sls-meta.json').read_text())
n=meta['n']; edges=meta['edges']; tests=meta['tests']
assert n==14 and len(edges)==21

def target(mask): return any(mask>>a&1 and mask>>b&1 for a,b in edges)
positive={1<<a | 1<<b for a,b in edges}
negative={mask for mask in range(1<<n) if not target(mask) and all(target(mask | 1<<i) for i in range(n) if not mask>>i&1)}
assert len(positive)==21 and len(negative)==37 and set(tests)==positive|negative and len(tests)==58

def review(c):
 gates=c['gates']; output=c['output']; dirty=set()
 assert len(gates)==c['active_gates']
 for j,(op,a,b) in enumerate(gates): assert op in [0,1] and 0<=a<n+j and 0<=b<n+j
 reached=set()
 def walk(w):
  if w<n or w-n in reached:return
  reached.add(w-n);_,a,b=gates[w-n];walk(a);walk(b)
 walk(output);assert len(reached)==len(gates)
 for mask in range(1<<n):
  wires=[bool(mask>>i&1) for i in range(n)]
  for j,(op,a,b) in enumerate(gates):
   val=wires[a] or wires[b] if op else wires[a] and wires[b]
   wires.append(val)
   if not op and val and not target(mask):dirty.add(j)
  assert wires[output]==target(mask)
 unread=[]
 for a,b in edges:
  states=[{(1,0)} if i==a else {(0,1)} if i==b else set() for i in range(n)]
  for op,u,v in gates:
   states.append(states[u]|states[v] if op else {(min(2,x+x1),min(2,y+y1)) for x,y in states[u] for x1,y1 in states[v]})
  if (1,1) not in states[output]:unread.append([a,b])
 return {'size':len(gates),'inputs_verified':1<<n,'wrong_inputs':0,'unread_edges':unread,'dirty_AND_gates':sorted(dirty)}

rows=[]
for name in ['inflation-1.stdout','cgp-normalized-dual-controls.stdout','cgp-normalized-dual-virtual-controls.stdout','fano-cgp-normalized.stdout','cgp-normalized-controls2.stdout']:
 for line in (base/name).read_text().splitlines():
  if not line.startswith('{'):continue
  record=json.loads(line);checked=review(record)
  assert record['and_gates']==sum(op==0 for op,a,b in record['gates'])
  assert record['or_gates']==sum(op==1 for op,a,b in record['gates'])
  unread={tuple(x) for x in checked['unread_edges']}
  mask=sum(1<<j for j,x in enumerate(tests) if any(x==(1<<a|1<<b) for a,b in unread))
  assert mask==record['unread_mask']
  rows.append({'source':name,'kind':record['kind'],**checked})
root=Path('/tmp/oec/pequalnp-pilot-94')
for archived,rerun in [('inflation-1.stdout','cgp-dual-review-inflation.stdout'),('cgp-normalized-dual-controls.stdout','cgp-dual-review-controls.stdout'),('cgp-normalized-dual-virtual-controls.stdout','cgp-dual-review-virtual.stdout')]:
 a=[json.loads(x) for x in (base/archived).read_text().splitlines()]
 b=[json.loads(x) for x in (root/rerun).read_text().splitlines()]
 for row in a+b:row.pop('seconds')
 assert a==b
assert rows[0]['size']==28 and rows[1]['size']==29
print(json.dumps({'status':'PASS','minimum_gates':min(x['size'] for x in rows),'records':rows},indent=2))
