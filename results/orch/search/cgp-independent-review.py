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

out=[]
for row in json.loads((base/'cgp-verified-evolution.json').read_text()):
 verified=review(row['circuit']);assert verified=={k:v for k,v in row.items() if k!='circuit'}
 out.append(verified)
archive=json.loads((base.parent/'fano_search.json').read_text())
assert archive['cgp_verified_evolution']==json.loads((base/'cgp-verified-evolution.json').read_text())
for name in ['cgp-controls.stdout','cgp-readtrack-controls.stdout','fano-cgp.stdout']:
 for line in (base/name).read_text().splitlines():
  c=json.loads(line);checked=review(c)
  if 'unread_mask' in c:
   unread=set(map(tuple,checked['unread_edges']))
   mask=sum(1<<j for j,x in enumerate(tests) if x in positive and any(x==(1<<a|1<<b) for a,b in unread))
   assert mask==c['unread_mask']
  out.append({'file':name,'kind':c['kind'],**checked})
raw=[json.loads(x) for x in (base/'fano-cgp.stdout').read_text().splitlines()]
assert [x for x in raw if x['kind']=='improvement']==[x['circuit'] for x in json.loads((base/'cgp-verified-evolution.json').read_text())]
assert raw[-1]['kind']=='final' and raw[-1]['active_gates']==27 and raw[-1]['iterations']==3997351680
print(json.dumps({'status':'independent verification passed','all_test_vectors':'21 minimal positives plus 37 maximal negatives verified','records':out},indent=2))
