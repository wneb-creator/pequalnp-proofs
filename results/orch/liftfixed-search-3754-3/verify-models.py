from pathlib import Path
from itertools import combinations
import json
base=Path(__file__).resolve().parent
count=0
for p in sorted(base.glob('*-model.json')):
 d=json.loads(p.read_text());n=d['n'];gates=d['gates'];m=len(gates)
 edges={tuple(sorted(e)) for e in d['edges']};neighbors=[set() for _ in range(n)]
 for a,b in edges:
  assert 0<=a<b<n
  assert d['bipartition'][a]!=d['bipartition'][b]
  neighbors[a].add(b);neighbors[b].add(a)
 assert all(len(neighbors[a]&neighbors[b])<=1 for a in range(n) for b in range(a))
 def target(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
 F=sum(1<<x for x in range(1<<n) if target(x));mask=(1<<(1<<n))-1
 values=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
 for i,(op,a,b) in enumerate(gates):
  assert op in ['and','or'] and 0<=a<=b<n+i
  values.append(values[a]&values[b] if op=='and' else values[a]|values[b])
 assert d['output']==n+m-1 and values[-1]==F
 below=[v&(mask^F)==0 for v in values]
 assert below[n:]==d['below_gate']
 dirty=[i for i,(op,a,b) in enumerate(gates) if op=='and' and not below[n+i]]
 assert dirty==d['dirty_and_indices']
 if '-dirty-' in p.name:assert dirty
 if '-one-' in p.name:assert len(dirty)==1
 for op,a,b in gates:
  if op=='or':assert below[a]==below[b]
 reached=set();todo=[d['output']]
 while todo:
  w=todo.pop()
  if w<n or w in reached:continue
  reached.add(w);todo.extend(gates[w-n][1:])
 assert len(reached)==m
 tau=next(k for k in range(n+1) if any(all(a in S or b in S for a,b in edges) for S in combinations(range(n),k)))
 assert len(d['cover'])==tau and all(a in d['cover'] or b in d['cover'] for a,b in edges)
 assert d['standard_bound']==len(edges)+tau-1
 if 'critical' in p.name or '-normal-' in p.name or '-bypass-' in p.name:
  minima=[(1<<a)|(1<<b) for a,b in edges]
  maxima=[x for x in range(1<<n) if not target(x) and all(x>>a&1 or target(x|(1<<a)) for a in range(n))]
  samples=sorted(set(minima+maxima))
  sampled=[sum(1<<i for i,x in enumerate(samples) if v>>x&1) for v in values]
  for i,(op,a,b) in enumerate(gates):
   assert sampled[n+i] not in [0,(1<<len(samples))-1]+sampled[:n+i]
   assert op=='or' or (not below[a] and not below[b])
   modified=values[:n]
   for j,(operation,c,e) in enumerate(gates):
    modified.append(0 if i==j else (modified[c]&modified[e] if operation=='and' else modified[c]|modified[e]))
   assert any(not (modified[-1]>>x&1) for x in minima)
 if '-bypass-' in p.name or '-dirty-normal-' in p.name:
  for fault,(op,fa,fb) in enumerate(gates):
   for replacement in [fa,fb]:
    changed=values[:n]
    for i,(operation,a,b) in enumerate(gates):changed.append(changed[replacement] if i==fault else (changed[a]&changed[b] if operation=='and' else changed[a]|changed[b]))
    assert changed[-1]!=F
 if 'bypass_gate_index' in d:
  changed=values[:n]
  for i,(op,a,b) in enumerate(gates):changed.append(changed[d['bypass_replacement']] if i==d['bypass_gate_index'] else (changed[a]&changed[b] if op=='and' else changed[a]|changed[b]))
  assert changed[-1]==F
 print(p.name,'verified',1<<n,'assignments',len(dirty),'dirty ANDs')
 count+=1
print('MODELS_VERIFIED',count)
