import argparse, json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('model');ap.add_argument('--out',required=True);a=ap.parse_args()
data=json.loads(Path(a.model).read_text());args=data['args'];p,l=args['p'],args['l'];n=p+l
edges=[tuple(map(int,e.split(','))) for e in args['edges'].split(';')]
inputs=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
target=sum(1<<x for x in range(1<<n) if any(x>>u&1 and x>>(p+v)&1 for u,v in edges))
positive=sum(1<<((1<<u)|(1<<(p+v))) for u,v in edges)
gates=[(g['op'],g['left'],g['right']) for g in data['binary_gates']];out=data['binary_output']
values=inputs.copy();colours=[1 if i<p else 2 for i in range(n)];cones=[{i} for i in range(n)];ands=[];badors=[]
for j,(op,u,v) in enumerate(gates):
 assert 0<=u<n+j and 0<=v<n+j and op in ['and','or']
 if op=='or':
  values.append(values[u]|values[v]);colours.append(colours[u]|colours[v]);cones.append(cones[u]|cones[v])
  if colours[-1]==3:badors.append(n+j)
 else:
  values.append(values[u]&values[v]);colours.append(0);cones.append({n+j});ands.append(n+j)
assert values[out]==target
dirty=[w for w in ands if values[w]&~target]
readers={w:[n+j for j,(op,u,v) in enumerate(gates) if op=='and' and w in cones[u]|cones[v]] for w in ands}
loss={}
for q in ands:
 forced=values[:q]+[0]
 for op,u,v in gates[q-n+1:]:forced.append((forced[u]|forced[v]) if op=='or' else (forced[u]&forced[v]))
 loss[q]=[(u,v) for u,v in edges if not(forced[out]>>((1<<u)|(1<<(p+v)))&1)]
first=min(dirty) if dirty else None
rawsides=[] if first is None else [sorted(w for w in cones[i] if w<n) for i in gates[first-n][1:]]
live=set();pending=[out]
while pending:
 w=pending.pop()
 if w<n or w in live:continue
 live.add(w);pending.extend(gates[w-n][1:])
result={'inputs':n,'gates':len(gates),'and_gates':len(ands),'or_gates':len(gates)-len(ands),'validated_assignments':1<<n,'exact_function':True,'tcount':len(badors),'dirty_and_wires':dirty,'and_readers':readers,'first_dirty_raw_sides':rawsides,'lost_edges_by_and':loss,'first_dirty_loss_nonstar':False if first is None else any(u!=s and v!=t for u,v in loss[first] for s,t in loss[first]),'topform':all(not readers[w] for w in ands if w not in dirty),'every_and_positive_on_edge':all(values[w]&positive for w in ands),'all_gates_live':len(live)==len(gates)}
Path(a.out).write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
