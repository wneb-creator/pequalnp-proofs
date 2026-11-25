from pathlib import Path
from collections import Counter
import json,time

base=Path(__file__).resolve().parent
p=base/'signed17-joint-measurement';data=json.loads((p/'proof-states.json').read_text())
with (base.parent/'root-mono18-oredge-weak-proof'/'proof.jsonl').open() as f:autos=json.loads(next(f))['automorphisms']
inputs=[sum(1<<r for r in range(1024) if r>>j&1) for j in range(10)]
full=(1<<1024)-1
edges=((0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5))
target=0
for a,b in edges:target|=inputs[a]&inputs[b]
swaps=[]
for perm in autos:
 q=list(range(10));ss=[]
 for i in range(10):
  if q[i]!=perm[i]:
   j=q.index(perm[i]);assert j>i;q[i],q[j]=q[j],q[i]
   ss.append(((1<<j)-(1<<i),inputs[i]&(full^inputs[j])))
 swaps.append(ss)
def moved(w,g):
 for shift,mask in swaps[g]:
  t=((w>>shift)^w)&mask;w^=t^(t<<shift)
 return w
assert all(moved(target,g)==target for g in range(120))
started=time.monotonic();words=[int(w,16) for w in data['signals']]
moves=[[moved(w,g) for g in range(120)] for w in words]
classes={};records=[];counts=Counter();rootclasses={r:set() for r in ['edge','nonedge']}
for rec in data['states']:
 state=rec['state'];g=min(range(120),key=lambda g:tuple(sorted(moves[j][g] for j in state)))
 key=(rec['remaining'],tuple(sorted(moves[j][g] for j in state)))
 if key not in classes:
  classes[key]=len(classes);counts[rec['kind']]+=1
 identity=classes[key]
 records.append({'part':rec['part'],'node':rec['node'],'kind':rec['kind'],'class':identity,'automorphism':g})
 for r in rec['roots']:rootclasses[r].add(identity)
summary={'unique_proof_state_orbits':len(classes),'first_representative_kinds':dict(counts),
 'root_orbits':{r:len(s) for r,s in rootclasses.items()},'shared_orbits':len(set.intersection(*rootclasses.values())),
 'seconds':time.monotonic()-started,'scope':'Full120 graph automorphism census of exact truth pools at equal budgets. A final DAG still needs actual memo transport and acyclic dependency choices.'}
(p/'symmetry-classes.json').write_text(json.dumps({'summary':summary,'automorphisms':autos,'states':records},separators=(',',':'))+'\n')
(p/'symmetry-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
