from pathlib import Path
import importlib.util,json
base=Path('/tmp/oec/pequalnp-pilot-152/gap-1884')
spec=importlib.util.spec_from_file_location('petersen_enc2',base/'petersen-enc2.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
model=json.loads((base/'petersen-ao-size20-canonical-model.json').read_text());desc=model['gates'];n=11;s=20
mapping={i:i for i in range(n)};todo=set(range(s));ordered=[]
opindex={'and':0,'or':1,'true':2,'not':3}
while todo:
 ready=[]
 for i in todo:
  op,a,b=desc[i]
  if a in mapping and b in mapping:
   aa,bb=sorted([mapping[a],mapping[b]]);ready.append(((aa,bb,opindex[op]),i,op,aa,bb))
 _,i,op,a,b=min(ready);mapping[n+i]=n+len(ordered);ordered.append([op,a,b]);todo.remove(i)
assert mapping[model['output']]==n+s-1
samples=mod.seed_samples();rows=[r+1024*(1-(r&1)) for r in samples]
clauses,width=mod.encode(n,s,rows)
def v(kd,j,a):return (kd*(s+1)+j)*width+a+1
assignment={};units=[]
def fix(atom,value):assignment[atom]=value;units.append([atom if value else -atom])
for j,(op,a,b) in enumerate(ordered):
 for o in range(4):fix(v(0,j,o),o==opindex[op])
 for e,k in [(1,a),(2,b)]:
  for t in range(n+j+1):fix(v(e,j,t),t==k)
 fix(v(7,j,0),False)
for k in range(n+s+1):fix(v(6,0,k),k==n+s-1)
for r in rows:
 values=[bool(r>>i&1) for i in range(n)]
 for j,(op,a,b) in enumerate(ordered):
  va,vb=values[a],values[b]
  value=va and vb if op=='and' else va or vb if op=='or' else not va
  values.append(value);assignment[v(3,j,r)]=value;assignment[v(4,j,r)]=va;assignment[v(5,j,r)]=vb
 assert values[-1]==mod.target(r)
assert all(any(assignment.get(abs(lit),False)==(lit>0) for lit in c) for c in clauses)
for x in range(1024):
 values=[bool(x>>i&1) for i in range(10)]+[not bool(x&1)]
 for op,a,b in ordered:values.append(values[a] and values[b] if op=='and' else values[a] or values[b] if op=='or' else not values[a])
 assert values[-1]==mod.target(x)
allclauses=clauses+units;maxvar=max(abs(l) for c in allclauses for l in c)
out=base/'petersen-enc2-control20-fixed.cnf'
with out.open('w') as f:
 f.write(f'p cnf {maxvar} {len(allclauses)}\n')
 for c in allclauses:f.write(' '.join(map(str,c))+' 0\n')
(base/'petersen-enc2-control20-model.json').write_text(json.dumps(dict(inputs=n,gates=ordered,output=n+s-1,free_unary='not'),indent=2))
print('EXACT_CNF_ASSIGNMENT_VERIFIED',len(clauses),'baseclauses',len(units),'fixedunits','FULL1024_VERIFIED','bytes',out.stat().st_size)
