import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-42/sat')
stars=[[4,8,9],[6,7,9],[5,6,8],[4,5,7]]
raw=[];terms=[]
for v,es in enumerate(stars):
 raw.append((True,es[0],es[1]));p=12+len(raw)
 raw.append((True,p,es[2]));p=12+len(raw)
 raw.append((False,v,p));terms.append(12+len(raw))
p=terms[0]
for q in terms[1:]:raw.append((True,p,q));p=12+len(raw)
# Canonical greedy topological ordering.
pending=list(enumerate(raw,13));mapping={i:i for i in range(13)};circ=[]
while pending:
 choices=[(max(mapping[a],mapping[b]),min(mapping[a],mapping[b]),o,i) for i,(o,a,b) in pending if a in mapping and b in mapping]
 b,a,o,i=min(choices)
 circ.append((o,a,b));mapping[i]=12+len(circ);pending=[(j,g) for j,g in pending if i!=j]
rows=json.loads((base/'rows-15.json').read_text());names=json.loads((base/'vars-15.json').read_text())
vs=[[bool(p>>i&1) for p,t in rows] for i in range(13)];assign={}
for k,(o,a,b) in enumerate(circ,13):
 for j in range(k-1):assign[f'a{k}_{j}']=j==a
 for j in range(1,k):assign[f'b{k}_{j}']=j==b
 assign[f'o{k}']=o
 out=[]
 for r,(av,bv) in enumerate(zip(vs[a],vs[b])):
  value=av or bv if o else av and bv
  assign[f'av{k}_{r}']=av;assign[f'bv{k}_{r}']=bv;assign[f'v{k}_{r}']=value;out.append(value)
 vs.append(out)
assignment={v:assign[k] for k,v in names.items()}
lines=(base/'circuit-15.cnf').read_text().splitlines()[1:]
failed=[]
for i,l in enumerate(lines):
 c=list(map(int,l.split()))[:-1]
 if not any(assignment[abs(x)]==(x>0) for x in c):failed.append((i,c))
print('circuit',circ,'output correct',vs[-1]==[bool(t) for p,t in rows],'failed',failed[:5],len(failed))
(base/'known15.json').write_text(json.dumps(circ))
