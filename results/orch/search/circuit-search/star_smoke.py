import json
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
neighbors=[[0,1,3],[0,2,6],[1,5,6],[0,4,5],[3,4,6],[2,3,5],[1,2,4]]
gates=[]
terms=[]
for center,ns in enumerate(neighbors,7):
 first=14+len(gates);gates.append(('or',ns[0],ns[1]))
 second=14+len(gates);gates.append(('or',ns[2],first))
 terms.append(14+len(gates));gates.append(('and',center,second))
out=terms[0]
for t in terms[1:]:
 gates.append(('or',out,t));out=13+len(gates)
old=gates;gates=[];mapping={i:i for i in range(14)}
pending=set(range(len(old)))
while pending:
 choices=[]
 for i in pending:
  op,a,b=old[i]
  if a in mapping and b in mapping:
   a,b=sorted([mapping[a],mapping[b]])
   choices.append(((a,b,op=='or'),i,(op,a,b)))
 _,i,g=min(choices)
 mapping[14+i]=14+len(gates);gates.append(g);pending.remove(i)
meta=json.loads((base/'heawood27.map.json').read_text())
assert len(gates)==meta['gates']==27
units=[]
for (op,a,b),s in zip(gates,meta['structure']):
 a,b=sorted([a,b]);units.extend([s['left'][a],s['right'][b],s['op'] if op=='or' else -s['op']])
src=(base/'heawood27.cnf').read_text().splitlines()
fields=src[0].split();fields[-1]=str(int(fields[-1])+len(units));src[0]=' '.join(fields)
src.extend(str(v)+' 0' for v in units)
(base/'star27.cnf').write_text('\n'.join(src)+'\n')
(base/'star27.json').write_text(json.dumps(gates))
print('Fixed canonical27gate star network for SAT smoke test')
