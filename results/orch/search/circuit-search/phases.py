import json,sys
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-70/circuit-search')
meta=json.loads(Path(sys.argv[1]).read_text())
autos=json.loads(Path('/tmp/oec/pequalnp-pilot-70/sat-review/verified_symmetry.json').read_text())['automorphisms']
neighbors=[[1,3],[0,2,6],[1,5,6],[0,4,5],[3,4,6],[2,3,5],[1,2,4]]
old=[];terms=[]
for center,ns in enumerate(neighbors,7):
 wire=ns[0]
 for v in ns[1:]:
  old.append(('or',wire,v));wire=13+len(old)
 terms.append(14+len(old));old.append(('and',center,wire))
out=terms[0]
for t in terms[1:]:
 old.append(('or',out,t));out=13+len(old)
assert len(old)==26
def normalize(p):
 mapping={i:p[i] for i in range(14)};pending=set(range(len(old)));gates=[]
 while pending:
  choices=[]
  for i in pending:
   op,a,b=old[i]
   if a in mapping and b in mapping:
    a,b=sorted([mapping[a],mapping[b]])
    choices.append(((a,b,op=='or'),i,(op,a,b)))
  _,i,g=min(choices)
  mapping[14+i]=14+len(gates);gates.append(g);pending.remove(i)
 return gates
def key(gs):return [(a,b,op=='or') for op,a,b in gs]
gates=min(map(normalize,autos),key=key)
rows=meta['rows'];values=[[bool((r>>i)&1) for r in rows] for i in range(14)]
phases=[]
for (op,a,b),s in zip(gates,meta['structure']):
 phases.extend(v if i==a else -v for i,v in enumerate(s['left']))
 phases.extend(v if i==b else -v for i,v in enumerate(s['right']))
 phases.append(s['op'] if op=='or' else -s['op'])
 y=[x|z if op=='or' else x&z for x,z in zip(values[a],values[b])]
 phases.extend(v if b else -v for v,b in zip(s['out'],y));values.append(y)
assert sum(x!=bool(i<21) for i,x in enumerate(values[-1]))==1
Path(sys.argv[2]).write_text('\n'.join(map(str,phases))+'\n')
(base/'near26.json').write_text(json.dumps(gates))
print('phase literals',len(phases),'prefix',gates[:2],'boundary mismatches1')
