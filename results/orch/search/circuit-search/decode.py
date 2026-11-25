import json,sys
from pathlib import Path
meta=json.loads(Path(sys.argv[1]).read_text())
lines=Path(sys.argv[2]).read_text().splitlines()
v={int(w) for line in lines if line.startswith('v ') for w in line.split()[1:] if int(w)>0}
if not v:raise SystemExit('no SAT model')
gates=[]
for s in meta['structure']:
 a=next(i for i,x in enumerate(s['left']) if x in v)
 b=next(i for i,x in enumerate(s['right']) if x in v)
 gates.append(('or' if s['op'] in v else 'and',a,b))
edges=meta.get('edges',[(0,7),(0,8),(0,10),(1,7),(1,9),(1,13),(2,8),(2,12),(2,13),(3,7),(3,11),(3,12),(4,10),(4,11),(4,13),(5,9),(5,10),(5,12),(6,8),(6,9),(6,11)])
ninputs=meta.get('ninputs',14)
for m in range(1<<ninputs):
 w=[(m>>i)&1 for i in range(ninputs)]
 for op,a,b in gates:w.append(w[a]|w[b] if op=='or' else w[a]&w[b])
 want=any((m>>a)&(m>>b)&1 for a,b in edges)
 if w[-1]!=want:raise SystemExit(f'BAD input {m}: got {w[-1]}, expected {want}')
print('VERIFIED all',1<<ninputs,'inputs')
print(json.dumps(gates,indent=2))
print('packed:',[a+64*b+(4096 if op=='or' else 0) for op,a,b in gates])
