import json,sys
from pathlib import Path
base=Path(sys.argv[1]);log=Path(sys.argv[2]).read_text();d=json.loads(base.with_suffix('.json').read_text());assert 's SATISFIABLE' in log
sat={int(w) for line in log.splitlines() if line.startswith('v ') for w in line.split()[1:] if int(w)>0}
n=d['n'];m=d['m'];E=d['E'];gates=[]
for i in range(m):
 a=[j for j,s in enumerate(d['left'][i]) if s in sat];b=[j for j,s in enumerate(d['right'][i]) if s in sat];assert len(a)==len(b)==1
 op='not' if d['nots'][i] in sat else 'or' if d['ors'][i] in sat else 'and'
 gates.append((op,[a[0]] if op=='not' else [a[0],b[0]]))
o=[i for i,s in enumerate(d['outputs']) if s in sat];assert len(o)==1;output=n+o[0]
assert sum(op=='not' for op,ins in gates)<=1
if d['kind']=='mono':assert all(op!='not' for op,ins in gates)
if d['kind']=='one_not':assert sum(op=='not' for op,ins in gates)==1
for x in range(1<<n):
 w=[bool(x>>a&1) for a in range(n)]
 for i,(op,ins) in enumerate(gates):
  assert all(j<n+i for j in ins)
  v=not w[ins[0]] if op=='not' else w[ins[0]] or w[ins[1]] if op=='or' else w[ins[0]] and w[ins[1]]
  w.append(v);assert v==(d['vals'][i][x] in sat)
 target=any(bool(x>>a&1) and bool(x>>b&1) for a,b in E)
 assert w[output]==target
print('Verified all',1<<n,'inputs; gates',m,'NOTs',sum(op=='not' for op,ins in gates),'output',output)
for i,g in enumerate(gates):print(n+i,g)
base.with_suffix('.circuit.json').write_text(json.dumps(dict(n=n,E=E,gates=gates,output=output),indent=1)+'\n')
