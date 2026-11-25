import json
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-94/plane-structure')
summary=[]
for name in ['fano-star7-control','c5-dual3-control','c5-dual4-control']:
 row=json.loads((p/(name+'.result.json')).read_text())
 output=(p/(name+'.solver.stdout')).read_text().splitlines()
 status=[x for x in output if x.startswith('s ')]
 assert status==['s SATISFIABLE' if row['status']=='SAT' else 's UNSATISFIABLE']
 for suffix in ['.driver.stderr','.solver.stderr']: assert (p/(name+suffix)).read_bytes()==b''
 if row['status']=='SAT':
  assignment={int(v) for line in output if line.startswith('v ') for v in line[2:].split() if int(v)!=0}
  assert not any(-v in assignment for v in assignment)
  clauses=[list(map(int,line.split()[:-1])) for line in (p/(name+'.cnf')).read_text().splitlines() if line and line[0] not in 'cp']
  assert all(any(v in assignment for v in clause) for clause in clauses)
  n=row['n']; edges=row['edges']; gates=row['binary_circuit']
  def primal(x):return any(x>>a&1 and x>>b&1 for a,b in edges)
  for mask in range(1<<n):
   ws=[bool(mask>>i&1) for i in range(n)]
   for j,(op,a,b) in enumerate(gates):
    assert op in ['and','or'] and 0<=a<n+j and 0<=b<n+j
    ws.append(ws[a] and ws[b] if op=='and' else ws[a] or ws[b])
   assert ws[row['binary_output']]==primal(mask)
   fs=[bool(mask>>i&1) for i in range(n)]
   for a,b in row['gates']:
    fs.append(any(fs[i] for i in a) and any(fs[i] for i in b))
   target=not primal(((1<<n)-1)^mask) if row['dual'] else primal(mask)
   assert any(fs[n+i] for i in row['output_gates'])==target
  assert row['binary_size']==len(gates)
  assert row['binary_and_count']==sum(op=='and' for op,a,b in gates)
  assert row['binary_or_count']==sum(op=='or' for op,a,b in gates)
 summary.append({k:row[k] for k in ['graph','dual','and_gates','status','returncode','binary_size','binary_and_count','binary_or_count','verified_assignments'] if k in row})
print(json.dumps({'review':'PASS','results':summary,'limits':'UNSAT is the SAT solver verdict, not a Lean certificate; intended singleton-rejecting scope enforced in source.'},indent=2))
