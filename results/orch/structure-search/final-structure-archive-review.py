from pathlib import Path
import json,itertools,hashlib
p=Path('/workspace/pequalnp-proofs/results/orch/structure-search')
geometry=json.loads((p/'k4-cofactor-caps-geometry.json').read_text())
pairs=list(itertools.combinations(range(4),2));edges={(v,4+i) for i,e in enumerate(pairs) for v in e}
assert len(geometry)==19
for row in geometry:
 removed=set(row['removed']);remaining=[e for e in edges if not(removed & set(e))]
 assert len(remaining)==row['remaining_edges']
 vertices=set(range(10))-removed;seen=set();components=[]
 for v in sorted(vertices):
  if v in seen:continue
  component={v};pending=[v];seen.add(v)
  while pending:
   u=pending.pop()
   for a,b in remaining:
    if u in [a,b]:
     w=b if u==a else a
     if w not in seen:seen.add(w);pending.append(w);component.add(w)
  components.append({'vertices':sorted(component),'edges':sum(set(e)<=component for e in remaining)})
 assert components==row['components']
 for mask in range(1<<10):
  vs={i for i in range(10) if mask>>i&1}
  assert sum(set(e)<=vs for e in remaining)<=len(vs)
 for a,b in itertools.combinations(range(10),2):
  common=[v for v in range(10) if (tuple(sorted((a,v))) in remaining or (a,v) in remaining or (v,a) in remaining) and (tuple(sorted((b,v))) in remaining or (b,v) in remaining or (v,b) in remaining)]
  assert len(common)<2
 assert row['remaining_OR_lower']==len(remaining)-1
 assert row['reader_union_cap']==10-row['remaining_OR_lower']
for name in ['k4inc-dual10','k4inc-dual10-capped-clique','c5-dual4-clique-control']:
 row=json.loads((p/(name+'.result.json')).read_text())
 cnf=(p/(name+'.cnf')).read_text().splitlines();header=next(x for x in cnf if x.startswith('p ')).split()
 clauses=[list(map(int,line.split()[:-1])) for line in cnf if line and line[0] not in 'cp']
 assert int(header[2])==row['variables'] and int(header[3])==row['clauses']==len(clauses)
 assert max(abs(v) for clause in clauses for v in clause)==row['variables']
 log=(p/(name+'.solver.stdout')).read_text().splitlines()
 if row['status']=='SAT':
  assignment={int(v) for line in log if line.startswith('v ') for v in line[2:].split() if int(v)!=0}
  assert all(any(v in assignment for v in clause) for clause in clauses)
  n=row['n']; es=row['edges']
  for mask in range(1<<n):
   wires=[bool(mask>>i&1) for i in range(n)]
   for j,(op,a,b) in enumerate(row['binary_circuit']):
    assert op in ['and','or'] and 0<=a<n+j and 0<=b<n+j
    wires.append(wires[a] and wires[b] if op=='and' else wires[a] or wires[b])
   assert wires[row['binary_output']]==any(mask>>a&1 and mask>>b&1 for a,b in es)
  assert row['binary_size']==8 and row['binary_and_count']==row['binary_or_count']==4
 else:
  assert row['status']=='UNKNOWN' and row['returncode']==0 and not any(x.startswith('s SAT') or x.startswith('s UNSAT') for x in log)
 for suffix in ['.solver.stderr','.driver.stderr']:assert (p/(name+suffix)).read_bytes()==b''
print(json.dumps({'verdict':'PASS for restricted/UNKNOWN search archive','geometry_cases':19,'unrestricted_status':'UNKNOWN','restricted_status':'UNKNOWN','clique_control':'SAT model satisfies all1045 clauses; 8-gate circuit verified on all32 inputs','capped_source_sha256':hashlib.sha256((p/'andcount_capped_sat.py').read_bytes()).hexdigest(),'claim_limit':'No satisfying K4 witness, no UNSAT verdict, no Lean lower-bound proof.'},indent=2))
