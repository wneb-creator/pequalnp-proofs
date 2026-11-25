import importlib.util,itertools,json,hashlib,time
from pathlib import Path
base=Path('/tmp/oec/pequalnp-pilot-81')
source=base/'sat-fano-orcount.py'
spec=importlib.util.spec_from_file_location('orcount_encoder',source)
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
start=time.time();cases=[];assignments=0
for n in range(5):
 for threshold in range(n+2):
  c=mod.CNF();lits=[c.var() for _ in range(n)]
  dp=mod.at_least(c,lits,threshold)
  counts=[0]*(1<<n)
  for mask in range(1<<c.n):
   assignments+=1
   if all(any(bool(mask>>(abs(l)-1)&1)==(l>0) for l in row) for row in c.cs):
    counts[mask&((1<<n)-1)]+=1
  expected=[int(mask.bit_count()>=threshold) for mask in range(1<<n)]
  assert counts==expected,(n,threshold,counts,expected)
  cases.append(dict(inputs=n,threshold=threshold,variables=c.n,clauses=len(c.cs),all_assignments=1<<c.n))
# Exhaustively inspect the recurrence's four Boolean variables independently.
for a,b,x,z in itertools.product((False,True),repeat=4):
 clauses=[not a or z,not b or not x or z,not z or a or b,not z or a or x]
 assert all(clauses)==(z==(a or (b and x)))
report=dict(verdict='PASS',scope='Exhaustive input+auxiliary assignments for all n=0..4 and thresholds0..n+1; each satisfying input has exactly one auxiliary model; independent recurrence truth table',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),cases=cases,total_assignments=assignments,elapsed=round(time.time()-start,3))
(base/'sat-threshold-dp-test.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
