"""Replay stochastic fixed-prefix fixtures against the exact reviewed assembler."""
import json,runpy,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
case=json.loads((HERE.parent/'status_review'/'punctured-four-arc.json').read_text())
compact=runpy.run_path(str(HERE.parent/'algebra_strategy'/'assemble_five_owner.py'))['compact_core']
assemble=runpy.run_path(str(HERE.parent/'reduction_analysis'/'punctured_mixed_assembler.py'))['assemble']
n,raw=case['available_inputs'],case['raw_inputs'];fixtures=json.loads((HERE/'punctured-stochastic-budget-fixtures.json').read_text());counts=[0,0]
for sample in fixtures:
 g,out,_=compact(n,sample['gates']);used={out}
 for i in range(len(g)-1,-1,-1):
  if n+i in used:used.update(g[i][1:])
 okay=len(g)<=15 and all(len(set(group)&used)<=1 for group in case['optional_groups'])
 assert sample['accepted']==okay
 if okay:
  full=assemble(case,g,out);assert full['full_size']<=63
 counts[int(okay)]+=1
columns=[int(('1'*(1<<i)+'0'*(1<<i))*(1<<(raw-i-1)),2) for i in range(raw)]
for s in case['features']:
 v=0
 for i in s:v|=columns[i]
 columns.append(v)
target=0
for a,b in case['edges']:target|=columns[a]&columns[b]
def evaluate(g):
 v=columns.copy()
 for i,(op,a,b) in enumerate(g):
  assert op in(0,1) and 0<=a<n+i and 0<=b<n+i
  v.append(v[a]|v[b] if op else v[a]&v[b])
 return v[-1]
seeds=json.loads((HERE/'punctured-four-stochastic-seeds.json').read_text())
for x in seeds:
 value=evaluate(x['gates']);assert target&~value==0
 assert (value&~target).bit_count()==x['false_positives']
 assert sum(value>>mask&1 for mask in case['maximal_negatives'])==x['boundary_errors']
 g,out,_=compact(n,x['gates']);assert assemble(case,g,out)['full_size']<=63
rewrite=json.loads((HERE/'punctured-stochastic-correlated-fixture.json').read_text())
assert evaluate(rewrite)==evaluate(seeds[0]['gates'])
report=dict(budget_fixtures=len(fixtures),rejected=counts[0],accepted=counts[1],seeds=len(seeds),assignments_per_seed=1<<raw,correlated_rewrite_assignments=1<<raw,minimum_boundary_errors=min(x['boundary_errors'] for x in seeds),source_sha256=hashlib.sha256((HERE/'search_feature_essential_suppressed_archive.cpp').read_bytes()).hexdigest(),scope='Compatible-prefix sufficient profile only; no exact witness.')
(HERE/'punctured-stochastic-validation.json').write_text(json.dumps(report,indent=2));print(report)
