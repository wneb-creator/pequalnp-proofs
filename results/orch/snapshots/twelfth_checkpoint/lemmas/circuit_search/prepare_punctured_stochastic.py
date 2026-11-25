"""Prepare fixed-compatible outside-prefix stochastic profile for punctured arc."""
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
case=json.loads((HERE.parent/'status_review'/'punctured-four-arc.json').read_text())
n,raw=case['available_inputs'],case['raw_inputs']
tests=[]
for mask,y in case['raw_tests']+[[1<<i,False] for i in range(raw)]:
 encoded=mask
 for i,s in enumerate(case['features']):
  if any(mask>>j&1 for j in s):encoded|=1<<(raw+i)
 tests.append([encoded,int(y)])
(HERE/'punctured-four-tests.txt').write_text(str(len(tests))+'\n'+''.join(f'{m} {y}\n' for m,y in tests))
groups=case['optional_groups'];lines=[str(len(groups))]
for group in groups:
 costs=[0 if mask.bit_count()<=1 else 16 for mask in range(1<<len(group))]
 lines += [str(len(group))+' '+' '.join(map(str,group)), ' '.join(map(str,costs))]
(HERE/'punctured-four-compatibility-tables.txt').write_text('\n'.join(lines)+'\n')
seeds=json.loads((HERE/'punctured-four-restricted-seeds-structured.json').read_text())
seeds.sort(key=lambda x:(not bool(x['structure']['suppressed_dirty_witness']),x['boundary_errors']))
(HERE/'punctured-four-stochastic-seeds.json').write_text(json.dumps(seeds))
(HERE/'punctured-four-stochastic-seeds.txt').write_text(str(len(seeds))+'\n'+''.join(str(len(x['gates']))+'\n'+'\n'.join(' '.join(map(str,g)) for g in x['gates'])+'\n' for x in seeds))
record=dict(inputs=n,raw_inputs=raw,gates=15,minimum_ands=5,tests=len(tests),positive_edges=len(case['edges']),maximal_negatives=len(case['maximal_negatives']),prefix_groups=groups,compatibility_scope='At most one optional prefix per outside triple; table value16 forbids conflicts, not an asserted minimum synthesis cost.',outside_gates=47,final_or=1,seeds=len(seeds),first_seed_errors=seeds[0]['boundary_errors'])
(HERE/'punctured-four-stochastic-profile.json').write_text(json.dumps(record,indent=2));print(record)
