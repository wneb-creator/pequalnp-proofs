"""Independent A6 data and phase audit; no SAT or OR-cost claim."""
import json,hashlib
from pathlib import Path
HERE=Path(__file__).resolve().parent
SRC=HERE.parent/'lean_baseline'/'sat'
data=json.loads((SRC/'and_skeleton_six_data.json').read_text())
assert data['inputs']==17
mapping=data['input_original'];assert len(mapping)==len(set(mapping))==17
points=[x for x in mapping if x<13];lines=[x for x in mapping if x>=13]
assert points==[0,1,2,3,6,7]
expected_edges={(mapping.index(p),mapping.index(l)) for p in points for l in lines if (p+l-13)%13 in {0,1,3,9}}
assert set(map(tuple,data['edges']))==expected_edges and len(expected_edges)==24
N=1<<17
cols=[int(('1'*(1<<i)+'0'*(1<<i))*(N//(2<<i)),2) for i in range(17)]
target=0
for a,b in expected_edges:target|=cols[a]&cols[b]
maximal=[]
for mask in range(N):
 if target>>mask&1:continue
 if all(target>>(mask|(1<<i))&1 for i in range(17) if not mask>>i&1):maximal.append(mask)
assert len(maximal)==52
assert {(x['mask'],x['label']) for x in data['tests']}=={((1<<a)|(1<<b),1) for a,b in expected_edges}|{(x,0) for x in maximal}
reports=[]
for name in ['and_skeleton_six_baseline6.json','and_skeleton_six_filtered6_phase.json']:
 obj=json.loads((SRC/name).read_text());assert obj['inputs']==17 and obj['input_original']==mapping
 assert set(map(tuple,obj['edges']))==expected_edges and len(obj['and_gates'])==obj['and_count']==6
 assert obj['total_gate_bound_established'] is False
 values=cols[:]
 for i,g in enumerate(obj['and_gates']):
  sides=[]
  for side in ['left','right']:
   assert g[side]==sorted(set(g[side])) and all(0<=x<17+i for x in g[side])
   value=0
   for x in g[side]:value|=values[x]
   sides.append(value)
  values.append(sides[0]&sides[1])
 assert obj['output']==sorted(set(obj['output'])) and all(0<=x<23 for x in obj['output'])
 actual=0
 for x in obj['output']:actual|=values[x]
 expected=target
 for a,b in obj.get('extra_edges',[]):expected|=cols[a]&cols[b]
 assert actual==expected
 false=(actual&~target).bit_count();assert target&~actual==0
 if 'full_target_errors' in obj:assert obj['full_target_errors']==false
 dirty=obj.get('dirty_input')
 if dirty is not None:
  assert dirty.bit_count()<=2 and not(actual>>dirty&1) and not(target>>dirty&1)
  assert any(v>>dirty&1 for v in values[17:])
 reports.append(dict(file=name,sha256=hashlib.sha256((SRC/name).read_bytes()).hexdigest(),false_assignments=false,missing_assignments=0,dirty_input=dirty,exact_target=actual==target))
report=dict(status='APPROVED computational packet and phase; no OR-cost or Lean lower-bound conclusion',raw_inputs=17,required_edges=24,maximal_negatives=52,raw_assignments_per_phase=N,data_sha256=hashlib.sha256((SRC/'and_skeleton_six_data.json').read_bytes()).hexdigest(),phases=reports)
(HERE/'and-skeleton-six-independent-review.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
