from pathlib import Path
import json
p=Path('results/orch/lemmas');data=json.loads((p/'stochastic-p10-fourunit-classes.json').read_text());T=[11,69,98,49]
rows=[]
for cl in data['classes']:
 units=cl['canonical'];r=[sum(1<<j for j,m in enumerate(units) if m>>t&1) for t in range(7)]
 full=[i for i,s in enumerate(T) if any(s>>x&1 and r[x].bit_count()<=1 and sum(q>>x&1 for q in T)>=2 for x in range(7))]
 allowed=[]
 for v in range(16):
  forced=[i for i,s in enumerate(T) if any(s>>x&1 and r[x] and r[x]&v==r[x] for x in range(7))]
  if set(forced)&set(full):continue
  if len(forced)>1+v.bit_count():continue
  allowed.append(v)
 rows.append(dict(units=units,full_assigned_points=full,allowed_eligible_point_unit_masks=allowed))
r={'scope':'Additional necessary per-eligible-point residual-coordinate possibilities from proved three-slot-full, nonempty co-label and assigned_budget_extra. This is not a joint full-support existence test.','rows':rows}
(p/'stochastic-p10-fourunit-point-masks.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
