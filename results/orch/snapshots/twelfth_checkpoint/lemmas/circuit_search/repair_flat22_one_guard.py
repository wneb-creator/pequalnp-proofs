"""Exhaustive one-AND insertion guarding any nonempty subset of one wire's uses."""
import itertools,json,runpy,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
ALG=HERE.parent/'algebra_strategy'
case=json.loads((ALG/'five-owner-joint-packet.json').read_text())[0]
helpers=runpy.run_path(str(ALG/'assemble_five_owner.py'))
compact,assemble=helpers['compact_core'],helpers['assemble_five']
original=json.loads((HERE/'joint-five-essential10-flat22-equivalent.json').read_text())
n=case['inputs'];gcount=len(original);assert gcount==22
columns=[sum((mask>>i&1)<<j for j,(mask,_) in enumerate(case['tests'])) for i in range(n)]
target=sum(label<<j for j,(_,label) in enumerate(case['tests']))
uses=[[] for _ in range(n+gcount)]
for i,(_,a,b) in enumerate(original):uses[a].append((i,1));uses[b].append((i,2))
uses[-1].append((gcount,0))
checked=positive_survivors=budget_survivors=0;best=100;best_model=None;exact=[];started=time.monotonic()
for wire,locations in enumerate(uses):
 for subsetmask in range(1,1<<len(locations)):
  selected={locations[j] for j in range(len(locations)) if subsetmask>>j&1}
  position=min(i for i,_ in selected)
  for guard in range(n+position):
   if guard==wire:continue
   checked+=1;candidate=[]
   def remap(x):return x+int(x>=n+position)
   for i,(op,a,b) in enumerate(original):
    if i==position:candidate.append([0,wire,guard])
    candidate.append([op,n+position if (i,1) in selected else remap(a),n+position if (i,2) in selected else remap(b)])
   if position==gcount:candidate.append([0,wire,guard])
   assert len(candidate)==23
   v=columns.copy()
   for i,(op,a,b) in enumerate(candidate):
    assert a<n+i and b<n+i
    v.append(v[a]|v[b] if op else v[a]&v[b])
   if v[-1]&target!=target:continue
   positive_survivors+=1;errors=(v[-1]&~target).bit_count()
   if errors>best:continue
   full,meta=assemble(case,candidate)
   if not meta['within_budget']:continue
   budget_survivors+=1
   if errors<best:
    best=errors;best_model=dict(gates=candidate,wire=wire,guard=guard,position=position,selected_uses=sorted(selected),boundary_errors=errors,assembly=meta)
    print('BEST',best,'checked',checked,'gate',position,'wire',wire,'guard',guard,flush=True)
   if errors==0:
    exact.append(dict(gates=candidate,full_gates=full,assembly=meta,wire=wire,guard=guard,selected_uses=sorted(selected)))
report=dict(scope='Every one-AND insertion over existing raw/free/paid wires, replacing any nonempty subset of one existing wire\'s operand/output uses with the guarded wire; topological order retained.',candidates=checked,positive_survivors=positive_survivors,budget_checked_survivors=budget_survivors,best_boundary_errors=best,exact_models=len(exact),elapsed_seconds=time.monotonic()-started)
(HERE/'flat22-one-guard-report.json').write_text(json.dumps(report,indent=2))
(HERE/'flat22-one-guard-best.json').write_text(json.dumps(best_model))
(HERE/'flat22-one-guard-exact.json').write_text(json.dumps(exact))
print(report,flush=True)
