"""Apply checked one-edge junk replacement to approximate archived circuits."""
import json,runpy
from pathlib import Path
HERE=Path(__file__).resolve().parent
ALG=HERE.parent/'algebra_strategy';h=runpy.run_path(str(ALG/'assemble_five_owner.py'));compact=h['compact_core']
summary=[]
for tag,casefile,poolfile in [('punctured',HERE/'punctured-four-adapter.json',HERE/'puncturedfinal-pool.json'),('five',ALG/'five-owner-joint-packet.json',HERE/'joint-five-essential-final-pool.json'),('global',HERE/'full-case.json',HERE/'globalthreefinal-pool.json')]:
 case=json.loads(casefile.read_text());case=case[0] if isinstance(case,list) else case;n=case.get('inputs',26);raw=case.get('raw_inputs',26);tests=case['tests'];target=sum(y<<j for j,(_,y) in enumerate(tests));columns=[sum((m>>i&1)<<j for j,(m,_) in enumerate(tests)) for i in range(n)];pool=json.loads(poolfile.read_text());(HERE/f'{tag}-in-place-source.json').write_text(json.dumps(pool));out=[]
 def evaluate(gs):
  v=columns.copy()
  for op,a,b in gs:v.append(v[a]|v[b] if op else v[a]&v[b])
  return v
 def erase(gs,k):
  mapping=list(range(n));made=[];memo={}
  for j,(op,a,b) in enumerate(gs):
   if j==k:mapping.append(-1);continue
   a,b=mapping[a],mapping[b]
   if a<0 or b<0:mapping.append(max(a,b) if op else -1);continue
   if a==b:mapping.append(a);continue
   a,b=sorted((a,b));key=(op,a,b)
   if key not in memo:memo[key]=n+len(made);made.append([op,a,b])
   mapping.append(memo[key])
  assert mapping[-1]>=0
  return compact(n,made,mapping[-1])[0]
 for index,item in enumerate(pool):
  gs=compact(n,item['gates'])[0];initial=evaluate(gs);old_errors=(initial[-1]&~target).bit_count();trace=[]
  for iteration in range(len(gs)+1):
   v=evaluate(gs);choice=None
   for k,(op,_,_) in enumerate(gs):
    if op or not(v[n+k]&~target):continue
    z=v.copy();z[n+k]=0
    for j in range(k+1,len(gs)):
     op,a,b=gs[j];z[n+j]=z[a]|z[b] if op else z[a]&z[b]
    missing=target&~z[-1]
    if missing.bit_count()>1:continue
    if not missing:
     candidate=erase(gs,k);edge=[]
    else:
     bit=(missing&-missing).bit_length()-1;mask=tests[bit][0]&((1<<raw)-1);edge=[i for i in range(raw) if mask>>i&1];assert len(edge)==2
     candidate=[g.copy() for g in gs];candidate[k]=[0,*edge];candidate=compact(n,candidate)[0]
    val=evaluate(candidate)[-1];assert val&target==target and not(val&~v[-1]);errors=(val&~target).bit_count()
    rank=(errors,len(candidate),k)
    if choice is None or rank<choice[0]:choice=(rank,candidate,edge)
   if choice is None:break
   rank,candidate,edge=choice;trace.append(dict(and_gate=rank[2],restored_edge=edge,errors=rank[0],gates=rank[1]));gs=candidate
  else:raise AssertionError('Repair did not terminate within original gate count')
  errors=(evaluate(gs)[-1]&~target).bit_count()
  if trace:
   assert len(gs)<=len(item['gates'])
   out.append(dict(gates=gs,source_index=index,old_errors=old_errors,errors=errors,old_gates=len(item['gates']),gate_count=len(gs),and_count=sum(g[0]==0 for g in gs),trace=trace))
 out.sort(key=lambda x:(x['errors'],x['gate_count']));(HERE/f'{tag}-in-place-repair-results.json').write_text(json.dumps(out));report=dict(case=tag,models=len(pool),repaired=len(out),best_errors=out[0]['errors'] if out else None,best_gates=out[0]['gate_count'] if out else None,exact=sum(x['errors']==0 for x in out));summary.append(report);print(report,flush=True)
(HERE/'in-place-repair-summary.json').write_text(json.dumps(summary,indent=2))
