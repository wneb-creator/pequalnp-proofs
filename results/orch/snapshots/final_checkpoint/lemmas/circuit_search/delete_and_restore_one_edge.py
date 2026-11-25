"""Finite false-deletion/one-edge restoration on approximate circuit archives."""
import json,runpy,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
ALG=HERE.parent/'algebra_strategy'
h=runpy.run_path(str(ALG/'assemble_five_owner.py'));compact=h['compact_core']
puncture=json.loads((HERE.parent/'status_review'/'punctured-four-arc.json').read_text())
summary=[]
for tag,casefile,poolfile,budget in [('punctured',HERE/'punctured-four-adapter.json',HERE/'puncturedfinal-pool.json',15),('five',ALG/'five-owner-joint-packet.json',HERE/'joint-five-essential-final-pool.json',23),('global',HERE/'full-case.json',HERE/'globalthreefinal-pool.json',63)]:
 case=json.loads(casefile.read_text());case=case[0] if isinstance(case,list) else case;n=case.get('inputs',26);raw=case.get('raw_inputs',26);tests=case['tests'];target=sum(y<<j for j,(_,y) in enumerate(tests));columns=[sum((m>>i&1)<<j for j,(m,_) in enumerate(tests)) for i in range(n)]
 pool=json.loads(poolfile.read_text());(HERE/f'{tag}-one-edge-repair-source.json').write_text(json.dumps(pool));improvements=[];considered=0
 def evaluate(gs):
  v=columns.copy()
  for op,a,b in gs:v.append(v[a]|v[b] if op else v[a]&v[b])
  return v
 def cost(gs,out=None):
  gs,out,_=compact(n,gs,out)
  if tag=='five':
   _,m=h['assemble_five'](case,gs,out);return m['core_gates']+m['prefix_extra_cost']
  if tag=='punctured':
   used={out}
   for i in range(len(gs)-1,-1,-1):
    if n+i in used:used.update(gs[i][1:])
   if any(len(set(group)&used)>1 for group in puncture['optional_groups']):return 10000
  return len(gs)
 for pi,item in enumerate(pool):
  gs=item['gates'];old=evaluate(gs);oldwrong=(old[-1]&~target).bit_count();oldcost=cost(gs)
  for k,(op,_,_) in enumerate(gs):
   if op:continue
   v=old.copy();v[n+k]=0
   for j in range(k+1,len(gs)):
    op,a,b=gs[j];v[n+j]=v[a]|v[b] if op else v[a]&v[b]
   missing=target&~v[-1]
   if missing.bit_count()>1:continue
   considered+=1;mapping=list(range(n));made=[];memo={}
   for j,(op,a,b) in enumerate(gs):
    if j==k:mapping.append(-1);continue
    a,b=mapping[a],mapping[b]
    if a<0 or b<0:mapping.append(max(a,b) if op else -1);continue
    if a==b:mapping.append(a);continue
    a,b=sorted((a,b));key=(op,a,b)
    if key not in memo:memo[key]=n+len(made);made.append([op,a,b])
    mapping.append(memo[key])
   output=mapping[-1]
   assert output>=0
   made,output,_=compact(n,made,output)
   restored=[]
   if missing:
    bit=(missing&-missing).bit_length()-1;mask=tests[bit][0]&((1<<raw)-1);ends=[i for i in range(raw) if mask>>i&1];assert len(ends)==2
    a,b=sorted(ends);edge=next((n+i for i,x in enumerate(made) if x[0]==0 and sorted(x[1:])==[a,b]),None)
    if edge is None:edge=n+len(made);made.append([0,a,b])
    made.append([1,output,edge]);output=n+len(made)-1;restored=ends
   made,output,_=compact(n,made,output);newcost=cost(made,output)
   if newcost>budget:continue
   new=evaluate(made)[output];assert new&target==target and not(new&~old[-1]);wrong=(new&~target).bit_count()
   if wrong<oldwrong or newcost<oldcost:
    improvements.append(dict(gates=made,output=output,source_index=pi,removed_and=k,restored_edge=restored,old_errors=oldwrong,errors=wrong,old_cost=oldcost,cost=newcost,and_count=sum(x[0]==0 for x in made)))
 improvements.sort(key=lambda x:(x['errors'],x['cost']))
 (HERE/f'{tag}-one-edge-repair-results.json').write_text(json.dumps(improvements))
 report=dict(case=tag,models=len(pool),eligible_deletions=considered,improvements=len(improvements),best_errors=improvements[0]['errors'] if improvements else None,best_cost=improvements[0]['cost'] if improvements else None,exact_models=sum(x['errors']==0 for x in improvements));summary.append(report);print(report,flush=True)
(HERE/'one-edge-repair-summary.json').write_text(json.dumps(summary,indent=2))
