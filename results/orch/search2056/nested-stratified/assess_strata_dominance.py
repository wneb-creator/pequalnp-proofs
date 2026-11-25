import argparse
import datetime
import hashlib
import json
from pathlib import Path

parser=argparse.ArgumentParser()
for name in ('analysis','case','source','output'):parser.add_argument('--'+name,required=True,type=Path)
args=parser.parse_args()
case=json.loads(args.case.read_text())[0]
rows=case['positive']+case['negative'];n=case['ninputs']
positive=(1<<len(case['positive']))-1;mask=(1<<len(rows))-1;negative=mask^positive
analysis=json.loads(args.analysis.read_text())
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_sha256':hashlib.sha256(args.source.read_bytes()).hexdigest(),'case_sha256':hashlib.sha256(args.case.read_bytes()).hexdigest(),'dominator_scope':'all earlier inputs and gates, including dead wires; fixed63-slot budget','criterion':'P_w subset P_a and N_a subset N_w','status':analysis['status'],'bests':[]}
for rec in analysis['best']:
 gates=rec['gates'];values=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
 for j,(op,a,b) in enumerate(gates):
  if op not in (0,1) or not 0<=a<n+j or not 0<=b<n+j:raise ValueError('Invalid circuit')
  values.append(values[a]|values[b] if op else values[a]&values[b])
 live={n+len(gates)-1}
 for j in reversed(range(len(gates))):
  if n+j in live:live.update(gates[j][1:])
 shared={entry['wire'] for entry in rec['computed_shared_dirty_ands']};dominance=[]
 for j,g in enumerate(gates):
  w=n+j
  if w not in live:continue
  for earlier in range(w):
   if not((values[w]&positive)&~values[earlier]) and not((values[earlier]&negative)&~values[w]):
    dominance.append({'wire':w,'gate':g,'earlier_dominator':earlier,'dominator_live_or_input':earlier<n or earlier in live,'shared_dirty_gate':w in shared});break
 raw=((values[-1]^positive)&mask).bit_count();fp=(values[-1]&negative).bit_count()
 result['bests'].append({'mode':rec['mode'],'raw':raw,'fp':fp,'analysis_raw':rec['raw'],'shared_dirty_ands':len(shared),'live_gates':sum(w>=n for w in live),'dominated_live_gates':dominance,'inputs':n,'output':n+len(gates)-1,'gates':gates})
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'utc':result['utc'],'status':result['status'],'bests':[{k:r[k] for k in ('mode','raw','fp','shared_dirty_ands','live_gates','dominated_live_gates')} for r in result['bests']]}))
