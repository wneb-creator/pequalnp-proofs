import json
import argparse
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--log',required=True,type=Path)
parser.add_argument('--case',required=True,type=Path)
parser.add_argument('--output',required=True,type=Path)
args=parser.parse_args()
case=json.loads(args.case.read_text())[0]
rows=case['positive']+case['negative']
n=case['ninputs'];m=len(case['positive'])
target=(1<<m)-1;mask=(1<<len(rows))-1
inputs=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)]
records=[]
for text in args.log.read_text().splitlines():
 try: rec=json.loads(text)
 except json.JSONDecodeError: continue
 gates=rec['gates'];values=inputs[:]
 for j,(op,a,b) in enumerate(gates):
  assert op in (0,1) and 0<=a<n+j and 0<=b<n+j
  values.append(values[a]|values[b] if op else values[a]&values[b])
 raw=((values[-1]^target)&mask).bit_count()
 fp=(values[-1]&~target&mask).bit_count()
 assert raw==rec['raw'] and fp==rec['fp']
 live={n+len(gates)-1}
 for j in reversed(range(len(gates))):
  if n+j in live:live.update(gates[j][1:])
 rec['counts']={'gate_slots':len(gates),'live_gates':sum(w>=n for w in live),
  'and_gates':sum(g[0]==0 for g in gates),'or_gates':sum(g[0]==1 for g in gates),
  'materialized_copy_gates':sum(a==b for _,a,b in gates),
  'live_copy_gates':sum(a==b and n+j in live for j,(_,a,b) in enumerate(gates)),
  'atomic_edge_gates':sum(op==0 and a<n and b<n and ((1<<a)|(1<<b)) in case['positive'] for op,a,b in gates),
  'zero_positive_profile_gates':sum((v&target)==0 for v in values[n:]),
  'distinct_gate_functions':len(set(values[n:])),
  'false_negatives':raw-fp,'false_positives':fp}
 records.append(rec)
selected=[]
for mode in (0,1):
 choices=[r for r in records if r['mode']==mode]
 if choices:selected.append(min(choices,key=lambda r:(r['raw'],r['score'])))
result={'status':'no witness in log','record_count':len(records),'latest_seconds':max((r['seconds'] for r in records),default=0),'latest_iterations':max((r['iterations'] for r in records),default=0),'best':selected}
witnesses=[r for r in records if r['raw']==0]
if witnesses:
 result['status']='candidate needs exhaustive and Lean checking'
 result['witness']=witnesses[0]
 args.output.with_name('candidate.json').write_text(json.dumps(witnesses[0],indent=2)+'\n')
args.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('best','witness')}))
for r in selected:print(json.dumps({'mode':r['mode'],'score':r['score'],'raw':r['raw'],'seconds':r['seconds'],'counts':r['counts']}))
