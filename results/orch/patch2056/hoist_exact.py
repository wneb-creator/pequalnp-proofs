import argparse
import json
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('data');parser.add_argument('log');parser.add_argument('prefix')
args=parser.parse_args()
data=json.loads(Path(args.data).read_text())
n=data.get('ninputs',data.get('inputs'))
rows=data['rows'];edge_count=len(data.get('positive',data.get('edges',[])))
goal=(1<<edge_count)-1;negative=((1<<len(rows))-1)^goal
inputs=[sum(((row>>i)&1)<<j for j,row in enumerate(rows)) for i in range(n)]

def evaluate(gs,out):
 values=inputs[:]
 for j,(op,a,b) in enumerate(gs):
  assert op in (0,1) and 0<=a<n+j and 0<=b<n+j
  values.append(values[a]|values[b] if op else values[a]&values[b])
 assert 0<=out<len(values)
 return values

def compact(gs,out):
 live={out}
 for j in range(len(gs)-1,-1,-1):
  if n+j in live:live.update(gs[j][1:])
 mapping=list(range(n));result=[]
 for j,(op,a,b) in enumerate(gs):
  if n+j in live:
   mapping.append(n+len(result));result.append([op,mapping[a],mapping[b]])
  else:mapping.append(-1)
 return result,mapping[out]

def hoist(gs,out,wire):
 original=list(range(n));conditioned=list(range(n));built=[]
 def add(op,a,b):
  if op==0 and (a==-1 or b==-1):return -1
  if a==-1:return b
  if b==-1:return a
  if a==b:return a
  built.append([op,a,b]);return n+len(built)-1
 for j,(op,a,b) in enumerate(gs):
  if n+j<=wire:
   w=add(op,original[a],original[b]);original.append(w)
   conditioned.append(-1 if n+j==wire else w)
  else:
   original.append(-1)
   conditioned.append(add(op,conditioned[a],conditioned[b]))
 saved=original[wire];assert saved!=-1
 result=add(1,saved,conditioned[out]);assert result!=-1
 return compact(built,result)

def clean_violations(gs,out):
 values=evaluate(gs,out);clean=[not(v&negative) for v in values]
 return sum((not op and(clean[a] or clean[b])) or(op and clean[a]!=clean[b]) for op,a,b in gs)

text=Path(args.log).read_text();records=[];seen=set()
for i,line in enumerate(text.splitlines()):
 if i==len(text.splitlines())-1 and not text.endswith('\n'):break
 record=json.loads(line);gs=record['gates'];out=record.get('output',n+len(gs)-1)
 key=(tuple(map(tuple,gs)),out)
 if key in seen:continue
 seen.add(key);values=evaluate(gs,out);assert values[out]==goal
 raw_initial=len(gs);gs,out=compact(gs,out)
 initial=len(gs);moves=0
 while True:
  values=evaluate(gs,out)
  current=(len(gs),clean_violations(gs,out));chosen=None;score=current
  for wire in range(n,n+len(gs)):
   if values[wire]&negative:continue
   candidate,candidate_out=hoist(gs,out,wire)
   assert len(candidate)<=len(gs)
   assert evaluate(candidate,candidate_out)[candidate_out]==goal
   candidate_score=(len(candidate),clean_violations(candidate,candidate_out))
   if candidate_score<score:score=candidate_score;chosen=(candidate,candidate_out)
  if chosen is None:break
  gs,out=chosen;moves+=1
 records.append({'record':i,'raw_initial':raw_initial,'initial':initial,'size':len(gs),'violations':clean_violations(gs,out),'moves':moves,'output':out,'gates':gs})
prefix=Path(args.prefix)
prefix.with_suffix('.exact.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
best=min(records,key=lambda r:(r['size'],r['violations']))
prefix.with_suffix('.best.json').write_text(json.dumps(best,indent=2)+'\n')
report={'networks':len(records),'best_size':best['size'],'hit':best['size']<=63,'reduced':sum(r['size']<r['initial'] for r in records),'max_remaining_violations':max(r['violations'] for r in records)}
prefix.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
