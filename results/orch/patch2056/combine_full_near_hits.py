import json
import sys
from pathlib import Path

data=json.loads(Path(sys.argv[1]).read_text())
prefix=Path(sys.argv[2])
rows=data['rows'];n=data['ninputs'];edges=len(data['positive'])
positive=(1<<edges)-1;negative=((1<<len(rows))-1)^positive
inputs=[sum(((row>>i)&1)<<j for j,row in enumerate(rows)) for i in range(n)]
networks=[];seen=set()
for filename in sys.argv[3:]:
 for line in Path(filename).read_text().splitlines():
  record=json.loads(line);gs=record['gates'];out=record.get('output',n+len(gs)-1)
  key=(tuple(map(tuple,gs)),out)
  if key in seen:continue
  seen.add(key)
  values=inputs[:]
  for j,(op,a,b) in enumerate(gs):
   assert op in (0,1) and 0<=a<n+j and 0<=b<n+j
   values.append(values[a]|values[b] if op else values[a]&values[b])
  networks.append((gs,out,values[out]))

def combine(first,second,op):
 values=inputs[:];gates=[]
 def add(op,a,b):
  value=values[a]|values[b] if op else values[a]&values[b]
  for k,previous in enumerate(values):
   if not(value&positive&~previous) and not(previous&negative&~value):return k
  gates.append([op,a,b]);values.append(value);return len(values)-1
 def incorporate(network):
  gs,out,_=network;mapping=list(range(n))
  for op,a,b in gs:mapping.append(add(op,mapping[a],mapping[b]))
  return mapping[out]
 a=incorporate(first);b=incorporate(second);out=add(op,a,b)
 if values[out]!=positive:return None
 live={out}
 for j in range(len(gates)-1,-1,-1):
  if n+j in live:live.update(gates[j][1:])
 compact=[];mapping=list(range(n))
 for j,(op,a,b) in enumerate(gates):
  if n+j in live:
   mapping.append(n+len(compact));compact.append([op,mapping[a],mapping[b]])
  else:mapping.append(-1)
 output=mapping[out]
 check=inputs[:]
 for j,(op,a,b) in enumerate(compact):
  assert 0<=a<n+j and 0<=b<n+j
  check.append(check[a]|check[b] if op else check[a]&check[b])
 assert check[output]==positive
 return {'gates':compact,'output':output,'size':len(compact)}

correct=0;best=None;counts={}
for i,first in enumerate(networks):
 for j,second in enumerate(networks):
  for op in (0,1):
   result=combine(first,second,op)
   if result is None:continue
   correct+=1;counts[result['size']]=counts.get(result['size'],0)+1
   if best is None or result['size']<best['size']:
    best=result|{'first':i,'second':j,'op':op}
    prefix.with_suffix('.best.json').write_text(json.dumps(best,indent=2)+'\n')
report={'networks':len(networks),'correct_pairs':correct,'sizes':counts,'best_size':None if best is None else best['size'],'hit':best is not None and best['size']<=63}
prefix.with_suffix('.report.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
