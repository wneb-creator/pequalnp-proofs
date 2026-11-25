import argparse
import json
import re
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('log')
p.add_argument('output')
a=p.parse_args()
lines=Path(a.log).read_text().splitlines()
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
records=[]
for i,line in enumerate(lines):
 if not line.startswith('steps='):continue
 header=re.search(r'wrong=(\d+) score=(\d+) nots=(\d+)',line)
 assert header is not None
 gates=[]
 for j in range(19):
  wire,op,left,right=map(int,lines[i+1+j].split())
  assert wire==10+j and 0<=op<=2 and 0<=left<wire and 0<=right<wire
  gates.append([op,left,right])
 bad=[]
 for r in range(1024):
  w=[bool(r>>j&1) for j in range(10)]
  for op,left,right in gates:w.append(w[left]&w[right] if op==0 else w[left]|w[right] if op==1 else not w[left])
  desired=any((r>>u&1) and (r>>v&1) for u,v in edges)
  if w[28]!=desired:bad.append(r)
 not_count=sum(op==2 for op,_,_ in gates)
 assert len(bad)==int(header[1]) and not_count==int(header[3])
 live=set()
 def visit(k):
  if k<10 or k in live:return
  live.add(k)
  op,u,v=gates[k-10];visit(u)
  if op!=2:visit(v)
 visit(28)
 records.append({'header':line,'gates':gates,'output':28,'wrong':len(bad),'bad_rows':bad,'not_count':not_count,'live_not_count':sum(gates[k-10][0]==2 for k in live)})
assert records
out={'log':a.log,'checked_records':len(records),'best_any':min(records,key=lambda r:r['wrong'])}
neg=[r for r in records if r['not_count']]
if neg:out['best_with_not']=min(neg,key=lambda r:r['wrong'])
Path(a.output).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:({'wrong':v['wrong'],'not_count':v['not_count'],'live_not_count':v['live_not_count']} if isinstance(v,dict) else v) for k,v in out.items()},indent=2))
