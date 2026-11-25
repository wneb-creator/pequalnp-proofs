import json
from pathlib import Path
folder=Path(__file__).resolve().parent
ls=(folder/'gatecount-optimal-thirteen-base.txt').read_text().splitlines();n,k,r,want=map(int,ls[0].split())
raw=[tuple(map(int,l.split())) for l in ls[2:2+k]]
raw=[tuple(sorted(ab)) for ab in raw]
outmask=int(ls[2+k])
for suffix in ['', '-normalized']:
 stem=folder/f'gatecount-dual-and13{suffix}'
 meta=json.loads(stem.with_suffix('.json').read_text())
 vals=[[bool(x>>t&1) for t in range(r)] for x in meta['inputs']]
 sides=[]
 for j,(a,b) in enumerate(raw):
  ss=[[any(mask>>u&1 and vals[u][t] for u in range(n+j)) for t in range(r)] for mask in [a,b]]
  sides.append(ss);vals.append([ss[0][t] and ss[1][t] for t in range(r)])
 assigned={1:True}
 for label,i in meta['labels'].items():
  xs=label.split('_');tag=xs[0]
  if label=='true':v=True
  elif tag=='sel':j,b,u=map(int,xs[1:]);v=bool(raw[j][b]>>u&1)
  elif tag=='v':j,b,t,u=map(int,xs[1:]);v=bool(raw[j][b]>>u&1) and vals[u][t]
  elif tag=='side':j,b,t=map(int,xs[1:]);v=sides[j][b][t]
  elif tag=='gate':j,t=map(int,xs[1:]);v=vals[n+j][t]
  elif tag=='eq':j,u=map(int,xs[1:]);v=((raw[j][0]>>u)&1)==((raw[j][1]>>u)&1)
  elif tag=='prefix':j,u=map(int,xs[1:]);v=(raw[j][0]>>u)==(raw[j][1]>>u)
  elif tag=='out' and len(xs)==2:u=int(xs[1]);v=bool(outmask>>u&1)
  elif tag=='ov':t,u=map(int,xs[1:]);v=bool(outmask>>u&1) and vals[u][t]
  elif tag=='outval':t=int(xs[1]);v=any(outmask>>u&1 and vals[u][t] for u in range(n+k))
  elif tag=='left':j,t=map(int,xs[2:]);v=not sides[j][0][t] and sides[j][1][t]
  elif tag=='right':j,t=map(int,xs[2:]);v=sides[j][0][t] and not sides[j][1][t]
  else:raise ValueError(label)
  assigned[i]=v
 bad=[];count=0
 for line in stem.with_suffix('.cnf').read_text().splitlines():
  if line.startswith(('p','c')):continue
  lits=list(map(int,line.split()))[:-1];count+=1
  if not any(assigned[abs(l)]==(l>0) for l in lits):bad.append(count)
 print(stem.name,'clauses',count,'violated',len(bad),bad[:5])
 assert not bad
