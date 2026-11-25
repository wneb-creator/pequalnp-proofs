import argparse,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('data');p.add_argument('log');p.add_argument('output');args=p.parse_args();d=json.loads(Path(args.data).read_text());rows=d['rows'];n=d.get('inputs',d.get('ninputs',len(d['points'])+len(d['lines'])));np=len(d['points']);E=len(d['edges']) if 'edges' in d else len(d['positive']);goal=(1<<E)-1;negative=((1<<len(rows))-1)^goal;initial=[sum(((r>>i)&1)<<k for k,r in enumerate(rows)) for i in range(n)];text=Path(args.log).read_text();rs=[]
for i,line in enumerate(text.splitlines()):
 if i==len(text.splitlines())-1 and not text.endswith('\n'):break
 rs.append(json.loads(line))
def next_and_consumers(gs, uses, n, start):
 todo=[start];seen=set();ends=set()
 while todo:
  wire=todo.pop()
  if wire in seen:continue
  seen.add(wire)
  for j in uses[wire]:
   if gs[j][0]==0:ends.add(j)
   else:todo.append(n+j)
 return sorted(ends)
assert next_and_consumers([(0,0,1),(1,2,0),(0,3,0),(0,3,1)], [{0,1,2},{0,3},{1},{2,3},set(),set()], 2, 2)==[2,3]
seen=set();results=[]
for ix,r in enumerate(rs):
 gs=r['gates'];out=r.get('output',n+len(gs)-1);key=(tuple(map(tuple,gs)),out)
 if key in seen:continue
 seen.add(key);vs=initial[:];P=[v&goal if i<np else 0 for i,v in enumerate(vs)];L=[v&goal if i>=np else 0 for i,v in enumerate(vs)];G=[0]*n;clean=[v&negative==0 for v in vs];uses=[set() for _ in range(n+len(gs))];ca=mo=dom=0
 for j,(op,a,b) in enumerate(gs):
  assert op in (0,1) and 0<=a<n+j and 0<=b<n+j
  v=vs[a]|vs[b] if op else vs[a]&vs[b];ca+=not op and(clean[a] or clean[b]);mo+=op and(clean[a]!=clean[b]);dom+=any((v&goal&~av)==0 and(av&negative&~v)==0 for av in vs);vs.append(v);clean.append(v&negative==0);P.append(P[a]|P[b] if op else 0);L.append(L[a]|L[b] if op else 0);G.append(G[a]|G[b] if op else(P[a]&L[b])|(L[a]&P[b]));uses[a].add(j);uses[b].add(j)
 assert vs[out]==goal
 results.append({'record':ix,'gates':len(gs),'AND':sum(op==0 for op,a,b in gs),'accepted_without_read1':(goal&~G[out]).bit_count(),'clean_AND':int(ca),'mixed_OR':int(mo),'dominated':int(dom),'shared_dirty_AND':[j for j,(op,a,b) in enumerate(gs) if not op and not clean[n+j] and len(uses[n+j])>=2],'dirty_AND_multi_next_AND':{str(j):next_and_consumers(gs,uses,n,n+j) for j,(op,a,b) in enumerate(gs) if not op and not clean[n+j] and len(next_and_consumers(gs,uses,n,n+j))>=2}})
summary={'unique_exact_networks':len(results),'sizes':sorted({r['gates'] for r in results}),'nonread1_networks':sum(r['accepted_without_read1']>0 for r in results),'networks_with_shared_dirty_AND':sum(bool(r['shared_dirty_AND']) for r in results),'networks_with_indirect_dirty_AND_reuse':sum(bool(r['dirty_AND_multi_next_AND']) for r in results),'results':results};Path(args.output).write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps({k:v for k,v in summary.items() if k!='results'}),flush=True)
