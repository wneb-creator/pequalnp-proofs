from pathlib import Path
from itertools import combinations
import argparse,json
p=argparse.ArgumentParser()
p.add_argument('--side',type=int,default=4)
p.add_argument('--ors',type=int,default=4)
p.add_argument('--min-edges',type=int,default=6)
p.add_argument('--allow-c4',action='store_true')
p.add_argument('--stem',required=True)
a=p.parse_args()
source=Path(__file__).with_name('or_free_and_sat.py').read_text()
scope={}
exec('class CNF:'+source.split('class CNF:',1)[1].split('n=a.n;k=a.ors',1)[0],scope)
CNF=scope['CNF']
m=a.side;n=2*m;k=a.ors;c=CNF()
assert a.min_edges>m
edges=[(i,m+j) for i in range(m) for j in range(m)]
evs=[c.var() for e in edges]
edgevar=dict(zip(edges,evs))
if not a.allow_c4:
 for u,v in combinations(range(m),2):
  for x,y in combinations(range(m,n),2):
   c.add(-edgevar[(u,x)],-edgevar[(u,y)],-edgevar[(v,x)],-edgevar[(v,y)])
counts=[1]+[-1]*a.min_edges
for v in evs:
 counts=[1]+[c.or_many([counts[j],c.and_(counts[j-1],v)]) for j in range(1,a.min_edges+1)]
c.add(counts[-1])
original_rows=list(range(1<<n))
rows=[((1<<n)-1)^s for s in original_rows]
selectors=[]
vals=[[1 if s>>u&1 else -1 for s in rows] for u in range(n)]
for g in range(k):
 ss=[[c.var() for u in range(n+g)] for side in range(2)]
 selectors.append(ss)
 for side in ss:c.add(*side)
 for u in range(n+g):
  c.add(-ss[0][u],-ss[1][u])
  c.add(-ss[1][u],*ss[0][:u])
 vv=[]
 for r,s in enumerate(rows):
  ports=[c.or_many([c.and_(ss[side][u],vals[u][r]) for u in range(n+g)]) for side in range(2)]
  vv.append(c.and_(*ports))
 vals.append(vv)
outs=[c.var() for g in range(k)]
c.add(*outs)
for r,x in enumerate(original_rows):
 output=c.or_many([c.and_(outs[g],vals[n+g][r]) for g in range(k)])
 graphf=c.or_many([v for (i,j),v in zip(edges,evs) if x>>i&1 and x>>j&1])
 c.add(output,graphf)
 c.add(-output,-graphf)
stem=Path(a.stem)
stem.with_suffix('.cnf').write_text('p cnf '+str(c.n)+' '+str(len(c.clauses))+'\n'+'\n'.join(' '.join(map(str,cl))+' 0' for cl in c.clauses)+'\n')
stem.with_suffix('.meta.json').write_text(json.dumps(dict(n=n,k=k,side=m,min_edges=a.min_edges,allow_c4=a.allow_c4,edges=edges,edgevars=evs,original_rows=original_rows,rows=rows,selectors=selectors,outs=outs,dual=True,disjoint=True),indent=2)+'\n')
print(json.dumps(dict(variables=c.n,clauses=len(c.clauses),rows=len(rows),n=n,ors=k,min_edges=a.min_edges,allow_c4=a.allow_c4)))
