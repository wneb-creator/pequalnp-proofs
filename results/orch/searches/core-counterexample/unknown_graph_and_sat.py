from pathlib import Path
from itertools import combinations
import argparse,json
parser=argparse.ArgumentParser();parser.add_argument('--side',type=int,default=4);parser.add_argument('--ands',type=int);parser.add_argument('--pin',action='store_true');parser.add_argument('--stem',required=True);args=parser.parse_args()
source=Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/and_free_or_sat.py').read_text();scope={};exec('class CNF:'+source.split('class CNF:',1)[1].split('n=14;k=',1)[0],scope);CNF=scope['CNF']
m=args.side;n=2*m;k=m-1 if args.ands is None else args.ands;c=CNF();edges=[(a,m+b) for a in range(m) for b in range(m)];edgevars=[c.var() for _ in edges];gvar={(a,b):v for (a,b),v in zip(edges,edgevars)}
for a in range(m):c.add(gvar[a,m+a])
for a,b in combinations(range(m),2):
 for x,y in combinations(range(m,n),2):c.add(-gvar[a,x],-gvar[a,y],-gvar[b,x],-gvar[b,y])
rows=list(range(1<<n));selectors=[];vals=[[1 if s>>p&1 else -1 for s in rows] for p in range(n)]
for g in range(k):
 ss=[[c.var() for _ in range(n+g)] for _ in range(2)];selectors.append(ss)
 for side in ss:c.add(*side)
 vv=[]
 for r in range(len(rows)):
  ports=[c.or_many([c.and_(ss[side][a],vals[a][r]) for a in range(n+g)]) for side in range(2)]
  vv.append(c.and_(*ports))
 vals.append(vv)
outs=[c.var() for _ in range(k)];c.add(*outs);positive=[(a,m+a) for a in range(m)];posrows={(1<<a)|(1<<b) for a,b in positive}
for r,s in enumerate(rows):
 output=c.or_many([c.and_(outs[g],vals[n+g][r]) for g in range(k)])
 c.add(-output,*(v for (a,b),v in zip(edges,edgevars) if s>>a&1 and s>>b&1))
 if s in posrows:c.add(output)
for ss in selectors:
 prefix=1
 for a,(l,r) in enumerate(zip(*ss)):
  c.add(-prefix,l,-r)
  if a+1<len(ss[0]):prefix=c.and_(prefix,c.or_many([c.and_(l,r),c.and_(-l,-r)]))
for g in range(k-1):
 ss,tt=selectors[g],selectors[g+1]
 for a in range(n+g):
  upper=c.or_many([tt[b][v] for b in range(2) for v in range(a,n+g+1)])
  for b in range(2):c.add(-ss[b][a],upper)
for g in range(k):c.add(outs[g],*(selectors[h][b][n+g] for h in range(g+1,k) for b in range(2)))
if args.pin:
 assert k==m
 for (a,b),v in zip(edges,edgevars):c.add(v if b==m+a else -v)
 for g,ss in enumerate(selectors):
  for side in range(2):
   for a,v in enumerate(ss[side]):c.add(v if a==(g if side==0 else m+g) else -v)
 for v in outs:c.add(v)
stem=Path(args.stem);stem.with_suffix('.cnf').write_text('p cnf '+str(c.n)+' '+str(len(c.clauses))+'\n'+'\n'.join(' '.join(map(str,cl))+' 0' for cl in c.clauses)+'\n');stem.with_suffix('.meta.json').write_text(json.dumps(dict(n=n,left=m,k=k,edges=edges,edgevars=edgevars,rows=rows,positive=positive,selectors=selectors,outs=outs),indent=2));print(json.dumps(dict(variables=c.n,clauses=len(c.clauses),rows=len(rows),side=m,ands=k,pin=args.pin)))
