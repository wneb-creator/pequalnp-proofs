from pathlib import Path
from itertools import combinations
import argparse,json
parser=argparse.ArgumentParser();parser.add_argument('--gates',type=int,default=8);parser.add_argument('--roots',type=int,default=1);parser.add_argument('--matching',type=int,default=4);parser.add_argument('--ordered',action='store_true');parser.add_argument('--control',choices=['p4','c4']);parser.add_argument('--stem',required=True);args=parser.parse_args()
source=Path('/tmp/oec/pequalnp-pilot-71/core-counterexample/and_free_or_sat.py').read_text();scope={};exec('class CNF:'+source.split('class CNF:',1)[1].split('n=14;k=',1)[0],scope);CNF=scope['CNF']
def and_many(c,terms):
 q=1
 for t in terms:q=c.and_(q,t)
 return q
def gate(c,op,a,b):
 z=c.var();c.add(-op,a,b,-z);c.add(-op,-a,z);c.add(-op,-b,z);c.add(op,-a,-b,z);c.add(op,a,-z);c.add(op,b,-z);return z
def atleast(c,xs,k):
 prev=[1]+[-1]*k
 for x in xs:
  cur=[1]
  for j in range(1,k+1):cur.append(c.or_many([prev[j],c.and_(x,prev[j-1])]))
  prev=cur
 c.add(prev[k])
n=8;m=4;g=args.gates;r=args.roots;p=args.matching;assert 1<=r<=2 and r<=g and 0<=p<=m
c=CNF();edges=[(a,m+b) for a in range(m) for b in range(m)];ev=[c.var() for _ in edges];gvar=dict(zip(edges,ev));rootidx=list(range(g-r,g));rows=list(range(1<<n))
for a in range(p):c.add(gvar[a,m+a])
if args.control!='c4':
 for a,b in combinations(range(m),2):
  for x,y in combinations(range(m,n),2):c.add(-gvar[a,x],-gvar[a,y],-gvar[b,x],-gvar[b,y])
fvals=[c.or_many([v for (a,b),v in zip(edges,ev) if S>>a&1 and S>>b&1]) for S in rows]
ops=[c.var() for _ in range(g)];sels=[[[c.var() for a in range(n+j)] for side in range(2)] for j in range(g)];vals=[[1 if S>>a&1 else -1 for S in rows] for a in range(n)];singles=[[1 if a==b else -1 for b in range(n)] for a in range(n)];imp=[-1]*n;ports=[];simport=[];import_=[]
for j,ss in enumerate(sels):
 for side in ss:
  c.add(*side)
  for a,b in combinations(side,2):c.add(-a,-b)
 for a in range(n+j):
  for b in range(a):c.add(-ss[0][a],-ss[1][b])
 if j in rootidx:c.add(-ops[j])
 if r==2 and j==g-1:
  for side in ss:c.add(-side[n+g-2])
 pv=[[c.or_many([c.and_(ss[side][a],vals[a][S]) for a in range(n+j)]) for S in rows] for side in range(2)];ports.append(pv)
 ps=[[c.or_many([c.and_(ss[side][a],singles[a][u]) for a in range(n+j)]) for u in range(n)] for side in range(2)];simport.append(ps)
 pi=[c.or_many([c.and_(ss[side][a],imp[a]) for a in range(n+j)]) for side in range(2)];import_.append(pi)
 vv=[gate(c,ops[j],pv[0][S],pv[1][S]) for S in rows];vals.append(vv)
 singles.append([c.and_(ops[j],c.or_many([ps[0][u],ps[1][u]])) for u in range(n)])
 im=and_many(c,[c.or_many([-vv[S],fvals[S]]) for S in rows]);imp.append(im)
 if j in rootidx:
  c.add(im);c.add(-pi[0],-pi[1]);bad=[]
  for a,b in edges:
   read1=c.or_many([c.and_(ps[0][a],ps[1][b]),c.and_(ps[0][b],ps[1][a])]);bad.append(c.and_(vv[(1<<a)|(1<<b)],-read1))
  c.add(*bad)
for j in range(g-r):c.add(*(sels[h][side][n+j] for h in range(j+1,g) for side in range(2)))
if args.ordered:
 for j in range(g-1):
  if j==g-r-1:continue
  for a in range(n+j):
   for b in range(a):c.add(-sels[j][1][a],-sels[j+1][1][b])
D=[c.or_many([vals[n+j][(1<<a)|(1<<b)] for j in rootidx]) for a,b in edges];cover=[c.var() for _ in range(n)]
for (a,b),e,d in zip(edges,ev,D):c.add(-d,e);c.add(-e,d,cover[a],cover[b])
threshold=g+r+(0 if args.control=='p4' else 1)-p+n;atleast(c,D+[-z for z in cover],threshold)
if args.control:
 assert g==4 and r==1 and p==4
 if args.control=='p4':
  graph={(0,4),(0,5),(1,5),(2,6),(3,7)};gates=[(0,1,5),(1,4,5),(1,0,8),(0,9,10)]
 else:
  graph={(0,4),(0,5),(1,4),(1,5),(2,6),(3,7)};gates=[(1,0,1),(1,4,5),(0,8,9),(0,8,10)]
 for e,v in zip(edges,ev):c.add(v if e in graph else -v)
 for j,(op,a,b) in enumerate(gates):
  c.add(ops[j] if op else -ops[j])
  for side,target in [(0,a),(1,b)]:
   for idx,v in enumerate(sels[j][side]):c.add(v if idx==target else -v)
 for a,v in enumerate(cover):c.add(v if a in [2,3] else -v)
stem=Path(args.stem);stem.with_suffix('.cnf').write_text('p cnf '+str(c.n)+' '+str(len(c.clauses))+'\n'+'\n'.join(' '.join(map(str,cl))+' 0' for cl in c.clauses)+'\n');stem.with_suffix('.meta.json').write_text(json.dumps(dict(n=n,left=m,g=g,roots=rootidx,matching=p,edges=edges,edgevars=ev,ops=ops,selectors=sels,D=D,cover=cover,control=args.control),indent=2));print(json.dumps(dict(variables=c.n,clauses=len(c.clauses),gates=g,roots=r,matching=p,control=args.control)))
