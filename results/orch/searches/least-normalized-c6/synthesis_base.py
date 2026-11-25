import argparse
import itertools
import json
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('mode',choices=['c6','fano','k4','k5','mk'])
parser.add_argument('gates',type=int)
parser.add_argument('--sym',action='store_true')
parser.add_argument('--orbit',action='store_true')
args=parser.parse_args()
if args.mode=='c6':
 p=l=3; edges=[(i,p+j) for i in range(p) for j in range(l) if i!=j]
elif args.mode=='mk':
 p=l=8; edges=[(i,p+j) for i in range(p) for j in range(l) if (j-i)%8 in [0,1,3]]
elif args.mode=='fano':
 p=l=7; edges=[(i,p+j) for i in range(p) for j in range(l) if (j-i)%7 in [0,1,3]]
else:
 p=4 if args.mode=='k4' else 5;l=p*(p-1)//2
 edges=[(v,p+j) for j,vs in enumerate(itertools.combinations(range(p),2)) for v in vs]
n=p+l
positive=[(1<<i)|(1<<j) for i,j in edges]
negative=[]
def independent(x):return all(not (x>>i&1 and x>>j&1) for i,j in edges)
for x in range(1<<n):
 if independent(x) and all(not independent(x|(1<<i)) for i in range(n) if not x>>i&1):negative.append(x)
xs=positive+negative
clauses=[]
variables=0
def var():
 global variables
 variables+=1;return variables
def clause(*xs):
 if True in [x for x in xs if type(x) is bool]:return
 out=[]
 for x in xs:
  if type(x) is bool:continue
  if -x in out:return
  if x not in out:out.append(x)
 clauses.append(out)
def neg(x):return not x if type(x) is bool else -x
def onehot(vs):
 clause(*vs)
 # Sequential at-most-one.
 prev=None
 for v in vs[:-1]:
  s=var();clause(-v,s)
  if prev is not None:clause(-prev,s);clause(-v,-prev)
  prev=s
 if prev is not None:clause(-vs[-1],-prev)
A=[];B=[];O=[];V=[]
for i in range(args.gates):
 a=[var() for _ in range(n+i)];b=[var() for _ in range(n+i)];o=var()
 onehot(a);onehot(b)
 for ai in range(n+i):
  for bi in range(ai+1):clause(-a[ai],-b[bi])
 va=[var() for _ in xs];vb=[var() for _ in xs];v=[var() for _ in xs]
 for t,x in enumerate(xs):
  for s in range(n+i):
   w=bool(x>>s&1) if s<n else V[s-n][t]
   clause(-a[s],-va[t],w);clause(-a[s],va[t],neg(w))
   clause(-b[s],-vb[t],w);clause(-b[s],vb[t],neg(w))
  # o false = AND, o true = OR.
  clause(o,-v[t],va[t]);clause(o,-v[t],vb[t]);clause(o,v[t],-va[t],-vb[t])
  clause(-o,v[t],-va[t]);clause(-o,v[t],-vb[t]);clause(-o,-v[t],va[t],vb[t])
 A.append(a);B.append(b);O.append(o);V.append(v)
for t in range(len(xs)):clause(V[-1][t] if t<len(positive) else -V[-1][t])
# Minimum circuits have no gates unused by every later gate.
for i in range(args.gates-1):clause(*[selectors[n+i] for j in range(i+1,args.gates) for selectors in [A[j],B[j]]])
if args.sym:
 for i in range(1,args.gates):
  bound=n+i-1
  dependency=B[i][bound]
  for ap in range(bound):
   for ac in range(ap):clause(dependency,-A[i-1][ap],-A[i][ac])
  for a in range(bound):
   for bp in range(a+1,bound):
    for bc in range(a+1,bp):clause(dependency,-A[i-1][a],-A[i][a],-B[i-1][bp],-B[i][bc])
    clause(dependency,-A[i-1][a],-A[i][a],-B[i-1][bp],-B[i][bp],-O[i-1],O[i])
if args.orbit:
 columns=[frozenset(i for i,j in edges if j==p+c) for c in range(l)]
 autos=[]
 for perm in itertools.permutations(range(p)):
  image=[frozenset(perm[i] for i in col) for col in columns]
  if all(col in columns for col in image):
   autos.append(list(perm)+[p+columns.index(col) for col in image])
 if p==l:
  if args.mode in ['fano','mk']:dual=[p+(-i)%p for i in range(p)]+[(-i)%p for i in range(p)]
  else:dual=list(range(p,p+l))+list(range(p))
  original=list(autos)
  autos.extend([[dual[i] for i in aut] for aut in original])
 edge_set={tuple(sorted(e)) for e in edges}
 assert all({tuple(sorted((aut[i],aut[j]))) for i,j in edges}==edge_set for aut in autos)
 reps={min(tuple(sorted((aut[a],aut[b]))) for aut in autos) for a,b in itertools.combinations(range(n),2)}
 for a,b in itertools.combinations(range(n),2):
  if (a,b) not in reps:clause(-A[0][a],-B[0][b])
 print('Verified automorphisms',len(autos),'first gate pair orbits',sorted(reps))
base=Path('/tmp/oec/pequalnp-pilot-86/read1-construction')/(args.mode+'-'+str(args.gates)+('-sym' if args.sym else '')+('-orbit' if args.orbit else ''))
with base.with_suffix('.cnf').open('w') as f:
 f.write(f'p cnf {variables} {len(clauses)}\n')
 for c in clauses:f.write(' '.join(map(str,c))+' 0\n')
base.with_suffix('.json').write_text(json.dumps(dict(n=n,p=p,l=l,edges=edges,tests=xs,positive=len(positive),A=A,B=B,O=O,V=V)))
print(args.mode,args.gates,'variables',variables,'clauses',len(clauses),'tests',len(xs),'files',base)
