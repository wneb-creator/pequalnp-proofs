from pathlib import Path
import sys,json,argparse
parser=argparse.ArgumentParser();parser.add_argument('--ands',type=int,default=6);parser.add_argument('--mode',choices=['exact','matching'],default='exact');parser.add_argument('--pin',action='store_true');parser.add_argument('--ordered',action='store_true');parser.add_argument('--cycle-side',type=int);parser.add_argument('--stem',required=True);args=parser.parse_args()
class CNF:
 def __init__(self):self.n=1;self.clauses=[[1]]
 def var(self):self.n+=1;return self.n
 def add(self,*lits):
  if 1 in lits:return
  ss=set(lits)-{-1}
  if any(-v in ss for v in ss):return
  self.clauses.append(sorted(ss,key=lambda x:(abs(x),x)))
 def and_(self,a,b):
  if a==1:return b
  if b==1:return a
  if a==-1 or b==-1:return -1
  if a==b:return a
  z=self.var();self.add(-a,-b,z);self.add(a,-z);self.add(b,-z);return z
 def or_many(self,terms):
  terms=set(terms)-{-1}
  if 1 in terms:return 1
  if not terms:return -1
  if len(terms)==1:return next(iter(terms))
  z=self.var();self.add(-z,*terms)
  for t in terms:self.add(-t,z)
  return z
m=args.cycle_side or 7;n=2*m;k=args.ands
edges=([(p,m+l) for p in range(m) for l in range(m) if l in [p,(p-1)%m]] if args.cycle_side else [(p,7+l) for p in range(7) for l in range(7) if (p-l)%7 in [0,1,3]])
adj=[set() for _ in range(n)]
for a,b in edges:adj[a].add(b);adj[b].add(a)
mis=[s for s in range(1<<n) if not any(s>>a&1 and s>>b&1 for a,b in edges) and all(s>>a&1 or any(s>>b&1 for b in adj[a]) for a in range(n))]
positive=edges if args.mode=='exact' else [(p,m+p) for p in range(m)]
rows=mis+[(1<<a)|(1<<b) for a,b in positive];c=CNF();selectors=[];vals=[[1 if s>>p&1 else -1 for s in rows] for p in range(n)]
for g in range(k):
 ss=[[c.var() for a in range(n+g)] for side in range(2)];selectors.append(ss)
 for side in range(2):c.add(*ss[side])
 for a in range(n+g):c.add(-ss[0][a],-ss[1][a])
 vv=[]
 for r,s in enumerate(rows):
  ports=[c.or_many([c.and_(ss[side][a],vals[a][r]) for a in range(n+g)]) for side in range(2)]
  vv.append(c.and_(*ports))
 vals.append(vv)
outs=[c.var() for g in range(k)];c.add(*outs)
for r,s in enumerate(rows):
 output=c.or_many([c.and_(outs[g],vals[n+g][r]) for g in range(k)])
 c.add(output if r>=len(mis) else -output)
if args.ordered:
 # Lexicographically order the interchangeable ports of each AND.
 for ss in selectors:
  prefix=1
  for a,(l,r) in enumerate(zip(*ss)):
   c.add(-prefix,l,-r)
   if a+1<len(ss[0]):
    equal=c.or_many([c.and_(l,r),c.and_(-l,-r)])
    prefix=c.and_(prefix,equal)
 # Greedily order available AND nodes by their largest selected source wire.
 for g in range(k-1):
  ss,tt=selectors[g],selectors[g+1]
  for a in range(n+g):
   upper=c.or_many([tt[b][v] for b in range(2) for v in range(a,n+g+1)])
   for b in range(2):c.add(-ss[b][a],upper)
 # Common-factor normalization may delete gates. Dead disjoint-input ANDs pad to k.
 # Do not require each gate to remain live in this normalized model.
if args.pin:
 assert k==m
 for g,ss in enumerate(selectors):
  for side in range(2):
   center=(sorted(range(m),key=lambda a:max(b for x,b in edges if x==a))[g] if args.ordered else g)
   chosen={center} if side==0 else {b for a,b in edges if a==center}
   for a,v in enumerate(ss[side]):c.add(v if a in chosen else -v)
 for v in outs:c.add(v)
stem=Path(args.stem);stem.with_suffix('.cnf').write_text('p cnf '+str(c.n)+' '+str(len(c.clauses))+'\n'+'\n'.join(' '.join(map(str,cl))+' 0' for cl in c.clauses)+'\n');stem.with_suffix('.meta.json').write_text(json.dumps(dict(n=n,k=k,edges=edges,mis=mis,rows=rows,positive=positive,selectors=selectors,outs=outs),indent=2));print(json.dumps(dict(variables=c.n,clauses=len(c.clauses),rows=len(rows),mode=args.mode,ands=k,pin=args.pin,ordered=args.ordered)),flush=True)
