from pathlib import Path
import json,argparse
p=argparse.ArgumentParser()
p.add_argument('--n',type=int,default=6)
p.add_argument('--ors',type=int,default=4)
p.add_argument('--pin',action='store_true')
p.add_argument('--stem',required=True)
a=p.parse_args()
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
n=a.n;k=a.ors
assert n>=4 and n%2==0
edges=[(i,(i+1)%n) for i in range(n)]
adj=[set() for _ in range(n)]
for u,v in edges:adj[u].add(v);adj[v].add(u)
mis=[s for s in range(1<<n) if not any(s>>u&1 and s>>v&1 for u,v in edges) and all(s>>u&1 or any(s>>v&1 for v in adj[u]) for u in range(n))]
original_rows=mis+[(1<<u)|(1<<v) for u,v in edges]
rows=[((1<<n)-1)^s for s in original_rows]
c=CNF();selectors=[]
vals=[[1 if s>>u&1 else -1 for s in rows] for u in range(n)]
for g in range(k):
 ss=[[c.var() for u in range(n+g)] for side in range(2)];selectors.append(ss)
 for side in range(2):c.add(*ss[side])
 vv=[]
 for r,s in enumerate(rows):
  ports=[c.or_many([c.and_(ss[side][u],vals[u][r]) for u in range(n+g)]) for side in range(2)]
  vv.append(c.and_(*ports))
 vals.append(vv)
outs=[c.var() for g in range(k)];c.add(*outs)
for r,s in enumerate(rows):
 output=c.or_many([c.and_(outs[g],vals[n+g][r]) for g in range(k)])
 c.add(output if r<len(mis) else -output)
if a.pin:
 q=n//2
 assert k==n-1
 chosen=[]
 for g in range(q):chosen.append([{(2*g-1)%n},{(2*g+1)%n}])
 for g in range(1,q):
  left={0,n} if g==1 else {n+q+g-2}
  chosen.append([left,{2*g,n+g}])
 for g,ss in enumerate(selectors):
  for side in range(2):
   for u,v in enumerate(ss[side]):c.add(v if u in chosen[g][side] else -v)
 for g,v in enumerate(outs):c.add(v if g==k-1 else -v)
stem=Path(a.stem)
stem.with_suffix('.cnf').write_text('p cnf '+str(c.n)+' '+str(len(c.clauses))+'\n'+'\n'.join(' '.join(map(str,cl))+' 0' for cl in c.clauses)+'\n')
stem.with_suffix('.meta.json').write_text(json.dumps(dict(n=n,k=k,edges=edges,mis=mis,original_rows=original_rows,rows=rows,selectors=selectors,outs=outs,dual=True,pin=a.pin),indent=2)+'\n')
print(json.dumps(dict(variables=c.n,clauses=len(c.clauses),rows=len(rows),n=n,ors=k,pin=a.pin)),flush=True)
