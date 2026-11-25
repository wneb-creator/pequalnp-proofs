import argparse,json,itertools,time
from pathlib import Path
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix

p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=5);p.add_argument('--gates',type=int,default=6);p.add_argument('--seconds',type=int,default=300);p.add_argument('--unsafe-and',action='store_true');p.add_argument('--graph',choices=['cycle','theta233','petersen'],default='cycle');p.add_argument('--max-or',type=int);p.add_argument('--pair-only',action='store_true');a=p.parse_args()
n=a.n;s=a.gates
if a.graph=='theta233':
 n=7;edges=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
elif a.graph=='petersen':
 pairs=list(itertools.combinations(range(5),2));n=len(pairs)
 edges=[(i,j) for i in range(n) for j in range(i+1,n) if not set(pairs[i])&set(pairs[j])]
else:edges=[(i,(i+1)%n) for i in range(n)]
ind=[x for x in range(1<<n) if not any((x>>u)&1 and (x>>v)&1 for u,v in edges)]
maxind=[x for x in ind if all((x|(1<<v)) not in ind for v in range(n) if not ((x>>v)&1))]
if a.pair_only:
 edge_set={frozenset(e) for e in edges}
 samples=[((1<<u)|(1<<v),int(frozenset((u,v)) in edge_set)) for u,v in itertools.combinations(range(n),2)]+[(1<<v,0) for v in range(n)]+[(0,0)]
else:samples=[((1<<u)|(1<<v),1) for u,v in edges]+[(x,0) for x in maxind]
V={};vars=[]
def var(key):
 if key not in V: V[key]=len(vars);vars.append(key)
 return V[key]
rows=[];cols=[];dat=[];lb=[];ub=[]
def cons(terms,lo=-np.inf,hi=np.inf):
 row=len(lb)
 for key,v in terms.items(): rows.append(row);cols.append(var(key));dat.append(v)
 lb.append(lo);ub.append(hi)
def eq(terms,val):cons(terms,val,val)
for t in range(s):
 # op=0 AND, 1 OR
 op=('op',t);var(op)
 for side in [0,1]:
  choices={('sel',t,side,w):1 for w in range(n+t)}
  eq(choices,1)
 # symmetry: index operand A < B
 cons({**{('sel',t,0,w):w for w in range(n+t)},**{('sel',t,1,w):-w for w in range(n+t)}},hi=-1)
 for i,(x,target) in enumerate(samples):
  y=('val',t,i);var(y)
  for side in [0,1]:
   z=('arg',t,side,i);var(z)
   for w in range(n+t):
    sel=('sel',t,side,w)
    if w<n:
     bit=(x>>w)&1
     cons({z:1,sel:1},hi=bit+1)
     cons({z:1,sel:-1},lo=bit-1)
    else:
     val=('val',w-n,i)
     cons({z:1,val:-1,sel:1},hi=1)
     cons({z:1,val:-1,sel:-1},lo=-1)
  u=('arg',t,0,i);v=('arg',t,1,i)
  # AND constraints when op=0; OR constraints when op=1
  cons({y:1,u:-1,op:-1},hi=0)
  cons({y:1,v:-1,op:-1},hi=0)
  cons({y:1,u:-1,v:-1,op:1},lo=-1)
  cons({y:1,u:-1,op:-1},lo=-1)
  cons({y:1,v:-1,op:-1},lo=-1)
  cons({y:1,u:-1,v:-1,op:1},hi=1)
  if t==s-1: eq({y:1},target)
# Every non-output gate used later, which holds in a minimum circuit.
for t in range(s-1):
 cons({('sel',j,side,n+t):1 for j in range(t+1,s) for side in [0,1]},lo=1)
if a.max_or is not None:cons({('op',t):1 for t in range(s)},hi=a.max_or)
# Valid graph automorphisms remove equivalent choices for the first operand pair.
if a.graph=='cycle':
 eq({('sel',0,0,0):1},1)
 eq({('sel',0,1,w):1 for w in range(1,n//2+1)},1)
elif a.graph=='petersen':
 # Kneser(5,2) is transitive on edges and on distinct nonedges.
 eq({('sel',0,0,0):1},1)
 eq({('sel',0,1,w):1 for w in [1,7]},1)
elif a.graph=='theta233':
 edge_set={frozenset(e) for e in edges}
 degrees=[sum(i in e for e in edge_set) for i in range(n)]
 autos=[p for p in itertools.permutations(range(n))
        if all(degrees[i]==degrees[p[i]] for i in range(n))
        and {frozenset((p[u],p[v])) for u,v in edges}==edge_set]
 for u in range(n):
  for v in range(u+1,n):
   rep=min(tuple(sorted((p[u],p[v]))) for p in autos)
   if (u,v)!=rep:cons({('sel',0,0,u):1,('sel',0,1,v):1},hi=1)
if a.unsafe_and:
 bads={}
 for t in range(s-1):
  for i,(x,target) in enumerate(samples):
   if target:continue
   b=('bad',t,i);bads[b]=1
   cons({b:1,('op',t):1},hi=1)
   cons({b:1,('val',t,i):-1},hi=0)
 cons(bads,lo=1)
A=coo_matrix((np.array(dat,dtype=float),(np.array(rows,dtype=np.int32),np.array(cols,dtype=np.int32))),shape=(len(lb),len(vars))).tocsc()
print(json.dumps({'graph':a.graph,'n':n,'edges':edges,'gates':s,'max_or':a.max_or,'pair_only':a.pair_only,'samples':samples,'variables':len(vars),'constraints':len(lb)}),flush=True)
start=time.monotonic()
r=milp(np.zeros(len(vars)),integrality=np.ones(len(vars)),bounds=Bounds(np.zeros(len(vars)),np.ones(len(vars))),constraints=LinearConstraint(A,np.array(lb),np.array(ub)),options={'time_limit':a.seconds,'disp':True})
print('time',time.monotonic()-start,'status',r.status,'message',r.message,flush=True)
if r.x is not None:
 gates=[]
 for t in range(s):
  op='or' if r.x[V[('op',t)]]>.5 else 'and'
  ins=[next(w for w in range(n+t) if r.x[V[('sel',t,side,w)]]>.5) for side in [0,1]]
  gates.append((op,ins))
 for x in range(1<<n):
  vals=[bool((x>>i)&1) for i in range(n)]
  for op,(u,v) in gates: vals.append((vals[u] and vals[v]) if op=='and' else (vals[u] or vals[v]))
  if not a.pair_only or x.bit_count()<=2:
   assert vals[-1] == any(vals[u] and vals[v] for u,v in edges),(x,gates)
 if a.max_or is not None:assert sum(op=='or' for op,_ in gates)<=a.max_or
 print('WITNESS',gates,flush=True)
