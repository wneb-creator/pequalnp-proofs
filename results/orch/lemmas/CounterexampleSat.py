import argparse,itertools,time,signal,json
from sympy.logic.algorithms.dpll2 import SATSolver
p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=5);p.add_argument('--gates',type=int,default=7);p.add_argument('--seconds',type=int,default=120);p.add_argument('--unsafe-and',action='store_true');a=p.parse_args()
n=a.n;s=a.gates;edges=[(i,(i+1)%n) for i in range(n)]
ind=[x for x in range(1<<n) if not any((x>>u)&1 and (x>>v)&1 for u,v in edges)]
maxind=[x for x in ind if all((x|(1<<v)) not in ind for v in range(n) if not ((x>>v)&1))]
samples=[((1<<u)|(1<<v),1) for u,v in edges]+[(x,0) for x in maxind]
V={};clauses=[]
def var(*key):
 if key not in V:V[key]=len(V)+1
 return V[key]
def clause(*xs):clauses.append(list(xs))
def onehot(xs):
 clause(*xs)
 for x,y in itertools.combinations(xs,2):clause(-x,-y)
for t in range(s):
 op=var('op',t)
 for side in [0,1]:onehot([var('sel',t,side,w) for w in range(n+t)])
 for u in range(n+t):
  for v in range(u+1):clause(-var('sel',t,0,u),-var('sel',t,1,v))
 for i,(x,target) in enumerate(samples):
  y=var('val',t,i)
  for side in [0,1]:
   z=var('arg',t,side,i)
   for w in range(n+t):
    sel=var('sel',t,side,w)
    if w<n:clause(-sel,z if ((x>>w)&1) else -z)
    else:
     q=var('val',w-n,i)
     clause(-sel,-z,q);clause(-sel,z,-q)
  u=var('arg',t,0,i);v=var('arg',t,1,i)
  clause(op,-y,u);clause(op,-y,v);clause(op,y,-u,-v)
  clause(-op,y,-u);clause(-op,y,-v);clause(-op,-y,u,v)
  if t==s-1:clause(y if target else -y)
for t in range(s-1):clause(*(var('sel',j,side,n+t) for j in range(t+1,s) for side in [0,1]))
# Dihedral symmetry of a cycle makes the first gate use input zero and one input <= n/2.
clause(var('sel',0,0,0))
clause(*(var('sel',0,1,w) for w in range(1,n//2+1)))
if a.unsafe_and:
 bads=[]
 for t in range(s-1):
  for i,(_,target) in enumerate(samples):
   if target:continue
   b=var('bad',t,i);bads.append(b)
   clause(-b,-var('op',t));clause(-b,var('val',t,i))
 clause(*bads)
print(json.dumps({'n':n,'gates':s,'unsafe':a.unsafe_and,'vars':len(V),'clauses':len(clauses)}),flush=True)
def alarm(signum,frame):raise TimeoutError
signal.signal(signal.SIGALRM,alarm);signal.alarm(a.seconds)
t=time.monotonic();solver=SATSolver(clauses,set(range(1,len(V)+1)),set(),clause_learning='simple')
try:
 model=next(solver._find_model(),None)
 print('result', 'SAT' if model is not None else 'UNSAT','seconds',time.monotonic()-t,'decisions',solver.num_decisions,flush=True)
 if model is not None:
  gates=[]
  for t in range(s):
   op='or' if model.get(var('op',t),False) else 'and'
   ins=[next(w for w in range(n+t) if model.get(var('sel',t,side,w),False)) for side in [0,1]]
   gates.append((op,ins))
  for x in range(1<<n):
   vals=[bool((x>>i)&1) for i in range(n)]
   for op,(u,v) in gates: vals.append((vals[u] and vals[v]) if op=='and' else (vals[u] or vals[v]))
   assert vals[-1] == any(vals[u] and vals[v] for u,v in edges),(x,gates)
  print('WITNESS',gates,flush=True)
except TimeoutError:
 print('TIMEOUT','seconds',time.monotonic()-t,'decisions',solver.num_decisions,flush=True)
finally:signal.alarm(0)
