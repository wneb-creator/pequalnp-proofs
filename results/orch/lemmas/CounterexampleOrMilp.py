import argparse,itertools,time,json
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
p=argparse.ArgumentParser();p.add_argument('--graph',choices=['c5','theta233','petersen','friendship2'],default='theta233');p.add_argument('--or-gates',type=int,required=True);p.add_argument('--seconds',type=int,default=900);p.add_argument('--pair-only',action='store_true');a=p.parse_args();k=a.or_gates
if a.graph=='theta233':n=7;edges=[(0,2),(2,1),(0,3),(3,4),(4,1),(0,5),(5,6),(6,1)]
elif a.graph=='petersen':
 pairs=list(itertools.combinations(range(5),2));n=10;edges=[(i,j) for i in range(n) for j in range(i+1,n) if not set(pairs[i])&set(pairs[j])]
elif a.graph=='friendship2':n=5;edges=[(0,1),(0,2),(1,2),(0,3),(0,4),(3,4)]
else:n=5;edges=[(i,(i+1)%5) for i in range(5)]
E={frozenset(e) for e in edges}
if a.pair_only:samples=[((1<<u)|(1<<v),int(frozenset((u,v)) in E)) for u,v in itertools.combinations(range(n),2)]+[(1<<v,0) for v in range(n)]+[(0,0)]
else:
 ind=[x for x in range(1<<n) if not any((x>>u)&1 and (x>>v)&1 for u,v in edges)]
 mx=[x for x in ind if all((x|(1<<v)) not in ind for v in range(n) if not ((x>>v)&1))]
 samples=[((1<<u)|(1<<v),1) for u,v in edges]+[(x,0) for x in mx]
V={};ridx=[];cidx=[];data=[];lb=[];ub=[]
def var(key):
 if key not in V:V[key]=len(V)
 return V[key]
def cons(terms,lo=-np.inf,hi=np.inf):
 r=len(lb)
 for q,v in terms.items():ridx.append(r);cidx.append(var(q));data.append(v)
 lb.append(lo);ub.append(hi)
def eq(terms,b):cons(terms,b,b)

def sources(t):return [('false',0)]+[('input',j) for j in range(n)]+[('or',j) for j in range(t)]

def meet(label,t):
 src=sources(t)
 for w in src:var(('sel',label,w))
 for i,(x,target) in enumerate(samples):
  z=('meet',label,i);var(z);bad=[]
  for w in src:
   sel=('sel',label,w)
   if w[0]=='false' or (w[0]=='input' and not ((x>>w[1])&1)):
    bad.append(sel);cons({z:1,sel:1},hi=1)
   elif w[0]=='or':
    q=('orval',w[1],i);b=('bad',label,w[1],i);bad.append(b)
    cons({b:1,sel:-1},hi=0)
    cons({b:1,q:1},hi=1)
    cons({b:1,sel:-1,q:1},lo=0)
    cons({z:1,b:1},hi=1)
  terms={b:1 for b in bad};terms[z]=1;cons(terms,lo=1)
 return src

for t in range(k):
 src=meet((t,0),t);meet((t,1),t)
 # Commutativity: order the bitmasks of the two meet operands.
 terms={}
 for j,w in enumerate(src):terms[('sel',(t,0),w)]=1<<j;terms[('sel',(t,1),w)]=-(1<<j)
 cons(terms,hi=0)
 for i,_ in enumerate(samples):
  y=('orval',t,i);u=('meet',(t,0),i);v=('meet',(t,1),i)
  cons({y:1,u:-1},lo=0);cons({y:1,v:-1},lo=0);cons({y:1,u:-1,v:-1},hi=0)
meet('output',k)
for i,(_,target) in enumerate(samples):eq({('meet','output',i):1},target)
A=coo_matrix((np.array(data,dtype=float),(np.array(ridx,dtype=np.int32),np.array(cidx,dtype=np.int32))),shape=(len(lb),len(V))).tocsc()
print(json.dumps({'graph':a.graph,'n':n,'edges':edges,'or_gates':k,'and_gates':'unbounded via meet closure','pair_only':a.pair_only,'samples':samples,'variables':len(V),'constraints':len(lb)}),flush=True)
tm=time.monotonic();res=milp(np.zeros(len(V)),integrality=np.ones(len(V)),bounds=Bounds(np.zeros(len(V)),np.ones(len(V))),constraints=LinearConstraint(A,np.array(lb),np.array(ub)),options={'time_limit':a.seconds,'disp':True})
print('time',time.monotonic()-tm,'status',res.status,'message',res.message,flush=True)
if res.x is not None:
 choices={}
 for t in range(k):
  for side in [0,1]:choices[str((t,side))]=[w for w in sources(t) if res.x[V[('sel',(t,side),w)]]>.5]
 choices['output']=[w for w in sources(k) if res.x[V[('sel','output',w)]]>.5]
 def calc(x):
  ovs=[]
  def m(ws):return all(False if typ=='false' else bool((x>>j)&1) if typ=='input' else ovs[j] for typ,j in ws)
  for t in range(k):ovs.append(m(choices[str((t,0))]) or m(choices[str((t,1))]))
  return m(choices['output'])
 for x in range(1<<n):
  if not a.pair_only or x.bit_count()<=2:assert calc(x)==any((x>>u)&1 and (x>>v)&1 for u,v in edges),(x,choices)
 print('WITNESS',json.dumps(choices),flush=True)
