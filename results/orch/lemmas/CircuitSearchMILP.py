import sys,time,json
from itertools import combinations_with_replacement
from pathlib import Path
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_array

p=int(sys.argv[1]); l=int(sys.argv[2]); k=int(sys.argv[3]); graph=sys.argv[4]; limit=float(sys.argv[5])
n=p+l
if graph=='cycle6': E={(0,3),(0,4),(1,4),(1,5),(2,5),(2,3)}
elif graph=='path6': E={(0,3),(1,3),(1,4),(2,4),(2,5)}
else: E={tuple(map(int,e.split(','))) for e in graph.split(';')}
assert p >= 0 and l >= 0 and k > 0
assert all(0 <= a < p and p <= b < n for a,b in E), 'edges outside fixed bipartition'
assert all(not all((a,b) in E for a in (a0,a1) for b in (b0,b1))
           for a0 in range(p) for a1 in range(a0+1,p)
           for b0 in range(p,n) for b1 in range(b0+1,n)), 'graph has a four-cycle'
def target(x): return any(x>>a&1 and x>>b&1 for a,b in E)
positive=[(1<<a)|(1<<b) for a,b in E]
negative=[x for x in range(1<<n) if not target(x) and all(target(x|(1<<v)) for v in range(n) if not (x>>v&1))]
inputs=positive+negative
# Last two dimensions record structural reach of point and line inputs.
m=len(inputs)+2
wire_vars={(g,d):g*m+d for g in range(k) for d in range(m)}
nextvar=k*m; choices=[]
for g in range(k):
 row=[]
 for a,b in combinations_with_replacement(range(n+g),2):
  for op in range(2):
   row.append((nextvar,a,b,op)); nextvar+=1
 choices.append(row)
dirty=[]
if len(sys.argv)>6 and sys.argv[6]=='dirty':
 for g in range(k):
  for d in range(len(positive),len(inputs)):
   dirty.append((nextvar,g,d)); nextvar+=1
R=[];C=[];V=[];lo=[];hi=[]
def add(coeff,lower=-np.inf,upper=np.inf):
 idx=len(lo)
 for c,v in coeff.items():
  if v: R.append(idx);C.append(c);V.append(float(v))
 lo.append(float(lower));hi.append(float(upper))
def expr(items):
 coeff={};const=0
 for wire,d,mult in items:
  if wire<n:
   v=(inputs[d]>>wire&1) if d<len(inputs) else (wire<p if d==len(inputs) else wire>=p)
   const+=int(v)*mult
  else:
   ix=wire_vars[wire-n,d];coeff[ix]=coeff.get(ix,0)+mult
 return coeff,const
# impose sum terms <= rhs, gated by selector s.
def gated(s,items,rhs):
 coeff,c=expr(items); coeff[s]=coeff.get(s,0)+3
 add(coeff,upper=rhs-c+3)
for g,cs in enumerate(choices):
 add({s:1 for s,a,b,op in cs},1,1)
 # No two-color OR reach.
 add({wire_vars[g,m-2]:1,wire_vars[g,m-1]:1},upper=1)
 for s,a,b,op in cs:
  z=n+g
  for d in range(m):
   if d>=len(inputs) and op==0:
    gated(s,[(z,d,1)],0)
   elif op==0:
    gated(s,[(z,d,1),(a,d,-1)],0)
    gated(s,[(z,d,1),(b,d,-1)],0)
    gated(s,[(a,d,1),(b,d,1),(z,d,-1)],1)
   else:
    gated(s,[(a,d,1),(z,d,-1)],0)
    gated(s,[(b,d,1),(z,d,-1)],0)
    gated(s,[(z,d,1),(a,d,-1),(b,d,-1)],0)
for g in range(k-1):
 add({s:1 for h in range(g+1,k) for s,a,b,op in choices[h] if n+g in (a,b)},lower=1)
if dirty:
 add({v:1 for v,g,d in dirty},lower=1)
 for v,g,d in dirty:
  add({v:1,wire_vars[g,d]:-1},upper=0)
  coeff={v:1}
  coeff.update({s:-1 for s,a,b,op in choices[g] if op==0})
  add(coeff,upper=0)
for d in range(len(inputs)):
 add({wire_vars[k-1,d]:1},int(d<len(positive)),int(d<len(positive)))
print(json.dumps({'n':n,'k':k,'E':sorted(E),'positive':positive,'negative':negative,'vars':nextvar,'rows':len(lo)}),flush=True)
A=coo_array((np.array(V), (np.array(R,dtype=np.int32),np.array(C,dtype=np.int32))),shape=(len(lo),nextvar)).tocsc()
t=time.time()
res=milp(np.zeros(nextvar),integrality=np.ones(nextvar),bounds=Bounds(0,1),constraints=LinearConstraint(A,np.array(lo),np.array(hi)),options={'time_limit':limit,'disp':True})
print('result',res.message,'elapsed',time.time()-t,flush=True)
if res.x is not None:
 gates=[]
 for cs in choices:
  picked=[(a,b,op) for s,a,b,op in cs if res.x[s]>.5]
  assert len(picked)==1
  gates.append(picked[0])
 print('gates',gates,flush=True)
 for g,(a,b,op) in enumerate(gates): assert 0 <= a <= b < n+g and op in (0,1), 'invalid gate'
 dirty_witnesses={}
 for x in range(1<<n):
  values=[x>>v&1 for v in range(n)]
  for a,b,op in gates: values.append(values[a]|values[b] if op else values[a]&values[b])
  assert bool(values[-1])==target(x),(x,values[-1])
  if not target(x):
   for g,(a,b,op) in enumerate(gates):
    if op==0 and values[n+g]: dirty_witnesses.setdefault(g,x)
 if dirty: assert dirty_witnesses, 'requested dirty AND absent'
 print('dirty_AND_witnesses',dirty_witnesses,flush=True)
 reach=[(1 if v<p else 2) for v in range(n)]
 for a,b,op in gates:
  r=reach[a]|reach[b] if op else 0
  assert r!=3
  reach.append(r)
 print('FULL TRUTH TABLE AND COLOR VALIDATED',flush=True)
