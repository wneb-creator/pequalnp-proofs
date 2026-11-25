import itertools
import json
import math
import random
import resource
import sys
import time
from collections import defaultdict
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_array

OUT=Path('/tmp/oec/pequalnp-pilot-46/gap-2585/symbolic_p4')

def nofour(P,L,E):
 E=set(E)
 return all(sum((a,l) in E and (b,l) in E for l in range(L))<=1 for a in range(P) for b in range(a))

def mincover(P,L,E):
 n=P+L
 return next(k for k in range(n+1) if any(all((m>>a&1) or (m>>(P+b)&1) for a,b in E) for m in range(1<<n) if m.bit_count()==k))

def solve(name,P,L,E,seconds=5):
 t=time.monotonic();E=sorted(set(map(tuple,E)));assert nofour(P,L,E)
 n=P+L;baseline=len(E)+mincover(P,L,E)-1
 inputs=[sum(1<<x for x in range(1<<n) if x>>i&1) for i in range(n)]
 input_of={f:i for i,f in enumerate(inputs)}
 actions=[];known_actions=set();producers=defaultdict(list);blocks={}
 def add_action(op,a,b):
  if a>b:a,b=b,a
  f=(a|b) if op else (a&b)
  if f in input_of or f==a or f==b:return f
  k=(op,a,b,f)
  if k not in known_actions:
   known_actions.add(k);producers[f].append(len(actions));actions.append(k)
  return f
 ors={frozenset([i]):inputs[i] for i in range(n)}
 def orset(S):
  S=frozenset(S)
  if S in ors:return ors[S]
  v=sorted(S);f=0
  for i in v:f|=inputs[i]
  ors[S]=f
  # All binary trees for this OR set, with commutative partitions deduplicated.
  for mask in range(1,1<<len(v)):
   if not(mask&1) or mask==(1<<len(v))-1:continue
   A=[v[i] for i in range(len(v)) if mask>>i&1];B=[v[i] for i in range(len(v)) if not(mask>>i&1)]
   add_action(1,orset(A),orset(B))
  return f
 edges=[(a,P+b) for a,b in E]
 for v in range(n):
  N=[b if a==v else a for a,b in edges if a==v or b==v]
  for k in range(1,len(N)+1):
   for S in itertools.combinations(N,k):
    f=add_action(0,inputs[v],orset(S))
    blocks[f]=frozenset(i for i,(a,b) in enumerate(edges) if (a==v and b in S) or (b==v and a in S))
 p4count=0
 for p,l in E:
  for pp in range(P):
   if pp==p or (pp,l) not in E:continue
   for ll in range(L):
    if ll==l or (p,ll) not in E:continue
    assert (pp,ll) not in E
    clauses=[frozenset([p,pp]),frozenset([P+l,P+ll]),frozenset([p,P+l])]
    cv=[orset(s) for s in clauses]
    expected=0;covered=frozenset(E.index(e) for e in [(p,l),(pp,l),(p,ll)])
    for ei in covered:
     a,b=edges[ei];expected|=inputs[a]&inputs[b]
    for k in range(3):
     i,j=[a for a in range(3) if a!=k]
     mid=add_action(0,cv[i],cv[j])
     common=clauses[i]&clauses[j]
     if len(common)==1:
      shared=next(iter(common));a=next(iter(clauses[i]-common));b=next(iter(clauses[j]-common))
      edge=add_action(0,inputs[a],inputs[b]);assert add_action(1,inputs[shared],edge)==mid
     f=add_action(0,mid,cv[k]);assert f==expected
     blocks[f]=covered
    p4count+=1
 # Binary action variables and selected-output variables. Every used noninput
 # function must have exactly one selected producing action.
 block_items=list(blocks.items());A=len(actions);N=A+len(block_items)
 ri=[];ci=[];data=[];lo=[];hi=[]
 def constraint(coeff,lower=-np.inf,upper=np.inf):
  row=len(lo);lo.append(lower);hi.append(upper)
  for col,val in coeff.items():
   if val:ri.append(row);ci.append(col);data.append(float(val))
 for f,ids in producers.items():constraint({i:1 for i in ids},upper=1)
 for i,(op,a,b,f) in enumerate(actions):
  for parent in set([a,b]):
   if parent not in input_of:
    d={i:1}
    for j in producers[parent]:d[j]=d.get(j,0)-1
    constraint(d,upper=0)
 for bi,(f,covered) in enumerate(block_items):
  d={A+bi:1}
  for j in producers[f]:d[j]=d.get(j,0)-1
  constraint(d,upper=0)
 for ei in range(len(E)):
  constraint({A+bi:1 for bi,(_,covered) in enumerate(block_items) if ei in covered},lower=1)
 constraint({i:1 for i in range(N)},upper=baseline)
 mat=coo_array((data,(np.array(ri,dtype=np.int32),np.array(ci,dtype=np.int32))),shape=(len(lo),N)).tocsc()
 print('START',name,'P',P,'L',L,'edges',len(E),'baseline',baseline,'p4',p4count,'actions',A,'blocks',len(block_items),flush=True)
 result=milp(np.ones(N),integrality=np.ones(N),bounds=Bounds(np.zeros(N),np.ones(N)),constraints=LinearConstraint(mat,lo,hi),options={'time_limit':seconds,'mip_rel_gap':0})
 record={'name':name,'P':P,'L':L,'edges':E,'baseline':baseline,'solver_status':int(result.status),'solver_message':result.message,'seconds':time.monotonic()-t,'p4_templates':p4count,'actions':A,'blocks':len(block_items),'lower_bound':None if result.mip_dual_bound is None else float(result.mip_dual_bound)-1}
 if result.x is not None:
  selected={f:next((i for i in ids if result.x[i]>.5),None) for f,ids in producers.items()}
  gates=[];wire=dict(input_of);visiting=set()
  def emit(f):
   if f in wire:return wire[f]
   assert f not in visiting,'cyclic function support'
   visiting.add(f);i=selected[f];assert i is not None
   op,a,b,ff=actions[i];assert ff==f
   aa,bb=emit(a),emit(b);gates.append((op,aa,bb));wire[f]=n+len(gates)-1
   visiting.remove(f);return wire[f]
  outputs=[emit(f) for bi,(f,_) in enumerate(block_items) if result.x[A+bi]>.5]
  output=outputs[0]
  for w in outputs[1:]:gates.append((1,output,w));output=n+len(gates)-1
  errors=0
  for x in range(1<<n):
   values=[bool(x>>i&1) for i in range(n)]
   for op,a,b in gates:values.append((values[a] or values[b]) if op else (values[a] and values[b]))
   expect=any((x>>a&1) and (x>>b&1) for a,b in edges)
   errors+=values[output]!=expect
  assert errors==0
  record.update(size=len(gates),gates=gates,output=output,full_truth_errors=errors,full_truth_assignments=1<<n,improvement=baseline-len(gates))
 print('RESULT',json.dumps({k:v for k,v in record.items() if k not in ['edges','gates']}),flush=True)
 (OUT/(name+'.json')).write_text(json.dumps(record,indent=2)+'\n')
 return record

def family():
 yield 'k4-incidence',4,6,[(v,e) for e,ab in enumerate(itertools.combinations(range(4),2)) for v in ab]
 fano=[(p,l) for p in range(7) for l in range(7) if (p-l)%7 in [0,1,3]]
 for deleted_line in [0,1]:
  points=[p for p in range(7) if p!=0];lines=[l for l in range(7) if l!=deleted_line]
  yield 'fano-delete-'+str(deleted_line),6,6,[(points.index(p),lines.index(l)) for p,l in fano if p and l!=deleted_line]
 rng=random.Random(2585)
 seen=set()
 for trial in range(12):
  P=L=6;E=[];pairs=list(itertools.product(range(P),range(L)));rng.shuffle(pairs)
  for e in pairs:
   if sum(a==e[0] for a,b in E)>=4 or sum(b==e[1] for a,b in E)>=4:continue
   if nofour(P,L,E+[e]):E.append(e)
  key=tuple(sorted(E))
  if key not in seen:
   seen.add(key);yield 'greedy66-'+str(trial),P,L,E

if __name__=='__main__':
 resource.setrlimit(resource.RLIMIT_AS,(900*1024**2,900*1024**2))
 start=int(sys.argv[1]);count=int(sys.argv[2]);seconds=float(sys.argv[3])
 for name,P,L,E in list(family())[start:start+count]:
  rec=solve(name,P,L,E,seconds)
  if rec.get('improvement',0)>0:
   print('FULL_TRUTH_WITNESS',name,flush=True);break
