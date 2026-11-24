import json,sys
from pathlib import Path
T=int(sys.argv[1],0);k=int(sys.argv[2]);prefix=Path(sys.argv[3]);full=len(sys.argv)>4 and sys.argv[4]=='full'
assert 0<T<2**32-1 and 0<k<20
num_selectors=7*k+k*(k-1)//2
wstart=1;astart=1+32*(7+k);bstart=astart+num_selectors;opstart=bstart+num_selectors
avstart=opstart+3*k;bvstart=avstart+32*k;ostart=bvstart+32*k
num_vars=ostart+(7+k)-1
W=lambda w,r:wstart+32*w+r
A=lambda j,i:astart+7*j+j*(j-1)//2+i
B=lambda j,i:bstart+7*j+j*(j-1)//2+i
OP=lambda j,t:opstart+3*j+t
AV=lambda j,r:avstart+32*j+r
BV=lambda j,r:bvstart+32*j+r
O=lambda i:ostart+i
clauses=[]
def add(*xs):clauses.append(list(xs))
def one(xs):
 add(*xs)
 for a,x in enumerate(xs):
  for y in xs[a+1:]:add(-x,-y)
for w in range(7):
 for r in range(32):add(W(w,r) if (bool(r>>w&1) if w<5 else w==6) else -W(w,r))
for j in range(k):
 one([A(j,i) for i in range(7+j)]);one([B(j,i) for i in range(7+j)]);one([OP(j,t) for t in range(3)])
 for sel,val in [(A,AV),(B,BV)]:
  for i in range(7+j):
   for r in range(32):
    add(-sel(j,i),-W(i,r),val(j,r));add(-sel(j,i),W(i,r),-val(j,r))
 for r in range(32):
  a,b,w=AV(j,r),BV(j,r),W(7+j,r)
  add(-OP(j,0),-a,-b,w);add(-OP(j,0),a,-w);add(-OP(j,0),b,-w)
  add(-OP(j,1),a,b,-w);add(-OP(j,1),-a,w);add(-OP(j,1),-b,w)
  add(-OP(j,2),a,w);add(-OP(j,2),-a,-w)
if not full:
 for i in range(k):
  for j in range(i+1,k):add(-OP(i,2),-OP(j,2))
one([O(i) for i in range(7+k)])
for i in range(7+k):
 for r in range(32):add(-O(i),W(i,r) if T>>r&1 else -W(i,r))
assert all(0<abs(x)<=num_vars for c in clauses for x in c)
dimacs=f'p cnf {num_vars} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
prefix.with_suffix('.cnf').write_text(dimacs)
layout={'target':hex(T),'budget':k,'basis':'and/or/not','at_most_one_not':not full,'base_wires':'0..4 inputs,5=false,6=true','wire_truth':'W(w,r)=1+32*w+r','A':'astart+7*j+j*(j-1)//2+i','B':'bstart+7*j+j*(j-1)//2+i','op':'opstart+3*j+t where0and1or2not','Aval':'avstart+32*j+r','Bval':'bvstart+32*j+r','output':'ostart+i','offsets':{'astart':astart,'bstart':bstart,'opstart':opstart,'avstart':avstart,'bvstart':bvstart,'ostart':ostart},'variables':num_vars,'clauses':len(clauses),'dimacs_bytes':len(dimacs),'scope':'Fixed k slots, freeconstants, arbitrary bounded A/B selectors, onehot output overall wires, no duplicate/live/order constraints.'}
prefix.with_suffix('.layout.json').write_text(json.dumps(layout,indent=2)+'\n')
print(json.dumps(layout),flush=True)
