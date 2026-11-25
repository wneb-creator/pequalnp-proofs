import sys,json,time
from datetime import datetime, timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
k=int(sys.argv[1]);limit=int(sys.argv[2])
n=8
uv=[(0,1),(1,2),(2,7),(0,3),(3,4),(4,7),(0,5),(5,6),(6,7)]
def graph(x):return any((x>>a&1) and (x>>b&1) for a,b in uv)
minimal=[(1<<a)|(1<<b) for a,b in uv]
maxfalse=[x for x in range(1<<n) if not graph(x) and all(graph(x|(1<<v)) for v in range(n) if not x>>v&1)]
assignments=minimal+maxfalse
width=len(assignments)
inputs=[sum(1<<j for j,x in enumerate(assignments) if x>>i&1) for i in range(n)]
target=(1<<len(minimal))-1
s=z3.SolverFor('QF_BV');s.set(timeout=limit)
ones=z3.BitVecVal((1<<width)-1,width)
signals=[z3.BitVecVal(x,width) for x in inputs];selectors=[]
for i in range(k):
 sides=[];masks=[];sels=[]
 for t in range(2):
  bs=[z3.Bool(f's_{i}_{t}_{j}') for j in range(n+i)]
  val=ones;mask=z3.BitVecVal(0,n+i)
  for j,b in enumerate(bs):
   val=val&z3.If(b,signals[j],ones)
   mask=mask|z3.If(b,z3.BitVecVal(1<<j,n+i),z3.BitVecVal(0,n+i))
  s.add(z3.Or(bs));sides.append(val);masks.append(mask);sels.append(bs)
 s.add(z3.ULE(masks[0],masks[1]))
 g=z3.BitVec(f'g_{i}',width);s.add(g==sides[0]|sides[1]);signals.append(g);selectors.append(sels)
outs=[z3.Bool(f'out_{i}') for i in range(n+k)];out=ones
for i,b in enumerate(outs):out=out&z3.If(b,signals[i],ones)
s.add(z3.Or(outs));s.add(out==z3.BitVecVal(target,width))
print(datetime.now(timezone.utc).isoformat(),'theta333','OR budget',k,'assignments',width,'edges',len(minimal),'maxfalse',len(maxfalse),'Z3',z3.get_version_string(),flush=True)
start=time.monotonic();res=s.check();print('RESULT',res,'seconds',round(time.monotonic()-start,3),flush=True)
if res==z3.sat:
 mo=s.model();desc=[];concrete=[sum(1<<x for x in range(1<<n) if x>>v&1) for v in range(n)]
 fullones=(1<<(1<<n))-1
 for i,ss in enumerate(selectors):
  sets=[[j for j,b in enumerate(bs) if z3.is_true(mo.eval(b,model_completion=True))] for bs in ss]
  vals=[]
  for st in sets:
   v=fullones
   for j in st:v&=concrete[j]
   vals.append(v)
  concrete.append(vals[0]|vals[1]);desc.append(sets)
 os=[i for i,b in enumerate(outs) if z3.is_true(mo.eval(b,model_completion=True))]
 actual=fullones
 for i in os:actual&=concrete[i]
 fulltarget=sum(1<<x for x in range(1<<n) if graph(x))
 assert actual==fulltarget
 print(json.dumps(dict(n=n,edges=uv,or_gates=desc,outputs=os,full_truth_verified=True)),flush=True)
else:
 if res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
