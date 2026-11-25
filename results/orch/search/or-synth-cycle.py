import sys,json,time
from datetime import datetime, timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
p=int(sys.argv[1]);n=2*p;k=2*p-2;limit=int(sys.argv[2])
width=1<<n
inputs=[sum(1<<x for x in range(width) if x>>i&1) for i in range(n)]
edges=[(a,a) for a in range(p)]+[(a,(a+1)%p) for a in range(p)]
uv=[(a,p+b) for a,b in edges]
target=0
for a,b in uv:target|=inputs[a]&inputs[b]
neighbors=[[b for a,b in uv if a==v]+[a for a,b in uv if b==v] for v in range(n)]
s=z3.Solver();s.set(timeout=limit)
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
outs=[z3.Bool(f'out_{i}') for i in range(k)];out=ones
for i,b in enumerate(outs):out=out&z3.If(b,signals[n+i],ones)
s.add(out==z3.BitVecVal(target,width))
stars=[]
for vs in neighbors:
 sig=inputs[vs[0]]|inputs[vs[1]]
 stars.append(z3.Or([g==z3.BitVecVal(sig,width) for g in signals[n:]]))
for a,b in uv:s.add(z3.Or(stars[a],stars[b]))
print(datetime.now(timezone.utc).isoformat(),'cycle',n,'OR budget',k,'all star witnesses',flush=True)
start=time.monotonic();res=s.check();print('RESULT',res,'seconds',round(time.monotonic()-start,3),flush=True)
if res==z3.sat:
 mo=s.model();desc=[];concrete=inputs[:]
 for i,ss in enumerate(selectors):
  sets=[[j for j,b in enumerate(bs) if z3.is_true(mo.eval(b,model_completion=True))] for bs in ss]
  vals=[]
  for st in sets:
   v=(1<<width)-1
   for j in st:v&=concrete[j]
   vals.append(v)
  concrete.append(vals[0]|vals[1]);desc.append(sets)
 os=[i for i,b in enumerate(outs) if z3.is_true(mo.eval(b,model_completion=True))]
 actual=(1<<width)-1
 for i in os:actual&=concrete[n+i]
 assert actual==target
 print(json.dumps(dict(p=p,edges=edges,gates=desc,outputs=os)),flush=True)
else:
 if res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
