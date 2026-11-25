import sys,json,time
from pathlib import Path
from datetime import datetime,timezone
sys.path.insert(0,'/tmp/oec/pequalnp-pilot-152/z3-python')
import z3
spec=json.loads(Path(sys.argv[1]).read_text()); k=int(sys.argv[2]); limit=int(sys.argv[3])
p=spec['p'];q=spec['q'];n=p+q;label=spec['label'];edges=[tuple(e) for e in spec['edges']]
uv=[(a,p+b) for a,b in edges];fullwidth=1<<n;allmask=fullwidth-1
neighbors=[sum(1<<w for a,b in uv for w in ([b] if a==v else [a] if b==v else [])) for v in range(n)]
def target(x):return any(x>>a&1 and x>>b&1 for a,b in uv)
mins=[(1<<a)|(1<<b) for a,b in uv]
maxzeros=[x for x in range(fullwidth) if not target(x) and all(x>>v&1 or x&neighbors[v] for v in range(n))]
starrows=[(v,Q) for v,N in enumerate(neighbors) for Q in range(fullwidth) if Q&N==Q and Q.bit_count()>=2]
patterns=sorted(set(mins+maxzeros+[1<<i for i in range(n)]+[allmask^Q for v,Q in starrows]));width=len(patterns)
indexes={x:j for j,x in enumerate(patterns)}
inputs=[sum(1<<j for j,x in enumerate(patterns) if x>>i&1) for i in range(n)]
mask=sum(1<<indexes[x] for x in mins+maxzeros);expected=sum(1<<indexes[x] for x in mins)
s=z3.SolverFor('QF_BV');s.set(timeout=limit)
ones=z3.BitVecVal((1<<width)-1,width);signals=[z3.BitVecVal(v,width) for v in inputs];selectors=[];keys=[]
for i in range(k):
 sides=[];masks=[];sels=[]
 for side in range(2):
  bs=[z3.Bool(f's_{i}_{side}_{j}') for j in range(n+i)]
  val=ones;maskval=z3.BitVecVal(0,n+k)
  for j,b in enumerate(bs):
   val=val&z3.If(b,signals[j],ones)
   maskval=maskval|z3.If(b,z3.BitVecVal(1<<j,n+k),z3.BitVecVal(0,n+k))
  s.add(z3.Or(bs));sides.append(val);masks.append(maskval);sels.append(bs)
 s.add(z3.ULE(masks[0],masks[1]))
 key=z3.Concat(*masks)
 if i:s.add(z3.Or(sels[0][-1],sels[1][-1],z3.ULE(keys[-1],key)))
 keys.append(key)
 g=z3.BitVec(f'g_{i}',width);s.add(g==sides[0]|sides[1]);signals.append(g);selectors.append(sels)
outs=[z3.Bool(f'out_{i}') for i in range(k)];out=ones
for i,b in enumerate(outs):out=out&z3.If(b,signals[n+i],ones)
s.add(z3.Or(outs));s.add(out&z3.BitVecVal(mask,width)==z3.BitVecVal(expected,width))
stars=[]
for v,Q in starrows:
 hits=[]
 for g in signals[n:]:
  hits.append(z3.And(*[z3.Extract(indexes[1<<i],indexes[1<<i],g)==1 for i in range(n) if Q>>i&1],z3.Extract(indexes[allmask^Q],indexes[allmask^Q],g)==0))
 stars.append(z3.Or(hits))
for a,b in uv:s.add(z3.Or([stars[r] for r,(v,Q) in enumerate(starrows) if (v==a and Q>>b&1) or (v==b and Q>>a&1)]))
Path(f'/tmp/oec/pequalnp-pilot-152/or-synth-{label}-{k}.smt2').write_text(s.to_smt2())
print(datetime.now(timezone.utc).isoformat(),'GRAPH',label,'OR budget',k,'truth bits',width,'maxzeros',len(maxzeros),'all star witnesses',flush=True)
start=time.monotonic();res=s.check();print('RESULT',res,'seconds',round(time.monotonic()-start,3),flush=True)
if res==z3.sat:
 mo=s.model();desc=[]
 full=[sum(1<<x for x in range(fullwidth) if x>>i&1) for i in range(n)];fullones=(1<<fullwidth)-1
 for i,ss in enumerate(selectors):
  sets=[[j for j,b in enumerate(bs) if z3.is_true(mo.eval(b,model_completion=True))] for bs in ss];vals=[]
  for st in sets:
   value=fullones
   for j in st:value&=full[j]
   vals.append(value)
  full.append(vals[0]|vals[1]);desc.append(sets)
 os=[i for i,b in enumerate(outs) if z3.is_true(mo.eval(b,model_completion=True))]
 actual=fullones
 for i in os:actual&=full[n+i]
 assert actual==sum(1<<x for x in range(fullwidth) if target(x))
 ids=[]
 for v,Q in starrows:
  sf=0
  for i in range(n):
   if Q>>i&1:sf|=full[i]
  ids.append([j for j in range(k) if full[n+j]==sf])
 assert all(any(ids[r] for r,(v,Q) in enumerate(starrows) if (v==a and Q>>b&1) or (v==b and Q>>a&1)) for a,b in uv)
 data=dict(p=p,q=q,edges=edges,gates=desc,outputs=os,starrows=starrows,star_witnesses=ids)
 print('VERIFIED_FULL_TRUTH_TABLE',json.dumps(data),flush=True)
 Path(f'/tmp/oec/pequalnp-pilot-152/or-synth-{label}-{k}-model.json').write_text(json.dumps(data,indent=2))
else:
 if res==z3.unknown:print('REASON',s.reason_unknown(),flush=True)
print(s.statistics(),flush=True)
